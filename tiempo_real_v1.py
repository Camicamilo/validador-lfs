r"""
tiempo_real_v1.py - Fase 6: validacion en tiempo real, limites e instrumentacion

Que hace:
  1. Flujo: una SESION de validacion por bloques. Se le van dando pedazos del
     documento (como llegan por la red) y en cualquier momento dice en que va:
     bytes leidos, altura de la pila, errores encontrados (con su ruta JSON
     Pointer y la posicion en bytes). Corta si se pasa de un limite de
     profundidad, de tamano o de tiempo. Nunca guarda el documento.
  2. Instrumentacion: mide cada motor con las mismas columnas
        MB/s, ciclos por byte, pico de memoria, asignaciones, profundidad de
        pila y tamano del automata (estados y transiciones).
  3. Linea base: DOM + validador generico (json.loads + jsonschema), que es lo
     que haria un programa normal: armar TODO el arbol en memoria y luego revisar.
  4. Pruebas de bombeo: documentos u v^k x y^k z con k creciente.

Motores que se comparan:
  dpda-python   el interprete de la Fase 4 (automata_v2)
  dpda-c        el validador en C generado en la Fase 5
  dpda-rust     el validador en Rust generado en la Fase 5
  dom           la linea base

Uso:
  python tiempo_real_v1.py            -> pruebas
  python tiempo_real_v1.py banco      -> corre el banco, escribe salida/metricas.json y metricas.svg
"""
import sys
import os
import json
import time
import tempfile
import tracemalloc
import queue
import threading
import automata_v2 as A
import xml_v1 as X
from lexer_v4 import Lexer, ErrorLexico, Token
import generador_v1 as G
import payloads_v1 as P

try:
    import jsonschema
except ImportError:                                  # la linea base queda solo con json.loads
    jsonschema = None

# mensajes de los codigos de error que devuelve el validador nativo
MENSAJES = {
    "tipo": "el tipo no es el que pide el esquema", "nunca": "aqui el esquema no admite ningun valor",
    "enum": "el valor no esta en la lista permitida (enum)", "const": "el valor no es la constante pedida",
    "minimum": "numero menor que el minimo", "maximum": "numero mayor que el maximo",
    "minLength": "cadena mas corta que el minimo", "maxLength": "cadena mas larga que el maximo",
    "dup": "clave repetida en el objeto", "prohibida": "propiedad no permitida (additionalProperties)",
    "requeridos": "faltan propiedades obligatorias", "minItems": "el arreglo tiene menos elementos que el minimo",
    "maxItems": "el arreglo tiene mas elementos que el maximo", "sintaxis": "mal formado: sintaxis",
    "lexico": "mal formado: simbolo no reconocido", "incompleto": "el documento termino antes de tiempo",
    "sobra": "sobra texto despues del documento", "profundidad": "limite de profundidad superado",
    "tamano": "limite de tamano superado", "tiempo": "limite de tiempo superado",
    "numero_largo": "numero demasiado largo",
}


# =========================================================================
# 1. SESION DE STREAMING
# =========================================================================
class Flujo:
    """Validacion por bloques. alimentar(bloque) se puede llamar las veces que se
    quiera; terminar() da el veredicto. Da lo mismo que automata_v2.validar."""

    def __init__(self, compilado, parar=False, max_prof=None, max_bytes=None, max_ms=None, memoria_fija=False):
        M = compilado.M if isinstance(compilado, A.Compilado) else compilado
        self.lx = Lexer("json")
        self.v = A.Validador(M, parar, max_prof, False, memoria_fija)
        self.max_bytes, self.max_ms = max_bytes, max_ms
        self.bytes, self.ms, self.bloques, self.cerrado = 0, 0.0, 0, False

    def _fin(self):
        return bool(self.cerrado or self.v.terminado or (self.v.parar and self.v.errores))

    def _lexico(self, e):
        self.v.alimentar(self.lx.parcial)             # los tokens completos antes del error si cuentan
        if not self._fin():
            self.v._mal_formado(f"mal formado (lexico): {e}", Token("ERROR", "", e.linea, e.columna, e.pos))
        self.cerrado = True

    def alimentar(self, bloque):
        t0 = time.perf_counter()
        if not self._fin():
            sobra = self.max_bytes is not None and self.bytes + len(bloque) > self.max_bytes
            if sobra:
                bloque = bloque[:self.max_bytes - self.bytes]
            self.bytes += len(bloque)
            self.bloques += 1
            try:
                self.v.alimentar(self.lx.alimentar(bloque))
            except ErrorLexico as e:
                self._lexico(e)
            self.ms += (time.perf_counter() - t0) * 1000
            if not self._fin():
                if sobra:
                    self.v._limite(f"limite de tamano de {self.max_bytes} bytes superado")
                    self.cerrado = True
                elif self.max_ms is not None and self.ms > self.max_ms:
                    self.v._limite(f"limite de tiempo de {self.max_ms} ms superado")
                    self.cerrado = True
        return self.estado()

    def estado(self):
        v = self.v
        return {"bytes": self.bytes, "bloques": self.bloques, "pasos": v.pasos, "estado": v.q,
                "pila": len(v.pila), "pila_max": v.prof_max, "violaciones": v.violaciones,
                "costo": v.costo, "ms": round(self.ms, 3), "terminado": self._fin(),
                "errores": list(v.errores)}

    def terminar(self):
        if not self._fin():
            try:
                self.v.alimentar(self.lx.terminar())
            except ErrorLexico as e:
                self._lexico(e)
        self.cerrado = True
        return self.v.terminar()


class _Abortar(Exception):
    pass


class FlujoXML:
    """Lo mismo para XML. El validador de xml_v1 PIDE los tokens (es un generador), asi
    que corre en un hilo: cada alimentar() le entrega un bloque y espera a que lo consuma."""

    def __init__(self, M, parar=False, max_prof=None, max_bytes=None):
        self.v = X.ValidadorXML(M, parar, max_prof, False)
        self.max_bytes, self.limite = max_bytes, None
        self.bytes, self.ms, self.bloques = 0, 0.0, 0
        self.cola, self.pide, self.fin = queue.Queue(), threading.Event(), threading.Event()
        threading.Thread(target=self._trabajo, daemon=True).start()
        self.pide.wait()

    def _tokens(self):
        lx = X.LexerXML()
        while True:
            self.pide.set()                           # "ya consumi todo: denme otro bloque"
            bloque = self.cola.get()
            if bloque is None:
                break
            if bloque is False:
                raise _Abortar()
            try:
                yield from lx.alimentar(bloque)
            except ErrorLexico:
                yield from lx.parcial
                raise
        yield from lx.terminar()

    def _trabajo(self):
        v = self.v
        try:
            for ev, dato, tok in X.eventos(self._tokens()):
                v.evento(ev, dato, tok)
                if v.mal_formado or (v.parar and v.errores):
                    break
        except (X.ErrorXML, ErrorLexico) as e:
            v.mal_formado = True
            v._violar(f"mal formado: {e}", None, v._ruta())
        except _Abortar:
            pass
        self.fin.set()
        self.pide.set()

    def _dar(self, bloque):
        self.pide.clear()
        self.cola.put(bloque)
        self.pide.wait()

    def alimentar(self, bloque):
        t0 = time.perf_counter()
        if not self.fin.is_set():
            sobra = self.max_bytes is not None and self.bytes + len(bloque) > self.max_bytes
            if sobra:
                bloque = bloque[:self.max_bytes - self.bytes]
            self.bytes += len(bloque)
            self.bloques += 1
            self._dar(bloque)
            if sobra and not self.fin.is_set():
                self.limite = f"limite de tamano de {self.max_bytes} bytes superado"
                self._dar(False)
                self.v.mal_formado = True
                self.v._violar(self.limite, None, self.v._ruta())
        self.ms += (time.perf_counter() - t0) * 1000
        return self.estado()

    def estado(self):
        v = self.v
        return {"bytes": self.bytes, "bloques": self.bloques, "pasos": v.pasos, "estado": v.q,
                "pila": len(v.pila), "pila_max": v.prof_max, "violaciones": len(v.errores),
                "costo": v.costo, "ms": round(self.ms, 3), "terminado": self.fin.is_set(),
                "errores": list(v.errores)}

    def terminar(self):
        if not self.fin.is_set():
            self._dar(None)
            self.fin.wait()
        r = X.ResultadoXML(self.v)
        r.limite = self.limite
        return r


# =========================================================================
# 2. INSTRUMENTACION: todos los motores devuelven las mismas columnas
# =========================================================================
def _ghz():
    """Frecuencia del procesador, para ESTIMAR ciclos = nanosegundos x GHz."""
    try:
        for linea in open("/proc/cpuinfo"):
            if linea.startswith("cpu MHz"):
                return float(linea.split(":")[1]) / 1000
    except OSError:
        pass
    return None


def _fila(motor, valido, mal, n, ns, mem, asig, pila, estados, trans, ciclos=None, nota="", fallo=None):
    ghz = _ghz()
    if ciclos is None and ghz and n:
        ciclos = round(ns * ghz / n, 1)
    return {"motor": motor, "valido": valido, "mal_formado": mal, "bytes": n, "ms": round(ns / 1e6, 3),
            "mb_s": round(n / (ns / 1e9) / 1e6, 3) if ns else None, "ciclos_byte": ciclos,
            "mem_pico": mem, "asignaciones": asig, "pila_max": pila, "estados": estados,
            "transiciones": trans, "nota": nota, "fallo": fallo}


def medir_python(compilado, datos, bloque=4096, memoria=True, **limites):
    """El interprete: una pasada para el tiempo y otra (con tracemalloc) para la memoria.
    Su memoria depende del BLOQUE (los tokens de un bloque) y de la pila, no del documento."""
    def pasada():
        f = Flujo(compilado, **limites)
        for i in range(0, len(datos), bloque):
            if f.alimentar(datos[i:i + bloque])["terminado"]:
                break
        return f.terminar()
    t0 = time.perf_counter_ns()
    r = pasada()
    ns = time.perf_counter_ns() - t0
    mem = None
    if memoria:
        tracemalloc.start()
        pasada()
        mem = tracemalloc.get_traced_memory()[1]
        tracemalloc.stop()
    t = compilado.M.tamano()
    return _fila("dpda-python", r.valido, r.mal_formado, len(datos), ns, mem, None, r.prof_max,
                 t["estados"], t["transiciones"], nota="ciclos estimados con la frecuencia del procesador")


def _prof_dom(v):
    """Profundidad del arbol ya armado (sin recursion, para que no reviente con arboles hondos)."""
    mayor, pendientes = 0, [(v, 1)]
    while pendientes:
        x, p = pendientes.pop()
        if isinstance(x, (dict, list)):
            mayor = max(mayor, p)
            pendientes.extend((h, p + 1) for h in (x.values() if isinstance(x, dict) else x))
    return mayor


def medir_dom(texto_esquema, datos, memoria=True):
    """Linea base: json.loads arma TODO el arbol (DOM) y despues jsonschema lo recorre."""
    esq = json.loads(texto_esquema)
    val = jsonschema.Draft202012Validator(esq) if jsonschema else None

    def pasada():
        try:
            arbol = json.loads(datos)
        except RecursionError:
            return None, None, "RecursionError: json.loads se quedo sin pila"
        except ValueError as e:
            return None, None, "mal formado: " + str(e)[:60]
        try:
            ok = val.is_valid(arbol) if val else True
        except RecursionError:
            return None, arbol, "RecursionError: el validador generico se quedo sin pila"
        return ok, arbol, ""
    t0 = time.perf_counter_ns()
    ok, arbol, nota = pasada()
    ns = time.perf_counter_ns() - t0
    prof = _prof_dom(arbol) if arbol is not None else None
    del arbol
    mem = None
    if memoria:
        tracemalloc.start()
        pasada()
        mem = tracemalloc.get_traced_memory()[1]
        tracemalloc.stop()
    if not jsonschema:
        nota = (nota + " (sin jsonschema: solo json.loads)").strip()
    nota = (nota + " pila = profundidad del arbol (el DPDA cuenta ademas Z0)").strip()
    sin_pila = "RecursionError" in nota
    return _fila("dom", bool(ok), ok is None and not sin_pila, len(datos), ns, mem, None, prof, None, None, nota=nota,
                 fallo="se quedo sin pila" if sin_pila else None)


def medir_xml(M, datos, bloque=4096, memoria=True, **limites):
    """El DPDA de XML (xml_v1), medido igual que el de JSON."""
    def pasada():
        f = FlujoXML(M, **limites)
        for i in range(0, len(datos), bloque):
            if f.alimentar(datos[i:i + bloque])["terminado"]:
                break
        return f.terminar()
    t0 = time.perf_counter_ns()
    r = pasada()
    ns = time.perf_counter_ns() - t0
    mem = None
    if memoria:
        tracemalloc.start()
        pasada()
        mem = tracemalloc.get_traced_memory()[1]
        tracemalloc.stop()
    t = M.tamano()
    return _fila("dpda-python", r.valido, r.mal_formado, len(datos), ns, mem, None, r.prof_max,
                 t["estados"], t["transiciones"], nota="ciclos estimados con la frecuencia del procesador")


def medir_dom_xml(origen, texto_esquema, datos, memoria=True):
    """Linea base XML: lxml arma el arbol completo (DOM) y luego valida con la DTD o el XSD."""
    try:
        from lxml import etree
        from io import StringIO
    except ImportError:
        return None
    try:
        ref = (etree.DTD(StringIO(texto_esquema)) if origen == "DTD"
               else etree.XMLSchema(etree.fromstring(texto_esquema.encode())))
    except Exception as e:
        return _fila("dom", False, False, len(datos), 0, None, None, None, None, None, nota="lxml no acepto el esquema: " + str(e)[:60])
    seguro = etree.XMLParser(resolve_entities=False, no_network=True, load_dtd=False)

    def pasada():
        try:
            return bool(ref.validate(etree.fromstring(datos, seguro))), ""
        except etree.XMLSyntaxError as e:
            return None, "mal formado: " + str(e)[:60]
    t0 = time.perf_counter_ns()
    ok, nota = pasada()
    ns = time.perf_counter_ns() - t0
    return _fila("dom", bool(ok), ok is None, len(datos), ns, None, None, None, None, None,
                 nota=(nota + " lxml es codigo C: su memoria no la ve tracemalloc").strip())


def medir_nativo(binario, datos, motor, args=()):
    """El validador generado. Se corre 3 veces y se deja la mas rapida (menos ruido de la maquina)."""
    m = None
    for _ in range(3 if len(datos) < 8_000_000 else 1):
        _, x = G.ejecutar(binario, datos, ("--metricas", "--silencio") + tuple(args))
        if m is None or x["ns"] < m["ns"]:
            m = x
    asig = m["asignaciones"] if m["asignaciones"] >= 0 else None
    fila = _fila(motor, m["validos"] == 1, m["mal_formados"] == 1, m["bytes"], m["ns"], m["mem_validador"],
                 asig, None, m["estados"], m["transiciones"], ciclos=m["ciclos_byte"],
                 nota="ciclos medidos con el contador del procesador (rdtsc)")
    return fila


class Motores:
    """Compila una vez el esquema para todos los motores disponibles."""

    def __init__(self, texto_esquema, carpeta=None, pila_max=1024):
        self.texto = texto_esquema
        self.c = A.compilar_esquema(texto_esquema)
        self.carpeta = carpeta or tempfile.mkdtemp(prefix="dpda_")
        self.bin, self.avisos = {}, []
        G.generar(texto_esquema, self.carpeta, pila_max)
        for motor, leng, extra in (("dpda-c", "c", {"contar": True}), ("dpda-rust", "rust", {})):
            if not G.hay(leng):
                self.avisos.append(f"{motor}: no hay compilador de {leng} instalado")
                continue
            try:
                self.bin[motor] = G.compilar(self.carpeta, leng, **extra)
            except Exception as e:
                try:
                    self.bin[motor] = G.compilar(self.carpeta, leng)      # sin contar asignaciones
                except Exception:
                    self.avisos.append(f"{motor}: no compilo ({str(e)[:80]})")

    def medir(self, datos, python=True, dom=True, memoria=True, prof=None):
        datos = datos.encode("utf-8") if isinstance(datos, str) else datos
        filas = []
        if python:
            filas.append(medir_python(self.c, datos, memoria=memoria, max_prof=prof))
        for motor, b in self.bin.items():
            filas.append(medir_nativo(b, datos, motor, ("--prof", str(prof)) if prof else ()))
        if dom:
            filas.append(medir_dom(self.texto, datos, memoria=memoria))
        for f in filas:                                         # la pila la mide el DPDA
            if f["pila_max"] is None and f["motor"] != "dom":
                f["pila_max"] = filas[0]["pila_max"] if python else None
        return filas


# =========================================================================
# 3. BANCO: carga normal, tamano creciente y bombeo
# =========================================================================
ESQ_REGISTROS = '{"type":"array","items":' + A.ESQ + '}'


def registros(n_bytes, semilla=1):
    """Arreglo de registros validos del esquema del enunciado, de unos n_bytes."""
    g = P.GenJSON(json.loads(A.ESQ), semilla)
    partes, total = [], 2
    while total < n_bytes:
        partes.append(json.dumps(g.valido()))
        total += len(partes[-1]) + 1
    return ("[" + ",".join(partes) + "]").encode()


def banco(carpeta="salida", rapido=False):
    os.makedirs(carpeta, exist_ok=True)
    sal = {"fecha": time.strftime("%Y-%m-%d %H:%M"), "procesador_ghz": _ghz(), "avisos": []}
    m = Motores(ESQ_REGISTROS)
    sal["avisos"] += m.avisos
    sal["automata"] = m.c.M.tamano()

    # a) tamano creciente: la memoria del DOM crece con el documento, la del DPDA no
    sal["tamano"] = []
    for kb in ((16, 128) if rapido else (16, 64, 256, 1024)):
        sal["tamano"].append({"kb": kb, "filas": m.medir(registros(kb * 1024))})
    # b) documento grande solo en los motores nativos (streaming)
    if m.bin:
        grande = registros((2 if rapido else 32) * 1024 * 1024)
        sal["grande"] = {"mb": round(len(grande) / 1e6, 1), "filas": m.medir(grande, python=False, dom=False)}
    # c) carga sostenida: muchos documentos pequenos seguidos por el mismo proceso
    if m.bin:
        g = P.GenJSON(json.loads(ESQ_REGISTROS), 5)
        docs = [json.dumps(g.valido()).encode() for _ in range(2000 if rapido else 20000)]
        lote = b"\x1e".join(docs)
        sal["sostenida"] = []
        for motor, b in m.bin.items():
            _, met = G.ejecutar(b, lote, ("--lote", "--metricas", "--silencio"))
            sal["sostenida"].append({"motor": motor, "docs": met["docs"], "docs_s": round(met["docs"] / (met["ns"] / 1e9)),
                                     "p50_us": met["lat_p50_ns"] / 1000, "p99_us": met["lat_p99_ns"] / 1000,
                                     "max_us": met["lat_max_ns"] / 1000, "asignaciones": met["asignaciones"]})
    # d) bombeo: u v^k x y^k z con k creciente
    sal["bombeo"] = []
    esq, _ = P.bombeo_objetos(1)
    mb = Motores(esq, pila_max=4096)
    sal["avisos"] += [a for a in mb.avisos if a not in sal["avisos"]]
    for k in ((10, 100) if rapido else (10, 100, 1000, 4000)):
        _, doc = P.bombeo_objetos(k)
        sal["bombeo"].append({"k": k, "bytes": len(doc), "filas": mb.medir(doc)})
    json.dump(sal, open(os.path.join(carpeta, "metricas.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    open(os.path.join(carpeta, "metricas.svg"), "w", encoding="utf-8").write(grafico(sal))
    return sal


# ---- grafico SVG hecho a mano (sin librerias) ------------------------------
COLOR = {"dpda-python": "#2a78d6", "dpda-c": "#1baa6b", "dpda-rust": "#e07b1a", "dom": "#8a8f98"}


def _panel(x0, y0, w, h, titulo, series, etiquetas, unidad, log=True):
    """series: {motor: [valores]} sobre las mismas etiquetas del eje X."""
    import math
    vals = [v for s in series.values() for v in s if v]
    if not vals:
        return ""
    lo, hi = min(vals), max(vals)
    f = (lambda v: math.log10(v)) if log else (lambda v: v)
    a, b = (math.floor(f(lo)), math.ceil(f(hi)) or 1) if log else (0, hi * 1.1)
    if a == b:
        b = a + 1
    px = lambda i: x0 + 50 + i * (w - 70) / max(1, len(etiquetas) - 1)
    py = lambda v: y0 + h - 30 - (f(v) - a) / (b - a) * (h - 60)
    s = [f'<text x="{x0 + 50}" y="{y0 + 16}" font-size="13" font-weight="600" fill="#1c2430">{titulo}</text>']
    marcas = range(a, b + 1) if log else [b * i / 4 for i in range(5)]
    for t in marcas:
        v = 10 ** t if log else t
        y = y0 + h - 30 - ((t - a) / (b - a) if log else (v / b if b else 0)) * (h - 60)
        txt = f"{v:g}" if v < 1e6 else f"{v:.0e}"
        s.append(f'<line x1="{x0 + 50}" y1="{y:.1f}" x2="{x0 + w - 20}" y2="{y:.1f}" stroke="#e3e6ea"/>'
                 f'<text x="{x0 + 45}" y="{y + 4:.1f}" font-size="10" text-anchor="end" fill="#5b6470">{txt}</text>')
    for i, e in enumerate(etiquetas):
        s.append(f'<text x="{px(i):.1f}" y="{y0 + h - 12}" font-size="10" text-anchor="middle" fill="#5b6470">{e}</text>')
    for motor, serie in series.items():
        pts = [(px(i), py(v)) for i, v in enumerate(serie) if v]
        if len(pts) > 1:
            s.append('<polyline fill="none" stroke-width="2" stroke="%s" points="%s"/>'
                     % (COLOR[motor], " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)))
        for x, y in pts:
            s.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.5" fill="{COLOR[motor]}"/>')
    s.append(f'<text x="{x0 + w - 20}" y="{y0 + 16}" font-size="10" text-anchor="end" fill="#5b6470">{unidad}</text>')
    return "".join(s)


def grafico(sal):
    def col(bloque, campo, motores):
        return {mo: [next((f[campo] for f in p["filas"] if f["motor"] == mo), None) for p in bloque] for mo in motores}
    motores = [f["motor"] for f in sal["tamano"][0]["filas"]]
    ejx = [f'{p["kb"]} KB' for p in sal["tamano"]]
    ejk = [f'k={p["k"]}' for p in sal["bombeo"]]
    nombres = {"dpda-python": "DPDA en Python", "dpda-c": "DPDA en C", "dpda-rust": "DPDA en Rust",
               "dom": "Linea base (DOM + validador generico)"}
    leyenda = "".join(f'<circle cx="{60 + i * 170}" cy="16" r="5" fill="{COLOR[mo]}"/>'
                      f'<text x="{70 + i * 170}" y="20" font-size="12" fill="#1c2430">{nombres[mo]}</text>'
                      for i, mo in enumerate(motores))
    s = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 900 590" font-family="system-ui,Arial">',
         '<rect width="900" height="590" fill="#ffffff"/>', leyenda,
         _panel(0, 40, 450, 260, "Velocidad segun el tamano del documento", col(sal["tamano"], "mb_s", motores), ejx, "MB/s (escala log)"),
         _panel(450, 40, 450, 260, "Pico de memoria segun el tamano", col(sal["tamano"], "mem_pico", motores), ejx, "bytes (escala log)"),
         _panel(0, 320, 450, 260, "Bombeo: tiempo segun el anidamiento k", col(sal["bombeo"], "ms", motores), ejk, "ms (escala log)"),
         _panel(450, 320, 450, 260, "Bombeo: pico de memoria segun k", col(sal["bombeo"], "mem_pico", motores), ejk, "bytes (escala log)"),
         "</svg>"]
    return "".join(s)


def tabla(filas):
    """Las filas de una medicion como texto alineado."""
    cab = ("motor", "valido", "MB/s", "ciclos/byte", "mem pico", "asign.", "pila", "estados", "trans.")
    lin = ["  ".join(f"{c:>11}" for c in cab)]
    for f in filas:
        v = (f["motor"], "FALLO" if f.get("fallo") else "si" if f["valido"] else "no", f["mb_s"], f["ciclos_byte"], f["mem_pico"],
             f["asignaciones"], f["pila_max"], f["estados"], f["transiciones"])
        lin.append("  ".join(f"{'-' if x is None else x:>11}" for x in v))
    return "\n".join(lin)


# =========================================================================
# 4. PRUEBAS
# =========================================================================
def correr_pruebas():
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    def igual(r1, r2):
        return G.como_nativo(r1) == G.como_nativo(r2) and r1.limite == r2.limite

    # --- streaming: el resultado no depende de como lleguen los bloques ---
    c = A.compilar_esquema(G.ESQUEMAS_PRUEBA[1])
    g = P.GenJSON(json.loads(G.ESQUEMAS_PRUEBA[1]), 4)
    docs = []
    for _ in range(40):
        d = g.valido()
        docs.append(json.dumps(d, ensure_ascii=False).encode())
        docs += [json.dumps(x, ensure_ascii=False).encode() for _, _, x in g.invalidos(d)[:4]]
        docs += [x for _, x in P.malformados(d)]
    docs += [x for _, x in P.MALFORMADOS_FIJOS]
    mal = 0
    for doc in docs:
        ref = A.validar(c, doc)
        for bloque in (1, 3, 7, 4096):
            f = Flujo(c)
            for i in range(0, len(doc), bloque):
                f.alimentar(doc[i:i + bloque])
            if not igual(f.terminar(), ref):
                mal += 1
    chequear(f"Flujo = validar en {len(docs)} documentos x 4 tamanos de bloque", mal == 0)

    f = Flujo(c)
    e1 = f.alimentar(b'{"nombre":"ana","ed')
    chequear("a medio documento: sin veredicto todavia, pila 2", not e1["terminado"] and e1["pila"] == 2 and not e1["errores"])
    e2 = f.alimentar(b'ad":"x",')
    chequear("el error aparece apenas llega el bloque que lo contiene",
             len(e2["errores"]) == 1 and e2["errores"][0]["ruta"] == "/edad" and e2["errores"][0]["byte"] == 23)
    r = f.terminar()
    chequear("al cerrar a medias: mal formado + la violacion ya vista", r.mal_formado and r.violaciones >= 2)
    f = Flujo(c, parar=True)
    f.alimentar(b'{"nombre":1,')
    e = f.alimentar(b'"edad":"x"}')
    chequear("fallo temprano: se queda en el primer error", e["terminado"] and len(e["errores"]) == 1)
    chequear("error con ruta JSON Pointer, linea, columna y byte",
             set(e["errores"][0]) >= {"ruta", "mensaje", "linea", "columna", "byte"} and e["errores"][0]["ruta"] == "/nombre")

    # --- limites ---
    esq, hondo = P.bombeo_arreglos(500)
    ca = A.compilar_esquema(esq)
    f = Flujo(ca, max_prof=100)
    e = f.alimentar(hondo)
    r = f.terminar()
    chequear("limite de profundidad", r.limite and "profundidad" in r.limite and r.prof_max <= 101 and e["terminado"])
    esq, largo = P.arreglo_largo(5000)
    cl = A.compilar_esquema(esq)
    f = Flujo(cl, max_bytes=1000)
    for i in range(0, len(largo), 300):
        f.alimentar(largo[i:i + 300])
    r = f.terminar()
    chequear("limite de tamano", r.limite and "tamano" in r.limite and f.bytes == 1000 and igual(r, A.validar(cl, largo, max_bytes=1000)))
    f = Flujo(cl, max_ms=0)
    f.alimentar(largo[:2000])
    r = f.terminar()
    chequear("limite de tiempo", r.limite and "tiempo" in r.limite)
    f = Flujo(cl)
    f.alimentar(largo)
    chequear("sin limites el mismo documento pasa", f.terminar().valido)
    f = Flujo(cl)
    f.alimentar(b'[1,2,\xff')
    r = f.terminar()
    chequear("UTF-8 invalido: mal formado con posicion", r.mal_formado and r.errores[0]["byte"] is not None)

    # --- streaming de XML (DTD y XSD) ---
    for origen, texto, raiz in (("DTD", X.DTD_EJ, "biblioteca"), ("XSD", X.XSD_EJ, "pedido")):
        M = X.compilar(origen, texto, raiz) if origen == "DTD" else X.compilar(origen, texto)
        gx = P.GenXML(M.E, semilla=2)
        mal = n = 0
        for _ in range(25):
            arbol = gx.valido(raiz)
            for doc in [arbol.texto()] + [t for _, t in gx.invalidos(arbol)] + [t for _, t in P.malformados_xml(arbol.texto())]:
                ref = X.validar_xml(M, doc)
                datos = doc.encode("utf-8")
                for bloque in (1, 5, 4096):
                    f = FlujoXML(M)
                    for i in range(0, len(datos), bloque):
                        f.alimentar(datos[i:i + bloque])
                    r = f.terminar()
                    n += 1
                    if (r.valido, r.mal_formado, r.errores, r.prof_max) != (ref.valido, ref.mal_formado, ref.errores, ref.prof_max):
                        mal += 1
        chequear(f"FlujoXML = validar_xml con {origen} ({n} corridas)", mal == 0)
    M = X.compilar("DTD", X.DTD_EJ, "biblioteca")
    f = FlujoXML(M)
    e1 = f.alimentar(b'<biblioteca><libro id="1"><titulo>a</titulo>')
    chequear("XML a medio documento: pila armada y sin errores", e1["pila"] in (3, 4) and not e1["errores"] and not e1["terminado"])
    e2 = f.alimentar(b'<zzz/><autor>')          # el lector de XML va un token adelantado
    chequear("XML: el error aparece sin esperar al final del documento", len(e2["errores"]) >= 1)
    f.terminar()
    f = FlujoXML(M, max_bytes=20)
    f.alimentar(b'<biblioteca><libro id="1"><titulo>a</titulo>')
    r = f.terminar()
    chequear("XML: limite de tamano", r.limite and not r.valido and f.bytes == 20)
    filas = [medir_xml(M, X.DTD_EJ and b'<biblioteca><libro id="1"><titulo>a</titulo><autor>b</autor></libro></biblioteca>')]
    chequear("XML: medicion con las mismas columnas", filas[0]["valido"] and filas[0]["pila_max"] >= 3 and filas[0]["mb_s"] > 0)

    # --- instrumentacion ---
    m = Motores(ESQ_REGISTROS)
    doc = registros(60000)
    filas = m.medir(doc)
    nombres = [x["motor"] for x in filas]
    print(tabla(filas))
    chequear("estan el interprete y la linea base", "dpda-python" in nombres and "dom" in nombres)
    chequear("todos los motores dan el mismo veredicto", len({x["valido"] for x in filas}) == 1 and filas[0]["valido"])
    campos = {"mb_s", "ciclos_byte", "mem_pico", "asignaciones", "pila_max", "estados", "transiciones"}
    chequear("cada fila trae las 7 medidas del enunciado", all(campos <= set(x) for x in filas))
    py = filas[0]
    chequear("tamano del automata medido", py["estados"] == m.c.M.tamano()["estados"] and py["transiciones"] > 0)
    dom = filas[-1]
    chequear("el DPDA usa menos memoria que el DOM", py["mem_pico"] < dom["mem_pico"])
    for motor in m.bin:
        x = next(z for z in filas if z["motor"] == motor)
        chequear(f"{motor}: memoria fija y mas rapido que el interprete", x["mem_pico"] < 200000 and x["mb_s"] > py["mb_s"])
        if x["asignaciones"] is not None:
            chequear(f"{motor}: cero asignaciones de memoria", x["asignaciones"] == 0)
    malo = doc[:-1] + b',{"id":"x"}]'
    filas = m.medir(malo)
    chequear("documento invalido: todos dicen invalido",
             not any(x["valido"] for x in filas if x["motor"] != "dom" or jsonschema))
    filas = m.medir(doc[:500])
    chequear("documento cortado: todos lo detectan como mal formado", all(x["mal_formado"] for x in filas))

    # --- la memoria del DPDA no crece con el tamano; la del DOM si ---
    a, b = m.medir(registros(20000)), m.medir(registros(400000))
    pa, pb, da, db = a[0]["mem_pico"], b[0]["mem_pico"], a[-1]["mem_pico"], b[-1]["mem_pico"]
    chequear(f"documento 20 veces mas grande: DOM x{db / da:.0f}, DPDA x{pb / pa:.1f}", db > 8 * da and pb < 3 * pa)

    # --- bombeo ---
    esq, _ = P.bombeo_objetos(1)
    mb = Motores(esq, pila_max=4096)
    pilas, tiempos = [], []
    for k in (10, 100, 1000):
        _, d = P.bombeo_objetos(k)
        fl = mb.medir(d, memoria=False)
        pilas.append(fl[0]["pila_max"])
        tiempos.append(fl[0]["ms"])
        chequear(f"bombeo k={k}: los DPDA lo aceptan", all(x["valido"] for x in fl if x["motor"] != "dom"))
    chequear("bombeo: la pila crece igual que k (O(d))", pilas == [11 + 1, 101 + 1, 1001 + 1] or pilas == [11, 101, 1001] or pilas == [12, 102, 1002])
    chequear("bombeo: el tiempo crece en proporcion a los bytes (O(n))", tiempos[2] < tiempos[1] * 40)
    _, d = P.bombeo_objetos(3000)
    fl = mb.medir(d, memoria=False, prof=64)
    chequear("bombeo con limite de profundidad 64: todos los DPDA cortan", not any(x["valido"] for x in fl if x["motor"] != "dom"))
    dom = fl[-1]
    print("   linea base con k=3000:", dom["nota"][:70])

    # --- banco completo (version corta) ---
    with tempfile.TemporaryDirectory() as tmp:
        s = banco(tmp, rapido=True)
        svg = open(os.path.join(tmp, "metricas.svg"), encoding="utf-8").read()
        chequear("el banco escribe metricas.json y metricas.svg",
                 os.path.exists(os.path.join(tmp, "metricas.json")) and svg.startswith("<svg") and "polyline" in svg)
        chequear("el banco trae tamano y bombeo", len(s["tamano"]) == 2 and len(s["bombeo"]) == 2)
    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1:2] == ["banco"]:
        s = banco("salida")
        for p in s["tamano"]:
            print(f"\n--- documento de {p['kb']} KB ---\n" + tabla(p["filas"]))
        if "grande" in s:
            print(f"\n--- documento de {s['grande']['mb']} MB (solo nativos) ---\n" + tabla(s["grande"]["filas"]))
        for x in s.get("sostenida", []):
            print(f"\ncarga sostenida {x['motor']}: {x['docs']} documentos, {x['docs_s']} por segundo, "
                  f"p50 {x['p50_us']} us, p99 {x['p99_us']} us, asignaciones {x['asignaciones']}")
        for p in s["bombeo"]:
            print(f"\n--- bombeo k={p['k']} ({p['bytes']} bytes) ---\n" + tabla(p["filas"]))
        for a in s["avisos"]:
            print("AVISO:", a)
        print("\nEscritos salida/metricas.json y salida/metricas.svg")
    else:
        correr_pruebas()

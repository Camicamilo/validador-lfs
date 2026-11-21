r"""
payloads_v1.py - Fase 5: generador de payloads de prueba A PARTIR DEL ESQUEMA

Para alimentar las pruebas hacen falta muchos documentos de los que se sepa de
antemano si deben pasar o no. Este modulo los fabrica:

  JSON (a partir de un JSON Schema)
    GenJSON(esquema).valido()        un documento que cumple el esquema
    GenJSON(esquema).invalidos(doc)  copias del documento con UNA regla rota a
                                     proposito (tipo, required, rango, enum...)
    malformados(texto)               el mismo texto danado en su sintaxis
  XML (a partir de una DTD o un XSD ya leidos por xml_v1)
    GenXML(E).valido()               recorre el AFD de contenido de cada elemento
                                     hasta un estado final
    GenXML(E).invalidos()            una regla rota: falta un atributo, hijo que
                                     no va, tipo simple incorrecto...
  Bombeo (lema de bombeo: u v^k x y^k z)
    bombeo_arreglos(k), bombeo_objetos(k), arreglo_largo(n)

Cada invalido dice su MOTIVO, asi la prueba sabe que regla debia fallar.

Uso:
  python payloads_v1.py                         -> pruebas (contra jsonschema y lxml)
  python payloads_v1.py ESQUEMA.json [n]        -> imprime n validos y sus invalidos
"""
import sys
import json
import copy
import random
import xml_v1 as X


class Imposible(Exception):
    """El esquema no admite ningun valor en esa posicion (por ejemplo, false)."""


# =========================================================================
# 1. JSON
# =========================================================================
def _tipo_json(v):
    if isinstance(v, bool):
        return {"boolean"}
    if v is None:
        return {"null"}
    if isinstance(v, int):
        return {"integer", "number"}
    if isinstance(v, float):
        return {"integer", "number"} if v.is_integer() else {"number"}
    if isinstance(v, str):
        return {"string"}
    return {"array"} if isinstance(v, list) else {"object"}


class GenJSON:
    def __init__(self, esquema, semilla=0, prof_max=4):
        self.raiz = esquema
        self.rng = random.Random(semilla)
        self.prof_max = prof_max

    def _res(self, esq):
        n = 0
        while isinstance(esq, dict) and "$ref" in esq and n < 100:
            ref, nodo = esq["$ref"], self.raiz
            if ref != "#":
                for p in ref[2:].split("/"):
                    nodo = nodo[p]
            esq, n = nodo, n + 1
        return esq

    def _tipos(self, r):
        if "type" in r:
            return r["type"] if isinstance(r["type"], list) else [r["type"]]
        if any(k in r for k in ("properties", "required", "additionalProperties")):
            return ["object"]
        if any(k in r for k in ("items", "minItems", "maxItems")):
            return ["array"]
        if "minimum" in r or "maximum" in r:
            return ["number"]
        if "minLength" in r or "maxLength" in r:
            return ["string"]
        return ["string", "integer", "boolean", "null"]

    def valido(self, esq=None, prof=0):
        rng = self.rng
        r = self._res(self.raiz if esq is None else esq)
        if r is False:
            raise Imposible()
        if r is True or r == {}:
            return rng.choice(["x", 7, True, None, 2.5])
        if prof > self.prof_max + 40:
            raise Imposible("recursion obligatoria sin fin")
        minimo = prof > self.prof_max                       # ya muy hondo: solo lo obligatorio
        tipos = self._tipos(r)
        if "const" in r:
            return copy.deepcopy(r["const"])
        if "enum" in r:
            ok = [e for e in r["enum"] if "type" not in r or _tipo_json(e) & set(tipos)]
            if not ok:
                raise Imposible()
            return copy.deepcopy(rng.choice(ok))
        t = rng.choice(tipos if not minimo else [x for x in tipos if x not in ("object", "array")] or tipos)
        if t == "object":
            props = r.get("properties", {})
            extra = r.get("additionalProperties", True)
            d = {}
            for k in list(props) + [k for k in r.get("required", []) if k not in props]:
                obligatoria = k in r.get("required", [])
                if not obligatoria and (minimo or rng.random() < 0.3):
                    continue
                try:
                    d[k] = self.valido(props[k] if k in props else extra, prof + 1)
                except Imposible:
                    if obligatoria:
                        raise
            if extra is not False and not minimo and rng.random() < 0.2:
                try:
                    d["extra_" + str(rng.randint(1, 9))] = self.valido(extra, prof + 1)
                except Imposible:
                    pass
            return d
        if t == "array":
            mn = r.get("minItems", 0)
            mx = r.get("maxItems", mn + 3)
            n = mn if minimo else rng.randint(mn, max(mn, min(mx, mn + 3)))
            try:
                return [self.valido(r.get("items", True), prof + 1) for _ in range(n)]
            except Imposible:
                if mn == 0:
                    return []
                raise
        if t in ("integer", "number"):
            lo = r.get("minimum", r.get("maximum", 10) - 10)
            hi = r.get("maximum", lo + 10)
            if t == "integer" or rng.random() < 0.5:
                a, b = -(-lo // 1), hi // 1                 # techo y piso
                if a > b:
                    raise Imposible()
                return int(rng.randint(int(a), int(b)))
            return round(rng.uniform(lo, hi), 2) if lo < hi else lo
        if t == "string":
            mn = r.get("minLength", 0)
            mx = r.get("maxLength", mn + 6)
            return "".join(rng.choice("abcxyz é") for _ in range(rng.randint(mn, max(mn, mx))))
        return rng.choice([True, False]) if t == "boolean" else None

    # ---- inválidos: una mutacion garantizada por sitio ----
    def _sitios(self, esq, valor, ruta=()):
        r = self._res(esq)
        if not isinstance(r, dict):
            return
        yield ruta, r, valor
        if isinstance(valor, dict):
            for k, v in valor.items():
                sub = r.get("properties", {}).get(k, r.get("additionalProperties", True))
                yield from self._sitios(sub, v, ruta + (k,))
        elif isinstance(valor, list) and "items" in r:
            for i, v in enumerate(valor):
                yield from self._sitios(r["items"], v, ruta + (i,))

    def invalidos(self, doc):
        """Lista de (motivo, ruta, documento) con exactamente una regla rota."""
        sal = []

        def poner(motivo, ruta, nuevo):
            d = copy.deepcopy(doc)
            if not ruta:
                d = nuevo
            else:
                p = d
                for k in ruta[:-1]:
                    p = p[k]
                p[ruta[-1]] = nuevo
            sal.append((motivo, "/" + "/".join(map(str, ruta)), d))

        for ruta, r, v in self._sitios(self.raiz, doc):
            if "type" in r:
                tipos = set(r["type"] if isinstance(r["type"], list) else [r["type"]])
                for cand in ("x", 2.5, 3, True, None, [], {}):
                    if not (_tipo_json(cand) & tipos) and not ("number" in tipos and isinstance(cand, (int, float))
                                                              and not isinstance(cand, bool)):
                        poner("tipo", ruta, cand)
                        break
            if isinstance(v, dict):
                for k in r.get("required", []):
                    if k in v:
                        poner("requeridos", ruta, {a: b for a, b in v.items() if a != k})
                        break
                if r.get("additionalProperties") is False and "__extra__" not in r.get("properties", {}):
                    poner("prohibida", ruta, dict(v, __extra__=1))
            if isinstance(v, (int, float)) and not isinstance(v, bool):
                if "minimum" in r:
                    poner("minimum", ruta, r["minimum"] - 1)
                if "maximum" in r:
                    poner("maximum", ruta, r["maximum"] + 1)
            if isinstance(v, str):
                if r.get("minLength", 0) > 0:
                    poner("minLength", ruta, "a" * (r["minLength"] - 1))
                if "maxLength" in r:
                    poner("maxLength", ruta, "a" * (r["maxLength"] + 1))
            if "enum" in r:
                poner("enum", ruta, "__no__" + "_" * sum(1 for e in r["enum"] if isinstance(e, str)))
            if "const" in r:
                poner("const", ruta, "__no__" if r["const"] != "__no__" else 0)
            if isinstance(v, list):
                if r.get("minItems", 0) > 0 and len(v) >= r["minItems"]:
                    poner("minItems", ruta, v[:r["minItems"] - 1])
                if "maxItems" in r:
                    try:
                        relleno = [self.valido(r.get("items", True), self.prof_max + 1)
                                   for _ in range(r["maxItems"] + 1 - len(v))]
                        poner("maxItems", ruta, v + relleno)
                    except Imposible:
                        pass
        return sal


def malformados(doc):
    """(motivo, bytes): el documento (valor de Python) con la SINTAXIS rota."""
    t = json.dumps(doc)
    sal = [("sobra un cierre", (t + "}").encode()), ("arreglo sin cerrar", ("[" + t).encode()),
           ("dos valores seguidos", (t + " " + t).encode())]
    if t[-1] in '}]"':
        sal.append(("documento cortado", t[:-1].encode()))
    if t[-1] in "}]" and len(t) > 2:
        sal.append(("coma sobrante", (t[:-1] + "," + t[-1]).encode()))
    if '"' in t:
        i = t.index('"') + 1
        sal.append(("UTF-8 invalido", t[:i].encode() + b"\xff" + t[i:].encode()))
    if isinstance(doc, dict) and doc:
        k, v = next(iter(doc.items()))
        sal.append(("clave duplicada", (t[:-1] + "," + json.dumps(k) + ":" + json.dumps(v) + "}").encode()))
    return sal


MALFORMADOS_FIJOS = [("cero a la izquierda", b'{"a":01}'), ("coma final en arreglo", b"[1,]"),
                     ("faltan los dos puntos", b'{"a" 1}'), ("literal incompleto", b"nul"),
                     ("cadena sin cerrar", b'"abc'), ("escape invalido", b'"\\x"'), ("vacio", b"")]


# ---- bombeo: u v^k x y^k z -------------------------------------------------
ESQ_ARREGLOS = '{"$defs":{"a":{"type":"array","items":{"$ref":"#/$defs/a"}}},"$ref":"#/$defs/a"}'
ESQ_LISTA = ('{"type":"object","properties":{"v":{"type":"integer"},"sig":{"$ref":"#"}},'
             '"required":["v"],"additionalProperties":false}')
ESQ_ENTEROS = '{"type":"array","items":{"type":"integer","minimum":0}}'


def bombeo_arreglos(k, roto=False):
    """u='' v='[' x='' y=']' z=''  ->  [^k ]^k   (roto: un cierre menos)"""
    return ESQ_ARREGLOS, b"[" * k + b"]" * (k - 1 if roto else k)


def bombeo_objetos(k, roto=False):
    """v='{"v":1,"sig":'  x='{"v":0}'  y='}'  ->  lista enlazada de k+1 nodos"""
    return ESQ_LISTA, b'{"v":1,"sig":' * k + (b'{"v":"x"}' if roto else b'{"v":0}') + b"}" * k


def arreglo_largo(n):
    return ESQ_ENTEROS, b"[" + b",".join(b"%d" % (i % 1000) for i in range(n)) + b"]"


# =========================================================================
# 2. XML (reglas de xml_v1: DTD o XSD)
# =========================================================================
def _esc(t, attr=False):
    t = t.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    return t.replace('"', "&quot;") if attr else t


class Nodo:
    def __init__(self, regla, nombre):
        self.regla, self.nombre, self.attrs, self.hijos = regla, nombre, {}, []

    def texto(self):
        a = "".join(f' {k}="{_esc(v, True)}"' for k, v in self.attrs.items())
        if not self.hijos:
            return f"<{self.nombre}{a}/>"
        return (f"<{self.nombre}{a}>" + "".join(h.texto() if isinstance(h, Nodo) else _esc(h) for h in self.hijos)
                + f"</{self.nombre}>")

    def todos(self):
        yield self
        for h in self.hijos:
            if isinstance(h, Nodo):
                yield from h.todos()


class GenXML:
    def __init__(self, E, semilla=0, prof_max=5):
        self.E, self.rng, self.prof_max = E, random.Random(semilla), prof_max
        self.dist = {}
        for i, r in enumerate(E.reglas):                      # pasos minimos hasta un estado final
            d = {s: 0 for s in r["afd"].finales}
            cambio = True
            while cambio:
                cambio = False
                for (s, _), t in r["afd"].trans.items():
                    if t in d and d[t] + 1 < d.get(s, 10 ** 9):
                        d[s], cambio = d[t] + 1, True
            self.dist[i] = d

    def _simple(self, tipo):
        rng, base = self.rng, tipo.get("base", "string")
        if "enum" in tipo:
            return rng.choice(tipo["enum"])
        if base in ("integer", "decimal") or base in X.RANGO_INT:
            lo, hi = X.RANGO_INT.get(base, (None, None))
            for k, paso in (("minInclusive", 0), ("minExclusive", 1)):
                if k in tipo:
                    lo = int(float(tipo[k])) + paso
            for k, paso in (("maxInclusive", 0), ("maxExclusive", 1)):
                if k in tipo:
                    hi = int(float(tipo[k])) - paso
            lo = lo if lo is not None else (hi - 20 if hi is not None else 0)
            hi = hi if hi is not None else lo + 20
            return str(rng.randint(lo, max(lo, min(hi, lo + 1000))))
        if base == "boolean":
            return rng.choice(["true", "false"])
        if base == "date":
            return "2026-11-09"
        n = int(tipo.get("length", rng.randint(int(tipo.get("minLength", 1)),
                                               max(int(tipo.get("minLength", 1)), int(tipo.get("maxLength", 6))))))
        return "".join(rng.choice("abcxyz") for _ in range(n))

    def _elem(self, i, prof=0):
        r, rng = self.E.reglas[i], self.rng
        n = Nodo(i, r["nombre"])
        for an, spec in r["atributos"].items():
            if spec["req"] or rng.random() < 0.5:
                n.attrs[an] = spec["fijo"] if "fijo" in spec else self._simple(spec["tipo"])
        if r["contenido"] == "texto":
            n.hijos = [self._simple(r["texto"])]
        elif r["contenido"] in ("elementos", "mixto"):
            afd, s, d = r["afd"], 0, self.dist[i]
            while True:
                apuro = prof >= self.prof_max or len(n.hijos) > 6
                if s in afd.finales and (apuro or rng.random() < 0.35):
                    break
                ops = [(c, t) for (q, c), t in afd.trans.items() if q == s and t in d]
                if not ops:
                    break
                if apuro:
                    ops = [o for o in ops if d[o[1]] == min(d[x[1]] for x in ops)]
                c, s = rng.choice(ops)
                if r["contenido"] == "mixto" and rng.random() < 0.3:
                    n.hijos.append("texto ")
                n.hijos.append(self._elem(r["hijos"][c], prof + 1))
        return n

    def valido(self, raiz=None):
        nombre = raiz or self.rng.choice(sorted(self.E.raices))
        return self._elem(self.E.raices[nombre])

    def _acepta(self, i, nombres):
        afd, s = self.E.reglas[i]["afd"], 0
        for c in nombres:
            s = afd.paso(s, c)
            if s is None:
                return False
        return s in afd.finales

    def invalidos(self, arbol):
        """Lista de (motivo, texto XML) con una regla rota."""
        sal = []
        nodos = list(arbol.todos())

        def con(motivo, idx, cambio):
            copia = copy.deepcopy(arbol)
            cambio(list(copia.todos())[idx])
            sal.append((motivo, copia.texto()))

        vistos = set()

        def una(motivo, cond, cambio):
            for idx, n in enumerate(nodos):
                if (motivo, n.nombre) not in vistos and cond(n, self.E.reglas[n.regla]):
                    vistos.add((motivo, n.nombre))
                    con(motivo, idx, cambio)

        una("falta un atributo obligatorio",
            lambda n, r: any(s["req"] for s in r["atributos"].values()),
            lambda n: n.attrs.pop(next(a for a, s in self.E.reglas[n.regla]["atributos"].items() if s["req"])))
        una("atributo no declarado", lambda n, r: True, lambda n: n.attrs.update(zz="1"))
        una("atributo fuera de la enumeracion",
            lambda n, r: any("enum" in r["atributos"][a]["tipo"] for a in n.attrs),
            lambda n: n.attrs.update({next(a for a in n.attrs if "enum" in self.E.reglas[n.regla]["atributos"][a]["tipo"]): "__no__"}))
        una("hijo no permitido", lambda n, r: r["contenido"] in ("elementos", "vacio", "texto"),
            lambda n: n.hijos.append(Nodo(None, "zzz")))
        una("texto donde solo van elementos", lambda n, r: r["contenido"] == "elementos",
            lambda n: n.hijos.insert(0, "hola"))
        una("tipo simple incorrecto",
            lambda n, r: r["contenido"] == "texto" and (r["texto"].get("base") in ("integer", "decimal", "boolean", "date")
                                                        or r["texto"].get("base") in X.RANGO_INT or "enum" in r["texto"]),
            lambda n: n.hijos.__setitem__(slice(None), ["__no__"]))

        def quitar(n):
            hijos = [h for h in n.hijos if isinstance(h, Nodo)]
            for h in hijos:
                resto = [x.nombre for x in hijos if x is not h]
                if not self._acepta(n.regla, resto):
                    n.hijos.remove(h)
                    return
        una("falta un hijo obligatorio",
            lambda n, r: r["contenido"] in ("elementos", "mixto") and any(
                not self._acepta(n.regla, [x.nombre for x in n.hijos if isinstance(x, Nodo) and x is not h])
                for h in n.hijos if isinstance(h, Nodo)), quitar)
        return sal


def malformados_xml(texto):
    sal = [("dos raices", texto + texto), ("entidad no declarada", texto.replace(">", ">&bomba;", 1) if "</" in texto else "<a>&bomba;</a>"),
           ("cierre cruzado", "<a><b></a></b>"), ("texto fuera de la raiz", "hola" + texto)]
    if "</" in texto:
        sal.append(("etiqueta sin cerrar", texto[:texto.rindex("</")]))
    return sal


# =========================================================================
# 3. PRUEBAS: lo que se genera como valido DEBE pasar en la libreria de
#    referencia y en nuestro DPDA; lo invalido debe fallar en los dos.
# =========================================================================
def correr_pruebas():
    import automata_v2 as A
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    from generador_v1 import ESQUEMAS_PRUEBA
    esquemas = [e for e in ESQUEMAS_PRUEBA if e != "true"] + [ESQ_LISTA, ESQ_ENTEROS, ESQ_ARREGLOS]
    try:
        import jsonschema
    except ImportError:
        jsonschema = None
        print("  (jsonschema no instalada: solo se compara con nuestro DPDA)")
    nv = ni = nm = 0
    motivos = set()
    for n, texto in enumerate(esquemas):
        esq = json.loads(texto)
        c = A.compilar_esquema(texto)
        ref = jsonschema.Draft202012Validator(esq) if jsonschema else None
        g = GenJSON(esq, semilla=n)
        mal_v = mal_i = mal_m = 0
        for _ in range(150):
            try:
                doc = g.valido()
            except Imposible:
                continue
            nv += 1
            r = A.validar(c, json.dumps(doc))
            if not r.valido or (ref and not ref.is_valid(doc)):
                mal_v += 1
                if mal_v == 1:
                    print("   valido rechazado:", texto[:60], json.dumps(doc)[:100], r)
            for motivo, ruta, malo in g.invalidos(doc):
                ni += 1
                motivos.add(motivo)
                r = A.validar(c, json.dumps(malo))
                if r.valido or r.mal_formado or (ref and ref.is_valid(malo)):
                    mal_i += 1
                    if mal_i == 1:
                        print("   invalido aceptado:", motivo, ruta, texto[:60], json.dumps(malo)[:100])
            for motivo, datos in malformados(doc)[:3] + MALFORMADOS_FIJOS:
                nm += 1
                r = A.validar(c, datos)
                if not r.mal_formado and not (motivo == "clave duplicada" and not r.valido):
                    mal_m += 1
        chequear(f"esquema {n}: validos aceptados", mal_v == 0)
        chequear(f"esquema {n}: invalidos rechazados", mal_i == 0)
        chequear(f"esquema {n}: malformados detectados", mal_m == 0)
    chequear("se generaron todos los motivos de invalidez",
             {"tipo", "requeridos", "prohibida", "minimum", "maximum", "minLength", "maxLength",
              "enum", "const", "minItems", "maxItems"} <= motivos)
    print(f"  JSON: {nv} validos, {ni} invalidos, {nm} malformados generados y comprobados")

    # bombeo
    for k in (1, 10, 500):
        e, p = bombeo_arreglos(k)
        c = A.compilar_esquema(e)
        chequear(f"bombeo de arreglos k={k}", A.validar(c, p).valido and A.validar(c, bombeo_arreglos(k, True)[1]).mal_formado)
        e, p = bombeo_objetos(k)
        c = A.compilar_esquema(e)
        r = A.validar(c, bombeo_objetos(k, True)[1])
        chequear(f"bombeo de objetos k={k}", A.validar(c, p).valido and not r.valido and not r.mal_formado)

    # XML
    try:
        from lxml import etree
        from io import StringIO
    except ImportError:
        etree = None
        print("  (lxml no instalada: solo se compara con nuestro DPDA)")
    for origen, texto, raiz in (("DTD", X.DTD_EJ, "biblioteca"), ("XSD", X.XSD_EJ, "pedido")):
        M = X.compilar(origen, texto, raiz) if origen == "DTD" else X.compilar(origen, texto)
        if etree:
            ref = etree.DTD(StringIO(texto)) if origen == "DTD" else etree.XMLSchema(etree.fromstring(texto.encode()))
        g = GenXML(M.E, semilla=3)
        mal_v = mal_i = nv = ni = 0
        motivos = set()
        for _ in range(300):
            arbol = g.valido(raiz)
            doc = arbol.texto()
            nv += 1
            if not X.validar_xml(M, doc).valido or (etree and not ref.validate(etree.fromstring(doc))):
                mal_v += 1
                if mal_v == 1:
                    print("   XML valido rechazado:", doc[:200], X.validar_xml(M, doc))
            for motivo, malo in g.invalidos(arbol):
                ni += 1
                motivos.add(motivo)
                if X.validar_xml(M, malo).valido or (etree and ref.validate(etree.fromstring(malo))):
                    mal_i += 1
                    if mal_i == 1:
                        print("   XML invalido aceptado:", motivo, malo[:200])
            for motivo, malo in malformados_xml(doc):
                if not X.validar_xml(M, malo).mal_formado:
                    mal_i += 1
                    print("   XML malformado no detectado:", motivo)
        chequear(f"{origen}: {nv} validos aceptados (y por lxml)", mal_v == 0)
        chequear(f"{origen}: {ni} invalidos rechazados (y por lxml), motivos: {len(motivos)}", mal_i == 0 and len(motivos) >= 5)
    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        correr_pruebas()
    else:
        esq = json.load(open(a[0], encoding="utf-8"))
        g = GenJSON(esq, semilla=1)
        for _ in range(int(a[1]) if len(a) > 1 else 3):
            doc = g.valido()
            print("VALIDO   ", json.dumps(doc, ensure_ascii=False))
            for motivo, ruta, malo in g.invalidos(doc):
                print(f"  INVALIDO ({motivo} en {ruta})", json.dumps(malo, ensure_ascii=False))

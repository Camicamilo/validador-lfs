r"""
casos_v1.py - Casos de prueba (seccion 4 del enunciado) en un almacen de documentos

El enunciado pide guardar los casos en una base NoSQL en la nube (DynamoDB,
Cosmos DB o MongoDB Atlas). Aqui se usa lo mismo pero LOCAL y sin costo: una
coleccion de documentos guardada en un archivo JSON (casos.json). Cada caso es
un documento con _id y se consulta por campos, igual que en esas bases. Para
llevarlo a la nube solo habria que cambiar la clase Almacen.

Un caso:
  {"_id": "inv-0007", "categoria": "invalidos", "sub": "required",
   "formato": "json", "esquema": "...", "payload": "...",
   "esperado": "invalido", "nota": "..."}

  esperado:  valido | invalido | mal_formado | limite | no_comprobado
  (no_comprobado = regla fuera del DPDA puro: se avisa y no se revisa)

Categorias (las del enunciado): validos, invalidos, malformados, fuera,
bombeo y extremos.

Uso:
  python casos_v1.py            -> crea casos.json si no existe y corre toda la suite
  python casos_v1.py sembrar    -> vuelve a generar casos.json
  python casos_v1.py validos    -> corre solo una categoria
"""
import sys
import os
import json
import base64
import tempfile
import automata_v2 as A
import xml_v1 as X
import payloads_v1 as P
import generador_v1 as G

AQUI = os.path.dirname(os.path.abspath(__file__))
CATEGORIAS = ["validos", "invalidos", "malformados", "fuera", "bombeo", "extremos"]


# =========================================================================
# 1. ALMACEN DE DOCUMENTOS (NoSQL local)
# =========================================================================
class Almacen:
    def __init__(self, ruta=None, nuevo=False):
        self.ruta = ruta or os.path.join(AQUI, "casos.json")
        self.docs = []
        if not nuevo and os.path.exists(self.ruta):
            self.docs = json.load(open(self.ruta, encoding="utf-8"))["casos"]

    def insertar(self, **doc):
        doc = dict(_id=f"{doc['categoria'][:3]}-{len(self.docs) + 1:04d}", **doc)
        self.docs.append(doc)
        return doc["_id"]

    def buscar(self, **filtro):
        return [d for d in self.docs if all(d.get(k) == v for k, v in filtro.items())]

    def uno(self, _id):
        return next((d for d in self.docs if d["_id"] == _id), None)

    def guardar(self):
        json.dump({"coleccion": "casos_de_prueba", "total": len(self.docs), "casos": self.docs},
                  open(self.ruta, "w", encoding="utf-8"), ensure_ascii=False, indent=0)


FABRICAS = {"bombeo_objetos": P.bombeo_objetos, "bombeo_arreglos": P.bombeo_arreglos,
            "arreglo_largo": P.arreglo_largo}


def payload_de(caso):
    """Los bytes del payload. Los enormes no se guardan: se guarda como fabricarlos."""
    if "fabrica" in caso:
        return FABRICAS[caso["fabrica"][0]](*caso["fabrica"][1:])[1]
    if "payload_b64" in caso:
        return base64.b64decode(caso["payload_b64"])
    return caso["payload"].encode("utf-8")


# =========================================================================
# 2. SEMBRAR: los casos de cada categoria del enunciado
# =========================================================================
S_PERSONA = G.ESQUEMAS_PRUEBA[1]
S_ANIDADO = ('{"type":"object","properties":{"cliente":{"type":"object","properties":{"nombre":{"type":"string"},'
             '"dir":{"type":"object","properties":{"ciudad":{"type":"string"},"cp":{"type":"integer","minimum":0}},'
             '"required":["ciudad"]}},"required":["nombre"]},"items":{"type":"array","minItems":1,"items":'
             '{"type":"object","properties":{"sku":{"type":"string"},"cant":{"type":"integer","minimum":1,"maximum":99}},'
             '"required":["sku","cant"],"additionalProperties":false}}},"required":["cliente","items"]}')
S_ARBOL = ('{"$defs":{"nodo":{"type":"object","properties":{"v":{"type":"integer"},"hijos":{"type":"array",'
           '"items":{"$ref":"#/$defs/nodo"}}},"required":["v"],"additionalProperties":false}},"$ref":"#/$defs/nodo"}')
S_NUM = '{"type":"array","items":{"type":"number","minimum":0}}'
SUB_INVALIDO = {"tipo": "tipos", "requeridos": "required", "prohibida": "additionalProperties",
                "enum": "enum", "const": "enum"}
BOMBA = ('<?xml version="1.0"?><!DOCTYPE biblioteca [<!ENTITY a "aaaaaaaaaa">'
         '<!ENTITY b "&a;&a;&a;&a;&a;&a;&a;&a;"><!ENTITY c "&b;&b;&b;&b;&b;&b;&b;&b;">]>'
         '<biblioteca>&c;</biblioteca>')
XXE = ('<?xml version="1.0"?><!DOCTYPE biblioteca [<!ENTITY x SYSTEM "file:///etc/passwd">]>'
       '<biblioteca>&x;</biblioteca>')


def sembrar(ruta=None):
    a = Almacen(ruta, nuevo=True)

    def caso(cat, sub, formato, esquema, payload, esperado, nota="", **extra):
        d = dict(categoria=cat, sub=sub, formato=formato, esquema=esquema, esperado=esperado, nota=nota, **extra)
        if payload is not None:
            if isinstance(payload, bytes):
                try:
                    d["payload"] = payload.decode("utf-8")
                except UnicodeDecodeError:
                    d["payload_b64"] = base64.b64encode(payload).decode()
            else:
                d["payload"] = payload
        a.insertar(**d)

    def js(x):
        return json.dumps(x, ensure_ascii=False)

    # ---- validos e invalidos (JSON) ----
    for n, (sub, esq) in enumerate((("simples", A.ESQ), ("simples", S_PERSONA), ("anidados", S_ANIDADO),
                                    ("recursivos ($ref)", S_ARBOL), ("recursivos ($ref)", P.ESQ_LISTA))):
        g = P.GenJSON(json.loads(esq), semilla=20 + n, prof_max=3)
        vistos = {}
        for i in range(6):
            doc = g.valido()
            if i < 4:
                caso("validos", sub, "json", esq, js(doc), "valido")
            for motivo, ruta_m, malo in g.invalidos(doc):
                s = SUB_INVALIDO.get(motivo, "rangos")
                if vistos.get(motivo, 0) < 2:
                    vistos[motivo] = vistos.get(motivo, 0) + 1
                    caso("invalidos", s, "json", esq, js(malo), "invalido", f"{motivo} en {ruta_m}")
    # ---- validos e invalidos (XML con DTD y con XSD) ----
    for formato, texto, raiz in (("xml-dtd", X.DTD_EJ, "biblioteca"), ("xml-xsd", X.XSD_EJ, "pedido")):
        M = X.compilar("DTD", texto, raiz) if formato == "xml-dtd" else X.compilar("XSD", texto)
        g = P.GenXML(M.E, semilla=8)
        vistos = set()
        for i in range(8):
            arbol = g.valido(raiz)
            if i < 4:
                caso("validos", "XML", formato, texto, arbol.texto(), "valido", raiz=raiz)
            for motivo, malo in g.invalidos(arbol):
                if motivo not in vistos:
                    vistos.add(motivo)
                    caso("invalidos", "XML", formato, texto, malo, "invalido", motivo, raiz=raiz)
        doc = g.valido(raiz).texto()
        for motivo, malo in P.malformados_xml(doc):
            sub = "etiquetas XML sin cerrar" if motivo == "etiqueta sin cerrar" else "XML: sintaxis"
            caso("malformados", sub, formato, texto, malo, "mal_formado", motivo, raiz=raiz)
    # ---- malformados (JSON) ----
    doc = {"nombre": "ana", "edad": 30, "rol": "admin"}
    for motivo, datos in P.malformados(doc) + P.MALFORMADOS_FIJOS:
        if motivo == "clave duplicada":
            caso("malformados", "claves duplicadas", "json", S_PERSONA, datos, "invalido",
                 "el DPDA la reporta como violacion (bit repetido en la mascara del objeto)")
        else:
            caso("malformados", "UTF-8 invalido" if "UTF-8" in motivo else "sintaxis", "json", S_PERSONA,
                 datos, "mal_formado", motivo)
    caso("malformados", "UTF-8 invalido", "json", S_PERSONA, b'{"nombre":"\xc3\x28","edad":1}', "mal_formado",
         "secuencia de 2 bytes mal continuada")
    # ---- fuera del DPDA puro ----
    for clave, esq, viola, cumple in (
            ("anyOf", '{"type":"object","properties":{"v":{"anyOf":[{"type":"string"},{"type":"integer"}]}}}', '{"v":true}', '{"v":"x"}'),
            ("oneOf", '{"oneOf":[{"type":"integer"},{"type":"number"}]}', "3", "3.5"),
            ("pattern", '{"type":"string","pattern":"^[a-z]+$"}', '"ABC"', '"abc"'),
            ("uniqueItems", '{"type":"array","items":{"type":"integer"},"uniqueItems":true}', "[1,1]", "[1,2]")):
        caso("fuera", clave, "json", esq, cumple, "valido", "cumple tambien la regla que no se revisa", clave_roja=clave)
        caso("fuera", clave, "json", esq, viola, "no_comprobado",
             f"viola solo '{clave}': el DPDA avisa FUERA y no lo revisa; la linea base si lo rechaza", clave_roja=clave)
    # ---- bombeo: u v^k x y^k z ----
    for k in (1, 10, 100, 1000):
        caso("bombeo", "objetos anidados", "json", P.ESQ_LISTA, None, "valido", f"k={k}", fabrica=["bombeo_objetos", k])
        caso("bombeo", "objetos anidados", "json", P.ESQ_LISTA, None, "invalido", f"k={k}, el nodo del fondo esta mal",
             fabrica=["bombeo_objetos", k, True])
        caso("bombeo", "arreglos anidados", "json", P.ESQ_ARREGLOS, None, "valido", f"k={k}", fabrica=["bombeo_arreglos", k])
        caso("bombeo", "arreglos anidados", "json", P.ESQ_ARREGLOS, None, "mal_formado", f"k={k}, falta un cierre",
             fabrica=["bombeo_arreglos", k, True])
    caso("bombeo", "arreglo muy largo", "json", P.ESQ_ENTEROS, None, "valido", "100000 elementos, pila 2",
         fabrica=["arreglo_largo", 100000])
    # ---- extremos ----
    caso("extremos", "payload grande en streaming", "json", P.ESQ_ENTEROS, None, "valido",
         "mas de 1 MB leido en bloques de 4096 bytes", fabrica=["arreglo_largo", 300000])
    caso("extremos", "profundidad sobre el limite", "json", P.ESQ_ARREGLOS, None, "limite",
         "5000 niveles con limite de 1024", fabrica=["bombeo_arreglos", 5000], limites={"max_prof": 1024})
    caso("extremos", "limite de tamano", "json", P.ESQ_ENTEROS, None, "limite", "se corta en 1000 bytes",
         fabrica=["arreglo_largo", 5000], limites={"max_bytes": 1000})
    caso("extremos", "numeros enormes", "json", S_NUM, "[1e400, 123456789012345678901234567890]", "valido",
         "numeros fuera del rango de 64 bits")
    caso("extremos", "numeros enormes", "json", S_NUM, "[-1e400]", "invalido", "menor que el minimo 0")
    caso("extremos", "numeros enormes", "json", S_NUM, "[1" + "0" * 600 + "]", "limite",
         "numero de 601 digitos: supera el buffer fijo de 511 caracteres")
    caso("extremos", "expansion de entidades XML", "xml-dtd", X.DTD_EJ, BOMBA, "mal_formado",
         "bomba de entidades: el DOCTYPE interno se rechaza, nunca se expande", raiz="biblioteca")
    caso("extremos", "expansion de entidades XML", "xml-dtd", X.DTD_EJ, XXE, "mal_formado",
         "entidad externa (XXE): se rechaza, nunca se abre el archivo", raiz="biblioteca")
    a.guardar()
    return a


# =========================================================================
# 3. CORRER LA SUITE en todos los motores
# =========================================================================
def veredicto(r):
    """Un Resultado (o el diccionario del nativo) en una palabra."""
    d = r if isinstance(r, dict) else {"valido": r.valido, "limite": getattr(r, "limite", None), "mal_formado": r.mal_formado}
    return "valido" if d["valido"] else "limite" if d["limite"] else "mal_formado" if d["mal_formado"] else "invalido"


def _nativo(n, datos, max_prof=0, max_bytes=None):
    n.lib.dpda_iniciar(n.ctx, max_prof or 0, 0)
    tope = len(datos) if max_bytes is None else min(len(datos), max_bytes)
    corto = False
    for i in range(0, tope, 65536):
        trozo = datos[i:min(i + 65536, tope)]
        if n.lib.dpda_alimentar(n.ctx, trozo, len(trozo)):
            corto = True
            break
    if not corto and tope < len(datos):
        n.lib.dpda_cortar(n.ctx, 0)
    n.lib.dpda_terminar(n.ctx)
    k = n.lib.dpda_reporte(n.ctx, n.sal, len(n.sal))
    return json.loads(n.sal.raw[:k].decode("utf-8", errors="replace"))


class Suite:
    def __init__(self, nativos=True):
        self.cache, self.tmp = {}, tempfile.mkdtemp(prefix="suite_")
        self.leng = [x for x in ("c", "rust") if nativos and G.hay(x)]
        try:
            import jsonschema
            self.js = jsonschema
        except ImportError:
            self.js = None
        try:
            from lxml import etree
            self.etree = etree
        except ImportError:
            self.etree = None

    def _json(self, esq):
        if esq not in self.cache:
            c = A.compilar_esquema(esq)
            libs = {}
            carpeta = os.path.join(self.tmp, f"e{len(self.cache)}")
            G.generar(esq, carpeta, pila_max=2048)
            for leng in self.leng:
                sub = os.path.join(carpeta, leng)             # cada biblioteca en su carpeta
                os.makedirs(sub, exist_ok=True)
                for f in ("validador.c", "validador.rs"):
                    open(os.path.join(sub, f), "w", encoding="utf-8").write(open(os.path.join(carpeta, f), encoding="utf-8").read())
                libs[leng] = G.Nativo(G.compilar(sub, leng, biblioteca=True))
            ref = self.js.Draft202012Validator(json.loads(esq)) if self.js else None
            self.cache[esq] = (c, libs, ref)
        return self.cache[esq]

    def _xml(self, caso):
        k = (caso["formato"], caso["esquema"])
        if k not in self.cache:
            dtd = caso["formato"] == "xml-dtd"
            M = X.compilar("DTD", caso["esquema"], caso.get("raiz")) if dtd else X.compilar("XSD", caso["esquema"])
            ref = None
            if self.etree:
                from io import StringIO
                ref = (self.etree.DTD(StringIO(caso["esquema"])) if dtd
                       else self.etree.XMLSchema(self.etree.fromstring(caso["esquema"].encode())))
            self.cache[k] = (M, ref)
        return self.cache[k]

    def correr(self, caso):
        """Devuelve {motor: veredicto} y la lista de desacuerdos con lo esperado."""
        datos, esp, lim = payload_de(caso), caso["esperado"], caso.get("limites", {})
        v, fallas = {}, []
        if caso["formato"] == "json":
            c, libs, ref = self._json(caso["esquema"])
            v["python"] = veredicto(A.validar(c, datos, max_profundidad=lim.get("max_prof"),
                                              max_bytes=lim.get("max_bytes"), memoria_fija=True))
            for leng, n in libs.items():
                v[leng] = veredicto(_nativo(n, datos, lim.get("max_prof"), lim.get("max_bytes")))
            quiero = "valido" if esp == "no_comprobado" else esp
            fallas += [f"{m} dijo {x}, se esperaba {quiero}" for m, x in v.items() if x != quiero]
            if esp == "no_comprobado" and caso.get("clave_roja") not in c.clasificacion["rojo"]:
                fallas.append("no se aviso que la regla queda FUERA")
            if ref is not None and "limites" not in caso and len(datos) < 200000:
                try:
                    arbol = json.loads(datos)
                    base = "valido" if ref.is_valid(arbol) else "invalido"
                except RecursionError:
                    base = "sin pila (RecursionError)"
                except ValueError:
                    base = "mal_formado"
                v["linea base"] = base
                ok = {"valido": ("valido",), "invalido": ("invalido",), "mal_formado": ("mal_formado",),
                      "no_comprobado": ("invalido",), "limite": ("valido", "invalido", "mal_formado")}[esp]
                tolerado = (caso["sub"] == "claves duplicadas" or "RecursionError" in base
                            or caso["sub"] == "numeros enormes")
                if base not in ok and not tolerado:
                    fallas.append(f"la linea base dijo {base}")
        else:
            M, ref = self._xml(caso)
            v["python"] = veredicto(X.validar_xml(M, datos))
            if v["python"] != esp:
                fallas.append(f"python dijo {v['python']}, se esperaba {esp}")
            if ref is not None and caso["categoria"] != "extremos":
                try:
                    base = "valido" if ref.validate(self.etree.fromstring(datos)) else "invalido"
                except self.etree.XMLSyntaxError:
                    base = "mal_formado"
                v["linea base"] = base
                if base != esp:
                    fallas.append(f"lxml dijo {base}")
        return v, fallas


def correr_suite(categoria=None, almacen=None, nativos=True, silencio=False):
    a = almacen or Almacen()
    if not a.docs:
        a = sembrar(a.ruta)
    s = Suite(nativos)
    resumen, malos = {}, []
    for caso in a.docs:
        if categoria and caso["categoria"] != categoria:
            continue
        v, fallas = s.correr(caso)
        r = resumen.setdefault(caso["categoria"], {"casos": 0, "pasaron": 0, "subs": set()})
        r["casos"] += 1
        r["pasaron"] += not fallas
        r["subs"].add(caso["sub"])
        if fallas:
            malos.append((caso["_id"], caso["sub"], fallas))
    if not silencio:
        motores = ["python"] + s.leng + (["linea base"] if s.js or s.etree else [])
        print("  Motores: " + ", ".join(motores))
        print(f"  {'categoria':<13}{'casos':>6}{'pasaron':>9}   subcategorias")
        for cat in CATEGORIAS:
            if cat in resumen:
                r = resumen[cat]
                print(f"  {cat:<13}{r['casos']:>6}{r['pasaron']:>9}   " + ", ".join(sorted(r["subs"]))[:95])
        for _id, sub, fallas in malos[:8]:
            print(f"  FALLA {_id} ({sub}): " + "; ".join(fallas)[:160])
        total = sum(r["casos"] for r in resumen.values())
        print(f"\n  Pruebas: {total - len(malos)} de {total} pasaron")
    return resumen, malos


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    arg = sys.argv[1] if len(sys.argv) > 1 else None
    if arg == "sembrar":
        print(f"  {len(sembrar().docs)} casos guardados en casos.json")
    else:
        correr_suite(arg)

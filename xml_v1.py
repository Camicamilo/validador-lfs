r"""
xml_v1.py - XML bien formado + DTD + subconjunto de XSD -> DPDA ponderado

Fases que cubre (para XML):
  Fase 1  usa el lexer de lexer_v4 (AFD de etiquetas y de texto). Aqui se
          extiende solo para NO botar el texto que es puro espacio (hace falta:
          un elemento EMPTY con un espacio adentro es invalido).
  Fase 2  gramatica libre de contexto de XML bien formado y su parser con pila:
              DOC       -> MISC* ELEMENTO MISC*
              ELEMENTO  -> VACIA | ABRE CONTENIDO CIERRA     (mismo nombre)
              CONTENIDO -> (ELEMENTO | TEXTO | COMENTARIO)*
          Ademas lee DTD y XSD (el XSD es XML: lo lee este mismo parser).
  Fase 3  semantica del esquema: cada modelo de contenido, por ejemplo
          (titulo, autor+, resumen?) es una EXPRESION REGULAR sobre nombres de
          hijos. Se convierte ER -> AFN (Thompson) -> AFD (subconjuntos) -> AFD
          minimo (Moore). Se rechazan <!ENTITY> (bomba de entidades / XXE) y
          'pattern' queda en rojo (riesgo ReDoS, fuera del DPDA puro).
  Fase 4  DPDA: Gamma = {Z0} U { e@s : e elemento, s estado de su AFD minimo }.
          Abrir un hijo c estando en e@s: el tope pasa a e@delta_e(s,c) y se
          apila c@0. Cerrar e: solo si s es final del AFD de e. Asi el automata
          de pila "lleva" un AFD por cada etiqueta abierta.

Uso:
  python xml_v1.py                                   -> pruebas (compara con lxml)
  python xml_v1.py --dtd E.dtd D.xml [--traza]       -> valida con DTD
  python xml_v1.py --xsd E.xsd D.xml [--traza]       -> valida con XSD
  python xml_v1.py --formal (--dtd|--xsd) E          -> definicion formal + AFD
"""
import re
import sys
import json
from decimal import Decimal, InvalidOperation
from lexer_v4 import Lexer, ErrorLexico, Token

EPS = "ε"
COSTO = {"estructura": 1, "nombre": 1, "completo": 1, "solo_espacios": 1,
         "vacio": 1, "atributos": 1, "valor": 2, "no_declarado": 1}


# =========================================================================
# FASE 1 (extension): lexer XML que conserva el texto de solo espacios
# =========================================================================
class LexerXML(Lexer):
    def __init__(self):
        super().__init__("xml")

    def _emitir(self, salida):
        tipo = self.afd.aceptacion[self.q]
        try:
            texto = self.pedazo.decode("utf-8")
        except UnicodeDecodeError:
            self._error(f"UTF-8 invalido dentro de {self.afd.nombre}")
        salida.append(Token(tipo, texto, *self.inicio))
        self.afd = None


def tokenizar_xml(texto):
    lx = LexerXML()
    return lx.alimentar(texto) + lx.terminar()


# =========================================================================
# FASE 2: XML bien formado (parser con pila) y arbol del documento
# =========================================================================
class ErrorXML(Exception):
    """El documento no es XML bien formado."""


RE_NOMBRE = re.compile(r"[A-Za-z_:][\w.\-:]*")
RE_ATRIB = re.compile(r"([A-Za-z_:][\w.\-:]*)=(\"([^\"]*)\"|'([^']*)')")
ENTIDADES = {"lt": "<", "gt": ">", "amp": "&", "apos": "'", "quot": '"'}
RE_ENTIDAD = re.compile(r"&(#x[0-9A-Fa-f]+|#[0-9]+|[A-Za-z_:][\w.\-:]*);")


def decodificar(texto, tok=None):
    """Reemplaza &amp; &#65; ... Solo las 5 entidades predefinidas: una entidad
    desconocida es error (asi no hay expansion de entidades ni XXE)."""
    def rep(m):
        x = m.group(1)
        if x.startswith("#x"):
            return chr(int(x[2:], 16))
        if x.startswith("#"):
            return chr(int(x[1:]))
        if x in ENTIDADES:
            return ENTIDADES[x]
        donde = f" (linea {tok.linea}, columna {tok.columna})" if tok else ""
        raise ErrorXML(f"entidad no declarada &{x};{donde}: no se expanden entidades")
    if "&" in texto and "&" in RE_ENTIDAD.sub("", texto):
        raise ErrorXML("'&' suelto: debe escribirse &amp;")
    return RE_ENTIDAD.sub(rep, texto)


def etiqueta(tok):
    """Del texto '<a x="1" y='2'>' saca ('a', {'x': '1', 'y': '2'})."""
    t = tok.texto
    cuerpo = t[2:-1] if tok.tipo == "ETIQUETA_CIERRA" else t[1:-2] if tok.tipo == "ETIQUETA_VACIA" else t[1:-1]
    nombre = RE_NOMBRE.match(cuerpo.strip()).group(0)
    attrs = {}
    for m in RE_ATRIB.finditer(cuerpo[len(nombre):]):
        if m.group(1) in attrs:
            raise ErrorXML(f"atributo repetido '{m.group(1)}' en <{nombre}> "
                           f"(linea {tok.linea}, columna {tok.columna})")
        val = m.group(3) if m.group(3) is not None else m.group(4)
        attrs[m.group(1)] = decodificar(val, tok)
    return nombre, attrs


class NodoXML:
    def __init__(self, nombre, attrs, tok=None):
        self.nombre, self.attrs, self.tok = nombre, attrs, tok
        self.hijos = []          # NodoXML o str (texto)

    def texto(self):
        return "".join(h for h in self.hijos if isinstance(h, str))

    def elementos(self):
        return [h for h in self.hijos if isinstance(h, NodoXML)]


def eventos(tokens):
    """Tokens -> eventos (abre, cierra, texto) revisando que el XML este bien
    formado. Pila de nombres: <a><b></a> es error. Sin recursion."""
    pila = []
    hubo_raiz = False
    for tok in tokens:
        tipo = tok.tipo
        if tipo in ("COMENTARIO", "DECLARACION"):
            continue
        if tipo == "TEXTO":
            if not pila:
                if tok.texto.strip():
                    raise ErrorXML(f"texto fuera del elemento raiz (linea {tok.linea}, "
                                   f"columna {tok.columna})")
                continue
            yield ("texto", decodificar(tok.texto, tok), tok)
            continue
        nombre, attrs = etiqueta(tok)
        if tipo in ("ETIQUETA_ABRE", "ETIQUETA_VACIA"):
            if not pila and hubo_raiz:
                raise ErrorXML(f"segundo elemento raiz <{nombre}> (linea {tok.linea}): "
                               "XML admite una sola raiz")
            hubo_raiz = True
            yield ("abre", (nombre, attrs), tok)
            if tipo == "ETIQUETA_VACIA":
                yield ("cierra", nombre, tok)
            else:
                pila.append(nombre)
        else:
            if not pila:
                raise ErrorXML(f"</{nombre}> sin etiqueta abierta (linea {tok.linea})")
            if pila[-1] != nombre:
                raise ErrorXML(f"se esperaba </{pila[-1]}> y llego </{nombre}> "
                               f"(linea {tok.linea}, columna {tok.columna})")
            pila.pop()
            yield ("cierra", nombre, tok)
    if pila:
        raise ErrorXML(f"faltan etiquetas de cierre: {' '.join('</' + n + '>' for n in reversed(pila))}")
    if not hubo_raiz:
        raise ErrorXML("el documento no tiene elemento raiz")


def parsear_xml(texto):
    """Arbol del documento (lo usa el visor y el lector de XSD)."""
    raiz, pila = None, []
    for ev, dato, tok in eventos(tokenizar_xml(texto)):
        if ev == "abre":
            n = NodoXML(dato[0], dato[1], tok)
            if pila:
                pila[-1].hijos.append(n)
            else:
                raiz = n
            pila.append(n)
        elif ev == "cierra":
            pila.pop()
        else:
            pila[-1].hijos.append(dato)
    return raiz


# =========================================================================
# FASE 3a: ER de modelos de contenido -> AFN -> AFD -> AFD minimo
#   AST: ("n", nombre) | ("seq", [..]) | ("alt", [..]) | ("rep", e, min, max) | ("eps",)
# =========================================================================
MAX_EXPANSION = 64      # e{0,1000} se expande en 1000 copias: se acota (explosion)


class AFD:
    def __init__(self, n, finales, trans, alfabeto):
        self.n, self.finales, self.trans, self.alfabeto = n, finales, trans, alfabeto

    def paso(self, s, a):
        return self.trans.get((s, a))

    def esperados(self, s):
        return sorted(a for (q, a) in self.trans if q == s)

    def er(self):
        return None


def _thompson(ast):
    """AFN de Thompson. Devuelve (n_estados, inicio, fin, aristas[(p, simbolo|None, q)])."""
    aristas, cont = [], [0]

    def nuevo():
        cont[0] += 1
        return cont[0] - 1

    def construir(e):
        tipo = e[0]
        if tipo == "eps":
            a, b = nuevo(), nuevo()
            aristas.append((a, None, b))
            return a, b
        if tipo == "n":
            a, b = nuevo(), nuevo()
            aristas.append((a, e[1], b))
            return a, b
        if tipo == "seq":
            if not e[1]:
                return construir(("eps",))
            ini, fin = construir(e[1][0])
            for x in e[1][1:]:
                a, b = construir(x)
                aristas.append((fin, None, a))
                fin = b
            return ini, fin
        if tipo == "alt":
            a, b = nuevo(), nuevo()
            for x in e[1]:
                i, f = construir(x)
                aristas.append((a, None, i))
                aristas.append((f, None, b))
            return a, b
        if tipo == "rep":
            _, x, mn, mx = e
            partes = [x] * mn
            if mx is None:
                partes.append(("star", x))
            else:
                partes += [("opt", x)] * min(mx - mn, MAX_EXPANSION)
            if not partes:
                return construir(("eps",))
            ini = fin = None
            for p in partes:
                if p[0] == "star":
                    a, b = nuevo(), nuevo()
                    i, f = construir(p[1])
                    aristas.extend([(a, None, i), (f, None, b), (a, None, b), (f, None, i)])
                elif p[0] == "opt":
                    a, b = nuevo(), nuevo()
                    i, f = construir(p[1])
                    aristas.extend([(a, None, i), (f, None, b), (a, None, b)])
                else:
                    a, b = construir(p)
                if ini is None:
                    ini, fin = a, b
                else:
                    aristas.append((fin, None, a))
                    fin = b
            return ini, fin
        raise ValueError(tipo)

    i, f = construir(ast)
    return cont[0], i, f, aristas


def afd_de(ast):
    """ER -> AFN (Thompson) -> AFD (subconjuntos) -> AFD minimo (Moore)."""
    n, ini, fin, aristas = _thompson(ast)
    eps = {}
    mov = {}
    alfabeto = set()
    for p, s, q in aristas:
        if s is None:
            eps.setdefault(p, set()).add(q)
        else:
            mov.setdefault((p, s), set()).add(q)
            alfabeto.add(s)

    def cerradura(S):
        pila, res = list(S), set(S)
        while pila:
            x = pila.pop()
            for y in eps.get(x, ()):
                if y not in res:
                    res.add(y)
                    pila.append(y)
        return frozenset(res)

    inicio = cerradura({ini})
    ids, cola, trans = {inicio: 0}, [inicio], {}
    while cola:
        S = cola.pop(0)
        for a in sorted(alfabeto):
            T = set()
            for x in S:
                T |= mov.get((x, a), set())
            if not T:
                continue
            T = cerradura(T)
            if T not in ids:
                ids[T] = len(ids)
                cola.append(T)
            trans[(ids[S], a)] = ids[T]
    finales = {i for S, i in ids.items() if fin in S}
    sin_min = AFD(len(ids), finales, trans, sorted(alfabeto))
    return minimizar_afd(sin_min), sin_min


def minimizar_afd(d):
    """Moore: particion inicial {finales, no finales} (+ estado muerto implicito)
    y se refina por el bloque al que va cada simbolo."""
    MUERTO = d.n
    estados = list(range(d.n + 1))

    def ir(s, a):
        return MUERTO if s == MUERTO else d.trans.get((s, a), MUERTO)

    bloque = {s: (1 if s in d.finales else 0) for s in estados}
    while True:
        firmas = {}
        nuevo = {}
        for s in estados:
            f = (bloque[s],) + tuple(bloque[ir(s, a)] for a in d.alfabeto)
            nuevo[s] = firmas.setdefault(f, len(firmas))
        if len(firmas) == len(set(bloque.values())):
            break
        bloque = nuevo
    # renumerar: el inicial queda en 0 y el bloque muerto se elimina
    muerto = bloque[MUERTO]
    orden = {}
    cola = [0]
    while cola:
        s = cola.pop(0)
        b = bloque[s]
        if b in orden or b == muerto:
            continue
        orden[b] = len(orden)
        cola += [ir(s, a) for a in d.alfabeto]
    trans = {}
    for (s, a), t in d.trans.items():
        if bloque[s] in orden and bloque[t] in orden:
            trans[(orden[bloque[s]], a)] = orden[bloque[t]]
    finales = {orden[bloque[s]] for s in d.finales if bloque[s] in orden}
    return AFD(len(orden), finales, trans, d.alfabeto)


def texto_er(ast):
    t = ast[0]
    if t == "eps":
        return "ε"
    if t == "n":
        return ast[1]
    if t == "seq":
        return "(" + ", ".join(texto_er(x) for x in ast[1]) + ")"
    if t == "alt":
        return "(" + " | ".join(texto_er(x) for x in ast[1]) + ")"
    _, x, mn, mx = ast
    suf = {(0, 1): "?", (0, None): "*", (1, None): "+"}.get((mn, mx), f"{{{mn},{'' if mx is None else mx}}}")
    return texto_er(x) + suf


# =========================================================================
# FASE 3b: tipos simples (texto y atributos)
# =========================================================================
TIPOS_BASE = {"string", "normalizedString", "token", "integer", "int", "long", "short",
              "decimal", "boolean", "positiveInteger", "nonNegativeInteger",
              "negativeInteger", "nonPositiveInteger", "date", "NMTOKEN", "CDATA"}
RANGO_INT = {"int": (-2 ** 31, 2 ** 31 - 1), "long": (-2 ** 63, 2 ** 63 - 1),
             "short": (-2 ** 15, 2 ** 15 - 1), "positiveInteger": (1, None),
             "nonNegativeInteger": (0, None), "negativeInteger": (None, -1),
             "nonPositiveInteger": (None, 0)}


def chequear_simple(tipo, crudo):
    """tipo = {"base": ..., "enum": [...], "minInclusive": ..., ...}. Devuelve lista
    de mensajes de error (vacia si esta bien). Las comprobaciones van de la mas
    barata a la mas cara."""
    base = tipo.get("base", "string")
    if base in ("string", "CDATA"):
        v = crudo
    elif base == "normalizedString":
        v = re.sub(r"[\t\n\r]", " ", crudo)
    else:
        v = " ".join(crudo.split())                    # whiteSpace = collapse
    errores = []
    num = None
    if base in ("integer",) or base in RANGO_INT:
        if not re.fullmatch(r"[+-]?\d+", v):
            return [f"'{crudo}' no es un entero"]
        num = int(v)
        lo, hi = RANGO_INT.get(base, (None, None))
        if (lo is not None and num < lo) or (hi is not None and num > hi):
            return [f"'{crudo}' fuera del rango de {base}"]
    elif base == "decimal":
        if not re.fullmatch(r"[+-]?(\d+(\.\d*)?|\.\d+)", v):
            return [f"'{crudo}' no es un decimal"]
        num = Decimal(v)
    elif base == "boolean":
        if v not in ("true", "false", "1", "0"):
            return [f"'{crudo}' no es boolean (true/false/1/0)"]
    elif base == "date":
        if not re.fullmatch(r"-?\d{4,}-\d{2}-\d{2}", v):
            return [f"'{crudo}' no es una fecha AAAA-MM-DD"]
    elif base == "NMTOKEN":
        if not re.fullmatch(r"[\w.\-:]+", v):
            return [f"'{crudo}' no es un NMTOKEN"]
    if "enum" in tipo:
        if num is not None:
            ok = any(_num_igual(num, e) for e in tipo["enum"])
        else:
            ok = v in tipo["enum"]
        if not ok:
            errores.append(f"'{v}' no esta en la enumeracion {tipo['enum']}")
    for k, cmp in (("minInclusive", lambda a, b: a >= b), ("maxInclusive", lambda a, b: a <= b),
                   ("minExclusive", lambda a, b: a > b), ("maxExclusive", lambda a, b: a < b)):
        if k in tipo and num is not None and not cmp(num, Decimal(str(tipo[k]))):
            errores.append(f"{v} no cumple {k}={tipo[k]}")
    if "length" in tipo and len(v) != int(tipo["length"]):
        errores.append(f"longitud {len(v)} distinta de length={tipo['length']}")
    if "minLength" in tipo and len(v) < int(tipo["minLength"]):
        errores.append(f"longitud {len(v)} menor que minLength={tipo['minLength']}")
    if "maxLength" in tipo and len(v) > int(tipo["maxLength"]):
        errores.append(f"longitud {len(v)} mayor que maxLength={tipo['maxLength']}")
    return errores


def _num_igual(n, e):
    try:
        return Decimal(str(n)) == Decimal(" ".join(str(e).split()))
    except InvalidOperation:
        return False


# =========================================================================
# FASE 3c: reglas de elementos. Lo mismo sale de una DTD o de un XSD:
#   {"nombre", "contenido": "vacio"|"texto"|"elementos"|"mixto"|"cualquiera",
#    "modelo": AST, "afd": AFD minimo, "afd_sin_min": AFD, "hijos": {nombre: id},
#    "texto": tipo simple, "atributos": {n: {"req", "tipo", "fijo"}}}
# =========================================================================
class Esquema:
    def __init__(self, origen):
        self.origen = origen          # "DTD" o "XSD"
        self.reglas = []
        self.raices = {}              # nombre -> id de regla permitido como raiz
        self.avisos = []

    def agregar(self, regla):
        self.reglas.append(regla)
        return len(self.reglas) - 1

    def compilar_modelos(self):
        for r in self.reglas:
            if r["contenido"] in ("elementos", "mixto"):
                r["afd"], r["afd_sin_min"] = afd_de(r["modelo"])
            else:
                r["afd"] = r["afd_sin_min"] = AFD(1, {0}, {}, [])
        return self


# ---------------------------- DTD ----------------------------------------
RE_DECL = re.compile(r"<!(ELEMENT|ATTLIST|ENTITY|NOTATION)\s+(.*?)>", re.S)


def _parsear_modelo(texto):
    """Modelo de contenido DTD, por ejemplo (a, (b | c)*, d?) -> AST.
    Parser descendente con pila explicita de grupos."""
    s = texto.replace(" ", "").replace("\n", "").replace("\t", "").replace("\r", "")
    pila = [{"items": [], "sep": None}]
    i = 0
    while i < len(s):
        c = s[i]
        if c == "(":
            pila.append({"items": [], "sep": None})
            i += 1
            continue
        if c in ",|":
            if pila[-1]["sep"] not in (None, c):
                raise ValueError(f"no se pueden mezclar ',' y '|' en el mismo grupo: {texto}")
            pila[-1]["sep"] = c
            i += 1
            continue
        if c == ")":
            g = pila.pop()
            nodo = ("alt" if g["sep"] == "|" else "seq", g["items"])
            if len(g["items"]) == 1:
                nodo = g["items"][0]
            i += 1
        else:
            m = re.match(r"#PCDATA|[A-Za-z_:][\w.\-:]*", s[i:])
            if not m:
                raise ValueError(f"modelo de contenido invalido: {texto}")
            nodo = ("pcdata",) if m.group(0) == "#PCDATA" else ("n", m.group(0))
            i += len(m.group(0))
        if i < len(s) and s[i] in "?*+":
            mn, mx = {"?": (0, 1), "*": (0, None), "+": (1, None)}[s[i]]
            nodo = ("rep", nodo, mn, mx)
            i += 1
        pila[-1]["items"].append(nodo)
    if len(pila) != 1 or len(pila[0]["items"]) != 1:
        raise ValueError(f"parentesis desbalanceados: {texto}")
    return pila[0]["items"][0]


def leer_dtd(texto, raiz=None):
    texto = re.sub(r"<!--.*?-->", "", texto, flags=re.S)
    E = Esquema("DTD")
    decl_el, attlists = {}, {}
    for m in RE_DECL.finditer(texto):
        clase, cuerpo = m.group(1), m.group(2).strip()
        if clase == "ENTITY":
            E.avisos.append(("SEGURIDAD", f"<!ENTITY {cuerpo.split()[0]} ...> rechazada: no se "
                                          "expanden entidades (bomba de entidades / XXE)"))
            continue
        if clase == "NOTATION":
            continue
        nombre = cuerpo.split()[0]
        resto = cuerpo[len(nombre):].strip()
        if clase == "ELEMENT":
            if nombre in decl_el:
                raise ValueError(f"elemento '{nombre}' declarado dos veces")
            decl_el[nombre] = resto
        else:
            attlists.setdefault(nombre, []).append(resto)
    ids = {}
    for nombre, modelo in decl_el.items():
        r = {"nombre": nombre, "hijos": {}, "atributos": {}, "texto": None}
        if modelo == "EMPTY":
            r["contenido"] = "vacio"
        elif modelo == "ANY":
            r["contenido"], r["modelo"] = "mixto", ("rep", ("alt", [("n", x) for x in decl_el]), 0, None)
        else:
            ast = _parsear_modelo(modelo)
            pcdata = "#PCDATA" in modelo
            if pcdata:
                nombres = re.findall(r"[A-Za-z_:][\w.\-:]*", modelo.replace("#PCDATA", ""))
                if not nombres:
                    r["contenido"], r["texto"] = "texto", {"base": "CDATA"}
                else:
                    r["contenido"] = "mixto"
                    r["modelo"] = ("rep", ("alt", [("n", x) for x in nombres]), 0, None)
            else:
                r["contenido"], r["modelo"] = "elementos", ast
        ids[nombre] = E.agregar(r)
    for r in E.reglas:
        if "modelo" in r:
            for n in re.findall(r"'n', '([^']+)'", repr(r["modelo"])):
                if n not in ids:
                    raise ValueError(f"<{r['nombre']}> usa el elemento '{n}' que no esta declarado")
                r["hijos"][n] = ids[n]
    for nombre, lista in attlists.items():
        if nombre not in ids:
            raise ValueError(f"ATTLIST de '{nombre}', que no esta declarado")
        for cuerpo in lista:
            for m in re.finditer(r"([A-Za-z_:][\w.\-:]*)\s+(CDATA|NMTOKEN|ID|IDREF|\([^)]*\))\s+"
                                 r"(#REQUIRED|#IMPLIED|#FIXED\s+(\"[^\"]*\"|'[^']*')|\"[^\"]*\"|'[^']*')",
                                 cuerpo):
                an, at, uso = m.group(1), m.group(2), m.group(3)
                if at.startswith("("):
                    tipo = {"base": "NMTOKEN", "enum": [x.strip() for x in at[1:-1].split("|")]}
                elif at in ("ID", "IDREF"):
                    tipo = {"base": "NMTOKEN"}
                    E.avisos.append(("AVISO", f"{at} de '{an}': unicidad de ID no se revisa "
                                              "(necesita un conjunto no acotado)"))
                else:
                    tipo = {"base": at}
                a = {"req": uso == "#REQUIRED", "tipo": tipo}
                if uso.startswith("#FIXED"):
                    a["fijo"] = m.group(4)[1:-1]
                E.reglas[ids[nombre]]["atributos"][an] = a
    E.raices = {raiz: ids[raiz]} if raiz else dict(ids)
    return E.compilar_modelos()


# ---------------------------- XSD ----------------------------------------
def _local(nombre):
    return nombre.split(":")[-1]


def leer_xsd(texto):
    """Lee un subconjunto de XSD con el PROPIO parser XML de la Fase 2."""
    raiz = parsear_xml(texto)
    if _local(raiz.nombre) != "schema":
        raise ValueError("un XSD debe empezar con <xs:schema>")
    E = Esquema("XSD")
    globales = {"element": {}, "complexType": {}, "simpleType": {}}
    for h in raiz.elementos():
        k = _local(h.nombre)
        if k in globales:
            globales[k][h.attrs["name"]] = h
        elif k not in ("annotation", "import", "include"):
            E.avisos.append(("AVISO", f"<xs:{k}> global no soportado, se ignora"))
    hechos = {}            # id(nodo xs:element) -> id de regla

    def tipo_simple(nodo_o_nombre, donde):
        if isinstance(nodo_o_nombre, str):
            n = _local(nodo_o_nombre)
            if n in globales["simpleType"]:
                return tipo_simple(globales["simpleType"][n], donde)
            if n in TIPOS_BASE:
                return {"base": n}
            if n == "anySimpleType":
                return {"base": "string"}
            raise ValueError(f"tipo simple desconocido '{nodo_o_nombre}' en {donde}")
        rest = [x for x in nodo_o_nombre.elementos() if _local(x.nombre) == "restriction"]
        if not rest:
            raise ValueError(f"simpleType sin restriction en {donde} (list/union no soportados)")
        t = dict(tipo_simple(rest[0].attrs["base"], donde))
        for f in rest[0].elementos():
            fk = _local(f.nombre)
            if fk == "enumeration":
                t.setdefault("enum", []).append(f.attrs["value"])
            elif fk in ("minInclusive", "maxInclusive", "minExclusive", "maxExclusive",
                        "minLength", "maxLength", "length"):
                t[fk] = f.attrs["value"]
            elif fk == "pattern":
                E.avisos.append(("FUERA", f"pattern '{f.attrs['value']}' en {donde}: rojo "
                                          "(no es DPDA puro, riesgo ReDoS); no se revisa"))
            else:
                E.avisos.append(("AVISO", f"faceta {fk} en {donde} no soportada"))
        return t

    def atributos(ct, donde):
        res = {}
        for a in ct.elementos():
            if _local(a.nombre) != "attribute":
                continue
            simple = [x for x in a.elementos() if _local(x.nombre) == "simpleType"]
            t = tipo_simple(simple[0] if simple else a.attrs.get("type", "xs:string"), donde)
            res[a.attrs["name"]] = {"req": a.attrs.get("use") == "required", "tipo": t}
            if "fixed" in a.attrs:
                res[a.attrs["name"]]["fijo"] = a.attrs["fixed"]
        return res

    def ocurrencias(n):
        mn = int(n.attrs.get("minOccurs", "1"))
        mx = n.attrs.get("maxOccurs", "1")
        mx = None if mx == "unbounded" else int(mx)
        return mn, mx

    def particula(n, hijos, donde, pend):
        k = _local(n.nombre)
        mn, mx = ocurrencias(n)
        if k == "element":
            if "ref" in n.attrs:
                decl = globales["element"][_local(n.attrs["ref"])]
            else:
                decl = n
            nombre = decl.attrs["name"]
            if nombre in hijos and hijos[nombre][1] is not decl:
                raise ValueError(f"en {donde} hay dos <{nombre}> con declaraciones distintas")
            hijos[nombre] = (None, decl)
            pend.append(decl)
            ast = ("n", nombre)
        elif k in ("sequence", "choice"):
            partes = [particula(x, hijos, donde, pend) for x in n.elementos()
                      if _local(x.nombre) != "annotation"]
            ast = ("seq" if k == "sequence" else "alt", partes)
        elif k == "all":
            raise ValueError(f"xs:all en {donde}: orden libre = producto de automatas "
                             "(explosion n!), no soportado")
        else:
            raise ValueError(f"<xs:{k}> no soportado en {donde}")
        return ast if (mn, mx) == (1, 1) else ("rep", ast, mn, mx)

    def regla_de(decl):
        if id(decl) in hechos:
            return hechos[id(decl)]
        nombre = decl.attrs["name"]
        r = {"nombre": nombre, "hijos": {}, "atributos": {}, "texto": None}
        idx = E.agregar(r)
        hechos[id(decl)] = idx
        donde = f"<{nombre}>"
        inline = [x for x in decl.elementos() if _local(x.nombre) in ("complexType", "simpleType")]
        if inline:
            def_tipo = inline[0]
        elif "type" in decl.attrs:
            n = _local(decl.attrs["type"])
            def_tipo = globales["complexType"].get(n) or n
        else:
            def_tipo = None
        pend = []
        if def_tipo is None:
            r["contenido"] = "cualquiera"
            E.avisos.append(("AVISO", f"{donde} sin tipo (anyType): se acepta cualquier contenido"))
        elif isinstance(def_tipo, str) or _local(def_tipo.nombre) == "simpleType":
            r["contenido"], r["texto"] = "texto", tipo_simple(def_tipo, donde)
        else:
            ct = def_tipo
            r["atributos"] = atributos(ct, donde)
            hijos_ct = [x for x in ct.elementos() if _local(x.nombre) not in ("attribute", "annotation")]
            mixto = ct.attrs.get("mixed") == "true"
            if not hijos_ct:
                r["contenido"] = "mixto" if mixto else "vacio"
                r["modelo"] = ("eps",)
            elif _local(hijos_ct[0].nombre) == "simpleContent":
                ext = hijos_ct[0].elementos()[0]
                r["contenido"], r["texto"] = "texto", tipo_simple(ext.attrs["base"], donde)
                r["atributos"] = atributos(ext, donde)
            else:
                hijos = {}
                r["modelo"] = particula(hijos_ct[0], hijos, donde, pend)
                r["contenido"] = "mixto" if mixto else "elementos"
                r["_hijos_decl"] = hijos
        for decl_h in pend:
            regla_de(decl_h)
        if "_hijos_decl" in r:
            r["hijos"] = {n: hechos[id(d)] for n, (_, d) in r.pop("_hijos_decl").items()}
        return idx

    for nombre, decl in globales["element"].items():
        E.raices[nombre] = regla_de(decl)
    return E.compilar_modelos()


# =========================================================================
# FASE 4: el DPDA de XML como TABLA delta (datos) + interprete
#   Estados: Q0 (antes de la raiz), C (dentro de un elemento), R (retorno), QF
#   Simbolos de entrada: <e>  </e>  TEXTO   (y <*> para nombres no esperados)
#   Simbolos de pila:    Z0, e@s (elemento e con su AFD en el estado s), *
# =========================================================================
class DPDAXML:
    def __init__(self, E):
        self.E = E
        self.delta = {}
        self.conflictos = []
        self.Q = {"Q0", "C", "R", "QF"}
        self.Sigma, self.Gamma = set(), {"Z0", "*"}
        self.q0 = "Q0"
        R = E.reglas
        sim = lambda i, s: f"{R[i]['nombre']}@{s}"
        for nombre, i in E.raices.items():
            self.agregar("Q0", f"<{nombre}>", "Z0", "C", f"push:{sim(i, 0)}", [self._g_attrs(i)],
                         f"raiz <{nombre}>")
        self.agregar("Q0", "<*>", "Z0", "C", "push:*", [("no_declarado", 1, sorted(E.raices))],
                     "raiz no declarada")
        for i, r in enumerate(R):
            afd = r["afd"]
            for s in range(afd.n):
                X = sim(i, s)
                self.Gamma.add(X)
                for (q, c), t in afd.trans.items():
                    if q == s:
                        j = r["hijos"][c]
                        self.agregar("C", f"<{c}>", X, "C", f"cambia:{sim(i, t)}|push:{sim(j, 0)}",
                                     [self._g_attrs(j)], f"hijo <{c}>: AFD de {r['nombre']} {s}->{t}")
                if r["contenido"] == "cualquiera":
                    self.agregar("C", "<*>", X, "C", "push:*", [], "cualquier hijo")
                else:
                    self.agregar("C", "<*>", X, "C", "push:*",
                                 [("no_permitido", COSTO["nombre"], afd.esperados(s))],
                                 "hijo no permitido aqui")
                cierre = []
                if r["contenido"] in ("elementos", "mixto") and s not in afd.finales:
                    cierre.append(("completo", COSTO["completo"], afd.esperados(s)))
                if r["contenido"] == "texto":
                    cierre.append(("valor", COSTO["valor"], r["texto"]))
                self.agregar("C", f"</{r['nombre']}>", X, "R", "pop", cierre, f"cierra <{r['nombre']}>")
                g = {"vacio": [("vacio", COSTO["vacio"], None)],
                     "elementos": [("solo_espacios", COSTO["solo_espacios"], None)],
                     "texto": [("acumula", 0, None)]}.get(r["contenido"], [])
                self.agregar("C", "TEXTO", X, "C", "igual", g, "texto")
                self.agregar("R", EPS, X, "C", "igual", [], f"vuelve a <{r['nombre']}>")
        self.agregar("C", "<*>", "*", "C", "push:*", [], "dentro de un elemento no declarado")
        self.agregar("C", "</*>", "*", "R", "pop", [], "cierra elemento no declarado")
        self.agregar("C", "TEXTO", "*", "C", "igual", [], "texto libre")
        self.agregar("R", EPS, "*", "C", "igual", [], "vuelve")
        self.agregar("R", EPS, "Z0", "QF", "igual", [], "termino la raiz")

    def _g_attrs(self, i):
        return ("atributos", COSTO["atributos"] + len(self.E.reglas[i]["atributos"]), i)

    def agregar(self, q, a, X, destino, pila, guardas, nota):
        guardas = sorted(guardas, key=lambda g: g[1])
        fila = {"de": q, "a": a, "tope": X, "a_estado": destino, "pila": pila,
                "guardas": [list(g) for g in guardas], "nota": nota,
                "costo": COSTO["estructura"] + sum(g[1] for g in guardas)}
        if (q, a, X) in self.delta:
            self.conflictos.append((q, a, X))
            return
        self.delta[(q, a, X)] = fila
        if a != EPS:
            self.Sigma.add(a)

    def verificar_determinismo(self):
        prob = [f"fila repetida {c}" for c in self.conflictos]
        lect = {(q, X) for (q, a, X) in self.delta if a != EPS}
        prob += [f"epsilon y lectura en ({q}, {X})" for (q, a, X) in self.delta
                 if a == EPS and (q, X) in lect]
        return prob

    def tamano(self):
        return {"estados": len(self.Q), "transiciones": len(self.delta),
                "simbolos_entrada": len(self.Sigma), "simbolos_pila": len(self.Gamma)}


class Marco:
    __slots__ = ("sim", "regla", "nombre", "texto", "n")

    def __init__(self, sim, regla=None, nombre=None):
        self.sim, self.regla, self.nombre, self.texto, self.n = sim, regla, nombre, [], {}


class ResultadoXML:
    def __init__(self, v):
        self.valido = not v.errores
        self.errores, self.costo, self.violaciones = v.errores, v.costo, len(v.errores)
        self.mal_formado, self.traza, self.prof_max, self.pasos = v.mal_formado, v.traza, v.prof_max, v.pasos

    def __repr__(self):
        if self.valido:
            return f"VALIDO (costo {self.costo}, {self.pasos} pasos, pila max {self.prof_max})"
        return (f"{'MAL FORMADO' if self.mal_formado else 'INVALIDO'} ({self.violaciones} "
                f"violacion(es), costo {self.costo}): "
                + "; ".join(f"{e['ruta']}: {e['mensaje']}" for e in self.errores))


class ValidadorXML:
    def __init__(self, M, parar_en_primero=False, max_profundidad=None, traza=False):
        self.M, self.E = M, M.E
        self.q, self.pila = "Q0", [Marco("Z0")]
        self.parar, self.max_prof = parar_en_primero, max_profundidad
        self.errores, self.costo, self.pasos, self.prof_max = [], 0, 0, 1
        self.mal_formado = False
        self.traza = [] if traza else None

    def _ruta(self, incluir_tope=True):
        partes = []
        marcos = self.pila[1:] if incluir_tope else self.pila[1:-1]
        cuenta_padre = None
        for m in marcos:
            idx = cuenta_padre.get(m.nombre, 1) if cuenta_padre else 1
            partes.append(f"{m.nombre}[{idx}]")
            cuenta_padre = m.n
        return "/" + "/".join(partes)

    def _violar(self, msg, tok, ruta):
        self.errores.append({"ruta": ruta, "mensaje": msg,
                             "linea": tok.linea if tok else None,
                             "columna": tok.columna if tok else None,
                             "byte": tok.pos if tok else None})

    def _guarda(self, g, dato, tok):
        nombre, _, p = g
        tope = self.pila[-1]
        if nombre == "atributos":
            r = self.E.reglas[p]
            attrs = dato[1]
            fallas = []
            for an, spec in r["atributos"].items():
                if an not in attrs:
                    if spec["req"]:
                        fallas.append(f"falta el atributo obligatorio '{an}'")
                    continue
                if "fijo" in spec and attrs[an] != spec["fijo"]:
                    fallas.append(f"atributo '{an}' debe valer '{spec['fijo']}'")
                fallas += [f"atributo '{an}': {m}" for m in chequear_simple(spec["tipo"], attrs[an])]
            for an in attrs:
                if an not in r["atributos"] and not an.startswith("xmlns"):
                    fallas.append(f"atributo '{an}' no declarado")
            return fallas
        if nombre == "no_declarado":
            return [f"<{dato[0]}> no es un elemento raiz declarado (se esperaba {' o '.join(p)})"]
        if nombre == "no_permitido":
            esp = " o ".join(f"<{x}>" for x in p) or f"</{tope.nombre}>"
            return [f"<{dato[0]}> no permitido aqui; se esperaba {esp}"]
        if nombre == "completo":
            return [f"contenido incompleto: falta {' o '.join('<' + x + '>' for x in p)}"]
        if nombre == "valor":
            return chequear_simple(p, "".join(tope.texto))
        if nombre == "vacio":
            return [f"<{tope.nombre}> debe estar vacio (EMPTY) y tiene texto"]
        if nombre == "solo_espacios":
            return [] if not dato.strip() else [f"texto '{dato.strip()[:20]}' no permitido: "
                                                 f"<{tope.nombre}> solo admite elementos"]
        if nombre == "acumula":
            tope.texto.append(dato)
            return []
        raise ValueError(nombre)

    def _ejecutar(self, fila, ev, dato, tok, a):
        antes = (self.q, [m.sim for m in self.pila]) if self.traza is not None else None
        costo = 0 if a == EPS else COSTO["estructura"]
        fallas = []
        if fila["pila"] == "pop" or ev == "texto":
            ruta = self._ruta()
        else:
            ruta = None
        for g in fila["guardas"]:
            costo += g[1]
            msgs = self._guarda(g, dato, tok)
            if msgs:
                if ruta is None:      # abrir: el error es del hijo que se abre
                    padre = self.pila[-1]
                    idx = padre.n.get(dato[0], 0) + 1
                    ruta = self._ruta() + ("/" if len(self.pila) > 1 else "") + f"{dato[0]}[{idx}]"
                    ruta = ruta.replace("//", "/")
                for m in msgs:
                    fallas.append(m)
                    self._violar(m, tok, ruta)
                if self.parar or g[0] in ("no_permitido", "no_declarado"):
                    break
        self.costo += costo
        op = fila["pila"]
        for parte in op.split("|"):
            if parte == "pop":
                self.pila.pop()
            elif parte.startswith("cambia:"):
                self.pila[-1].sim = parte[7:]
            elif parte.startswith("push:"):
                if self.max_prof is not None and len(self.pila) >= self.max_prof:
                    self.mal_formado = True
                    self._violar(f"profundidad maxima {self.max_prof} superada", tok, self._ruta())
                    return False
                nombre_hijo = dato[0]
                padre = self.pila[-1]
                padre.n[nombre_hijo] = padre.n.get(nombre_hijo, 0) + 1
                s = parte[5:]
                regla = None if s == "*" else self.E.reglas[next(
                    j for j, r in enumerate(self.E.reglas) if r["nombre"] == s.split("@")[0]
                    and (padre.regla is None or padre.regla["hijos"].get(nombre_hijo) == j
                         or self.q == "Q0"))]
                self.pila.append(Marco(s, regla, nombre_hijo))
                self.prof_max = max(self.prof_max, len(self.pila))
        self.q = fila["a_estado"]
        self.pasos += 1
        if self.traza is not None:
            self.traza.append({"paso": self.pasos, "token": tok.texto if tok and a != EPS else EPS,
                               "simbolo": a, "de": antes[0], "pila_antes": antes[1], "a": self.q,
                               "pila_despues": [m.sim for m in self.pila],
                               "k": [fila["de"], a, fila["tope"]],
                               "fila": f"δ({fila['de']}, {a}, {fila['tope']}) = ({fila['a_estado']}, {fila['pila']})",
                               "costo": costo, "costo_acum": self.costo, "violaciones": fallas,
                               "nota": fila["nota"], "linea": tok.linea if tok else None,
                               "columna": tok.columna if tok else None})
        return True

    def evento(self, ev, dato, tok):
        X = self.pila[-1].sim
        if ev == "abre":
            a = f"<{dato[0]}>"
            if (self.q, a, X) not in self.M.delta:
                a = "<*>"
        elif ev == "cierra":
            a = f"</{dato}>" if X != "*" else "</*>"
        else:
            a = "TEXTO"
        if self.q == "QF":
            return
        fila = self.M.delta.get((self.q, a, X))
        if fila is None:      # no deberia pasar: eventos() ya reviso el buen formado
            self.mal_formado = True
            self._violar(f"evento inesperado {a} con tope {X}", tok, self._ruta())
            return
        if not self._ejecutar(fila, ev, dato, tok, a):
            return
        while (self.q, EPS, self.pila[-1].sim) in self.M.delta:
            self._ejecutar(self.M.delta[(self.q, EPS, self.pila[-1].sim)], None, None, tok, EPS)


def validar_xml(M, texto, bloque=4096, parar_en_primero=False, max_profundidad=None, traza=False):
    """Streaming: bytes -> tokens (AFD) -> eventos (pila de nombres) -> DPDA."""
    v = ValidadorXML(M, parar_en_primero, max_profundidad, traza)
    datos = texto.encode("utf-8") if isinstance(texto, str) else texto

    def tokens():
        lx = LexerXML()
        for i in range(0, len(datos), bloque):
            try:
                yield from lx.alimentar(datos[i:i + bloque])
            except ErrorLexico:
                yield from lx.parcial      # los tokens completos antes del error si cuentan
                raise
        yield from lx.terminar()
    try:
        for ev, dato, tok in eventos(tokens()):
            v.evento(ev, dato, tok)
            if v.mal_formado or (v.parar and v.errores):
                break
    except (ErrorXML, ErrorLexico) as e:
        v.mal_formado = True
        v._violar(f"mal formado: {e}", None, v._ruta())
    return ResultadoXML(v)


def compilar(origen, texto, raiz=None):
    E = leer_dtd(texto, raiz) if origen == "DTD" else leer_xsd(texto)
    return DPDAXML(E)


# =========================================================================
# Salidas: definicion formal, AFD de cada elemento (texto y Graphviz)
# =========================================================================
def definicion_formal(M):
    E, t = M.E, M.tamano()
    lin = [f"Esquema {E.origen}: {len(E.reglas)} elementos", ""]
    for r in E.reglas:
        if r["contenido"] in ("elementos", "mixto") and "modelo" in r:
            d, d0 = r["afd"], r["afd_sin_min"]
            lin.append(f"  <{r['nombre']}> {r['contenido']}: ER = {texto_er(r['modelo'])}")
            lin.append(f"      AFD {d0.n} estados -> AFD minimo {d.n} estados, finales {sorted(d.finales)}")
        else:
            extra = f" tipo {r['texto']}" if r["texto"] else ""
            lin.append(f"  <{r['nombre']}> {r['contenido']}{extra}")
        if r["atributos"]:
            lin.append("      atributos: " + ", ".join(
                f"{n}{'*' if a['req'] else ''}:{a['tipo'].get('base')}" for n, a in r["atributos"].items()))
    lin += ["", "M = (Q, Σ, Γ, δ, q0, Z0, F, w)",
            f"Q  = {{{', '.join(sorted(M.Q))}}}",
            f"Σ  ({t['simbolos_entrada']}) = {{{', '.join(sorted(M.Sigma))}}}",
            f"Γ  ({t['simbolos_pila']}) = {{{', '.join(sorted(M.Gamma))}}}",
            "     e@s = elemento e abierto, con su AFD de contenido en el estado s",
            f"δ  ({t['transiciones']} filas)    q0 = Q0    Z0 = Z0    F = {{QF}}",
            "w : δ -> (N ∪ {∞}, min, +, ∞, 0); comprobaciones ordenadas por costo", "",
            "Determinismo: " + ("OK" if not M.verificar_determinismo() else str(M.verificar_determinismo()))]
    for nivel, msg in E.avisos:
        lin.append(f"[{nivel}] {msg}")
    return "\n".join(lin)


def dot_afd(r):
    d = r["afd"]
    l = ["digraph AFD {", '  rankdir=LR; node [shape=circle, fontname="Helvetica", fontsize=11];',
         f'  labelloc="t"; label="<{r["nombre"]}>: {texto_er(r["modelo"]).replace(chr(34), "")}";',
         '  ini [shape=point];', "  ini -> 0;"]
    for s in d.finales:
        l.append(f"  {s} [shape=doublecircle];")
    juntas = {}
    for (s, a), t in d.trans.items():
        juntas.setdefault((s, t), []).append(a)
    for (s, t), aa in juntas.items():
        l.append(f'  {s} -> {t} [label="{", ".join(sorted(aa))}"];')
    l.append("}")
    return "\n".join(l)


def tabla_texto(M):
    lin = [f"{'de':<4} {'lee':<16} {'tope':<16} {'a':<4} {'pila':<34} {'w':>3}  comprobaciones"]
    for f in sorted(M.delta.values(), key=lambda f: (f["tope"], f["de"], f["a"])):
        lin.append(f"{f['de']:<4} {f['a']:<16} {f['tope']:<16} {f['a_estado']:<4} {f['pila']:<34} "
                   f"{f['costo']:>3}  {', '.join(g[0] for g in f['guardas'])}")
    return "\n".join(lin)


# =========================================================================
# PRUEBAS (contra lxml, que valida DTD y XSD de verdad)
# =========================================================================
DTD_EJ = """<!ELEMENT biblioteca (libro+)>
<!ELEMENT libro (titulo, autor+, anio?, (resumen | nota)*)>
<!ATTLIST libro id CDATA #REQUIRED estado (nuevo|usado) #IMPLIED>
<!ELEMENT titulo (#PCDATA)>
<!ELEMENT autor (#PCDATA)>
<!ELEMENT anio (#PCDATA)>
<!ELEMENT resumen (#PCDATA | b | i)*>
<!ELEMENT nota EMPTY>
<!ATTLIST nota tipo CDATA #FIXED "info">
<!ELEMENT b (#PCDATA)>
<!ELEMENT i (#PCDATA)>"""

XSD_EJ = """<xs:schema xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <xs:element name="pedido">
    <xs:complexType>
      <xs:sequence>
        <xs:element name="cliente" type="xs:string"/>
        <xs:element name="item" minOccurs="1" maxOccurs="3">
          <xs:complexType>
            <xs:sequence>
              <xs:element name="nombre" type="nombreCorto"/>
              <xs:element name="cantidad" type="xs:positiveInteger"/>
              <xs:element name="precio" type="precio" minOccurs="0"/>
            </xs:sequence>
            <xs:attribute name="sku" type="xs:string" use="required"/>
          </xs:complexType>
        </xs:element>
        <xs:choice minOccurs="0">
          <xs:element name="urgente"><xs:complexType/></xs:element>
          <xs:element name="nota" type="xs:string"/>
        </xs:choice>
      </xs:sequence>
      <xs:attribute name="id" type="xs:integer" use="required"/>
      <xs:attribute name="moneda" type="moneda"/>
    </xs:complexType>
  </xs:element>
  <xs:simpleType name="nombreCorto">
    <xs:restriction base="xs:string"><xs:minLength value="2"/><xs:maxLength value="8"/></xs:restriction>
  </xs:simpleType>
  <xs:simpleType name="precio">
    <xs:restriction base="xs:decimal"><xs:minInclusive value="0"/><xs:maxInclusive value="1000"/></xs:restriction>
  </xs:simpleType>
  <xs:simpleType name="moneda">
    <xs:restriction base="xs:string"><xs:enumeration value="COP"/><xs:enumeration value="USD"/></xs:restriction>
  </xs:simpleType>
</xs:schema>"""


def correr_pruebas():
    import random
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    # --- ER -> AFD minimo ---
    d, d0 = afd_de(_parsear_modelo("(a, b*, c?)"))
    acepta = lambda d, w: (lambda s: s is not None and s in d.finales)(
        __import__("functools").reduce(lambda s, x: None if s is None else d.paso(s, x), w, 0))
    chequear("AFD de (a,b*,c?)", all(acepta(d, w) for w in ["a", "ab", "abbbc", "ac"])
             and not any(acepta(d, w) for w in ["", "b", "acb", "aa"]))
    d, d0 = afd_de(_parsear_modelo("((a|b)*, a, (a|b))"))
    chequear("minimizacion reduce estados", d.n <= d0.n and d.n == 4)
    chequear("AFD minimo (a|b)*a(a|b): penultimo es a",
             all(acepta(d, w) for w in ["ab", "aa", "baa", "bab"]) and not any(acepta(d, w) for w in ["ba", "bb", "a", ""]))

    # --- XML bien formado ---
    for malo in ["<a><b></a></b>", "<a>", "</a>", "<a/><b/>", "texto<a/>", "<a x='1' x='2'/>",
                 "<a>&foo;</a>", "<a>x & y</a>", "<a><b></b>", ""]:
        try:
            list(eventos(tokenizar_xml(malo)))
            chequear(f"mal formado {malo!r}", False)
        except (ErrorXML, ErrorLexico):
            chequear(f"mal formado {malo!r}", True)
    raiz = parsear_xml('<?xml version="1.0"?><!-- c --><a k="&lt;1&gt;"><b>x &amp; y</b><c/></a>')
    chequear("arbol XML", raiz.nombre == "a" and raiz.attrs["k"] == "<1>"
             and raiz.elementos()[0].texto() == "x & y")

    # --- DTD ---
    M = compilar("DTD", DTD_EJ, raiz="biblioteca")
    chequear("DTD determinista", M.verificar_determinismo() == [])
    bueno = ('<biblioteca><libro id="1" estado="nuevo"><titulo>Automatas</titulo><autor>Brena</autor>'
             '<anio>2003</anio><resumen>Un <b>buen</b> libro</resumen><nota/></libro></biblioteca>')
    chequear("DTD valido", validar_xml(M, bueno).valido)
    r = validar_xml(M, '<biblioteca><libro estado="viejo"><autor>X</autor></libro></biblioteca>')
    chequear("DTD: 3 errores (falta id, estado invalido, falta titulo)",
             not r.valido and r.violaciones >= 3)
    chequear("DTD: ruta del error", any(e["ruta"].startswith("/biblioteca[1]/libro[1]") for e in r.errores))
    try:
        leer_dtd('<!ENTITY a "aaaa"><!ELEMENT r (#PCDATA)>')
        chequear("ENTITY rechazada (aviso de seguridad)",
                 any(n == "SEGURIDAD" for n, _ in leer_dtd('<!ENTITY a "x"><!ELEMENT r (#PCDATA)>').avisos))
    except Exception:
        chequear("ENTITY rechazada (aviso de seguridad)", False)

    # --- XSD (leido con nuestro propio parser XML) ---
    MX = compilar("XSD", XSD_EJ)
    chequear("XSD determinista", MX.verificar_determinismo() == [])
    bueno = ('<pedido id="7" moneda="COP"><cliente>Ana</cliente><item sku="A1"><nombre>pan</nombre>'
             '<cantidad>2</cantidad><precio>3.5</precio></item><urgente/></pedido>')
    chequear("XSD valido", validar_xml(MX, bueno).valido)
    r = validar_xml(MX, '<pedido id="x"><cliente>Ana</cliente><item><nombre>p</nombre>'
                        '<cantidad>0</cantidad></item></pedido>')
    chequear("XSD: 4 errores", not r.valido and r.violaciones == 4)
    chequear("streaming 1 byte", repr(validar_xml(MX, bueno, bloque=1)) == repr(validar_xml(MX, bueno)))
    n = 3000
    Mrec = compilar("DTD", "<!ELEMENT n (n?)>")
    chequear("anidamiento 3000", validar_xml(Mrec, "<n>" * n + "</n>" * n).valido)
    r = validar_xml(Mrec, "<n>" * 50 + "</n>" * 50, max_profundidad=10)
    chequear("limite de profundidad", not r.valido and "profundidad" in r.errores[0]["mensaje"])

    # --- contra lxml con documentos al azar ---
    try:
        from lxml import etree
        from io import StringIO
    except ImportError:
        print("  (lxml no instalada: se omite la comparacion)")
        etree = None
    if etree:
        random.seed(9)
        textos = ["Ana", "pan", "x", "2", "0", "-1", "3.5", "1001", "abcdefghij", " 4 ", "COP", "EUR"]

        def gen_dtd(nombre, p=0):
            hijos = {"biblioteca": ["libro"], "libro": ["titulo", "autor", "anio", "resumen", "nota"],
                     "resumen": ["b", "i"]}.get(nombre, [])
            attrs = ""
            if nombre == "libro":
                if random.random() < 0.85:
                    attrs += f' id="{random.choice(textos)}"'
                if random.random() < 0.4:
                    attrs += f' estado="{random.choice(["nuevo", "usado", "roto"])}"'
            if nombre == "nota" and random.random() < 0.3:
                attrs += f' tipo="{random.choice(["info", "otro"])}"'
            if random.random() < 0.05:
                attrs += ' raro="1"'
            if nombre == "nota":
                return f"<nota{attrs}/>" if random.random() < 0.9 else f"<nota{attrs}>t</nota>"
            if not hijos or p > 3:
                return f"<{nombre}{attrs}>{random.choice(textos)}</{nombre}>"
            orden = {"libro": ["titulo", "autor", "autor", "anio", "resumen", "nota"]}.get(nombre, hijos * 2)
            partes = [x for x in orden if random.random() < 0.75]
            if random.random() < 0.2:
                random.shuffle(partes)
            if random.random() < 0.1:
                partes.append(random.choice(["titulo", "b", "biblioteca"]))
            cuerpo = "".join(gen_dtd(x, p + 1) for x in partes)
            if nombre == "resumen" or random.random() < 0.05:
                cuerpo = random.choice(textos) + cuerpo
            return f"<{nombre}{attrs}>{cuerpo}</{nombre}>"

        def gen_xsd(nombre, p=0):
            if nombre == "pedido":
                attrs = (f' id="{random.choice(textos)}"' if random.random() < 0.9 else "") + \
                        (f' moneda="{random.choice(textos)}"' if random.random() < 0.4 else "")
                hijos = [x for x in ["cliente", "item", "item", "item", "item", "urgente", "nota"]
                         if random.random() < 0.6]
            elif nombre == "item":
                attrs = f' sku="{random.choice(textos)}"' if random.random() < 0.9 else ""
                hijos = [x for x in ["nombre", "cantidad", "precio"] if random.random() < 0.8]
            else:
                attrs = ""
                hijos = None
            if random.random() < 0.05:
                attrs += ' z="1"'
            if hijos is None:
                if nombre == "urgente":
                    return random.choice(["<urgente/>", "<urgente/>", "<urgente>x</urgente>"])
                return f"<{nombre}{attrs}>{random.choice(textos)}</{nombre}>"
            if random.random() < 0.15:
                random.shuffle(hijos)
            return f"<{nombre}{attrs}>" + "".join(gen_xsd(h, p + 1) for h in hijos) + f"</{nombre}>"

        dtd = etree.DTD(StringIO(DTD_EJ))
        dif = 0
        for _ in range(3000):
            raizn = random.choice(["biblioteca", "biblioteca", "libro", "resumen"])
            doc = gen_dtd(raizn)
            ref = dtd.validate(etree.fromstring(doc))
            nuestro = validar_xml(compilar("DTD", DTD_EJ), doc).valido
            if ref != nuestro:
                dif += 1
                if dif <= 3:
                    print("   DIF DTD", doc[:120], "lxml:", ref, validar_xml(compilar("DTD", DTD_EJ), doc))
        chequear("3000 documentos al azar: DTD = lxml", dif == 0)
        xsd = etree.XMLSchema(etree.fromstring(XSD_EJ.encode()))
        dif = 0
        for _ in range(3000):
            doc = gen_xsd("pedido")
            ref = xsd.validate(etree.fromstring(doc))
            nuestro = validar_xml(MX, doc).valido
            if ref != nuestro:
                dif += 1
                if dif <= 3:
                    print("   DIF XSD", doc[:150], "lxml:", ref, validar_xml(MX, doc))
        chequear("3000 documentos al azar: XSD = lxml", dif == 0)
        # bien formado igual que lxml
        random.seed(4)
        base = bueno
        dif = 0
        for _ in range(2000):
            t = list(base)
            for _ in range(random.randint(1, 2)):
                pos = random.randrange(len(t))
                op = random.choice("bis")
                if op == "b":
                    del t[pos]
                elif op == "i":
                    t.insert(pos, random.choice("<>/=\"'& a"))
                else:
                    t[pos] = random.choice("<>/=\"'& a")
            txt = "".join(t)
            try:
                etree.fromstring(txt)
                ref = True
            except etree.XMLSyntaxError:
                ref = False
            r = validar_xml(MX, txt)
            if ref == r.mal_formado:
                dif += 1
                if dif <= 3:
                    print("   DIF bien formado", repr(txt[:100]), "lxml:", ref, r)
        chequear("2000 documentos danados: bien/mal formado = lxml", dif == 0)

    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8")     # consola de Windows
    except Exception:
        pass
    a = sys.argv[1:]
    leer = lambda p: open(p, encoding="utf-8").read()
    if not a:
        correr_pruebas()
    elif a[0] == "--formal":
        M = compilar("DTD" if a[1] == "--dtd" else "XSD", leer(a[2]))
        print(definicion_formal(M))
    elif a[0] == "--tabla":
        M = compilar("DTD" if a[1] == "--dtd" else "XSD", leer(a[2]))
        print(tabla_texto(M))
    elif a[0] in ("--dtd", "--xsd"):
        M = compilar("DTD" if a[0] == "--dtd" else "XSD", leer(a[1]))
        r = validar_xml(M, leer(a[2]), traza="--traza" in a)
        if r.traza:
            for p in r.traza:
                print(f"  {p['paso']:>3}. {p['simbolo']:<14} {p['fila']:<60} w={p['costo']}"
                      + (f"  !! {'; '.join(p['violaciones'])}" if p["violaciones"] else ""))
        print(" ", r)

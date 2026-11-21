r"""
lexer_v4.py - Fase 1 completa del proyecto (JSON + XML, streaming)

Proyecto final LFA 2026-2 - UPTC Sogamoso
Validacion en tiempo real de esquemas JSON/XML con automatas de pila ponderados

Que cubre de la Fase 1:
  - Alfabeto de BYTES: el lexer lee bytes (0..255), no caracteres.
  - Delimitadores y tokens de JSON:  { } [ ] : ,  CADENA  NUMERO  LITERAL
  - Tokens de XML:  ETIQUETA_ABRE  ETIQUETA_CIERRA  ETIQUETA_VACIA
                    TEXTO  DECLARACION  COMENTARIO
  - Cada token se reconoce con un AFD guardado como TABLA de transicion:
        AFD_NUMERO   (q0..q8, con exponente)
        AFD_CADENA   (c0..c7, escapes \" \\ \/ \b \f \n \r \t y \uXXXX)
        AFD_LITERAL  (true, false, null)
        AFD_ETIQUETA (etiquetas XML con atributos, declaracion, comentario)
        AFD_TEXTO    (texto XML con entidades &amp; &#38; ...)
  - Tokenizador en STREAMING: se le dan bloques de bytes con alimentar()
    y recuerda en que estado quedo entre un bloque y otro.
  - Cada token guarda su posicion (linea y columna).
  - Gramaticas regulares y diagramas: salen de las MISMAS tablas
    (python lexer_v4.py --gramaticas  /  --dot).
  - El lexer del propio esquema: el esquema es JSON, lo lee el mismo lexer.

Como correrlo:
  python lexer_v4.py                     -> corre todas las pruebas
  python lexer_v4.py archivo.json        -> tokeniza un archivo (bloques de 4 KB)
  python lexer_v4.py archivo.xml         -> igual, en modo XML
  python lexer_v4.py --texto '{"a": 1}'  -> tokeniza un texto
  python lexer_v4.py --gramaticas        -> imprime las gramaticas regulares
  python lexer_v4.py --dot               -> escribe los diagramas .dot (Graphviz)
"""

import sys
from collections import namedtuple

# pos = byte (desde 0) donde empieza el token; lo usa la Fase 6 para reportar errores
Token = namedtuple("Token", "tipo texto linea columna pos", defaults=(None,))


class ErrorLexico(Exception):
    """Se lanza cuando un pedazo de la entrada no es un token valido."""


# ===================================================================
# 1. UN AFD ES: nombre, estado inicial, funcion de clases, tabla,
#    y estados de aceptacion (cada uno dice que token produce).
# ===================================================================
class AFD:
    def __init__(self, nombre, inicial, clase, tabla, aceptacion,
                 no_puede_seguir=b"", leyenda=None):
        self.nombre = nombre
        self.inicial = inicial
        self.clase = clase              # byte -> nombre de clase
        self.tabla = tabla              # (estado, clase) -> estado
        self.aceptacion = aceptacion    # estado -> tipo de token
        self.no_puede_seguir = no_puede_seguir  # bytes prohibidos justo despues
        self.leyenda = leyenda or {}    # clase -> explicacion (para gramaticas)

    def paso(self, q, b):
        return self.tabla.get((q, self.clase(b)))


def _rango(desde, hasta):
    return set(range(ord(desde), ord(hasta) + 1))


DIG = _rango("0", "9")
HEX = DIG | _rango("a", "f") | _rango("A", "F")
LETRA = _rango("a", "z") | _rango("A", "Z") | {ord("_"), ord(":")}
NOMBRE = LETRA | DIG | {ord("-"), ord(".")}
ESPACIO = {ord(" "), ord("\t"), ord("\n"), ord("\r")}

# ===================================================================
# 2. AFD DE NUMEROS (q0..q8)
#    q0 inicio  q1 "-"  q2 "0" solo  q3 enteros  q4 "."  q5 decimales
#    q6 "e"  q7 signo del exponente  q8 digitos del exponente
# ===================================================================
def clase_numero(b):
    c = chr(b)
    if c == "-": return "menos"
    if c == "+": return "mas"
    if c == "0": return "cero"
    if "1" <= c <= "9": return "dig19"
    if c == ".": return "punto"
    if c in "eE": return "exp"
    return "otro"

AFD_NUMERO = AFD(
    "NUMERO", "q0", clase_numero,
    {
        ("q0", "menos"): "q1", ("q0", "cero"): "q2", ("q0", "dig19"): "q3",
        ("q1", "cero"): "q2", ("q1", "dig19"): "q3",
        ("q2", "punto"): "q4", ("q2", "exp"): "q6",
        ("q3", "cero"): "q3", ("q3", "dig19"): "q3",
        ("q3", "punto"): "q4", ("q3", "exp"): "q6",
        ("q4", "cero"): "q5", ("q4", "dig19"): "q5",
        ("q5", "cero"): "q5", ("q5", "dig19"): "q5", ("q5", "exp"): "q6",
        ("q6", "mas"): "q7", ("q6", "menos"): "q7",
        ("q6", "cero"): "q8", ("q6", "dig19"): "q8",
        ("q7", "cero"): "q8", ("q7", "dig19"): "q8",
        ("q8", "cero"): "q8", ("q8", "dig19"): "q8",
    },
    {"q2": "NUMERO", "q3": "NUMERO", "q5": "NUMERO", "q8": "NUMERO"},
    no_puede_seguir=b"0123456789.eE+-",
    leyenda={"menos": "-", "mas": "+", "cero": "0", "dig19": "1..9",
             "punto": ".", "exp": "e | E"},
)

# ===================================================================
# 3. AFD DE CADENAS (c0..c7)
#    c0 inicio  c1 dentro de la cadena  c2 cadena cerrada (acepta)
#    c3 despues de "\"   c4..c7 los 4 hexadecimales de \uXXXX
# ===================================================================
def clase_cadena(b):
    c = chr(b)
    if b < 0x20: return "control"     # JSON no permite saltos de linea crudos
    if c == '"': return "comilla"
    if c == "\\": return "barra"
    if c == "u": return "u"
    if c in "bf": return "bf"          # son escape Y tambien hexadecimal
    if c in "nrt/": return "esc"
    if b in HEX: return "hex"
    return "otro"                      # cualquier otro byte (incluye UTF-8)

_tabla_cadena = {("c0", "comilla"): "c1"}
for k in ("u", "bf", "esc", "hex", "otro"):
    _tabla_cadena[("c1", k)] = "c1"
_tabla_cadena[("c1", "comilla")] = "c2"
_tabla_cadena[("c1", "barra")] = "c3"
for k in ("comilla", "barra", "bf", "esc"):
    _tabla_cadena[("c3", k)] = "c1"
_tabla_cadena[("c3", "u")] = "c4"
for a, s in (("c4", "c5"), ("c5", "c6"), ("c6", "c7"), ("c7", "c1")):
    _tabla_cadena[(a, "hex")] = s
    _tabla_cadena[(a, "bf")] = s

AFD_CADENA = AFD(
    "CADENA", "c0", clase_cadena, _tabla_cadena, {"c2": "CADENA"},
    leyenda={"comilla": '"', "barra": "\\", "u": "u", "bf": "b | f",
             "esc": "n | r | t | /", "hex": "0..9 a c d e A..F",
             "otro": "cualquier otro byte >= 0x20"},
)

# ==================================================================
# 4. AFD DE LITERALES (true, false, null) - se arma como un arbol
# ==================================================================
def _afd_palabras(nombre, palabras, tipo):
    tabla, acept, n = {}, {}, 0
    for p in palabras:
        q = "l0"
        for ch in p:
            if (q, ch) not in tabla:
                n += 1
                tabla[(q, ch)] = f"l{n}"
            q = tabla[(q, ch)]
        acept[q] = tipo
    return AFD(nombre, "l0", lambda b: chr(b), tabla, acept,
               no_puede_seguir=bytes(sorted(LETRA | DIG)))

AFD_LITERAL = _afd_palabras("LITERAL", ["true", "false", "null"], "LITERAL")

# ==================================================================
# 5. AFD DE ETIQUETAS XML
#    x0 inicio  x1 "<"  x2 nombre  x3 espacio dentro de la etiqueta
#    x4 nombre de atributo  x5 "="  x6 valor "..."  x7 valor '...'
#    x8 "/" de <a/>  x9 acepta ABRE  x10 "</"  x11 despues del valor
#    x12 acepta VACIA  x13 nombre de cierre  x14 espacio en cierre
#    x15 acepta CIERRA   x16 espacio entre el nombre del atributo y el '=' (v4)
#    d1 d2 d3: declaracion <? ... ?>      k1..k6: comentario <!-- ... -->
# ==================================================================
def clase_etiqueta(b):
    c = chr(b)
    if c == "<": return "menor"
    if c == ">": return "mayor"
    if c == "/": return "barra"
    if c == "=": return "igual"
    if c == '"': return "comilla2"
    if c == "'": return "comilla1"
    if c == "?": return "interrog"
    if c == "!": return "exclam"
    if c == "-": return "guion"
    if b in ESPACIO: return "esp"
    if b in LETRA: return "letra"
    if b in NOMBRE: return "nomchar"
    return "otro"

_T = {}
def _f(q, clases, p):
    for k in clases.split():
        _T[(q, k)] = p

TODAS = "menor mayor barra igual comilla2 comilla1 interrog exclam guion esp letra nomchar otro"
_f("x0", "menor", "x1")
_f("x1", "letra", "x2"); _f("x1", "barra", "x10")
_f("x1", "interrog", "d1"); _f("x1", "exclam", "k1")
_f("x2", "letra nomchar guion", "x2"); _f("x2", "esp", "x3")
_f("x2", "mayor", "x9"); _f("x2", "barra", "x8")
_f("x3", "esp", "x3"); _f("x3", "letra", "x4")
_f("x3", "mayor", "x9"); _f("x3", "barra", "x8")
_f("x4", "letra nomchar guion", "x4"); _f("x4", "igual", "x5")
# v4: XML permite espacios alrededor del '=' (Eq ::= S? '=' S?)
_f("x4", "esp", "x16"); _f("x16", "esp", "x16"); _f("x16", "igual", "x5")
_f("x5", "esp", "x5")
_f("x5", "comilla2", "x6"); _f("x5", "comilla1", "x7")
_f("x6", TODAS.replace("menor ", "").replace("comilla2 ", ""), "x6")
_f("x6", "comilla2", "x11")
_f("x7", TODAS.replace("menor ", "").replace("comilla1 ", ""), "x7")
_f("x7", "comilla1", "x11")
_f("x11", "esp", "x3"); _f("x11", "mayor", "x9"); _f("x11", "barra", "x8")
_f("x8", "mayor", "x12")
_f("x10", "letra", "x13")
_f("x13", "letra nomchar guion", "x13"); _f("x13", "esp", "x14")
_f("x13", "mayor", "x15")
_f("x14", "esp", "x14"); _f("x14", "mayor", "x15")
# declaracion <? ... ?>
_f("d1", TODAS.replace("interrog ", ""), "d1"); _f("d1", "interrog", "d2")
_f("d2", "interrog", "d2"); _f("d2", "mayor", "d3")
_f("d2", TODAS.replace("interrog ", "").replace("mayor ", ""), "d1")
# comentario <!-- ... -->
_f("k1", "guion", "k2"); _f("k2", "guion", "k3")
_f("k3", TODAS.replace("guion ", ""), "k3"); _f("k3", "guion", "k4")
_f("k4", TODAS.replace("guion ", ""), "k3"); _f("k4", "guion", "k5")
_f("k5", "mayor", "k6")

AFD_ETIQUETA = AFD(
    "ETIQUETA", "x0", clase_etiqueta, _T,
    {"x9": "ETIQUETA_ABRE", "x12": "ETIQUETA_VACIA", "x15": "ETIQUETA_CIERRA",
     "d3": "DECLARACION", "k6": "COMENTARIO"},
    leyenda={"menor": "<", "mayor": ">", "barra": "/", "igual": "=",
             "comilla2": '"', "comilla1": "'", "interrog": "?", "exclam": "!",
             "guion": "-", "esp": "espacio", "letra": "a..z A..Z _ :",
             "nomchar": "0..9 .", "otro": "cualquier otro byte"},
)

# ==================================================================
# 6. AFD DE TEXTO XML (entre etiquetas), con entidades &nombre; &#123;
#    t0 inicio  t1 texto (acepta)  t2 "&"  t3 nombre de entidad
#    t4 "&#"  t5 digitos de la entidad numerica
# ==================================================================
def clase_texto(b):
    c = chr(b)
    if c == "<": return "menor"
    if c == "&": return "amp"
    if c == ";": return "pyc"
    if c == "#": return "num"
    if b in DIG: return "dig"
    if b in LETRA: return "letra"
    return "otro"

AFD_TEXTO = AFD(
    "TEXTO", "t0", clase_texto,
    {
        ("t0", "otro"): "t1", ("t0", "letra"): "t1", ("t0", "dig"): "t1",
        ("t0", "pyc"): "t1", ("t0", "num"): "t1", ("t0", "amp"): "t2",
        ("t1", "otro"): "t1", ("t1", "letra"): "t1", ("t1", "dig"): "t1",
        ("t1", "pyc"): "t1", ("t1", "num"): "t1", ("t1", "amp"): "t2",
        ("t2", "letra"): "t3", ("t2", "num"): "t4",
        ("t3", "letra"): "t3", ("t3", "dig"): "t3", ("t3", "pyc"): "t1",
        ("t4", "dig"): "t5", ("t5", "dig"): "t5", ("t5", "pyc"): "t1",
    },
    {"t1": "TEXTO"},
    leyenda={"amp": "&", "pyc": ";", "num": "#", "dig": "0..9",
             "letra": "a..z A..Z _ :", "otro": "otro byte distinto de < & ; #"},
)

TODOS_LOS_AFD = [AFD_NUMERO, AFD_CADENA, AFD_LITERAL, AFD_ETIQUETA, AFD_TEXTO]

SIMBOLOS_JSON = {
    ord("{"): "LLAVE_ABRE", ord("}"): "LLAVE_CIERRA",
    ord("["): "CORCHETE_ABRE", ord("]"): "CORCHETE_CIERRA",
    ord(":"): "DOS_PUNTOS", ord(","): "COMA",
}


# ===================================================================
# 7. EL TOKENIZADOR EN STREAMING
#    alimentar(bloque) recibe bytes y devuelve los tokens completos.
#    Lo que quede a medias se guarda (estado del AFD + bytes leidos)
#    y sigue con el proximo bloque. terminar() cierra al final.
# ===================================================================
class Lexer:
    def __init__(self, modo="json"):
        if modo not in ("json", "xml"):
            raise ValueError("modo debe ser 'json' o 'xml'")
        self.modo = modo
        self.afd = None          # AFD que esta trabajando (None = entre tokens)
        self.q = None            # estado actual de ese AFD
        self.pedazo = bytearray()
        self.linea, self.columna = 1, 1
        self.pos = 0             # bytes leidos hasta ahora
        self.inicio = (1, 1, 0)  # linea, columna y byte donde empezo el token actual
        self.parcial = []        # tokens ya completos del bloque en curso (por si hay error)

    # --- escoger el AFD segun el primer byte (modo JSON) ---
    def _elegir_json(self, b):
        if b == ord('"'):
            return AFD_CADENA
        if b == ord("-") or b in DIG:
            return AFD_NUMERO
        if chr(b) in "tfn":
            return AFD_LITERAL
        return None

    def _error(self, msg):
        e = ErrorLexico(f"Error lexico en linea {self.linea}, "
                        f"columna {self.columna}: {msg}")
        e.linea, e.columna, e.pos = self.linea, self.columna, self.pos   # donde fallo
        raise e

    def _avanzar(self, b):
        self.pos += 1
        if b == ord("\n"):
            self.linea += 1
            self.columna = 1
        else:
            self.columna += 1

    def _emitir(self, salida):
        tipo = self.afd.aceptacion[self.q]
        try:
            texto = self.pedazo.decode("utf-8")
        except UnicodeDecodeError:
            self._error(f"UTF-8 invalido dentro de {self.afd.nombre}")
        if not (tipo == "TEXTO" and texto.strip() == ""):
            salida.append(Token(tipo, texto, *self.inicio))
        self.afd = None

    def _byte(self, b, salida):
        while True:
            if self.afd is None:                        # entre tokens
                if self.modo == "json":
                    if b in ESPACIO:
                        self._avanzar(b); return
                    if b in SIMBOLOS_JSON:
                        salida.append(Token(SIMBOLOS_JSON[b], chr(b),
                                            self.linea, self.columna, self.pos))
                        self._avanzar(b); return
                    afd = self._elegir_json(b)
                    if afd is None:
                        self._error(f"byte no permitido {bytes([b])!r}")
                else:
                    afd = AFD_ETIQUETA if b == ord("<") else AFD_TEXTO
                self.afd, self.q = afd, afd.inicial
                self.pedazo = bytearray()
                self.inicio = (self.linea, self.columna, self.pos)

            siguiente = self.afd.paso(self.q, b)
            if siguiente is not None:                   # hay flecha: avanzar
                self.q = siguiente
                self.pedazo.append(b)
                self._avanzar(b)
                return
            # No hay flecha: el token llego hasta aqui
            if self.q not in self.afd.aceptacion:
                self._error(f"{self.afd.nombre} mal formado: "
                            f"{bytes(self.pedazo + bytes([b]))!r} "
                            f"(estado {self.q}, sin flecha para {bytes([b])!r})")
            if b in self.afd.no_puede_seguir:
                self._error(f"{self.afd.nombre} mal formado: "
                            f"{bytes(self.pedazo + bytes([b]))!r}")
            self._emitir(salida)
            # y se vuelve a procesar el mismo byte (no se avanza)

    def alimentar(self, bloque):
        if isinstance(bloque, str):
            bloque = bloque.encode("utf-8")
        salida = []
        self.parcial = salida    # si _byte lanza ErrorLexico, aqui quedan los tokens anteriores
        for b in bloque:
            self._byte(b, salida)
        return salida

    def terminar(self):
        salida = []
        self.parcial = salida
        if self.afd is not None:
            if self.q not in self.afd.aceptacion:
                self._error(f"la entrada termino con un {self.afd.nombre} "
                            f"incompleto: {bytes(self.pedazo)!r}")
            self._emitir(salida)
        return salida


def tokenizar(entrada, modo="json"):
    lx = Lexer(modo)
    return lx.alimentar(entrada) + lx.terminar()


def tokenizar_archivo(ruta, modo=None, tam_bloque=4096):
    """Lee el archivo en bloques (streaming real) y va soltando tokens."""
    if modo is None:
        modo = "xml" if ruta.lower().endswith(".xml") else "json"
    lx = Lexer(modo)
    with open(ruta, "rb") as f:
        while True:
            bloque = f.read(tam_bloque)
            if not bloque:
                break
            yield from lx.alimentar(bloque)
    yield from lx.terminar()


# ===================================================================
# 8. GRAMATICAS REGULARES Y DIAGRAMAS (salen de las mismas tablas)
#    Regla: por cada flecha  q --a--> p  se escribe  q -> a p
#           y si p es de aceptacion, tambien  q -> a
# ===================================================================
def gramatica(afd):
    reglas = {}
    for (q, a), p in afd.tabla.items():
        reglas.setdefault(q, []).append(f"{a} {p}")
        if p in afd.aceptacion:
            reglas[q].append(f"{a}")
    lineas = [f"Gramatica regular de {afd.nombre} (simbolo inicial {afd.inicial})"]
    orden = sorted(reglas, key=lambda s: (s[0], int(s[1:]) if s[1:].isdigit() else 0))
    for q in orden:
        lineas.append(f"  {q} -> " + " | ".join(dict.fromkeys(reglas[q])))
    if afd.leyenda:
        lineas.append("  Clases: " + "; ".join(f"{k} = {v}" for k, v in afd.leyenda.items()))
    return "\n".join(lineas)


def dot(afd):
    l = [f'digraph {afd.nombre} {{', "  rankdir=LR;",
         '  inicio [shape=point];', f"  inicio -> {afd.inicial};"]
    for q in afd.aceptacion:
        l.append(f"  {q} [shape=doublecircle];")
    juntas = {}
    for (q, a), p in afd.tabla.items():
        juntas.setdefault((q, p), []).append(a)
    for (q, p), cs in juntas.items():
        etiqueta = ", ".join(cs)
        etiqueta = etiqueta.replace("\\", "\\\\").replace('"', '\\"')
        l.append(f'  {q} -> {p} [label="{etiqueta}"];')
    l.append("}")
    return "\n".join(l)


# ===================================================================
# 9. PRUEBAS
# ===================================================================
def _tipos(entrada, modo="json"):
    return [t.tipo for t in tokenizar(entrada, modo)]


def _falla(entrada, modo="json"):
    try:
        tokenizar(entrada, modo)
        return False
    except ErrorLexico:
        return True


def correr_pruebas():
    import re, itertools, random, json
    ok = total = 0

    def chequear(nombre, condicion):
        nonlocal ok, total
        total += 1
        if condicion:
            ok += 1
        else:
            print("  FALLA:", nombre)

    # --- JSON: los 13 ejemplos de la version 1 ---
    chequear("v1 id", _tipos('{"id": 7}') ==
             ["LLAVE_ABRE", "CADENA", "DOS_PUNTOS", "NUMERO", "LLAVE_CIERRA"])
    chequear("v1 arreglo", _tipos('[10, "a b"]') ==
             ["CORCHETE_ABRE", "NUMERO", "COMA", "CADENA", "CORCHETE_CIERRA"])
    chequear("v1 negativo", tokenizar('{"x": -3.5}')[3].texto == "-3.5")
    chequear("v1 hora", tokenizar('{"hora": "5:30"}')[3].texto == '"5:30"')
    chequear("v1 escape", tokenizar(r'{"frase": "dijo \"hola\""}')[3].texto
             == r'"dijo \"hola\""')
    chequear("v1 literales", _tipos('{"ok": true, "nada": null}').count("LITERAL") == 2)
    esquema = '{"type":"object","properties":{"id":{"type":"integer"}},"required":["id"]}'
    chequear("v1 esquema", len(tokenizar(esquema)) == 23)
    chequear("v1 desorden", len(tokenizar("}{ 7 : :")) == 5)
    for mala in ['{"id": 7@}', '{"id": "hola}', '{"id": 01}',
                 '{"id": 5.}', '{"ok": verdadero}']:
        chequear(f"v1 error {mala}", _falla(mala))

    # --- Numeros con exponente ---
    chequear("exp validos", [t.texto for t in tokenizar("[1.5e3, 2E-3, 0e+5, -7E10]")
                             if t.tipo == "NUMERO"] == ["1.5e3", "2E-3", "0e+5", "-7E10"])
    for mala in ["[2e]", "[2e+]", "[1.e3]", "[1e5e2]", "[-]", "[--1]", "[.5]"]:
        chequear(f"exp error {mala}", _falla(mala))
    patron = re.compile(r"-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?$")
    distintos = 0
    for n in range(1, 6):
        for t in itertools.product("0159.eE+-", repeat=n):
            s = "".join(t)
            if not (s[0] == "-" or s[0].isdigit()):
                continue
            try:
                r = tokenizar(s); acepta = len(r) == 1 and r[0].tipo == "NUMERO"
            except ErrorLexico:
                acepta = False
            distintos += acepta != bool(patron.match(s))
    chequear("numeros = gramatica oficial JSON (exhaustivo hasta 5)", distintos == 0)

    # --- Cadenas con escapes ---
    for buena in [r'"a\nb"', r'"\\"', r'"\/"', r'"\b\f\r\t"', r'"\u00e9"',
                  r'"\uABCD"', '"cañón"', '""', r'"\"\""']:
        chequear(f"cadena valida {buena}", _tipos(buena) == ["CADENA"])
    for mala in [r'"\x"', r'"\u12"', r'"\u12G4"', '"a\nb"', '"abc', r'"\"']:
        chequear(f"cadena invalida {mala!r}", _falla(mala))
    chequear("UTF-8 invalido", _falla(b'"\xff\xfe"'))
    chequear("UTF-8 de 2 bytes", tokenizar('"é"')[0].texto == '"é"')

    # --- Literales ---
    chequear("literales", _tipos("[true,false,null]").count("LITERAL") == 3)
    for mala in ["[tru]", "[trueX]", "[nul]", "[True]", "[falso]"]:
        chequear(f"literal invalido {mala}", _falla(mala))

    # --- Posiciones ---
    t = tokenizar('{\n  "a": 12\n}')
    chequear("posicion de 12", (t[3].linea, t[3].columna) == (2, 8))
    chequear("posicion de }", (t[4].linea, t[4].columna) == (3, 1))
    chequear("posicion en bytes", [x.pos for x in t] == [0, 4, 7, 9, 12])
    lx = Lexer("json")
    try:
        lx.alimentar('{"a": 1, "b": 0')
        lx.alimentar('1}')
    except ErrorLexico:
        pass
    chequear("tokens parciales al fallar", lx.parcial == [])
    lx = Lexer("json")
    try:
        lx.alimentar('{"a": @')
    except ErrorLexico:
        pass
    chequear("tokens parciales del mismo bloque", [x.tipo for x in lx.parcial] == ["LLAVE_ABRE", "CADENA", "DOS_PUNTOS"])

    # --- Streaming: dar la entrada de a 1 byte o de a bloques da lo mismo ---
    random.seed(7)

    def gen(prof=0):
        r = random.random()
        if prof > 3 or r < 0.3:
            return random.choice([0, -12, 3.25, 1.5e-7, "hola", "ñ\"\\x\n",
                                  True, False, None, 123456789, "\u00e9"])
        if r < 0.65:
            return [gen(prof + 1) for _ in range(random.randint(0, 4))]
        return {f"k{i}": gen(prof + 1) for i in range(random.randint(0, 4))}

    iguales = coincide_json = True
    for _ in range(300):
        doc = json.dumps(gen(), ensure_ascii=random.random() < 0.5).encode()
        entero = tokenizar(doc)
        lx = Lexer("json"); partes = []
        i = 0
        while i < len(doc):
            n = random.randint(1, 7)
            partes += lx.alimentar(doc[i:i + n]); i += n
        partes += lx.terminar()
        iguales &= [tuple(x) for x in partes] == [tuple(x) for x in entero]
        # cada cadena y numero debe ser JSON valido segun la libreria json
        for tk in entero:
            if tk.tipo in ("CADENA", "NUMERO"):
                try:
                    json.loads(tk.texto)
                except Exception:
                    coincide_json = False
    chequear("streaming por bloques = de una vez (300 documentos)", iguales)
    chequear("cada CADENA/NUMERO es aceptado por la libreria json", coincide_json)

    # --- XML ---
    xml = ('<?xml version="1.0"?>\n<!-- catalogo -->\n'
           '<libro id="7" tipo=\'nuevo\'>\n  <titulo>Autómatas &amp; lenguajes</titulo>\n'
           '  <vacio/>\n  <n>&#65;</n>\n</libro>')
    chequear("xml tipos", _tipos(xml, "xml") == [
        "DECLARACION", "COMENTARIO", "ETIQUETA_ABRE", "ETIQUETA_ABRE", "TEXTO",
        "ETIQUETA_CIERRA", "ETIQUETA_VACIA", "ETIQUETA_ABRE", "TEXTO",
        "ETIQUETA_CIERRA", "ETIQUETA_CIERRA"])
    chequear("xml texto", tokenizar(xml, "xml")[4].texto == "Autómatas &amp; lenguajes")
    for mala in ["<1a>", "<a b>", '<a b="1>', "<a/ >", "</ a>", "<a>x & y</a>",
                 "<a>&#x;</a>", "<!-- a", "<a", "<a b=1>"]:
        chequear(f"xml invalido {mala!r}", _falla(mala, "xml"))
    chequear("v4: espacios alrededor de '='", _tipos("<a b = '1' c =\"2\"/>", "xml") == ["ETIQUETA_VACIA"])
    lx = Lexer("xml"); partes = []
    for i in range(len(xml)):
        partes += lx.alimentar(xml[i])
    partes += lx.terminar()
    chequear("xml streaming de a 1 caracter", [p.tipo for p in partes] == _tipos(xml, "xml"))

    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


def mostrar(tokens):
    n = 0
    for n, t in enumerate(tokens, start=1):
        print(f"  {n:>3}. ({t.linea}:{t.columna}) {t.tipo:<16} {t.texto}")
    print(f"  Total: {n} tokens")


if __name__ == "__main__":
    args = sys.argv[1:]
    try:
        if not args:
            correr_pruebas()
        elif args[0] == "--gramaticas":
            for a in TODOS_LOS_AFD:
                print(gramatica(a), end="\n\n")
        elif args[0] == "--dot":
            for a in TODOS_LOS_AFD:
                with open(f"afd_{a.nombre.lower()}.dot", "w", encoding="utf-8") as f:
                    f.write(dot(a))
                print(f"  escrito afd_{a.nombre.lower()}.dot")
            print("  Para la imagen: dot -Tpng afd_numero.dot -o afd_numero.png")
        elif args[0] == "--texto":
            modo = "xml" if args[1].lstrip().startswith("<") else "json"
            mostrar(tokenizar(args[1], modo))
        else:
            mostrar(tokenizar_archivo(args[0]))
    except ErrorLexico as e:
        print(" ", e)

r"""
parser_v2.py - Fase 2: analizador sintactico LL(1) para JSON (y esquemas JSON)

Toma los tokens de lexer_v3.py y construye el arbol de derivacion.
No usa recursion: usa una PILA explicita, como un automata de pila.

Como correrlo:
  python parser_v2.py                 -> corre las pruebas
  python parser_v2.py --tabla         -> imprime la gramatica y la tabla LL(1)
  python parser_v2.py --texto '{"a": [1, 2]}'   -> parsea un texto
"""
import sys
from lexer_v4 import tokenizar, ErrorLexico


class ErrorSintactico(Exception):
    """Los tokens estan bien escritos pero en mal orden."""


# Terminales: los tipos de token que produce el lexer
TERMINALES = {"LLAVE_ABRE", "LLAVE_CIERRA", "CORCHETE_ABRE", "CORCHETE_CIERRA",
              "DOS_PUNTOS", "COMA", "CADENA", "NUMERO", "LITERAL"}

# Gramatica libre de contexto. Una regla vacia [] es epsilon (no consume nada).
GRAMATICA = {
    "VALOR":       [["OBJETO"], ["ARREGLO"], ["CADENA"], ["NUMERO"], ["LITERAL"]],
    "OBJETO":      [["LLAVE_ABRE", "MIEMBROS", "LLAVE_CIERRA"]],
    "MIEMBROS":    [["PAR", "MAS_PARES"], []],
    "MAS_PARES":   [["COMA", "PAR", "MAS_PARES"], []],
    "PAR":         [["CADENA", "DOS_PUNTOS", "VALOR"]],
    "ARREGLO":     [["CORCHETE_ABRE", "ELEMENTOS", "CORCHETE_CIERRA"]],
    "ELEMENTOS":   [["VALOR", "MAS_VALORES"], []],
    "MAS_VALORES": [["COMA", "VALOR", "MAS_VALORES"], []],
}
INICIAL = "VALOR"


# ---------------------------------------------------------------
# PRIMEROS y SIGUIENTES (se calculan, no se escriben a mano)
# ---------------------------------------------------------------
def calcular_primeros():
    primeros = {nt: set() for nt in GRAMATICA}
    cambio = True
    while cambio:
        cambio = False
        for nt, reglas in GRAMATICA.items():
            for regla in reglas:
                antes = len(primeros[nt])
                anulable = True
                for s in regla:
                    if s in TERMINALES:
                        primeros[nt].add(s)
                        anulable = False
                        break
                    primeros[nt] |= primeros[s] - {"eps"}
                    if "eps" not in primeros[s]:
                        anulable = False
                        break
                if anulable:
                    primeros[nt].add("eps")
                cambio |= len(primeros[nt]) != antes
    return primeros


def primeros_de(secuencia, primeros):
    res = set()
    for s in secuencia:
        if s in TERMINALES:
            res.add(s)
            return res
        res |= primeros[s] - {"eps"}
        if "eps" not in primeros[s]:
            return res
    res.add("eps")
    return res


def calcular_siguientes(primeros):
    sig = {nt: set() for nt in GRAMATICA}
    sig[INICIAL].add("$")
    cambio = True
    while cambio:
        cambio = False
        for nt, reglas in GRAMATICA.items():
            for regla in reglas:
                for i, s in enumerate(regla):
                    if s in TERMINALES:
                        continue
                    resto = primeros_de(regla[i + 1:], primeros)
                    antes = len(sig[s])
                    sig[s] |= resto - {"eps"}
                    if "eps" in resto:
                        sig[s] |= sig[nt]
                    cambio |= len(sig[s]) != antes
    return sig


def construir_tabla():
    primeros = calcular_primeros()
    siguientes = calcular_siguientes(primeros)
    tabla = {}
    for nt, reglas in GRAMATICA.items():
        for k, regla in enumerate(reglas):
            p = primeros_de(regla, primeros)
            for t in p - {"eps"}:
                assert (nt, t) not in tabla, f"conflicto: no es LL(1) en ({nt}, {t})"
                tabla[(nt, t)] = k
            if "eps" in p:
                for t in siguientes[nt]:
                    assert (nt, t) not in tabla, f"conflicto: no es LL(1) en ({nt}, {t})"
                    tabla[(nt, t)] = k
    return tabla, primeros, siguientes


TABLA, PRIMEROS, SIGUIENTES = construir_tabla()


# ---------------------------------------------------------------
# EL PARSER (con pila explicita)
# ---------------------------------------------------------------
class Nodo:
    def __init__(self, simbolo):
        self.simbolo = simbolo
        self.token = None       # solo los terminales
        self.hijos = []

    def __repr__(self):
        return f"{self.simbolo}({self.token.texto})" if self.token else self.simbolo


def _error(tok, esperado):
    if tok is None:
        raise ErrorSintactico("Error sintactico: la entrada termino antes de tiempo, "
                              f"se esperaba {esperado}")
    raise ErrorSintactico(f"Error sintactico en linea {tok.linea}, columna {tok.columna}: "
                          f"llego {tok.tipo} ({tok.texto!r}), se esperaba {esperado}")


def parsear(tokens):
    """Recibe la lista de tokens y devuelve la raiz del arbol de derivacion."""
    entrada = list(tokens) + [None]        # None = fin de la entrada ($)
    i = 0
    raiz = Nodo(INICIAL)
    pila = [raiz]
    while pila:
        nodo = pila.pop()
        tok = entrada[i]
        actual = tok.tipo if tok else "$"
        if nodo.simbolo in TERMINALES:
            if actual != nodo.simbolo:
                _error(tok, nodo.simbolo)
            nodo.token = tok
            i += 1
        else:
            k = TABLA.get((nodo.simbolo, actual))
            if k is None:
                esperados = sorted(t for (n, t) in TABLA if n == nodo.simbolo)
                _error(tok, " o ".join(esperados))
            nodo.hijos = [Nodo(s) for s in GRAMATICA[nodo.simbolo][k]]
            pila.extend(reversed(nodo.hijos))     # el primero queda arriba
    if entrada[i] is not None:
        _error(entrada[i], "el fin de la entrada")
    return raiz


# ---------------------------------------------------------------
# Del arbol de derivacion a un arbol simple (para ver y para pruebas)
# ---------------------------------------------------------------
def simplificar(raiz):
    """Convierte el arbol de derivacion en dict / list / valores de Python.
    Sin recursion: usa pilas explicitas, asi que aguanta cualquier anidamiento."""
    import json
    # Paso 1: recorrer el arbol en post-orden con una pila
    resultado = {}                      # id(nodo) -> valor Python
    pila = [(raiz, False)]
    while pila:
        nodo, visitado = pila.pop()
        s = nodo.simbolo
        if s in ("CADENA", "NUMERO", "LITERAL"):
            resultado[id(nodo)] = json.loads(nodo.token.texto)
            continue
        if not visitado:
            pila.append((nodo, True))
            for h in nodo.hijos:
                if h.simbolo in ("VALOR", "OBJETO", "ARREGLO", "CADENA", "NUMERO", "LITERAL",
                                 "MIEMBROS", "MAS_PARES", "PAR", "ELEMENTOS", "MAS_VALORES"):
                    pila.append((h, False))
            continue
        h = nodo.hijos
        if s == "VALOR":
            resultado[id(nodo)] = resultado[id(h[0])]
        elif s == "PAR":
            resultado[id(nodo)] = (resultado[id(h[0])], resultado[id(h[2])])
        elif s in ("MIEMBROS", "MAS_PARES"):
            if not h:
                resultado[id(nodo)] = []
            else:
                par = h[0] if s == "MIEMBROS" else h[1]
                resto = h[1] if s == "MIEMBROS" else h[2]
                resultado[id(nodo)] = [resultado[id(par)]] + resultado[id(resto)]
        elif s in ("ELEMENTOS", "MAS_VALORES"):
            if not h:
                resultado[id(nodo)] = []
            else:
                val = h[0] if s == "ELEMENTOS" else h[1]
                resto = h[1] if s == "ELEMENTOS" else h[2]
                resultado[id(nodo)] = [resultado[id(val)]] + resultado[id(resto)]
        elif s == "OBJETO":
            resultado[id(nodo)] = dict(resultado[id(h[1])])
        elif s == "ARREGLO":
            resultado[id(nodo)] = resultado[id(h[1])]
        else:
            raise ValueError(s)
    return resultado[id(raiz)]


def parsear_texto(texto):
    return parsear(tokenizar(texto))


def profundidad(nodo):
    """Profundidad del arbol, calculada sin recursion."""
    mx, pila = 0, [(nodo, 1)]
    while pila:
        n, d = pila.pop()
        mx = max(mx, d)
        pila.extend((h, d + 1) for h in n.hijos)
    return mx


# ---------------------------------------------------------------
# PRUEBAS
# ---------------------------------------------------------------
def correr_pruebas():
    import json, random
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    def falla(texto):
        try:
            parsear_texto(texto)
            return False
        except ErrorSintactico:
            return True

    # Validos
    for texto in ['{"id": 7}', '[1, 2, 3]', '[]', '{}', '"hola"', '7', 'true', 'null',
                  '{"a": [1, {"b": null}], "c": "x"}', '[[[[]]]]', '{"a":{"b":{"c":1}}}',
                  '[1.5e3, -2, "a\\n"]',
                  '{"type":"object","properties":{"id":{"type":"integer"}},"required":["id"]}']:
        try:
            chequear(f"valido {texto}", simplificar(parsear_texto(texto)) == json.loads(texto))
        except Exception as e:
            chequear(f"valido {texto} ({e})", False)

    # Invalidos
    for texto in ['{"a" 1}', '{"a": }', '{"a": 1,}', '[1 2]', '[1,]', '[,1]', '{,}',
                  '{"a": 1', '[1, 2', '}{', ']', '{1: 2}', '{"a": 1}}', '[1] [2]',
                  '1 2', '', '{"a"}', '{"a":: 1}', '[}', '{]']:
        chequear(f"invalido {texto!r}", falla(texto))

    # El mensaje de error dice donde y que se esperaba
    try:
        parsear_texto('{"a": 1,}')
    except ErrorSintactico as e:
        chequear("mensaje con posicion", "columna 9" in str(e) and "CADENA" in str(e))

    # Anidamiento profundo: no hay recursion, no se rompe
    n = 5000
    chequear("anidamiento 5000", profundidad(parsear_texto("[" * n + "]" * n)) > n)
    chequear("anidamiento 5000 desbalanceado", falla("[" * n + "]" * (n - 1)))
    # simplificar tambien aguanta el anidamiento (sin recursion)
    prof = simplificar(parsear_texto("[" * n + "1" + "]" * n))
    d = 0
    while isinstance(prof, list):
        prof = prof[0]
        d += 1
    chequear("simplificar con anidamiento 5000", d == n and prof == 1)

    # Comparacion con la libreria json: documentos al azar
    random.seed(11)

    def gen(p=0):
        r = random.random()
        if p > 3 or r < 0.3:
            return random.choice([0, -5, 2.5, 1e-7, "hola", "a\"b", True, False, None, 10 ** 12])
        if r < 0.65:
            return [gen(p + 1) for _ in range(random.randint(0, 4))]
        return {f"k{i}": gen(p + 1) for i in range(random.randint(0, 4))}

    bien = True
    for _ in range(500):
        doc = json.dumps(gen())
        bien &= simplificar(parsear_texto(doc)) == json.loads(doc)
    chequear("500 documentos = libreria json", bien)

    # Documentos dañados: aceptar o rechazar igual que la libreria json
    base = ['{"a": [1, 2, {"b": null}], "c": "x"}', '[1, [2, [3]], {"k": true}]']
    igual = True
    for _ in range(3000):
        t = list(random.choice(base))
        for _ in range(random.randint(1, 3)):
            op = random.choice("bis")
            pos = random.randrange(len(t)) if t else 0
            if op == "b" and t:
                del t[pos]
            elif op == "i":
                t.insert(pos, random.choice('{}[]:,"01a '))
            elif t:
                t[pos] = random.choice('{}[]:,"01a ')
        txt = "".join(t)
        try:
            ref = json.loads(txt)
            esperado = True
        except Exception:
            esperado = False
        try:
            mio = simplificar(parsear_texto(txt)) is not None or True
            mio = True
        except (ErrorSintactico, ErrorLexico):
            mio = False
        except Exception:
            mio = None
        if mio != esperado:
            igual = False
            print("  DIFERENCIA:", repr(txt), "json:", esperado, "parser:", mio)
            break
    chequear("3000 documentos danados: acepta y rechaza igual que json", igual)

    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


def mostrar_tabla():
    print("GRAMATICA")
    for nt, reglas in GRAMATICA.items():
        print(f"  {nt:<12} -> " + " | ".join(" ".join(r) if r else "eps" for r in reglas))
    print("\nPRIMEROS / SIGUIENTES")
    for nt in GRAMATICA:
        print(f"  {nt:<12} P = {sorted(PRIMEROS[nt])}   S = {sorted(SIGUIENTES[nt])}")
    print("\nTABLA LL(1)  (no terminal, token) -> regla")
    for (nt, t), k in sorted(TABLA.items()):
        r = GRAMATICA[nt][k]
        print(f"  ({nt}, {t}) -> {nt} -> " + (" ".join(r) if r else "eps"))


def mostrar_arbol(nodo):
    pila = [(nodo, 0)]
    while pila:
        n, d = pila.pop()
        print("  " * d + repr(n))
        pila.extend((h, d + 1) for h in reversed(n.hijos))


if __name__ == "__main__":
    args = sys.argv[1:]
    try:
        if not args:
            correr_pruebas()
        elif args[0] == "--tabla":
            mostrar_tabla()
        elif args[0] == "--texto":
            mostrar_arbol(parsear_texto(args[1]))
        else:
            mostrar_arbol(parsear_texto(open(args[0], encoding="utf-8").read()))
    except (ErrorLexico, ErrorSintactico) as e:
        print(" ", e)

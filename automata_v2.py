r"""
automata_v2.py - Fase 4: construccion del automata de pila DETERMINISTA PONDERADO

    M = (Q, Sigma, Gamma, delta, q0, Z0, F, w)

Que cambia respecto a automata_v1.py
  1. El validador ES un interprete de la tabla delta: lee la fila (q, a, X) y la
     ejecuta. No hay reglas escritas a mano aparte de la tabla.
  2. La tabla controla tambien la SINTAXIS: si llega un token para el que no hay
     fila, el documento esta mal formado (antes se aceptaba {"a":1 "b":2}).
  3. Pesos en el semianillo tropical (N u {inf}, min, +, inf, 0): cada fila tiene
     un costo; el costo de una corrida es la SUMA de los costos de sus filas.
     Dentro de cada fila las comprobaciones van de la mas barata a la mas cara,
     asi el fallo temprano (parar_en_primero) gasta lo minimo.
     Aparte se cuentan las violaciones (conformidad del payload).
  4. Construccion COMPOSICIONAL: cada nodo del esquema aporta su sub-automata
     (estados V, K, N, C, M para objetos; E, G, B para arreglos) y se pegan por
     la pila: al cerrar una estructura se pasa al estado R, que mira el tope de
     la pila con una transicion epsilon y vuelve al contenedor correcto.
  5. Verificacion de DETERMINISMO de delta (sin filas repetidas, sin choque entre
     comodin y simbolo concreto, sin epsilon junto a una lectura).
  6. MINIMIZACION: los nodos del esquema que se comportan igual se fusionan
     (refinamiento de particiones, como Moore en AFD) y el DPDA sale mas chico.
  7. Claves duplicadas, profundidad maxima y ruta JSON Pointer del error.

Registros acotados (por eso Gamma sigue siendo finito):
  - cada simbolo O<i> lleva una mascara de bits sobre sus propiedades declaradas
    (sirve para required y para detectar claves duplicadas);
  - cada simbolo A<j> lleva un contador saturado en max(minItems, maxItems + 1).
  Las claves NO declaradas repetidas se detectan con un conjunto: eso ya no es
  acotado y se documenta como verificacion diferida.

Como correrlo:
  python automata_v2.py                                  -> pruebas
  python automata_v2.py --formal  E.json                 -> definicion formal de M
  python automata_v2.py --tabla   E.json                 -> tabla delta
  python automata_v2.py --dot     E.json  > dpda.dot     -> diagrama (Graphviz)
  python automata_v2.py --validar E.json D.json [--traza] -> valida un documento
"""
import sys
import json
from lexer_v4 import Lexer, ErrorLexico, Token
from parser_v2 import parsear_texto, simplificar
from semantico_v1 import analizar

EPS = "ε"
COMODIN = "*"          # "cualquier simbolo de pila, y se deja igual"
TOKEN_A_SIMBOLO = {"LLAVE_ABRE": "{", "LLAVE_CIERRA": "}", "CORCHETE_ABRE": "[",
                   "CORCHETE_CIERRA": "]", "DOS_PUNTOS": ":", "COMA": ",",
                   "CADENA": "CADENA", "NUMERO": "NUMERO", "LITERAL": "LITERAL"}
ESCALARES = ("CADENA", "NUMERO", "LITERAL")

# Costo estimado de cada comprobacion (unidades = comparaciones aproximadas).
# Es el peso w: se suma por cada fila ejecutada.
COSTO = {"estructura": 1, "tipo": 1, "const": 1, "requeridos": 1, "dup": 1,
         "prohibida": 1, "minItems": 1, "maxItems": 1, "nunca": 0,
         "minimum": 2, "maximum": 2, "minLength": 3, "maxLength": 3}
# enum cuesta una comparacion por cada valor de la lista (se calcula al compilar)


# =========================================================================
# 1. COMPILADOR DE REGLAS: un "nodo" por cada sub-esquema (construccion
#    composicional). $ref no crea nodo nuevo: apunta a uno existente.
# =========================================================================
class Compilador:
    def __init__(self, esquema):
        self.raiz = esquema
        self.reglas = []
        self.rutas = []             # ruta del esquema de cada nodo (para mostrar)
        self.por_ruta = {}

    def _resolver(self, ref):
        if ref == "#":
            return self.raiz
        nodo = self.raiz
        for p in ref[2:].split("/"):
            nodo = nodo[p.replace("~1", "/").replace("~0", "~")]
        return nodo

    def compilar(self):
        cola = [("#", self.raiz)]
        pend = []
        while cola:
            ruta, esq = cola.pop(0)
            # seguir $ref hasta un esquema real (la Fase 3 ya descarto ciclos vacios)
            vistos = 0
            while isinstance(esq, dict) and "$ref" in esq and vistos < 1000:
                destino = esq["$ref"]
                if destino in self.por_ruta:              # ya compilado: alias
                    self.por_ruta[ruta] = self.por_ruta[destino]
                    esq = None
                    break
                self.por_ruta.setdefault(destino, None)   # se resuelve abajo
                pend.append((ruta, destino))
                ruta, esq = destino, self._resolver(destino)
                vistos += 1
            if esq is None or (ruta in self.por_ruta and self.por_ruta[ruta] is not None):
                continue
            idx = len(self.reglas)
            self.por_ruta[ruta] = idx
            self.reglas.append(None)
            self.rutas.append(ruta)
            regla, hijos = self._regla(ruta, esq)
            self.reglas[idx] = regla
            cola.extend(hijos)
        for origen, destino in pend:                   # alias de los $ref
            if self.por_ruta.get(origen) is None:
                self.por_ruta[origen] = self.por_ruta[destino]
        for r in self.reglas:                           # rutas -> numeros de nodo
            if "props" in r:
                r["props"] = {k: self.por_ruta[v] for k, v in r["props"].items()}
            for campo in ("items", "extra"):
                if isinstance(r.get(campo), str):
                    r[campo] = self.por_ruta[r[campo]]
        return self.reglas

    def _regla(self, ruta, esq):
        hijos = []
        if esq is True or esq == {}:
            return {"cualquiera": True}, hijos
        if esq is False:
            return {"nunca": True}, hijos
        r = {}
        if "type" in esq:
            t = esq["type"]
            r["tipos"] = sorted(t if isinstance(t, list) else [t])
        if "enum" in esq:
            r["enum"] = esq["enum"]
        if "const" in esq:
            r["const"] = [esq["const"]]
        for k in ("minimum", "maximum", "minLength", "maxLength", "minItems", "maxItems"):
            if k in esq:
                r[k] = esq[k]
        if "required" in esq:
            r["required"] = list(esq["required"])
        if "properties" in esq:
            r["props"] = {}
            for nombre, sub in esq["properties"].items():
                sr = f"{ruta}/properties/{nombre}"
                r["props"][nombre] = sr
                hijos.append((sr, sub))
        if "items" in esq:
            sr = f"{ruta}/items"
            r["items"] = sr
            hijos.append((sr, esq["items"]))
        if "additionalProperties" in esq:
            ap = esq["additionalProperties"]
            if ap is False:
                r["extra"] = None                       # prohibidas
            elif isinstance(ap, dict) and ap != {}:
                sr = f"{ruta}/additionalProperties"
                r["extra"] = sr
                hijos.append((sr, ap))
        if not r:                                       # solo palabras ignoradas
            return {"cualquiera": True}, hijos
        return r, hijos


# =========================================================================
# 2. MINIMIZACION de los nodos (refinamiento de particiones).
#    Dos nodos son equivalentes si sus comprobaciones locales son iguales y
#    sus hijos caen en las mismas clases. Igual que Moore: se parte de una
#    particion por "firma local" y se refina hasta que no cambia.
# =========================================================================
def _firma_local(r):
    local = {k: v for k, v in r.items() if k not in ("props", "items", "extra")}
    local["_props"] = sorted(r.get("props", {}))
    local["_items"] = "items" in r
    local["_extra"] = ("prohibido" if "extra" in r and r["extra"] is None
                       else "regla" if "extra" in r else "libre")
    return json.dumps(local, sort_keys=True)


def minimizar_reglas(reglas):
    """Devuelve (reglas_minimas, clase_de) donde clase_de[i] = nodo minimo de i."""
    n = len(reglas)
    clase = {}
    ids = {}
    for i in range(n):
        clase[i] = ids.setdefault(_firma_local(reglas[i]), len(ids))
    while True:
        ids2, nueva = {}, {}
        for i in range(n):
            r = reglas[i]
            firma = (clase[i],
                     tuple((k, clase[v]) for k, v in sorted(r.get("props", {}).items())),
                     clase[r["items"]] if isinstance(r.get("items"), int) else None,
                     clase[r["extra"]] if isinstance(r.get("extra"), int) else None)
            nueva[i] = ids2.setdefault(firma, len(ids2))
        if len(ids2) == len(ids):
            break
        clase, ids = nueva, ids2
    # renumerar para que el nodo raiz (0) siga siendo 0
    orden = {}
    for i in range(n):
        orden.setdefault(clase[i], len(orden))
    clase_de = [orden[clase[i]] for i in range(n)]
    minimas = [None] * len(orden)
    for i in range(n):
        c = clase_de[i]
        if minimas[c] is None:
            r = dict(reglas[i])
            if "props" in r:
                r["props"] = {k: clase_de[v] for k, v in r["props"].items()}
            for campo in ("items", "extra"):
                if isinstance(r.get(campo), int):
                    r[campo] = clase_de[r[campo]]
            minimas[c] = r
    return minimas, clase_de


# =========================================================================
# 3. EL DPDA: los datos (Q, Sigma, Gamma, delta, q0, Z0, F) y el constructor.
#    Una fila de delta es un dict serializable (asi la Fase 5 la vuelve C/Rust):
#      {"de","a","tope","a_estado","pila","registro","guardas","costo","nota"}
#    pila: "igual" | "push:SIM" | "pop"
#    guardas: lista ordenada [[nombre, costo, parametro], ...]
# =========================================================================
class DPDA:
    def __init__(self):
        self.Q, self.Sigma, self.Gamma = set(), set(), {"Z0"}
        self.delta = {}
        self.q0, self.Z0, self.F = None, "Z0", {"qF"}
        self.conflictos = []
        self.estados_clave = {}      # estado -> claves declaradas (para clasificar)
        self.info_estado = {}        # estado -> explicacion
        self.reg_pila = {}           # simbolo -> {"bits": [...], "tope": n}

    def agregar(self, q, a, X, destino, pila="igual", registro=None, guardas=(),
                nota=""):
        guardas = sorted(guardas, key=lambda g: g[1])      # mas barata primero
        fila = {"de": q, "a": a, "tope": X, "a_estado": destino, "pila": pila,
                "registro": registro, "guardas": [list(g) for g in guardas],
                "costo": COSTO["estructura"] + sum(g[1] for g in guardas), "nota": nota}
        clave = (q, a, X)
        if clave in self.delta:
            self.conflictos.append((clave, self.delta[clave], fila))
            return
        self.delta[clave] = fila
        self.Q.update({q, destino})
        if a != EPS:
            self.Sigma.add(a)
        if X != COMODIN:
            self.Gamma.add(X)
        if pila.startswith("push:"):
            self.Gamma.add(pila[5:])

    def filas(self):
        return list(self.delta.values())

    # ---- verificacion de determinismo ----
    def verificar_determinismo(self):
        problemas = [f"fila repetida {c}" for c, _, _ in self.conflictos]
        por_qa = {}
        for (q, a, X) in self.delta:
            por_qa.setdefault((q, a), set()).add(X)
        for (q, a), tops in por_qa.items():
            if COMODIN in tops and len(tops) > 1:
                problemas.append(f"comodin y simbolo concreto a la vez en ({q}, {a})")
        lecturas = {(q, X) for (q, a, X) in self.delta if a != EPS}
        comodines = {q for (q, a, X) in self.delta if a != EPS and X == COMODIN}
        for (q, a, X) in self.delta:
            if a == EPS and ((q, X) in lecturas or q in comodines):
                problemas.append(f"epsilon y lectura a la vez en ({q}, {X})")
        return problemas

    # ---- tamano ----
    def tamano(self):
        gamma_expandido = 1
        for s in self.Gamma - {"Z0"}:
            info = self.reg_pila.get(s, {})
            gamma_expandido += (2 ** len(info.get("bits", []))) * (info.get("tope", 0) + 1)
        return {"estados": len(self.Q), "transiciones": len(self.delta),
                "simbolos_entrada": len(self.Sigma), "simbolos_pila": len(self.Gamma),
                "simbolos_pila_con_registros": gamma_expandido}


def _es_generico(r):
    return r is None or r.get("cualquiera")


def _guardas_valor(r, a):
    """Comprobaciones que hace una fila al empezar un valor (token a)."""
    if _es_generico(r):
        return []
    if r.get("nunca"):
        return [("nunca", COSTO["nunca"], None)]
    g = []
    if "tipos" in r:
        g.append(("tipo", COSTO["tipo"], r["tipos"]))
    if "enum" in r:
        g.append(("enum", max(1, len(r["enum"])), r["enum"]))
    if "const" in r:
        g.append(("const", COSTO["const"], r["const"][0]))
    if a == "NUMERO":
        for k in ("minimum", "maximum"):
            if k in r:
                g.append((k, COSTO[k], r[k]))
    if a == "CADENA":
        for k in ("minLength", "maxLength"):
            if k in r:
                g.append((k, COSTO[k], r[k]))
    return g


def _admite(r, clase):
    """None si la regla deja pasar 'object'/'array'; si no, falla el tipo."""
    return _es_generico(r) or "tipos" not in r or clase in r["tipos"]


def _es_objeto(r):
    return not _es_generico(r) and ("props" in r or "required" in r or "extra" in r)


def _es_arreglo(r):
    return not _es_generico(r) and ("items" in r or "minItems" in r or "maxItems" in r)


def construir_dpda(reglas, rutas=None):
    """Construccion composicional: cada nodo aporta sus estados y filas."""
    M = DPDA()
    rutas = rutas or [f"nodo {i}" for i in range(len(reglas))]
    R = "R"
    necesita = [("V", 0)]
    M.info_estado[R] = "retorno: mira el tope de la pila (epsilon) y vuelve al contenedor"
    M.info_estado["qF"] = "aceptacion: ya se leyo el valor principal"

    def regla(t):
        return None if t is None else reglas[t]

    def nom(t):
        return "*" if t is None or _es_generico(regla(t)) else str(t)

    def valor_desde(S, t, X, siguiente_escalar, registro=None):
        """Filas que EMPIEZAN un valor de la regla t estando en S con tope X."""
        r = regla(t)
        for a in ESCALARES:
            M.agregar(S, a, X, siguiente_escalar, "igual", registro,
                      _guardas_valor(r, a), f"valor {a.lower()} de la regla {nom(t)}")
        # objeto
        g = _guardas_valor(r, "OBJETO")
        if _es_objeto(r) and _admite(r, "object"):
            sim, dest = f"O{t}", f"K{t}"
            necesita.append(("O", t))
        else:
            sim, dest = "O*", "K*"
            necesita.append(("O", None))
        M.agregar(S, "{", X, dest, f"push:{sim}", registro,
                  [x if x[0] != "tipo" else ("tipo", x[1], x[2] + ["@object"]) for x in g],
                  f"abre objeto: apila {sim}")
        # arreglo
        g = _guardas_valor(r, "ARREGLO")
        if _es_arreglo(r) and _admite(r, "array"):
            sim, dest = f"A{t}", f"E{t}"
            necesita.append(("A", t))
        else:
            sim, dest = "A*", "E*"
            necesita.append(("A", None))
        M.agregar(S, "[", X, dest, f"push:{sim}", registro,
                  [x if x[0] != "tipo" else ("tipo", x[1], x[2] + ["@array"]) for x in g],
                  f"abre arreglo: apila {sim}")

    def sub_objeto(i):
        r = regla(i)
        s = "*" if i is None else str(i)
        sim = f"O{s}"
        K, N, Mm = f"K{s}", f"N{s}", f"M{s}"
        M.info_estado[K] = f"objeto {s}: espera clave o '}}'"
        M.info_estado[N] = f"objeto {s}: espera clave (despues de ',')"
        M.info_estado[Mm] = f"objeto {s}: despues de un miembro, espera ',' o '}}'"
        props = {} if r is None else r.get("props", {})
        requeridas = [] if r is None else r.get("required", [])
        # una propiedad obligatoria que no esta en properties tambien necesita su bit
        nombres = sorted(set(props) | set(requeridas))
        prohibidas = r is not None and "extra" in r and r["extra"] is None
        destino_extra = None if r is None else r.get("extra")
        M.estados_clave[K] = M.estados_clave[N] = set(nombres)
        M.reg_pila[sim] = {"bits": nombres, "tope": 0}
        cierre = []
        if r is not None and "required" in r:
            cierre.append(("requeridos", COSTO["requeridos"],
                           [n for n in r["required"]]))
        for S in (K, N):
            for p in nombres:
                C = f"C{s}.{p}"
                M.info_estado[C] = f"objeto {s}: leyo la clave '{p}', espera ':'"
                g = [("dup", COSTO["dup"], p)]
                if p not in props and prohibidas:
                    g.append(("prohibida", COSTO["prohibida"], None))
                M.agregar(S, f"CLAVE({p})", sim, C, "igual", f"marca:{p}", g,
                          f"clave declarada '{p}'")
            otra = []
            if prohibidas:
                otra.append(("prohibida", COSTO["prohibida"], None))
            otra.append(("dup", COSTO["dup"], None))
            Cx = f"C{s}.+"
            M.info_estado[Cx] = f"objeto {s}: leyo una clave no declarada, espera ':'"
            M.agregar(S, "CLAVE(*)", sim, Cx, "igual", "marca:*", otra,
                      "clave no declarada")
        M.agregar(K, "}", sim, R, "pop", None, cierre, "cierra objeto vacio")
        M.agregar(Mm, "}", sim, R, "pop", None, cierre, "cierra objeto: desapila")
        M.agregar(Mm, ",", sim, N, "igual", None, [], "otro miembro")
        for p in nombres:
            destino = props[p] if p in props else destino_extra
            M.agregar(f"C{s}.{p}", ":", sim, f"V{nom(destino)}", "igual", None, [],
                      f"el valor de '{p}' usa la regla {nom(destino)}")
        M.agregar(f"C{s}.+", ":", sim, f"V{nom(destino_extra)}", "igual", None, [],
                  "valor de clave no declarada")
        M.agregar(R, EPS, sim, Mm, "igual", None, [], f"termino un valor dentro de {sim}")
        necesita.extend(("V", props[p]) for p in props)
        necesita.append(("V", destino_extra))

    def sub_arreglo(j):
        r = regla(j)
        s = "*" if j is None else str(j)
        sim = f"A{s}"
        E, G, B = f"E{s}", f"G{s}", f"B{s}"
        M.info_estado[E] = f"arreglo {s}: espera elemento o ']'"
        M.info_estado[G] = f"arreglo {s}: espera elemento (despues de ',')"
        M.info_estado[B] = f"arreglo {s}: despues de un elemento, espera ',' o ']'"
        tope = 0
        cierre = []
        if r is not None:
            for k in ("minItems", "maxItems"):
                if k in r:
                    cierre.append((k, COSTO[k], r[k]))
            tope = max(r.get("minItems", 0), r.get("maxItems", -1) + 1)
        M.reg_pila[sim] = {"bits": [], "tope": tope}
        items = None if r is None else r.get("items")
        if items is not None and _es_generico(regla(items)):
            items = None
        valor_desde(E, items, sim, B, "cuenta")
        valor_desde(G, items, sim, B, "cuenta")
        M.agregar(E, "]", sim, R, "pop", None, cierre, "cierra arreglo vacio")
        M.agregar(B, "]", sim, R, "pop", None, cierre, "cierra arreglo: desapila")
        M.agregar(B, ",", sim, G, "igual", None, [], "otro elemento")
        M.agregar(R, EPS, sim, B, "igual", None, [], f"termino un elemento dentro de {sim}")

    # --- recorrer lo alcanzable desde la raiz (lista de trabajo) ---
    raiz = 0 if not _es_generico(regla(0)) else None
    M.q0 = f"V{nom(raiz)}"
    hechos = set()
    while necesita:
        tipo, t = necesita.pop()
        t = None if t is None or _es_generico(regla(t)) else t
        if (tipo, t) in hechos:
            continue
        hechos.add((tipo, t))
        if tipo == "V":
            V = f"V{nom(t)}"
            M.info_estado[V] = (f"espera un valor de la regla {nom(t)}"
                                + (f" ({rutas[t]})" if t is not None else " (cualquiera)"))
            valor_desde(V, t, COMODIN, R)
        elif tipo == "O":
            sub_objeto(t)
        else:
            sub_arreglo(t)
    M.agregar(R, EPS, "Z0", "qF", "igual", None, [], "termino el valor principal")
    return M


# =========================================================================
# 4. EL INTERPRETE: lee delta fila por fila. Una pasada, pila explicita.
# =========================================================================
class Marco:
    __slots__ = ("sim", "mascara", "otras", "n", "clave")

    def __init__(self, sim):
        self.sim, self.mascara, self.otras, self.n, self.clave = sim, 0, None, 0, None


class Resultado:
    def __init__(self, valido, errores, costo, violaciones, mal_formado, traza,
                 prof_max, pasos, limite=None):
        self.limite = limite
        self.valido, self.errores, self.costo = valido, errores, costo
        self.violaciones, self.mal_formado, self.traza = violaciones, mal_formado, traza
        self.prof_max, self.pasos = prof_max, pasos

    def __repr__(self):
        if self.valido:
            return f"VALIDO (costo {self.costo}, {self.pasos} pasos, pila max {self.prof_max})"
        return (f"INVALIDO ({self.violaciones} violacion(es), costo {self.costo}): "
                + "; ".join(f"{e['ruta']}: {e['mensaje']}" for e in self.errores))


def _puntero(partes):
    return "".join("/" + str(p).replace("~", "~0").replace("/", "~1") for p in partes)


def _igual(a, b):
    if isinstance(a, bool) or isinstance(b, bool):
        return type(a) == type(b) and a == b
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return a == b
    return type(a) == type(b) and a == b


def _es_tipo(v, tok_tipo, t):
    if t == "string":
        return tok_tipo == "CADENA"
    if t == "number":
        return tok_tipo == "NUMERO"
    if t == "integer":
        return tok_tipo == "NUMERO" and (isinstance(v, int) or
                                         (isinstance(v, float) and v.is_integer()))
    if t == "boolean":
        return isinstance(v, bool)
    if t == "null":
        return tok_tipo == "LITERAL" and v is None
    return False


class Validador:
    def __init__(self, M, parar_en_primero=False, max_profundidad=None, traza=False,
                 memoria_fija=False):
        self.M = M
        self.memoria_fija = memoria_fija     # True = como el nativo: sin conjunto de claves
        self.q = M.q0
        self.pila = [Marco("Z0")]
        self.parar = parar_en_primero
        self.max_prof = max_profundidad
        self.errores, self.costo, self.violaciones = [], 0, 0
        self.mal_formado = False
        self.terminado = False
        self.prof_max = 1
        self.pasos = 0
        self.limite = None
        self.traza = [] if traza else None

    # ---- ruta JSON Pointer a partir de la pila ----
    def _ruta(self, sin_tope=False):
        partes = []
        marcos = self.pila[1:-1] if sin_tope else self.pila[1:]
        for m in marcos:
            if m.sim.startswith("O") and m.clave is not None:
                partes.append(m.clave)
            elif m.sim.startswith("A") and m.n > 0:
                partes.append(m.n - 1)
        return _puntero(partes)

    def _violar(self, mensaje, tok, ruta):
        self.violaciones += 1
        self.errores.append({"ruta": ruta or "/", "mensaje": mensaje,
                             "linea": tok.linea if tok else None,
                             "columna": tok.columna if tok else None,
                             "byte": tok.pos if tok else None})

    def _mal_formado(self, mensaje, tok):
        self.mal_formado = True
        self.terminado = True
        self._violar(mensaje, tok, self._ruta())

    def _limite(self, mensaje, tok=None):
        """Se supero un limite (profundidad, tamano o tiempo): se corta la validacion."""
        self.limite = mensaje
        self._mal_formado(mensaje, tok)

    # ---- clasificar el token en un simbolo de Sigma ----
    def _clasificar(self, tok):
        a = TOKEN_A_SIMBOLO[tok.tipo]
        if a == "CADENA" and self.q in self.M.estados_clave:
            clave = json.loads(tok.texto)
            return (f"CLAVE({clave})" if clave in self.M.estados_clave[self.q]
                    else "CLAVE(*)"), clave
        return a, None

    def _fila(self, a):
        X = self.pila[-1].sim
        return self.M.delta.get((self.q, a, X)) or self.M.delta.get((self.q, a, COMODIN))

    # ---- evaluar una guarda (comprobacion) ----
    def _guarda(self, g, tok, valor, clave, ruta):
        nombre, _, p = g
        tope = self.pila[-1]
        if nombre == "tipo":
            if p and p[-1] in ("@object", "@array"):
                ok = p[-1][1:] in p[:-1]
                llego = p[-1][1:]
            else:
                ok = any(_es_tipo(valor, tok.tipo, t) for t in p)
                llego = f"{tok.tipo} {tok.texto}"
            tipos = [t for t in p if not t.startswith("@")]
            return ok, f"se esperaba {'|'.join(tipos)} y llego {llego}"
        if nombre == "nunca":
            return False, "este valor no esta permitido (esquema false)"
        if nombre == "enum":
            if tok.tipo not in ESCALARES:
                return (any(isinstance(e, (dict, list)) for e in p),
                        "un objeto o arreglo no esta en enum")
            return any(_igual(valor, e) for e in p), f"{tok.texto} no esta en enum {json.dumps(p)}"
        if nombre == "const":
            if tok.tipo not in ESCALARES:
                return isinstance(p, (dict, list)), f"debia ser {json.dumps(p)}"
            return _igual(valor, p), f"debia ser {json.dumps(p)}"
        if nombre == "minimum":
            return valor >= p, f"{tok.texto} es menor que minimum {p}"
        if nombre == "maximum":
            return valor <= p, f"{tok.texto} es mayor que maximum {p}"
        if nombre == "minLength":
            return len(valor) >= p, f"longitud {len(valor)} menor que minLength {p}"
        if nombre == "maxLength":
            return len(valor) <= p, f"longitud {len(valor)} mayor que maxLength {p}"
        if nombre == "dup":
            if p is None:      # clave no declarada: hace falta un conjunto (memoria no acotada)
                return (self.memoria_fija or clave not in (tope.otras or ()),
                        f"clave duplicada '{clave}'")
            bit = 1 << self.M.reg_pila[tope.sim]["bits"].index(p)
            return not tope.mascara & bit, f"clave duplicada '{clave}'"
        if nombre == "prohibida":
            return False, f"propiedad no permitida '{clave}'"
        if nombre == "requeridos":
            bits = self.M.reg_pila[tope.sim]["bits"]
            faltan = [n for n in p if n not in bits or not tope.mascara >> bits.index(n) & 1]
            return not faltan, f"faltan propiedades obligatorias: {faltan}"
        if nombre == "minItems":
            return tope.n >= p, f"{tope.n} elementos, minItems es {p}"
        if nombre == "maxItems":
            return tope.n <= p, f"{tope.n} elementos, maxItems es {p}"
        raise ValueError(nombre)

    # ---- ejecutar una fila ----
    def _ejecutar(self, fila, tok, a, clave):
        tope = self.pila[-1]
        antes = (self.q, [m.sim for m in self.pila]) if self.traza is not None else None
        reg = fila["registro"]
        if reg == "cuenta":
            tope.n += 1
        if reg and reg.startswith("marca:"):
            tope.clave = clave
        valor = json.loads(tok.texto) if tok is not None and tok.tipo in ESCALARES and \
            not a.startswith("CLAVE") else None
        es_cierre = fila["pila"] == "pop"
        ruta = None                       # se calcula solo si hay violacion (O(d))
        costo = COSTO["estructura"] if a != EPS else 0
        fallas = []
        for g in fila["guardas"]:
            costo += g[1]
            ok, msg = self._guarda(g, tok, valor, clave, ruta)
            if not ok:
                ruta = ruta or self._ruta(sin_tope=es_cierre)
                fallas.append(msg)
                self._violar(msg, tok, ruta)
                if g[0] in ("tipo", "nunca") or self.parar:
                    break                 # lo demas ya no importa: fallo temprano
        self.costo += costo
        # registros que se actualizan DESPUES de comprobar
        if reg == "marca:*":
            tope.otras = tope.otras or set()
            tope.otras.add(clave)
        elif reg and reg.startswith("marca:"):
            bits = self.M.reg_pila[tope.sim]["bits"]
            tope.mascara |= 1 << bits.index(reg[6:])
        # pila
        op = fila["pila"]
        if op == "pop":
            self.pila.pop()
        elif op.startswith("push:"):
            if self.max_prof is not None and len(self.pila) >= self.max_prof:
                self._limite(f"profundidad maxima {self.max_prof} superada", tok)
                return
            self.pila.append(Marco(op[5:]))
            self.prof_max = max(self.prof_max, len(self.pila))
        self.q = fila["a_estado"]
        self.pasos += 1
        if self.traza is not None:
            self.traza.append({"paso": self.pasos,
                               "token": tok.texto if tok is not None else EPS,
                               "simbolo": a, "de": antes[0], "pila_antes": antes[1],
                               "a": self.q, "pila_despues": [m.sim for m in self.pila],
                               "k": [fila["de"], a if a != EPS else EPS, fila["tope"]],
                               "fila": f"δ({fila['de']}, {a}, {fila['tope']}) = "
                                       f"({fila['a_estado']}, {fila['pila']})",
                               "costo": costo, "costo_acum": self.costo,
                               "violaciones": fallas, "nota": fila["nota"],
                               "linea": tok.linea if tok is not None else None,
                               "columna": tok.columna if tok is not None else None,
                               "byte": tok.pos if tok is not None else None})

    def _paso(self, tok):
        if self.memoria_fija and tok.tipo == "NUMERO" and len(tok.texto) > 511:
            self._limite("numero de mas de 511 caracteres (limite del validador de memoria fija)", tok)
            return
        if self.q == "qF":
            self._mal_formado("hay contenido despues del valor principal", tok)
            return
        a, clave = self._clasificar(tok)
        fila = self._fila(a)
        if fila is None:
            X = self.pila[-1].sim
            esperados = sorted({b for (q, b, Y) in self.M.delta
                                if q == self.q and Y in (X, COMODIN) and b != EPS})
            esperados = sorted({("CADENA (clave)" if b.startswith("CLAVE") else b)
                                for b in esperados})
            self._mal_formado(f"mal formado: llego {tok.texto!r}, se esperaba "
                              + " o ".join(esperados), tok)
            return
        self._ejecutar(fila, tok, a, clave)
        # transiciones epsilon (estado R): se decide por el tope
        while not self.terminado and (self.q, EPS, self.pila[-1].sim) in self.M.delta:
            self._ejecutar(self.M.delta[(self.q, EPS, self.pila[-1].sim)], None, EPS, None)

    def alimentar(self, tokens):
        for tok in tokens:
            if self.terminado or (self.parar and self.errores):
                return
            self._paso(tok)

    def terminar(self):
        if not self.terminado and self.q != "qF" and not (self.parar and self.errores):
            self._mal_formado("el documento termino antes de tiempo", None)
        return Resultado(not self.errores, self.errores, self.costo, self.violaciones,
                         self.mal_formado, self.traza, self.prof_max, self.pasos, self.limite)


# =========================================================================
# 5. API
# =========================================================================
class Compilado:
    """Resultado de compilar un esquema: reglas, DPDA y reporte."""

    def __init__(self, reglas, rutas, M, reglas_sin_min, M_sin_min, clase_de, clasif):
        self.reglas, self.rutas, self.M = reglas, rutas, M
        self.reglas_sin_min, self.M_sin_min, self.clase_de = reglas_sin_min, M_sin_min, clase_de
        self.clasificacion = clasif


def compilar_esquema(texto_esquema, minimizar=True):
    esquema = simplificar(parsear_texto(texto_esquema))
    errores, _, clasif = analizar(esquema)
    if errores:
        raise ValueError("el esquema no pasa la Fase 3:\n  " + "\n  ".join(map(str, errores)))
    comp = Compilador(esquema)
    reglas = comp.compilar()
    M_sin = construir_dpda(reglas, comp.rutas)
    minimas, clase_de = minimizar_reglas(reglas)
    rutas_min = [None] * len(minimas)
    for i, c in enumerate(clase_de):
        rutas_min[c] = rutas_min[c] or comp.rutas[i]
    M = construir_dpda(minimas, rutas_min) if minimizar else M_sin
    return Compilado(minimas if minimizar else reglas, rutas_min if minimizar else comp.rutas,
                     M, reglas, M_sin, clase_de, clasif)


def validar(compilado, texto_doc, bloque=4096, parar_en_primero=False,
            max_profundidad=None, traza=False, max_bytes=None, max_ms=None, memoria_fija=False):
    """Valida en streaming: lee por bloques, no guarda el documento ni arma arbol.
    Limites (Fase 6): profundidad de pila, tamano en bytes y tiempo en milisegundos.
    El resultado no depende del tamano del bloque."""
    import time
    M = compilado.M if isinstance(compilado, Compilado) else compilado
    lx = Lexer("json")
    v = Validador(M, parar_en_primero, max_profundidad, traza, memoria_fija)
    datos = texto_doc.encode("utf-8") if isinstance(texto_doc, str) else texto_doc
    tope = len(datos) if max_bytes is None else min(len(datos), max_bytes)
    t0 = time.perf_counter()
    try:
        for i in range(0, tope, bloque):
            v.alimentar(lx.alimentar(datos[i:min(i + bloque, tope)]))
            if v.terminado or (v.parar and v.errores):
                break
            if max_ms is not None and (time.perf_counter() - t0) * 1000 > max_ms:
                v._limite(f"limite de tiempo de {max_ms} ms superado")
                break
        else:
            if len(datos) > tope:
                v._limite(f"limite de tamano de {max_bytes} bytes superado")
            else:
                v.alimentar(lx.terminar())
    except ErrorLexico as e:
        v.alimentar(lx.parcial)          # los tokens completos antes del error si cuentan
        if not v.terminado and not (v.parar and v.errores):
            v._mal_formado(f"mal formado (lexico): {e}",
                           Token("ERROR", "", e.linea, e.columna, e.pos))
    return v.terminar()


# =========================================================================
# 6. SALIDAS: definicion formal, tabla y diagrama
# =========================================================================
def definicion_formal(c):
    M = c.M
    t = M.tamano()
    lin = ["M = (Q, Σ, Γ, δ, q0, Z0, F, w)", ""]
    lin.append(f"Q  ({t['estados']} estados) = {{{', '.join(sorted(M.Q))}}}")
    lin.append(f"Σ  ({t['simbolos_entrada']} simbolos) = {{{', '.join(sorted(M.Sigma))}}}")
    lin.append(f"Γ  ({t['simbolos_pila']} simbolos) = {{{', '.join(sorted(M.Gamma))}}}")
    for s in sorted(M.reg_pila):
        info = M.reg_pila[s]
        if s in M.Gamma and (info["bits"] or info["tope"]):
            partes = []
            if info["bits"]:
                partes.append(f"mascara de {len(info['bits'])} bits {info['bits']}")
            if info["tope"]:
                partes.append(f"contador saturado en {info['tope']}")
            lin.append(f"     {s} lleva " + " y ".join(partes))
    lin.append(f"     Γ con registros expandidos: {t['simbolos_pila_con_registros']} simbolos (finito)")
    lin.append(f"δ  ({t['transiciones']} filas): ver --tabla")
    lin.append(f"q0 = {M.q0}    Z0 = Z0    F = {{qF}}")
    lin.append("w : δ -> (N ∪ {∞}, min, +, ∞, 0)  semianillo tropical")
    lin.append("     w(fila) = 1 (estructura) + suma de los costos de sus comprobaciones")
    lin.append("     w(corrida) = suma de w de cada fila; comprobaciones ordenadas de menor a mayor costo")
    det = M.verificar_determinismo()
    lin.append("")
    lin.append("Determinismo de δ: " + ("OK, ninguna configuracion tiene dos filas"
                                         if not det else f"{len(det)} PROBLEMAS: {det}"))
    a, b = c.M_sin_min.tamano(), t
    lin.append(f"Minimizacion: {len(c.reglas_sin_min)} nodos -> {len(c.reglas)} nodos;  "
               f"{a['estados']} -> {b['estados']} estados;  "
               f"{a['transiciones']} -> {b['transiciones']} filas")
    return "\n".join(lin)


def tabla_texto(M):
    lin = [f"{'de':<10} {'lee':<14} {'tope':<6} {'a':<10} {'pila':<10} {'w':>3}  comprobaciones"]
    for f in sorted(M.filas(), key=lambda f: (f["de"], f["a"], f["tope"])):
        g = ", ".join(x[0] for x in f["guardas"])
        reg = f"  [{f['registro']}]" if f["registro"] else ""
        lin.append(f"{f['de']:<10} {f['a']:<14} {f['tope']:<6} {f['a_estado']:<10} "
                   f"{f['pila']:<10} {f['costo']:>3}  {g}{reg}")
    return "\n".join(lin)


def dot(M, titulo="DPDA", compacto=True, rutas=None):
    """Diagrama del DPDA (Graphviz).
    compacto=True: el sub-automata generico (cualquier JSON, estados con *) se
    dibuja como UNA sola caja, y los estados se agrupan por nodo del esquema."""
    import re

    def q(x):
        return '"' + x.replace('"', '\\"') + '"'

    def generico(e):
        return "*" in e

    def caja(e):
        return "JSON*" if compacto and generico(e) else e

    def nodo_de(e):
        m = re.match(r"^[VKNMCEGB](\d+)", e)
        return int(m.group(1)) if m else None

    l = ["digraph DPDA {", '  rankdir=LR; bgcolor="white"; nodesep=0.35; ranksep=0.55;',
         '  node [shape=circle, fontname="Helvetica", fontsize=11, style=filled, fillcolor="#eef3fb", color="#4a6fa5"];',
         '  edge [fontname="Helvetica", fontsize=9, color="#666666", arrowsize=0.7];',
         f'  labelloc="t"; fontname="Helvetica"; label={q(titulo)};',
         '  inicio [shape=point, width=0.12];', f"  inicio -> {q(M.q0)};",
         '  "qF" [shape=doublecircle, fillcolor="#d7f0d9", color="#2e7d32"];',
         '  "R" [fillcolor="#fff1c6", color="#b8860b", label="R\\n(retorno ε)"];']
    if compacto:
        l.append('  "JSON*" [shape=box, style="rounded,dashed,filled", fillcolor="#f4f4f4", '
                 'fontcolor="#666666", label="JSON*\\nsub-automata generico\\n(cualquier valor, solo sintaxis)"];')
    grupos = {}
    for e in M.Q:
        n = nodo_de(e)
        if n is not None and not generico(e):
            grupos.setdefault(n, []).append(e)
    for n, es in sorted(grupos.items()):
        ruta = rutas[n] if rutas and n < len(rutas) and rutas[n] else f"nodo {n}"
        l.append(f"  subgraph cluster_{n} {{ style=rounded; color=\"#b0bec5\"; "
                 f"fontname=\"Helvetica\"; fontsize=10; label={q('nodo ' + str(n) + ': ' + ruta)};")
        for e in sorted(es):
            l.append(f"    {q(e)};")
        l.append("  }")
    if not compacto:
        for e in sorted(M.Q):
            if generico(e):
                l.append(f'  {q(e)} [fillcolor="#f2f2f2", fontcolor="#777777"];')
    juntas = {}
    for f in M.filas():
        de, a = caja(f["de"]), caja(f["a_estado"])
        if compacto and de == "JSON*" and a in ("JSON*", "R"):
            continue                       # lo interno del generico no se dibuja
        k = (de, a, f["pila"], f["tope"])
        juntas.setdefault(k, []).append(f)
    for (de, a, pila, tope), fs in juntas.items():
        lee = ",".join(sorted({x["a"] for x in fs}))
        if pila == "igual":
            op = tope
        elif pila == "pop":
            op = "ε"
        else:
            op = pila[5:] + " " + tope
        w = max(x["costo"] for x in fs)
        chequea = sorted({g[0] for x in fs for g in x["guardas"]})
        color = "#c0392b" if chequea else "#666666"
        etiqueta = f"{lee}, {tope} / {op}\\nw={w}" + (f"  [{', '.join(chequea)}]" if chequea else "")
        l.append(f"  {q(de)} -> {q(a)} [label={q(etiqueta)}, color={q(color)}, fontcolor={q(color)}];")
    l.append("}")
    return "\n".join(l)


# =========================================================================
# 7. PRUEBAS
# =========================================================================
ESQ = ('{"type":"object","properties":{"id":{"type":"integer"},'
       '"tags":{"type":"array","items":{"type":"string"}}},"required":["id"]}')


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

    c = compilar_esquema(ESQ)
    # --- el ejemplo del enunciado ---
    r = validar(c, '{"id":7,"tags":["a"]}')
    chequear("valido", r.valido)
    r = validar(c, '{"tags":[5]}')
    chequear("invalido", not r.valido and not r.mal_formado)
    chequear("ruta /tags/0", any(e["ruta"] == "/tags/0" for e in r.errores))
    chequear("falta id en /", any(e["ruta"] == "/" and "obligatorias" in e["mensaje"]
                                  for e in r.errores))

    # --- la tabla es DATOS y el validador la lee ---
    chequear("delta serializable", json.loads(json.dumps(c.M.filas())) == c.M.filas())
    chequear("determinista", c.M.verificar_determinismo() == [])
    vacio = DPDA()
    vacio.agregar("V0", "{", "*", "K0")
    vacio.agregar("V0", "{", "Z0", "K1")
    vacio.agregar("R", EPS, "O0", "M0")
    vacio.agregar("R", ",", "O0", "N0")
    chequear("detecta no determinismo (comodin y epsilon)", len(vacio.verificar_determinismo()) == 2)

    # --- errores de v1 que ya no pasan ---
    for malo in ['{"id" 7}', '{"id":7 "tags":["a"]}', '{"id":7,,,"tags":["a"]}',
                 '{"id":7,"tags":["a" "b"]}', '{"id":7, }', '{"id":7,"tags":[,"a"]}',
                 '{"id":7,"tags":["a",]}', '{"id":7}}', '[1 2]', '{"id":7} {"id":8}',
                 '{"id":7', '', '{"id":}', '{:7}', '{"id":7,"tags":["a"],}']:
        try:
            r = validar(c, malo)
            chequear(f"mal formado {malo!r}", not r.valido and r.mal_formado)
        except Exception as e:
            chequear(f"mal formado {malo!r} sin excepcion ({e})", False)
    r = validar(c, '{"id":7,"id":8}')
    chequear("clave duplicada", not r.valido and "duplicada" in r.errores[0]["mensaje"])
    r = validar(compilar_esquema('{"type":"object"}'), '{"x":1,"x":2}')
    chequear("clave no declarada duplicada", not r.valido)

    # --- pesos: costo y violaciones ---
    r = validar(c, '{"id":"x","tags":[1,2]}')
    chequear("cuenta 3 violaciones", r.violaciones == 3)
    r1 = validar(c, '{"id":"x","tags":[1,2]}', parar_en_primero=True)
    chequear("fallo temprano: 1 violacion y menos costo", r1.violaciones == 1 and r1.costo < r.costo)
    for f in c.M.filas():
        costos = [g[1] for g in f["guardas"]]
        if costos != sorted(costos):
            chequear("guardas ordenadas por costo", False)
            break
    else:
        chequear("guardas ordenadas por costo", True)

    # --- streaming: el resultado no depende del tamano del bloque ---
    doc = '{"id": 12, "tags": ["aa", "bb"]}'
    chequear("streaming 1 byte", repr(validar(c, doc, bloque=1)) == repr(validar(c, doc)))
    for doc in ['{"id":"x","tags":[1,@]}', '{"id":01}', '{"tags":[5],"id":tru', '{"id":7,"tags":["a\x01"]}']:
        a, b = validar(c, doc, bloque=1), validar(c, doc)
        chequear(f"bloques iguales en {doc!r}", (a.errores, a.costo, a.pasos) == (b.errores, b.costo, b.pasos))

    # --- posicion en bytes y limites de tamano y tiempo (Fase 6) ---
    r = validar(c, '{"tags": [5]}')
    chequear("posicion en bytes del error", r.errores[0]["byte"] == 10 and r.errores[1]["byte"] == 12)
    r = validar(c, '{"id":7,"tags":["a","b","c"]}', max_bytes=10)
    chequear("limite de tamano", not r.valido and "tamano" in r.limite)
    r = validar(c, '[' + '1,' * 200000 + '1]', bloque=64, max_ms=1)
    chequear("limite de tiempo", not r.valido and "tiempo" in (r.limite or ""))

    # --- anidamiento profundo sin recursion, y limite de profundidad ---
    c2 = compilar_esquema('{"type":"object","properties":{"h":{"$ref":"#"}}}')
    n = 20000
    chequear("anidamiento 20000", validar(c2, '{"h":' * n + '{}' + '}' * n).valido)
    chequear("anidamiento 20000 con un 1 adentro", not validar(c2, '{"h":' * n + '1' + '}' * n).valido)
    r = validar(c2, '{"h":' * 50 + '{}' + '}' * 50, max_profundidad=10)
    chequear("limite de profundidad", not r.valido and "profundidad" in r.errores[0]["mensaje"])

    # --- minimizacion ---
    e3 = ('{"type":"object","properties":{"a":{"type":"string"},"b":{"type":"string"},'
          '"c":{"type":"array","items":{"type":"string"}},"d":{"type":"array","items":{"type":"string"}}}}')
    c3 = compilar_esquema(e3)
    chequear("minimizacion fusiona nodos iguales", len(c3.reglas) < len(c3.reglas_sin_min))
    chequear("minimizacion reduce estados", c3.M.tamano()["estados"] < c3.M_sin_min.tamano()["estados"])

    # --- bug de v1: sin "type", properties NO obliga a que sea objeto ---
    c4 = compilar_esquema('{"properties":{"a":{"type":"integer"}},"required":["a"]}')
    chequear("sin type, un arreglo pasa properties", validar(c4, "[1,2]").valido)
    chequear("sin type, un numero pasa properties", validar(c4, "5").valido)

    # --- contra json.loads: documentos danados (mal formados) ---
    random.seed(3)
    base = ['{"id": 7, "tags": ["a", "b"]}', '{"id": 1, "tags": []}']
    distintos = 0
    for _ in range(3000):
        t = list(random.choice(base))
        for _ in range(random.randint(1, 3)):
            pos = random.randrange(len(t)) if t else 0
            op = random.choice("bis")
            if op == "b" and t:
                del t[pos]
            elif op == "i":
                t.insert(pos, random.choice('{}[]:,"7a '))
            elif t:
                t[pos] = random.choice('{}[]:,"7a ')
        txt = "".join(t)
        try:
            ref = json.loads(txt)
            bien_formado = True
        except Exception:
            bien_formado = False
        r = validar(c, txt)
        if bien_formado == r.mal_formado:
            # si json lo acepta pero tiene claves repetidas, nosotros lo rechazamos a proposito
            if not (bien_formado and "duplicada" in str(r.errores)):
                distintos += 1
    chequear("3000 documentos danados: bien/mal formado igual que json.loads", distintos == 0)

    # --- contra la libreria jsonschema ---
    try:
        import jsonschema
    except ImportError:
        jsonschema = None
        print("  (jsonschema no instalada: se omite la comparacion)")
    if jsonschema:
        esquemas = [
            ESQ, e3,
            '{"type":"array","items":{"type":"integer","minimum":0,"maximum":100},"minItems":1,"maxItems":4}',
            '{"type":"object","properties":{"nombre":{"type":"string","minLength":2,"maxLength":5},'
            '"edad":{"type":"integer","minimum":0},"activo":{"type":"boolean"},"x":{"type":"null"}},'
            '"required":["nombre","edad"],"additionalProperties":false}',
            '{"type":"array","items":{"type":"array","items":{"type":"number"}}}',
            '{"type":"object","properties":{"a":{"enum":[1,"x",null]},"b":{"const":true},'
            '"c":{"type":["string","null"]}}}',
            '{"type":"object","properties":{"hijo":{"$ref":"#"},"v":{"type":"integer"}}}',
            '{"$defs":{"n":{"type":"integer","minimum":1}},"type":"array","items":{"$ref":"#/$defs/n"}}',
            '{"type":"object","properties":{"u":{"type":"object","properties":{"id":{"type":"integer"},'
            '"l":{"type":"array","items":{"type":"string"},"maxItems":2}},"required":["id"]}},"required":["u"]}',
            '{"properties":{"a":{"type":"integer"}},"required":["a"],"items":{"type":"string"}}',
            '{"type":"object","additionalProperties":{"type":"integer"}}',
            '{"type":"array","items":false}',
            '{"$defs":{"nodo":{"type":"object","properties":{"v":{"type":"integer"},'
            '"hijos":{"type":"array","items":{"$ref":"#/$defs/nodo"}}},"required":["v"]}},"$ref":"#/$defs/nodo"}',
            '{"type":["object","array"],"properties":{"a":{"type":"string"}},"minItems":2}',
            '{"minimum":3,"maxLength":2}',
            '{"required":["a"]}',
            '{"required":["a","id"],"additionalProperties":false}',
            '{"required":["a"],"additionalProperties":{"type":"integer"}}',
        ]
        random.seed(5)
        claves = ["id", "tags", "nombre", "edad", "activo", "x", "a", "b", "c", "d",
                  "hijo", "v", "u", "l", "hijos", "zz"]

        def gen(p=0):
            r = random.random()
            if p > 3 or r < 0.5:
                return random.choice([0, 1, 7, -3, 150, 2.5, 3.0, "a", "hola", "abcdefg", "",
                                      True, False, None, "x"])
            if r < 0.75:
                return [gen(p + 1) for _ in range(random.randint(0, 5))]
            return {k: gen(p + 1) for k in random.sample(claves, random.randint(0, 5))}

        dif = comparaciones = dif_min = 0
        for esq in esquemas:
            cc = compilar_esquema(esq)
            cs = compilar_esquema(esq, minimizar=False)
            val = jsonschema.Draft202012Validator(json.loads(esq))
            for _ in range(3000):
                d = gen()
                txt = json.dumps(d)
                comparaciones += 1
                nuestro = validar(cc, txt).valido
                if val.is_valid(d) != nuestro:
                    dif += 1
                    if dif <= 3:
                        print("   DIF", esq[:60], txt[:80], "jsonschema:", val.is_valid(d))
                if validar(cs, txt).valido != nuestro:
                    dif_min += 1
        chequear(f"{comparaciones} documentos al azar = jsonschema", dif == 0)
        chequear("DPDA minimo y sin minimizar dan lo mismo", dif_min == 0)
        chequear("todos los esquemas son deterministas",
                 all(compilar_esquema(e).M.verificar_determinismo() == [] for e in esquemas))

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
        print(definicion_formal(compilar_esquema(leer(a[1]))))
    elif a[0] == "--tabla":
        print(tabla_texto(compilar_esquema(leer(a[1])).M))
    elif a[0] == "--dot":
        c = compilar_esquema(leer(a[1]))
        print(dot(c.M, rutas=c.rutas, compacto="--completo" not in a))
    elif a[0] == "--validar":
        c = compilar_esquema(leer(a[1]))
        r = validar(c, leer(a[2]), traza="--traza" in a)
        if r.traza:
            for p in r.traza:
                print(f"  {p['paso']:>3}. {p['token']:<10} {p['fila']:<40} pila={p['pila_despues']}"
                      f"  w={p['costo']} {'  !! ' + '; '.join(p['violaciones']) if p['violaciones'] else ''}")
        print(" ", r)

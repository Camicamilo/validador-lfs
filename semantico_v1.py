r"""
semantico_v1.py - Fase 3: analisis semantico del esquema JSON

El parser (Fase 2) garantiza que el esquema esta bien ESCRITO.
Aqui se revisa que tenga SENTIDO y se clasifica cada palabra clave:

  VERDE    (directa)     cabe en los estados y la pila del automata
  AMARILLO (registros)   necesita un contador o una mascara de bits
  ROJO     (fuera)       no cabe en un automata de pila puro: se detecta y se documenta

Como correrlo:
  python semantico_v1.py                       -> corre las pruebas
  python semantico_v1.py --texto '{"type":"string"}'   -> analiza un esquema
"""
import sys
import json
from parser_v2 import parsear_texto, simplificar, ErrorSintactico
from lexer_v4 import ErrorLexico

TIPOS = {"object", "array", "string", "number", "integer", "boolean", "null"}

# palabra clave -> color
CLAVES = {
    # VERDE
    "type": "verde", "properties": "verde", "items": "verde", "enum": "verde",
    "const": "verde", "minimum": "verde", "maximum": "verde",
    "minLength": "verde", "maxLength": "verde", "additionalProperties": "verde",
    "$ref": "verde", "$defs": "verde", "definitions": "verde",
    "title": "verde", "description": "verde", "$schema": "verde", "$id": "verde",
    # AMARILLO
    "required": "amarillo", "minItems": "amarillo", "maxItems": "amarillo",
    # ROJO
    "anyOf": "rojo", "oneOf": "rojo", "allOf": "rojo", "not": "rojo",
    "pattern": "rojo", "uniqueItems": "rojo", "dependencies": "rojo",
    "dependentRequired": "rojo", "if": "rojo", "then": "rojo", "else": "rojo",
}


class Hallazgo:
    def __init__(self, nivel, ruta, mensaje):
        self.nivel, self.ruta, self.mensaje = nivel, ruta, mensaje

    def __repr__(self):
        return f"[{self.nivel}] {self.ruta or '/'}: {self.mensaje}"


def _es_entero_no_neg(v):
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0


def _es_numero(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def analizar(esquema):
    """Recorre el esquema SIN recursion (pila explicita).
    Devuelve (errores, avisos, clasificacion)."""
    errores, avisos = [], []
    clasificacion = {"verde": set(), "amarillo": set(), "rojo": set()}
    # $ref: nombres definidos y referencias encontradas
    definidos = set()
    refs = []

    pila = [(esquema, "")]
    while pila:
        nodo, ruta = pila.pop()
        if isinstance(nodo, bool):          # true / false son esquemas validos
            continue
        if not isinstance(nodo, dict):
            errores.append(Hallazgo("ERROR", ruta, "un esquema debe ser un objeto (o true/false)"))
            continue
        for clave, valor in nodo.items():
            r = f"{ruta}/{clave}"
            color = CLAVES.get(clave)
            if color is None:
                avisos.append(Hallazgo("AVISO", r, f"palabra clave desconocida '{clave}', se ignora"))
                continue
            clasificacion[color].add(clave)
            if color == "rojo":
                avisos.append(Hallazgo("FUERA", r, f"'{clave}' no cabe en un automata de pila puro: "
                                                  "se detecta y se documenta"))

            if clave == "type":
                tipos = valor if isinstance(valor, list) else [valor]
                if isinstance(valor, list) and not valor:
                    errores.append(Hallazgo("ERROR", r, "'type' no puede ser una lista vacia"))
                for t in tipos:
                    if not isinstance(t, str) or t not in TIPOS:
                        errores.append(Hallazgo("ERROR", r, f"tipo desconocido {t!r}; "
                                                          f"validos: {sorted(TIPOS)}"))
            elif clave in ("minItems", "maxItems", "minLength", "maxLength"):
                if not _es_entero_no_neg(valor):
                    errores.append(Hallazgo("ERROR", r, f"'{clave}' debe ser un entero >= 0, llego {valor!r}"))
            elif clave in ("minimum", "maximum"):
                if not _es_numero(valor):
                    errores.append(Hallazgo("ERROR", r, f"'{clave}' debe ser un numero"))
            elif clave == "required":
                if (not isinstance(valor, list) or not all(isinstance(x, str) for x in valor)):
                    errores.append(Hallazgo("ERROR", r, "'required' debe ser una lista de cadenas"))
                elif len(set(valor)) != len(valor):
                    errores.append(Hallazgo("ERROR", r, "'required' tiene nombres repetidos"))
                else:
                    props = nodo.get("properties")
                    if isinstance(props, dict):
                        for nombre in valor:
                            if nombre not in props:
                                errores.append(Hallazgo("ERROR", r, f"'{nombre}' es obligatorio pero no esta en 'properties'"))
            elif clave == "enum":
                if not isinstance(valor, list) or not valor:
                    errores.append(Hallazgo("ERROR", r, "'enum' debe ser una lista no vacia"))
            elif clave == "properties":
                if not isinstance(valor, dict):
                    errores.append(Hallazgo("ERROR", r, "'properties' debe ser un objeto"))
                else:
                    for nombre, sub in valor.items():
                        pila.append((sub, f"{r}/{nombre}"))
            elif clave in ("items", "additionalProperties"):
                if isinstance(valor, (dict, bool)):
                    pila.append((valor, r))
                else:
                    errores.append(Hallazgo("ERROR", r, f"'{clave}' debe ser un esquema"))
            elif clave in ("$defs", "definitions"):
                if not isinstance(valor, dict):
                    errores.append(Hallazgo("ERROR", r, f"'{clave}' debe ser un objeto"))
                else:
                    for nombre, sub in valor.items():
                        definidos.add(f"#/{clave}/{nombre}")
                        pila.append((sub, f"{r}/{nombre}"))
            elif clave == "$ref":
                if not isinstance(valor, str):
                    errores.append(Hallazgo("ERROR", r, "'$ref' debe ser una cadena"))
                else:
                    refs.append((valor, r))
            elif clave in ("anyOf", "oneOf", "allOf"):
                if not isinstance(valor, list) or not valor:
                    errores.append(Hallazgo("ERROR", r, f"'{clave}' debe ser una lista no vacia"))

        # coherencia entre claves del mismo objeto
        mn, mx = nodo.get("minimum"), nodo.get("maximum")
        if _es_numero(mn) and _es_numero(mx) and mn > mx:
            errores.append(Hallazgo("ERROR", ruta, "'minimum' es mayor que 'maximum'"))
        for a, b in (("minItems", "maxItems"), ("minLength", "maxLength")):
            if _es_entero_no_neg(nodo.get(a)) and _es_entero_no_neg(nodo.get(b)) and nodo[a] > nodo[b]:
                errores.append(Hallazgo("ERROR", ruta, f"'{a}' es mayor que '{b}'"))

    # $ref: deben apuntar a algo definido
    for ref, ruta in refs:
        if ref != "#" and ref not in definidos:
            errores.append(Hallazgo("ERROR", ruta, f"'$ref' apunta a {ref!r}, que no existe"))
    # ciclos de $ref que se apuntan solos sin consumir nada
    errores.extend(_ciclos_ref(esquema, definidos))
    return errores, avisos, clasificacion


def _ciclos_ref(esquema, definidos):
    """Una definicion que es SOLO un $ref a otra, formando un ciclo, nunca termina."""
    defs = {}
    for k in ("$defs", "definitions"):
        if isinstance(esquema, dict) and isinstance(esquema.get(k), dict):
            for nombre, sub in esquema[k].items():
                defs[f"#/{k}/{nombre}"] = sub
    if isinstance(esquema, dict):
        defs["#"] = esquema                      # la raiz tambien puede apuntarse a si misma
    sal = []
    for inicio, sub in defs.items():
        visto, actual = [inicio], sub
        while isinstance(actual, dict) and isinstance(actual.get("$ref"), str):
            sig = actual["$ref"]
            if sig in visto:
                sal.append(Hallazgo("ERROR", inicio, "ciclo de $ref sin fin: " + " -> ".join(visto + [sig])))
                break
            if sig not in defs:
                break
            visto.append(sig)
            actual = defs[sig]
    return sal


def analizar_texto(texto):
    return analizar(simplificar(parsear_texto(texto)))


# ---------------------------------------------------------------
# PRUEBAS
# ---------------------------------------------------------------
def correr_pruebas():
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    def errs(t):
        return analizar_texto(t)[0]

    # Esquemas validos
    validos = [
        '{"type":"object","properties":{"id":{"type":"integer"},"tags":{"type":"array","items":{"type":"string"}}},"required":["id"]}',
        '{"type":"string","minLength":1,"maxLength":10}',
        '{"type":["string","null"]}',
        '{"type":"integer","minimum":0,"maximum":100}',
        '{"enum":[1,2,3]}', 'true', '{}',
        '{"$defs":{"n":{"type":"integer"}},"properties":{"a":{"$ref":"#/$defs/n"}}}',
        '{"type":"array","minItems":1,"maxItems":3,"items":{"type":"number"}}',
    ]
    for t in validos:
        chequear(f"valido {t[:50]}", errs(t) == [])

    # Esquemas con error de sentido (pasan la Fase 2, no la 3)
    malos = {
        '{"type":"numero"}': "tipo desconocido",
        '{"type":[]}': "lista vacia",
        '{"minItems":-3}': "entero >= 0",
        '{"minItems":2.5}': "entero >= 0",
        '{"minItems":true}': "entero >= 0",
        '{"minItems":5,"maxItems":2}': "mayor que",
        '{"minimum":10,"maximum":1}': "mayor que",
        '{"type":"object","properties":{"a":{}},"required":["b"]}': "no esta en 'properties'",
        '{"required":"id"}': "lista de cadenas",
        '{"required":["a","a"]}': "repetidos",
        '{"enum":[]}': "no vacia",
        '{"properties":[]}': "debe ser un objeto",
        '{"items":3}': "debe ser un esquema",
        '{"properties":{"a":{"type":"x"}}}': "tipo desconocido",
        '{"properties":{"a":{"items":{"minLength":-1}}}}': "entero >= 0",
        '{"$ref":"#/$defs/nada"}': "no existe",
        '{"$defs":{"a":{"$ref":"#/$defs/b"},"b":{"$ref":"#/$defs/a"}}}': "ciclo",
        '{"$defs":{"a":{"$ref":"#/$defs/a"}}}': "ciclo",
        '{"$ref":"#"}': "ciclo",
        '[1,2]': "debe ser un objeto",
    }
    for t, parte in malos.items():
        e = errs(t)
        chequear(f"malo {t[:45]} -> {parte}", any(parte in x.mensaje for x in e))

    # La ruta del error apunta al lugar exacto
    e = errs('{"properties":{"a":{"items":{"minLength":-1}}}}')
    chequear("ruta exacta", e and e[0].ruta == "/properties/a/items/minLength")

    # Clasificacion
    _, avisos, cl = analizar_texto('{"type":"array","minItems":1,"uniqueItems":true,"items":{"type":"string"}}')
    chequear("verde", {"type", "items"} <= cl["verde"])
    chequear("amarillo", cl["amarillo"] == {"minItems"})
    chequear("rojo", cl["rojo"] == {"uniqueItems"})
    chequear("aviso FUERA", any(a.nivel == "FUERA" and a.ruta == "/uniqueItems" for a in avisos))
    _, avisos, _ = analizar_texto('{"foo":1}')
    chequear("clave desconocida = aviso", any("desconocida" in a.mensaje for a in avisos))
    _, _, cl = analizar_texto('{"anyOf":[{"type":"string"},{"type":"null"}]}')
    chequear("anyOf es rojo", "anyOf" in cl["rojo"])

    # Anidamiento profundo: no hay recursion
    n = 3000
    t = '{"items":' * n + '{"type":"string"}' + '}' * n
    chequear("anidamiento 3000", errs(t) == [])

    # Contra la libreria jsonschema (si esta instalada):
    #  todo lo que ELLA rechaza, nosotros tambien lo rechazamos.
    # (ella es mas permisiva: acepta minItems > maxItems, required sin properties, etc.;
    #  esas son justo las incoherencias que la Fase 3 existe para atrapar)
    try:
        import jsonschema
        casos = validos + [t for t in malos if not t.startswith("[")]
        casos += ['{"type":"foo"}', '{"minItems":"a"}', '{"required":[1]}', '{"properties":5}',
                  '{"items":5}', '{"minLength":-2}', '{"enum":5}', '{"type":5}']
        ella_rechaza_nosotros_no = []
        for t in casos:
            esq = json.loads(t)
            try:
                jsonschema.Draft202012Validator.check_schema(esq)
                ref = True
            except Exception:
                ref = False
            if not ref and errs(t) == []:
                ella_rechaza_nosotros_no.append(t)
        chequear("lo que jsonschema rechaza, lo rechazamos tambien", not ella_rechaza_nosotros_no)
        if ella_rechaza_nosotros_no:
            print("   ", ella_rechaza_nosotros_no)
    except ImportError:
        print("  (jsonschema no instalada: se omite la comparacion)")

    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


def mostrar(texto):
    try:
        errores, avisos, cl = analizar_texto(texto)
    except (ErrorLexico, ErrorSintactico) as e:
        print(" ", e)
        return
    for e in errores:
        print(" ", e)
    for a in avisos:
        print(" ", a)
    print("  verde:", sorted(cl["verde"]), " amarillo:", sorted(cl["amarillo"]), " rojo:", sorted(cl["rojo"]))
    print("  =>", "ESQUEMA VALIDO" if not errores else f"{len(errores)} ERROR(ES)")


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        correr_pruebas()
    elif a[0] == "--texto":
        mostrar(a[1])
    else:
        mostrar(open(a[0], encoding="utf-8").read())

r"""
prueba_app.py - Pruebas de la Fase 7: levanta app.py y le habla como un navegador

Prueba la API REST (compilar, descargar, visor, payloads, casos) y el WebSocket
(validacion por bloques, limites y comparacion en vivo).

Uso:  python prueba_app.py
"""
import sys
import os
import json
import time
import socket
import asyncio
import subprocess
import urllib.request
import urllib.error

AQUI = os.path.dirname(os.path.abspath(__file__))


def puerto_libre():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


def correr_pruebas():
    try:
        import websockets
        import fastapi          # noqa: F401
        import uvicorn          # noqa: F401
    except ImportError:
        print("  Faltan librerias:  pip install fastapi uvicorn websockets")
        return False
    puerto = puerto_libre()
    base = f"http://127.0.0.1:{puerto}"
    srv = subprocess.Popen([sys.executable, os.path.join(AQUI, "app.py"), str(puerto), "--sin-navegador"],
                           cwd=AQUI, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    def get(ruta):
        return urllib.request.urlopen(base + ruta, timeout=120).read()

    def post(ruta, cuerpo):
        r = urllib.request.Request(base + ruta, data=json.dumps(cuerpo).encode(), headers={"Content-Type": "application/json"})
        return urllib.request.urlopen(r, timeout=300).read()

    def codigo(f):
        try:
            f()
            return 200
        except urllib.error.HTTPError as e:
            return e.code

    try:
        for _ in range(100):                                   # esperar a que arranque
            try:
                get("/api/ejemplos")
                break
            except Exception:
                time.sleep(0.2)
        pagina = get("/").decode()
        chequear("la pagina carga y trae las 5 pestanas", all(x in pagina for x in ("tvisor", "tcodigo", "tflujo", "tcomp", "tcasos")))
        ej = json.loads(get("/api/ejemplos"))
        chequear("ejemplos de JSON, DTD y XSD", {v[0] for v in ej.values()} == {"json", "dtd", "xsd"})
        tipo, esq, doc = ej["JSON: enunciado (invalido)"]

        t = json.loads(post("/api/compilar", {"tipo": tipo, "esquema": esq}))
        chequear("compilar: automata con su tamano y definicion formal", t["ok"] and t["tamano"]["estados"] > 0 and "Q" in t["definicion"])
        chequear("compilar: genera validador.c, validador.rs y tablas.json", t["archivos"] == ["validador.c", "validador.rs", "tablas.json"])
        nativos = [m for m, v in t["nativos"].items() if v == "compilado"]
        print("  motores nativos compilados en la caja de arena:", nativos or "ninguno (falta gcc o rustc)")
        c = get(f"/api/descargar/{t['id']}/validador.c").decode()
        rs = get(f"/api/descargar/{t['id']}/validador.rs").decode()
        chequear("descarga del codigo C y Rust", "dpda_alimentar" in c and "dpda_alimentar" in rs)
        chequear("descarga del zip", get(f"/api/descargar/{t['id']}/codigo.zip")[:2] == b"PK")
        chequear("no se puede pedir otro archivo (lista blanca)",
                 codigo(lambda: get(f"/api/descargar/{t['id']}/app.py")) == 404
                 and codigo(lambda: get(f"/api/descargar/{t['id']}/..%2Fapp.py")) == 404)
        t2 = json.loads(post("/api/compilar", {"tipo": "json", "esquema": '{"type": "cosa"}'}))
        chequear("esquema con error: se reporta sin caerse", not t2["ok"] and t2["errores"])
        chequear("esquema gigante: rechazado", codigo(lambda: post("/api/compilar", {"tipo": "json", "esquema": " " * 300000})) == 413)
        h = post("/api/visor", {"tipo": tipo, "esquema": esq, "documento": doc}).decode()
        chequear("visor: fases 1 a 4 con el automata dibujado", "Fase 4" in h and "<svg" in h)
        x = ej["XML + XSD: pedido (valido)"]
        h = post("/api/visor", {"tipo": x[0], "esquema": x[1], "documento": x[2]}).decode()
        chequear("visor XML", "Fase 4" in h)
        p = json.loads(post("/api/payloads", {"tipo": tipo, "esquema": esq, "n": 3}))
        chequear("payloads JSON: validos, invalidos y mal formados", p["validos"] and p["invalidos"] and p["malformados"])
        p = json.loads(post("/api/payloads", {"tipo": x[0], "esquema": x[1], "n": 2}))
        chequear("payloads XML", p["validos"] and p["invalidos"])
        casos = json.loads(get("/api/casos"))
        chequear("casos: las 6 categorias del enunciado", {c["categoria"] for c in casos} ==
                 {"validos", "invalidos", "malformados", "fuera", "bombeo", "extremos"})
        uno = json.loads(get("/api/casos/" + casos[0]["_id"]))
        chequear("un caso trae esquema y payload", uno["esquema"] and "payload" in uno)
        r = json.loads(post("/api/casos/correr", {"id": next(c["_id"] for c in casos if c["categoria"] == "invalidos")}))
        chequear("correr un caso: todos los motores coinciden con lo esperado", not r["fallas"] and len(set(r["veredictos"].values())) == 1)
        r = json.loads(post("/api/casos/correr", {"categoria": "fuera"}))
        chequear("correr una categoria", r["resumen"][0]["casos"] == r["resumen"][0]["pasaron"] == 8)

        async def ws():
            async with websockets.connect(f"ws://127.0.0.1:{puerto}/ws", max_size=None) as s:
                async def pedir(m):
                    await s.send(m if isinstance(m, bytes) else json.dumps(m))
                    return json.loads(await s.recv())
                m = await pedir({"accion": "iniciar", "n": 1, "tipo": tipo, "esquema": esq})
                chequear("ws: iniciar", m["evento"] == "listo" and m["n"] == 1)
                datos, pilas, errs = b'{"id": 1, "tags": ["a", 7, "b"]}', [], []
                for i in range(0, len(datos), 4):
                    m = await pedir(datos[i:i + 4])
                    pilas.append(m["pila"])
                    errs += m["errores"]
                chequear("ws: la pila sube y baja bloque a bloque", max(pilas) == 3 and pilas[-1] == 1)
                chequear("ws: el error llega antes del final, con ruta y byte",
                         len(errs) == 1 and errs[0]["ruta"] == "/tags/1" and errs[0]["byte"] == 24)
                m = await pedir({"accion": "fin"})
                chequear("ws: veredicto", m["evento"] == "veredicto" and not m["valido"] and m["violaciones"] == 1)
                m = await pedir({"accion": "iniciar", "n": 2, "tipo": "json", "esquema": "{mal"})
                chequear("ws: esquema malo", m["evento"] == "error_esquema")
                await pedir({"accion": "iniciar", "n": 3, "tipo": "json", "esquema": '{"type":"array"}', "profundidad": 5})
                m = await pedir(b"[" * 50)
                m2 = await pedir({"accion": "fin"})
                chequear("ws: limite de profundidad", m["terminado"] and m2["limite"] and "profundidad" in m2["limite"])
                await pedir({"accion": "iniciar", "n": 4, "tipo": "json", "esquema": '{"type":"array"}', "max_bytes": 10})
                await pedir(b"[1,2,3,4,5,6,7,8,9]")
                m = await pedir({"accion": "fin"})
                chequear("ws: limite de tamano", m["limite"] and "tamano" in m["limite"] and m["bytes"] == 10)
                d = ej["XML + DTD: biblioteca (invalido)"]
                await pedir({"accion": "iniciar", "n": 5, "tipo": d[0], "esquema": d[1]})
                bd = d[2].encode()
                for i in range(0, len(bd), 16):
                    await pedir(bd[i:i + 16])
                m = await pedir({"accion": "fin"})
                chequear("ws: XML por bloques", not m["valido"] and not m["mal_formado"] and m["violaciones"] >= 1)
                await s.send(json.dumps({"accion": "comparar", "tipo": tipo, "esquema": esq, "documento": '{"id": 1}'}))
                filas = []
                while True:
                    m = json.loads(await s.recv())
                    if m["evento"] == "fila":
                        filas.append(m)
                    elif m["evento"] == "comparado":
                        break
                motores = [f["motor"] for f in filas]
                chequear("ws: comparacion en vivo con el interprete y la linea base", motores[0] == "dpda-python" and motores[-1] == "dom")
                chequear("ws: todos los motores dan el mismo veredicto", all(f["valido"] for f in filas))
                chequear("ws: los nativos compilados aparecen en la comparacion", all(n in motores for n in nativos))
        asyncio.run(ws())
    finally:
        srv.terminate()
        try:
            srv.wait(5)
        except subprocess.TimeoutExpired:
            srv.kill()
    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


if __name__ == "__main__":
    correr_pruebas()

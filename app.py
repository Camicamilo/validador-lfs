r"""
app.py - Fase 7: aplicacion web (API REST + WebSocket)

    pip install fastapi uvicorn websockets
    python app.py              (abre http://localhost:8000)
    python app.py 9000 --sin-navegador

Que trae la pagina:
  - Editor de esquema (JSON Schema, DTD o XSD) y de documento, con validacion
    EN VIVO mientras se escribe (por WebSocket).
  - Automata y arbol: las fases 1 a 4 dibujadas, con el reproductor paso a paso.
  - Codigo generado: compila el esquema, deja descargar validador.c,
    validador.rs y las tablas, y genera payloads validos e invalidos.
  - Streaming: manda el documento por bloques y muestra la pila subir y bajar.
  - Comparacion en vivo: DPDA en Python, C y Rust contra la linea base (DOM +
    validador generico): MB/s, ciclos por byte, memoria, asignaciones, pila.
  - Casos de prueba: la coleccion local (casos.json) y la suite completa.

API REST
  GET  /api/ejemplos                    POST /api/compilar
  GET  /api/descargar/{id}/{archivo}    POST /api/visor
  POST /api/payloads                    GET  /api/casos   GET /api/casos/{id}
  POST /api/casos/correr                GET  /api/metricas   POST /api/banco
WebSocket  /ws
  -> {"accion":"iniciar", tipo, esquema, parar, profundidad, max_bytes, max_ms}
  -> bloques del documento (mensajes binarios)        <- {"evento":"estado", ...}
  -> {"accion":"fin"}                                 <- {"evento":"veredicto", ...}
  -> {"accion":"comparar", tipo, esquema, documento}  <- {"evento":"fila", ...} por motor

Caja de arena (sandbox): el codigo generado se compila y se ejecuta en una
carpeta temporal propia, con nombres fijos, sin shell, con limite de tiempo y
(en Linux/macOS) limites de CPU y memoria y sin variables de entorno. Los
textos del esquema nunca llegan al compilador como codigo: van como numeros.

Todo corre en tu computador; no usa ningun servicio de nube.
"""
import sys
import os
import io
import json
import time
import shutil
import hashlib
import zipfile
import asyncio
import tempfile
import webbrowser

try:
    from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Body
    from fastapi.responses import HTMLResponse, Response
    import uvicorn
except ImportError:
    print("Faltan las librerias de la aplicacion web. Instalalas con:\n\n"
          "    pip install fastapi uvicorn websockets\n")
    sys.exit(1)

import automata_v2 as A
import xml_v1 as X
import generador_v1 as G
import payloads_v1 as P
import tiempo_real_v1 as T
import casos_v1 as C
import visor
from semantico_v1 import analizar_texto
from ejemplos import EJEMPLOS

AQUI = os.path.dirname(os.path.abspath(__file__))
CAJA = tempfile.mkdtemp(prefix="lfa_caja_")          # raiz de la caja de arena
LIM_ESQUEMA, LIM_DOC, LIM_BLOQUE, MAX_TALLER = 200_000, 3_000_000, 1_000_000, 40
TALLER = {}                                           # id -> esquema compilado (cache)
DESCARGAS = ("validador.c", "validador.rs", "tablas.json")
FORMATO = {"json": "json", "xml-dtd": "dtd", "xml-xsd": "xsd"}

app = FastAPI(title="Validador JSON/XML con automatas de pila ponderados")


# =========================================================================
# 1. COMPILAR (con cache) Y CAJA DE ARENA
# =========================================================================
def preparar(tipo, esquema, raiz=None):
    """Esquema -> automata (Fases 1 a 4). Rapido: es lo que se usa mientras se escribe."""
    if tipo not in ("json", "dtd", "xsd"):
        raise HTTPException(400, "tipo debe ser json, dtd o xsd")
    if len(esquema.encode("utf-8")) > LIM_ESQUEMA:
        raise HTTPException(413, "esquema demasiado grande")
    ident = hashlib.sha256(f"{tipo}\0{raiz}\0{esquema}".encode("utf-8")).hexdigest()[:16]
    if ident in TALLER:
        return TALLER[ident]
    t = {"id": ident, "tipo": tipo, "esquema": esquema, "ok": False, "errores": [], "avisos": [],
         "nativos": {}, "bin": {}, "archivos": []}
    t0 = time.perf_counter()
    try:
        if tipo == "json":
            c = A.compilar_esquema(esquema)
            _, avisos, _ = analizar_texto(esquema)
            t.update(obj=c, tamano=c.M.tamano(), definicion=A.definicion_formal(c),
                     clasificacion={k: sorted(v) for k, v in c.clasificacion.items()},
                     avisos=[{"nivel": a.nivel, "ruta": a.ruta or "/", "mensaje": a.mensaje} for a in avisos])
        else:
            M = X.compilar(tipo.upper(), esquema, raiz) if tipo == "dtd" else X.compilar("XSD", esquema)
            t.update(obj=M, tamano=M.tamano(), definicion=X.definicion_formal(M))
        t["ok"] = True
    except Exception as e:                            # esquema con errores: se reporta, no se cae
        t["errores"] = [str(e)[:800]]
    t["ms_automata"] = round((time.perf_counter() - t0) * 1000, 1)
    TALLER[ident] = t
    while len(TALLER) > MAX_TALLER:                   # se bota el mas viejo, con su carpeta
        viejo = TALLER.pop(next(iter(TALLER)))
        shutil.rmtree(viejo.get("carpeta", ""), ignore_errors=True)
    return t


def nativos(t):
    """Fase 5: genera C y Rust y los compila dentro de la caja de arena (una vez por esquema)."""
    if not t["ok"] or t["nativos"]:
        return t
    if t["tipo"] != "json":
        t["nativos"] = {"dpda-c": "solo se genera para JSON Schema", "dpda-rust": "solo se genera para JSON Schema"}
        return t
    carpeta = os.path.join(CAJA, t["id"])
    t0 = time.perf_counter()
    G.generar(t["esquema"], carpeta)
    t["carpeta"], t["archivos"] = carpeta, list(DESCARGAS)
    for motor, leng in (("dpda-c", "c"), ("dpda-rust", "rust")):
        if not G.hay(leng):
            t["nativos"][motor] = "no hay compilador instalado (el codigo igual se puede descargar)"
            continue
        try:
            try:
                t["bin"][motor] = G.compilar(carpeta, leng, contar=True) if leng == "c" else G.compilar(carpeta, leng)
            except Exception:
                t["bin"][motor] = G.compilar(carpeta, leng)
            t["nativos"][motor] = "compilado"
        except Exception as e:
            t["nativos"][motor] = "no compilo: " + str(e)[:300]
    t["ms_nativos"] = round((time.perf_counter() - t0) * 1000, 1)
    return t


def publico(t):
    return {k: v for k, v in t.items() if k not in ("obj", "bin", "carpeta", "esquema")}


def filas_de(t, datos, prof=None):
    """Mide el mismo documento en cada motor; va entregando las filas de a una."""
    if t["tipo"] == "json":
        py = T.medir_python(t["obj"], datos, max_prof=prof)
        yield py
        for motor, b in t["bin"].items():
            f = T.medir_nativo(b, datos, motor, ("--prof", str(prof)) if prof else ())
            f["pila_max"] = py["pila_max"]
            yield f
        yield T.medir_dom(t["esquema"], datos)
    else:
        yield T.medir_xml(t["obj"], datos, max_prof=prof)
        f = T.medir_dom_xml(t["tipo"].upper(), t["esquema"], datos)
        if f:
            yield f


# =========================================================================
# 2. API REST
# =========================================================================
@app.get("/", response_class=HTMLResponse)
def inicio():
    return PAGINA


@app.get("/api/ejemplos")
def ejemplos():
    return EJEMPLOS


@app.post("/api/compilar")
def api_compilar(p: dict = Body(...)):
    t = preparar(p.get("tipo", "json"), p.get("esquema", ""))
    return publico(nativos(t))


@app.get("/api/descargar/{ident}/{nombre}")
def descargar(ident: str, nombre: str):
    t = TALLER.get(ident)
    if not t or not t.get("carpeta") or nombre not in DESCARGAS + ("codigo.zip",):   # lista blanca
        raise HTTPException(404, "no existe")
    if nombre == "codigo.zip":
        mem = io.BytesIO()
        with zipfile.ZipFile(mem, "w", zipfile.ZIP_DEFLATED) as z:
            for n in DESCARGAS:
                z.write(os.path.join(t["carpeta"], n), n)
        return Response(mem.getvalue(), media_type="application/zip",
                        headers={"Content-Disposition": "attachment; filename=codigo_generado.zip"})
    datos = open(os.path.join(t["carpeta"], nombre), "rb").read()
    return Response(datos, media_type="text/plain; charset=utf-8",
                    headers={"Content-Disposition": f"attachment; filename={nombre}"})


@app.post("/api/visor", response_class=HTMLResponse)
def api_visor(p: dict = Body(...)):
    """Las fases 1 a 4 dibujadas: tokens, arbol de derivacion, semantica y automata."""
    if len(p.get("documento", "").encode("utf-8")) > 200_000:
        return "<p style='font-family:sans-serif'>El documento es muy grande para dibujarlo paso a paso (maximo 200 KB). " \
               "Usa las pestanas Streaming o Comparacion.</p>"
    try:
        prof = int(p["profundidad"]) if p.get("profundidad") else None
        if p.get("tipo") == "json":
            return visor.generar(p["esquema"], p["documento"], bool(p.get("parar")), prof)
        return visor.generar_xml(p["tipo"].upper(), p["esquema"], p["documento"], bool(p.get("parar")), prof)
    except Exception as e:
        return "<pre style='color:#b71c1c'>No se pudo dibujar:\n" + visor.e(str(e)[:2000]) + "</pre>"


@app.post("/api/payloads")
def api_payloads(p: dict = Body(...)):
    """Fase 5: payloads validos e invalidos fabricados a partir del esquema."""
    t = preparar(p.get("tipo", "json"), p.get("esquema", ""))
    if not t["ok"]:
        raise HTTPException(400, "; ".join(t["errores"]))
    n, semilla = min(int(p.get("n", 3)), 10), int(p.get("semilla", 1))
    sal = {"validos": [], "invalidos": [], "malformados": []}
    try:
        if t["tipo"] == "json":
            g = P.GenJSON(json.loads(t["esquema"]), semilla)
            for _ in range(n):
                doc = g.valido()
                sal["validos"].append(json.dumps(doc, ensure_ascii=False, indent=1))
                for motivo, ruta, malo in g.invalidos(doc):
                    if len(sal["invalidos"]) < 30 and not any(x["motivo"] == f"{motivo} en {ruta}" for x in sal["invalidos"]):
                        sal["invalidos"].append({"motivo": f"{motivo} en {ruta}", "doc": json.dumps(malo, ensure_ascii=False)})
            for motivo, datos in P.malformados(doc):
                sal["malformados"].append({"motivo": motivo, "doc": datos.decode("utf-8", errors="replace")})
        else:
            g = P.GenXML(t["obj"].E, semilla)
            for _ in range(n):
                arbol = g.valido()
                sal["validos"].append(arbol.texto())
                for motivo, malo in g.invalidos(arbol):
                    if not any(x["motivo"] == motivo for x in sal["invalidos"]):
                        sal["invalidos"].append({"motivo": motivo, "doc": malo})
            sal["malformados"] = [{"motivo": m, "doc": d} for m, d in P.malformados_xml(arbol.texto())]
    except P.Imposible:
        raise HTTPException(400, "el esquema no admite ningun documento")
    return sal


def _almacen():
    a = C.Almacen()
    return a if a.docs else C.sembrar(a.ruta)


@app.get("/api/casos")
def casos(categoria: str = ""):
    return [{k: d.get(k) for k in ("_id", "categoria", "sub", "formato", "esperado", "nota")}
            for d in _almacen().docs if not categoria or d["categoria"] == categoria]


@app.get("/api/casos/{ident}")
def caso(ident: str):
    d = _almacen().uno(ident)
    if not d:
        raise HTTPException(404, "no existe")
    datos = C.payload_de(d)
    sal = {k: v for k, v in d.items() if k not in ("payload", "payload_b64")}
    sal.update(tipo=FORMATO[d["formato"]], bytes=len(datos), grande=len(datos) > 100_000)
    if not sal["grande"]:
        sal["payload"] = datos.decode("utf-8", errors="replace")
    return sal


@app.post("/api/casos/correr")
def correr_casos(p: dict = Body(default={})):
    t0 = time.perf_counter()
    if p.get("id"):
        d = _almacen().uno(p["id"])
        if not d:
            raise HTTPException(404, "no existe")
        v, fallas = C.Suite().correr(d)
        return {"veredictos": v, "fallas": fallas, "esperado": d["esperado"]}
    resumen, malos = C.correr_suite(p.get("categoria") or None, _almacen(), silencio=True)
    return {"resumen": [{"categoria": c, "casos": resumen[c]["casos"], "pasaron": resumen[c]["pasaron"],
                         "subs": sorted(resumen[c]["subs"])} for c in C.CATEGORIAS if c in resumen],
            "fallas": [{"id": i, "sub": s, "detalle": f} for i, s, f in malos[:20]],
            "segundos": round(time.perf_counter() - t0, 1)}


@app.get("/api/metricas")
def metricas():
    ruta = os.path.join(AQUI, "salida", "metricas.json")
    return json.load(open(ruta, encoding="utf-8")) if os.path.exists(ruta) else {}


@app.get("/api/metricas.svg")
def metricas_svg():
    ruta = os.path.join(AQUI, "salida", "metricas.svg")
    if not os.path.exists(ruta):
        raise HTTPException(404, "todavia no se ha corrido el banco")
    return Response(open(ruta, "rb").read(), media_type="image/svg+xml")


@app.post("/api/banco")
def api_banco():
    """Corre la version corta del banco de la Fase 6 (unos segundos)."""
    return T.banco(os.path.join(AQUI, "salida"), rapido=True)


# =========================================================================
# 3. WEBSOCKET: validacion por bloques y comparacion en vivo
# =========================================================================
def _entero(v):
    try:
        return int(v) if v not in (None, "") else None
    except (TypeError, ValueError):
        return None


@app.websocket("/ws")
async def ws(sock: WebSocket):
    await sock.accept()
    flujo, n, vistos = None, None, 0
    try:
        while True:
            msg = await sock.receive()
            if msg["type"] == "websocket.disconnect":
                break
            if msg.get("bytes") is not None:                         # un bloque del documento
                if flujo is None:
                    continue
                if len(msg["bytes"]) > LIM_BLOQUE or flujo.bytes + len(msg["bytes"]) > LIM_DOC:
                    await sock.send_json({"evento": "error", "n": n, "mensaje": "bloque o documento demasiado grande"})
                    continue
                est = await asyncio.to_thread(flujo.alimentar, msg["bytes"])
                est["errores"], vistos = est["errores"][vistos:], len(est["errores"])
                await sock.send_json({"evento": "estado", "n": n, **est})
                continue
            p = json.loads(msg.get("text") or "{}")
            accion = p.get("accion")
            if accion == "iniciar":
                if flujo is not None:
                    flujo.terminar()
                n, vistos, flujo = p.get("n"), 0, None
                t = await asyncio.to_thread(preparar, p.get("tipo", "json"), p.get("esquema", ""))
                if not t["ok"]:
                    await sock.send_json({"evento": "error_esquema", "n": n, "errores": t["errores"]})
                    continue
                prof, tope = _entero(p.get("profundidad")), _entero(p.get("max_bytes"))
                if t["tipo"] == "json":
                    flujo = T.Flujo(t["obj"], bool(p.get("parar")), prof, tope, _entero(p.get("max_ms")))
                else:
                    flujo = T.FlujoXML(t["obj"], bool(p.get("parar")), prof, tope)
                await sock.send_json({"evento": "listo", "n": n, "id": t["id"], "tamano": t["tamano"],
                                      "avisos": t["avisos"]})
            elif accion == "fin" and flujo is not None:
                r = await asyncio.to_thread(flujo.terminar)
                await sock.send_json({"evento": "veredicto", "n": n, "valido": r.valido, "mal_formado": r.mal_formado,
                                      "limite": getattr(r, "limite", None), "violaciones": r.violaciones,
                                      "costo": r.costo, "pasos": r.pasos, "pila_max": r.prof_max,
                                      "errores": r.errores[:100], "bytes": flujo.bytes, "ms": round(flujo.ms, 3)})
                flujo = None
            elif accion == "comparar":
                if p.get("caso"):
                    d = _almacen().uno(p["caso"])
                    tipo, esquema, datos, raiz = FORMATO[d["formato"]], d["esquema"], C.payload_de(d), d.get("raiz")
                    prof = d.get("limites", {}).get("max_prof")
                else:
                    tipo, esquema, raiz = p.get("tipo", "json"), p.get("esquema", ""), None
                    datos, prof = p.get("documento", "").encode("utf-8"), _entero(p.get("profundidad"))
                if len(datos) > LIM_DOC:
                    await sock.send_json({"evento": "error", "mensaje": "documento demasiado grande"})
                    continue
                t = await asyncio.to_thread(lambda: nativos(preparar(tipo, esquema, raiz)))
                if not t["ok"]:
                    await sock.send_json({"evento": "error_esquema", "errores": t["errores"]})
                    continue
                await sock.send_json({"evento": "comparando", "bytes": len(datos), "nativos": t["nativos"]})
                it = filas_de(t, datos, prof)
                while True:
                    fila = await asyncio.to_thread(next, it, None)
                    if fila is None:
                        break
                    await sock.send_json({"evento": "fila", **fila})
                await sock.send_json({"evento": "comparado"})
    except (WebSocketDisconnect, RuntimeError):
        pass
    finally:
        if flujo is not None:
            flujo.terminar()


# =========================================================================
# 4. LA PAGINA (un solo archivo, sin librerias externas)
# =========================================================================
PAGINA = r"""<!DOCTYPE html><html lang="es"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><link rel="icon" href="data:,">
<title>Validador JSON/XML con automatas de pila</title>
<style>
:root{--azul:#1f3b5b;--verde:#1b7f3b;--rojo:#b3261e;--gris:#5b6470;--borde:#cfd6de;--fondo:#eef1f5}
*{box-sizing:border-box} body{font-family:system-ui,Helvetica,Arial,sans-serif;margin:0;background:var(--fondo);color:#1c2430}
header{background:var(--azul);color:#fff;padding:10px 18px} header h1{font-size:18px;margin:0 0 6px}
.barra{display:flex;gap:10px;align-items:center;flex-wrap:wrap;font-size:14px}
select,button,input[type=number]{padding:6px 9px;border-radius:6px;border:1px solid #9aa9bb;font-size:14px}
button{cursor:pointer;background:#fff} button.p{background:var(--verde);color:#fff;border:0;font-weight:600;padding:8px 16px}
button:disabled{opacity:.5;cursor:wait}
.editores{display:grid;grid-template-columns:1fr 1fr;gap:12px;padding:12px 18px 6px}
@media(max-width:800px){.editores{grid-template-columns:1fr}}
.tit{display:flex;justify-content:space-between;align-items:center;margin-bottom:4px;font-size:14px;font-weight:600}
textarea{width:100%;height:210px;font-family:Consolas,Menlo,monospace;font-size:13px;border:1px solid #b0bec5;border-radius:6px;padding:8px;resize:vertical;tab-size:2}
#pildora{margin:4px 18px 8px;padding:9px 12px;border-radius:8px;background:#fff;border:1px solid var(--borde);font-size:14px;min-height:38px}
#pildora.ok{border-left:6px solid var(--verde)} #pildora.mal{border-left:6px solid var(--rojo)}
#pildora ul{margin:6px 0 0;padding-left:20px} code{background:#eef1f5;padding:1px 5px;border-radius:4px;font-size:13px}
nav{display:flex;gap:4px;padding:0 18px;flex-wrap:wrap} nav button{border-radius:8px 8px 0 0;border-bottom:0;background:#dde3ea}
nav button.act{background:#fff;font-weight:600;border-top:3px solid var(--azul)}
section{display:none;background:#fff;margin:0 18px 30px;padding:14px 16px;border:1px solid var(--borde);border-radius:0 8px 8px 8px;overflow-x:auto}
section.act{display:block} h2{font-size:16px;margin:4px 0 8px} p.ay{color:var(--gris);font-size:13px;margin:4px 0 10px}
table{border-collapse:collapse;font-size:13px;margin:8px 0} th,td{border:1px solid var(--borde);padding:5px 9px;text-align:right}
th{background:#f3f5f8} td:first-child,th:first-child{text-align:left} td.t,th.t{text-align:left}
iframe{width:100%;height:1300px;border:1px solid var(--borde);border-radius:6px}
pre{background:#f6f8fa;border:1px solid var(--borde);border-radius:6px;padding:10px;font-size:12px;overflow:auto;max-height:340px;white-space:pre-wrap;word-break:break-all}
.si{color:var(--verde);font-weight:600} .no{color:var(--rojo);font-weight:600} .chip{display:inline-block;padding:2px 8px;border-radius:10px;background:#e8edf3;font-size:12px;margin:2px}
.barraH{height:14px;border-radius:3px;display:inline-block;vertical-align:middle;min-width:2px}
.hecho{background:#d7f0dd} .falta{color:#9aa3ad} .fila{display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin:6px 0}
.doc{cursor:pointer} .doc:hover{background:#eef6ff} label{white-space:nowrap}
</style></head><body>
<header><h1>Validador en tiempo real &middot; automatas de pila ponderados</h1>
<div class="barra">
  <label>Esquema <select id="tipo"><option value="json">JSON Schema</option><option value="dtd">XML + DTD</option><option value="xsd">XML + XSD</option></select></label>
  <label>Ejemplo <select id="ejemplo"><option value="">(elige uno)</option></select></label>
  <label><input type="checkbox" id="parar"> fallo temprano</label>
  <label>profundidad max <input id="prof" type="number" min="1" style="width:80px" placeholder="sin limite"></label>
  <label><input type="checkbox" id="envivo" checked> validar mientras escribo</label>
  <button class="p" id="bvalidar">&#9654; Validar</button>
</div></header>
<div class="editores">
  <div><div class="tit"><span>Esquema</span><input type="file" id="fesq"></div><textarea id="esquema" spellcheck="false"></textarea></div>
  <div><div class="tit"><span>Documento (payload)</span><input type="file" id="fdoc"></div><textarea id="doc" spellcheck="false"></textarea></div>
</div>
<div id="pildora">Escribe o elige un ejemplo.</div>
<nav id="nav">
  <button data-t="tvisor" class="act">Automata y arbol</button><button data-t="tcodigo">Codigo generado</button>
  <button data-t="tflujo">Streaming</button><button data-t="tcomp">Comparacion en vivo</button><button data-t="tcasos">Casos de prueba</button>
</nav>

<section id="tvisor" class="act"><h2>Fases 1 a 4 dibujadas</h2>
  <p class="ay">Tokens, arbol de derivacion, semantica del esquema y el automata de pila con su reproductor paso a paso.</p>
  <button id="bvisor">Dibujar</button><div id="evisor" class="ay"></div>
  <iframe id="visor" title="fases" sandbox="allow-scripts"></iframe></section>

<section id="tcodigo"><h2>Fase 5 &middot; Compilar el esquema y descargar el validador</h2>
  <p class="ay">El esquema se convierte en tablas y se emite un validador en C y otro en Rust. Se compilan dentro de una caja de arena.</p>
  <button class="p" id="bcompilar">Compilar esquema</button> <span id="ecompilar" class="ay"></span>
  <div id="rcompilar"></div>
  <h2 style="margin-top:18px">Generador de payloads</h2>
  <p class="ay">Documentos validos e invalidos fabricados a partir del esquema. Clic en uno para llevarlo al editor.</p>
  <button id="bpayloads">Generar payloads</button><div id="rpayloads"></div></section>

<section id="tflujo"><h2>Fase 6 &middot; Validacion por bloques (streaming)</h2>
  <p class="ay">El documento se envia por WebSocket en pedazos. El validador responde despues de cada pedazo: nunca espera a tener el documento completo.</p>
  <div class="fila"><label>bytes por bloque <input id="sbloque" type="number" min="1" value="8" style="width:80px"></label>
  <label>pausa (ms) <input id="spausa" type="number" min="0" value="40" style="width:80px"></label>
  <label>limite de pila <input id="sprof" type="number" min="1" style="width:80px"></label>
  <label>limite de bytes <input id="sbytes" type="number" min="1" style="width:90px"></label>
  <label>limite de ms <input id="sms" type="number" min="0" style="width:80px"></label>
  <button class="p" id="bflujo">Enviar por bloques</button></div>
  <div id="sestado" class="ay"></div>
  <svg id="spila" viewBox="0 0 800 170" style="width:100%;max-width:900px;border:1px solid var(--borde);border-radius:6px;background:#fbfcfd"></svg>
  <pre id="sdoc"></pre><div id="serr"></div></section>

<section id="tcomp"><h2>Comparacion en vivo de los motores</h2>
  <p class="ay">El mismo documento en cada motor. La linea base arma todo el arbol en memoria (DOM) y luego lo revisa con un validador generico. Con documentos de pocos bytes casi todo el tiempo es de arranque: para comparar velocidad elige un caso grande de la lista.</p>
  <div class="fila"><label>Documento <select id="cfuente"><option value="">el del editor</option></select></label>
  <button class="p" id="bcomp">Comparar</button><label><input type="checkbox" id="crepetir"> repetir cada 3 s</label>
  <span id="ecomp" class="ay"></span></div>
  <div id="rcomp"></div>
  <h2 style="margin-top:18px">Banco de la Fase 6</h2>
  <p class="ay">Tamano creciente y pruebas de bombeo. <button id="bbanco">Correr banco corto</button> <span id="ebanco"></span></p>
  <div id="rbanco"></div></section>

<section id="tcasos"><h2>Casos de prueba (coleccion local casos.json)</h2>
  <div class="fila" id="cfiltros"></div>
  <div class="fila"><button class="p" id="bsuite">Correr la suite</button><span id="esuite" class="ay"></span></div>
  <div id="rsuite"></div><div id="rcasos"></div></section>

<script>
const $ = id => document.getElementById(id);
const esc = s => String(s == null ? '' : s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const num = id => { const v = parseInt($(id).value, 10); return isNaN(v) ? null : v; };
const enc = new TextEncoder(), dec = new TextDecoder();
const dormir = ms => new Promise(r => setTimeout(r, ms));
const json = (url, cuerpo) => fetch(url, cuerpo === undefined ? {} : {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify(cuerpo)})
  .then(async r => { if (!r.ok) throw new Error((await r.json().catch(() => ({}))).detail || r.statusText); return r.json(); });
const cuerpo = () => ({tipo: $('tipo').value, esquema: $('esquema').value, documento: $('doc').value, parar: $('parar').checked, profundidad: num('prof')});
let EJ = {}, CASOS = [], catActual = '';

/* ---------- conexion WebSocket con cola de mensajes ---------- */
function conectar(){
  return new Promise((ok, mal) => {
    const s = new WebSocket((location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + '/ws');
    const cola = []; let espera = null;
    s.onmessage = e => { const m = JSON.parse(e.data); if (espera) { const f = espera; espera = null; f(m); } else cola.push(m); };
    s.siguiente = () => cola.length ? Promise.resolve(cola.shift()) : new Promise(r => espera = r);
    s.onclose = () => { if (espera) espera({evento:'cerrado'}); };
    s.onopen = () => ok(s); s.onerror = () => mal(new Error('no se pudo abrir el WebSocket'));
  });
}
function errores(lista){
  return '<ul>' + lista.slice(0, 8).map(x => '<li><code>' + esc(x.ruta) + '</code> ' + esc(x.mensaje) +
    (x.linea ? ' <small>(linea ' + x.linea + ', col ' + x.columna + (x.byte != null ? ', byte ' + x.byte : '') + ')</small>' : '') + '</li>').join('') +
    (lista.length > 8 ? '<li>... y ' + (lista.length - 8) + ' mas</li>' : '') + '</ul>';
}
function pintarVeredicto(m, donde){
  const d = $(donde);
  if (m.evento === 'error_esquema') { d.className = 'mal'; d.innerHTML = '<b class="no">El esquema tiene errores</b><ul>' + m.errores.map(x => '<li>' + esc(x) + '</li>').join('') + '</ul>'; return; }
  if (m.valido) { d.className = 'ok'; d.innerHTML = '<b class="si">VALIDO</b> &mdash; costo ' + m.costo + ', ' + m.pasos + ' pasos, pila maxima ' + m.pila_max + ', ' + m.bytes + ' bytes en ' + m.ms + ' ms'; return; }
  d.className = 'mal';
  d.innerHTML = '<b class="no">' + (m.limite ? 'LIMITE SUPERADO' : m.mal_formado ? 'MAL FORMADO' : 'INVALIDO') + '</b> &mdash; ' + m.violaciones + ' violacion(es), costo ' + m.costo + errores(m.errores);
}

/* ---------- validacion en vivo mientras se escribe ---------- */
let wsVivo = null, nVivo = 0, tVivo = null;
async function vivo(){
  try {
    if (!wsVivo || wsVivo.readyState !== 1) {
      wsVivo = await conectar();
      (async s => { for (;;) { const m = await s.siguiente(); if (m.evento === 'cerrado') break;
        if (m.n === nVivo && (m.evento === 'veredicto' || m.evento === 'error_esquema')) pintarVeredicto(m, 'pildora'); } })(wsVivo);
    }
    const n = ++nVivo, c = cuerpo();
    wsVivo.send(JSON.stringify({accion:'iniciar', n, tipo:c.tipo, esquema:c.esquema, parar:c.parar, profundidad:c.profundidad}));
    const datos = enc.encode(c.documento);
    for (let i = 0; i < datos.length || i === 0; i += 65536) { wsVivo.send(datos.slice(i, i + 65536)); if (!datos.length) break; }
    wsVivo.send(JSON.stringify({accion:'fin', n}));
  } catch (e) { $('pildora').className = 'mal'; $('pildora').textContent = 'Sin conexion con el servidor: ' + e.message; }
}
function alEscribir(){ if (!$('envivo').checked) return; clearTimeout(tVivo); tVivo = setTimeout(vivo, 250); }
['esquema','doc'].forEach(id => $(id).addEventListener('input', alEscribir));
['tipo','parar','prof'].forEach(id => $(id).addEventListener('change', alEscribir));
$('bvalidar').onclick = () => { vivo(); dibujar(); };

/* ---------- ejemplos, archivos y pestanas ---------- */
function cargarEjemplo(){ const k = $('ejemplo').value; if (!k) return; const [t, e, d] = EJ[k]; $('tipo').value = t; $('esquema').value = e; $('doc').value = d; vivo(); dibujar(); }
$('ejemplo').onchange = cargarEjemplo;
function leerArchivo(inp, dest){ $(inp).onchange = () => { const f = $(inp).files[0]; if (!f) return; const r = new FileReader();
  r.onload = () => { $(dest).value = r.result; const n = f.name.toLowerCase();
    if (dest === 'esquema') $('tipo').value = n.endsWith('.dtd') ? 'dtd' : n.endsWith('.xsd') ? 'xsd' : 'json'; vivo(); }; r.readAsText(f); }; }
leerArchivo('fesq', 'esquema'); leerArchivo('fdoc', 'doc');
document.querySelectorAll('textarea').forEach(t => t.addEventListener('keydown', e => {
  if (e.key === 'Tab') { e.preventDefault(); t.setRangeText('  ', t.selectionStart, t.selectionEnd, 'end'); }
  if (e.ctrlKey && e.key === 'Enter') { vivo(); dibujar(); } }));
document.querySelectorAll('#nav button').forEach(b => b.onclick = () => {
  document.querySelectorAll('#nav button, section').forEach(x => x.classList.remove('act'));
  b.classList.add('act'); $(b.dataset.t).classList.add('act');
  if (b.dataset.t === 'tcasos' && !CASOS.length) cargarCasos();
  if (b.dataset.t === 'tcomp') pintarBanco(); });

/* ---------- automata y arbol (fases 1 a 4) ---------- */
async function dibujar(){
  $('evisor').textContent = 'dibujando...';
  try { const r = await fetch('/api/visor', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify(cuerpo())});
    $('visor').srcdoc = await r.text(); $('evisor').textContent = ''; }
  catch (e) { $('evisor').textContent = 'error: ' + e.message; }
}
$('bvisor').onclick = dibujar;

/* ---------- compilar y descargar ---------- */
$('bcompilar').onclick = async () => {
  $('bcompilar').disabled = true; $('ecompilar').textContent = 'compilando en la caja de arena...';
  try {
    const t = await json('/api/compilar', {tipo: $('tipo').value, esquema: $('esquema').value});
    if (!t.ok) { $('rcompilar').innerHTML = '<p class="no">El esquema tiene errores</p><pre>' + esc(t.errores.join('\n')) + '</pre>'; return; }
    let h = '<table><tr><th>estados</th><th>transiciones</th><th>simbolos de entrada</th><th>simbolos de pila</th><th>automata (ms)</th><th>C y Rust (ms)</th></tr><tr><td>' +
      [t.tamano.estados, t.tamano.transiciones, t.tamano.simbolos_entrada, t.tamano.simbolos_pila, t.ms_automata, t.ms_nativos == null ? '-' : t.ms_nativos].join('</td><td>') + '</td></tr></table>';
    h += '<table><tr><th>motor</th><th class="t">estado</th></tr>' + Object.entries(t.nativos).map(([k, v]) =>
      '<tr><td>' + esc(k) + '</td><td class="t ' + (v === 'compilado' ? 'si' : '') + '">' + esc(v) + '</td></tr>').join('') + '</table>';
    if (t.archivos.length) h += '<p>Descargar: ' + t.archivos.concat(['codigo.zip']).map(a => '<a class="chip" href="/api/descargar/' + t.id + '/' + a + '">' + a + '</a>').join(' ') +
      ' <button id="bverc">ver validador.c</button> <button id="bverrs">ver validador.rs</button></p><pre id="codigo" style="display:none"></pre>';
    if (t.avisos.length) h += '<p><b>Avisos de la Fase 3</b></p><ul>' + t.avisos.map(a => '<li><span class="chip">' + esc(a.nivel) + '</span> <code>' + esc(a.ruta) + '</code> ' + esc(a.mensaje) + '</li>').join('') + '</ul>';
    h += '<p><b>Definicion formal</b></p><pre>' + esc(t.definicion) + '</pre>';
    $('rcompilar').innerHTML = h;
    const ver = a => async () => { const x = await (await fetch('/api/descargar/' + t.id + '/' + a)).text(); $('codigo').style.display = 'block'; $('codigo').textContent = x.slice(0, 6000) + '\n... (' + x.length + ' caracteres en total; descarga el archivo para verlo completo)'; };
    if ($('bverc')) { $('bverc').onclick = ver('validador.c'); $('bverrs').onclick = ver('validador.rs'); }
  } catch (e) { $('rcompilar').innerHTML = '<p class="no">' + esc(e.message) + '</p>'; }
  finally { $('bcompilar').disabled = false; $('ecompilar').textContent = ''; }
};
$('bpayloads').onclick = async () => {
  try {
    const p = await json('/api/payloads', {tipo: $('tipo').value, esquema: $('esquema').value, n: 3, semilla: Math.floor(Math.random() * 1e6)});
    const fila = (clase, motivo, doc) => '<tr class="doc" data-doc="' + esc(doc) + '"><td class="' + clase + '">' + esc(motivo) + '</td><td class="t"><code>' + esc(doc.length > 160 ? doc.slice(0, 160) + '...' : doc) + '</code></td></tr>';
    $('rpayloads').innerHTML = '<table><tr><th>que es</th><th class="t">documento</th></tr>' + p.validos.map(d => fila('si', 'valido', d)).join('') +
      p.invalidos.map(x => fila('no', 'invalido: ' + x.motivo, x.doc)).join('') + p.malformados.map(x => fila('no', 'mal formado: ' + x.motivo, x.doc)).join('') + '</table>';
    document.querySelectorAll('#rpayloads tr.doc').forEach(tr => tr.onclick = () => { $('doc').value = tr.dataset.doc; vivo(); window.scrollTo(0, 0); });
  } catch (e) { $('rpayloads').innerHTML = '<p class="no">' + esc(e.message) + '</p>'; }
};

/* ---------- streaming por bloques ---------- */
function pintarPila(alt, tope){
  const w = 800, h = 170, m = Math.max(4, ...alt), n = Math.max(1, alt.length - 1);
  const x = i => 40 + i * (w - 55) / n, y = v => h - 22 - v * (h - 40) / m;
  let s = '<text x="40" y="13" font-size="11" fill="#5b6470">altura de la pila despues de cada bloque</text>';
  for (let v = 0; v <= m; v += Math.max(1, Math.ceil(m / 5))) s += '<line x1="40" x2="' + (w - 15) + '" y1="' + y(v) + '" y2="' + y(v) + '" stroke="#e3e6ea"/><text x="34" y="' + (y(v) + 4) + '" font-size="10" text-anchor="end" fill="#5b6470">' + v + '</text>';
  if (tope) s += '<line x1="40" x2="' + (w - 15) + '" y1="' + y(Math.min(tope, m)) + '" y2="' + y(Math.min(tope, m)) + '" stroke="#b3261e" stroke-dasharray="5 4"/>';
  s += '<polyline fill="none" stroke="#2a78d6" stroke-width="2" points="' + alt.map((v, i) => x(i).toFixed(1) + ',' + y(v).toFixed(1)).join(' ') + '"/>';
  $('spila').innerHTML = s;
}
$('bflujo').onclick = async () => {
  const b = $('bflujo'); b.disabled = true; $('serr').innerHTML = ''; $('serr').className = '';
  try {
    const c = cuerpo(), datos = enc.encode(c.documento); let tam = Math.max(1, num('sbloque') || 8);
    if (datos.length / tam > 2000) tam = Math.ceil(datos.length / 2000);
    const pausa = num('spausa') || 0, s = await conectar(), alt = [1]; let errs = [];
    s.send(JSON.stringify({accion:'iniciar', n:1, tipo:c.tipo, esquema:c.esquema, parar:c.parar, profundidad:num('sprof'), max_bytes:num('sbytes'), max_ms:num('sms')}));
    let m = await s.siguiente();
    if (m.evento !== 'listo') { pintarVeredicto(m, 'serr'); s.close(); return; }
    const total = Math.ceil(datos.length / tam);
    for (let i = 0, k = 1; i < datos.length; i += tam, k++) {
      s.send(datos.slice(i, i + tam)); m = await s.siguiente();
      if (m.evento !== 'estado') break;
      alt.push(m.pila); errs = errs.concat(m.errores); pintarPila(alt, num('sprof'));
      $('sestado').innerHTML = 'bloque ' + k + ' de ' + total + ' (' + tam + ' bytes c/u) &middot; ' + m.bytes + ' de ' + datos.length + ' bytes &middot; estado <code>' + esc(m.estado) +
        '</code> &middot; pila ' + m.pila + ' (max ' + m.pila_max + ') &middot; violaciones ' + m.violaciones;
      if (datos.length <= 20000) $('sdoc').innerHTML = '<span class="hecho">' + esc(dec.decode(datos.slice(0, m.bytes))) + '</span><span class="falta">' + esc(dec.decode(datos.slice(m.bytes))) + '</span>';
      if (errs.length) $('serr').innerHTML = '<b class="no">Errores detectados hasta ahora (sin esperar al final)</b>' + errores(errs);
      if (m.terminado) break;
      if (pausa) await dormir(pausa);
    }
    s.send(JSON.stringify({accion:'fin', n:1})); m = await s.siguiente();
    if (m.evento === 'veredicto') pintarVeredicto(m, 'serr');
    s.close();
  } catch (e) { $('serr').innerHTML = '<p class="no">' + esc(e.message) + '</p>'; }
  finally { b.disabled = false; }
};

/* ---------- comparacion en vivo ---------- */
const COLOR = {'dpda-python':'#2a78d6', 'dpda-c':'#1baa6b', 'dpda-rust':'#e07b1a', 'dom':'#8a8f98'};
const NOMBRE = {'dpda-python':'DPDA en Python', 'dpda-c':'DPDA en C (generado)', 'dpda-rust':'DPDA en Rust (generado)', 'dom':'Linea base: DOM + validador generico'};
function fmt(v){ return v == null ? '-' : typeof v === 'number' ? v.toLocaleString('es-CO', {maximumFractionDigits: 2}) : esc(v); }
function tablaFilas(filas){
  const mx = Math.max(...filas.map(f => f.mb_s || 0)), mm = Math.max(...filas.map(f => f.mem_pico || 0));
  const barra = (v, m, col) => v ? '<span class="barraH" style="background:' + col + ';width:' + Math.max(2, 120 * Math.log10(1 + 99 * v / m) / 2).toFixed(0) + 'px"></span> ' : '';
  return '<table><tr><th>motor</th><th>veredicto</th><th>MB/s</th><th>ciclos por byte</th><th>pico de memoria (bytes)</th><th>asignaciones</th><th>pila</th><th>estados</th><th>transiciones</th><th>ms</th></tr>' +
    filas.map(f => '<tr><td><b style="color:' + COLOR[f.motor] + '">' + NOMBRE[f.motor] + '</b></td><td class="' + (f.valido ? 'si">valido' : 'no">' + (f.fallo ? 'FALLO: ' + esc(f.fallo) : f.mal_formado ? 'mal formado' : 'invalido')) + '</td><td>' +
      barra(f.mb_s, mx, COLOR[f.motor]) + fmt(f.mb_s) + '</td><td>' + fmt(f.ciclos_byte) + '</td><td>' + barra(f.mem_pico, mm, COLOR[f.motor]) + fmt(f.mem_pico) + '</td><td>' + fmt(f.asignaciones) + '</td><td>' +
      fmt(f.pila_max) + '</td><td>' + fmt(f.estados) + '</td><td>' + fmt(f.transiciones) + '</td><td>' + fmt(f.ms) + '</td></tr>').join('') + '</table>';
}
let comparando = false;
async function comparar(){
  if (comparando) return; comparando = true; $('bcomp').disabled = true; $('ecomp').textContent = 'midiendo...';
  try {
    const c = cuerpo(), s = await conectar(), filas = []; let info = '';
    s.send(JSON.stringify({accion:'comparar', tipo:c.tipo, esquema:c.esquema, documento:c.documento, profundidad:c.profundidad, caso: $('cfuente').value || null}));
    for (;;) { const m = await s.siguiente();
      if (m.evento === 'comparando') info = '<p class="ay">Documento de ' + fmt(m.bytes) + ' bytes. ' + Object.entries(m.nativos).filter(([k, v]) => v !== 'compilado').map(([k, v]) => esc(k) + ': ' + esc(v)).join(' &middot; ') + '</p>';
      else if (m.evento === 'fila') { filas.push(m); $('rcomp').innerHTML = info + tablaFilas(filas) + '<p class="ay">' + filas.filter(f => f.nota).map(f => '<b>' + f.motor + '</b>: ' + esc(f.nota)).join('<br>') + '</p>'; }
      else { if (m.evento === 'error_esquema' || m.evento === 'error') $('rcomp').innerHTML = '<p class="no">' + esc((m.errores || [m.mensaje]).join('; ')) + '</p>'; break; } }
    s.close(); $('ecomp').textContent = 'medido a las ' + new Date().toLocaleTimeString();
  } catch (e) { $('ecomp').textContent = 'error: ' + e.message; }
  finally { comparando = false; $('bcomp').disabled = false; if ($('crepetir').checked && $('tcomp').classList.contains('act')) setTimeout(comparar, 3000); }
}
$('bcomp').onclick = comparar; $('crepetir').onchange = () => { if ($('crepetir').checked) comparar(); };
async function pintarBanco(){
  const m = await json('/api/metricas').catch(() => ({}));
  if (!m.tamano) { $('rbanco').innerHTML = '<p class="ay">Todavia no hay mediciones guardadas. Corre el banco corto o: <code>python tiempo_real_v1.py banco</code></p>'; return; }
  let h = '<img src="/api/metricas.svg?' + Date.now() + '" style="width:100%;max-width:900px;border:1px solid #cfd6de;border-radius:6px" alt="graficas del banco">';
  h += '<p class="ay">Medido el ' + esc(m.fecha) + '. Documento mas grande de la serie:</p>' + tablaFilas(m.tamano[m.tamano.length - 1].filas);
  const b = m.bombeo[m.bombeo.length - 1]; h += '<p class="ay">Bombeo con k = ' + b.k + ' (' + fmt(b.bytes) + ' bytes):</p>' + tablaFilas(b.filas);
  $('rbanco').innerHTML = h;
}
$('bbanco').onclick = async () => { $('bbanco').disabled = true; $('ebanco').textContent = 'corriendo (unos 15 segundos)...';
  try { await json('/api/banco', {}); await pintarBanco(); $('ebanco').textContent = ''; } catch (e) { $('ebanco').textContent = 'error: ' + e.message; } finally { $('bbanco').disabled = false; } };

/* ---------- casos de prueba ---------- */
function pintarCasos(){
  const lista = CASOS.filter(c => !catActual || c.categoria === catActual);
  $('rcasos').innerHTML = '<table><tr><th>id</th><th class="t">categoria</th><th class="t">subcategoria</th><th class="t">formato</th><th class="t">esperado</th><th class="t">nota</th><th></th></tr>' +
    lista.map(c => '<tr><td>' + c._id + '</td><td class="t">' + c.categoria + '</td><td class="t">' + esc(c.sub) + '</td><td class="t">' + c.formato + '</td><td class="t">' + c.esperado + '</td><td class="t">' + esc(c.nota) +
      '</td><td><button data-id="' + c._id + '" class="bc">cargar</button> <button data-id="' + c._id + '" class="br">correr</button> <span id="v' + c._id + '"></span></td></tr>').join('') + '</table>';
  document.querySelectorAll('.bc').forEach(b => b.onclick = async () => { const c = await json('/api/casos/' + b.dataset.id);
    $('tipo').value = c.tipo; $('esquema').value = c.esquema; $('prof').value = (c.limites && c.limites.max_prof) || '';
    $('doc').value = c.grande ? '' : c.payload; window.scrollTo(0, 0);
    if (c.grande) { $('pildora').className = ''; $('pildora').textContent = 'El payload de ' + c._id + ' pesa ' + c.bytes + ' bytes: no se trae al editor. Usa "correr" o eligelo en Comparacion en vivo.'; } else vivo(); });
  document.querySelectorAll('.br').forEach(b => b.onclick = async () => { const d = $('v' + b.dataset.id); d.textContent = '...';
    try { const r = await json('/api/casos/correr', {id: b.dataset.id});
      d.innerHTML = Object.entries(r.veredictos).map(([k, v]) => '<span class="chip">' + esc(k) + ': ' + esc(v) + '</span>').join('') + (r.fallas.length ? ' <b class="no">FALLA</b>' : ' <b class="si">como se esperaba</b>'); }
    catch (e) { d.textContent = e.message; } });
}
async function cargarCasos(){
  CASOS = await json('/api/casos');
  const cats = [...new Set(CASOS.map(c => c.categoria))];
  $('cfiltros').innerHTML = ['', ...cats].map(c => '<button data-c="' + c + '">' + (c || 'todos') + ' (' + CASOS.filter(x => !c || x.categoria === c).length + ')</button>').join('');
  document.querySelectorAll('#cfiltros button').forEach(b => b.onclick = () => { catActual = b.dataset.c; pintarCasos(); });
  $('cfuente').innerHTML = '<option value="">el del editor</option>' + CASOS.filter(c => c.categoria === 'bombeo' || c.categoria === 'extremos').filter(c => c.formato === 'json')
    .map(c => '<option value="' + c._id + '">' + c._id + ' &middot; ' + esc(c.sub) + ' &middot; ' + esc(c.nota) + '</option>').join('');
  pintarCasos();
}
$('bsuite').onclick = async () => { $('bsuite').disabled = true; $('esuite').textContent = 'corriendo en todos los motores (unos 20 segundos)...';
  try { const r = await json('/api/casos/correr', {categoria: catActual});
    $('rsuite').innerHTML = '<table><tr><th>categoria</th><th>casos</th><th>pasaron</th><th class="t">subcategorias</th></tr>' + r.resumen.map(x => '<tr><td>' + x.categoria + '</td><td>' + x.casos + '</td><td class="' + (x.casos === x.pasaron ? 'si' : 'no') + '">' + x.pasaron +
      '</td><td class="t">' + esc(x.subs.join(', ')) + '</td></tr>').join('') + '</table>' + r.fallas.map(f => '<p class="no">' + f.id + ' (' + esc(f.sub) + '): ' + esc(f.detalle.join('; ')) + '</p>').join('');
    $('esuite').textContent = 'listo en ' + r.segundos + ' s'; }
  catch (e) { $('esuite').textContent = 'error: ' + e.message; } finally { $('bsuite').disabled = false; } };

/* ---------- arranque ---------- */
json('/api/ejemplos').then(d => { EJ = d; Object.keys(d).forEach(k => { const o = document.createElement('option'); o.value = k; o.textContent = k; $('ejemplo').appendChild(o); });
  $('ejemplo').value = Object.keys(d)[1]; cargarEjemplo(); });
cargarCasos().catch(() => {});
</script></body></html>"""


if __name__ == "__main__":
    puerto = next((int(x) for x in sys.argv[1:] if x.isdigit()), 8000)
    url = f"http://localhost:{puerto}"
    print(f"  Validador corriendo en {url}   (Ctrl+C para salir)")
    faltan = [x for x in ("c", "rust") if not G.hay(x)]
    if faltan:
        print("  Aviso: no hay compilador de " + " ni de ".join(faltan) + ". El codigo se genera y se descarga,\n"
              "         pero ese motor no aparece en la comparacion.")
    if "--sin-navegador" not in sys.argv:
        try:
            webbrowser.open(url)
        except Exception:
            pass
    try:
        uvicorn.run(app, host="127.0.0.0", port=puerto, log_level="warning")
    finally:
        shutil.rmtree(CAJA, ignore_errors=True)

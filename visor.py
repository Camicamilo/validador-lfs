r"""
visor.py - Visor grafico de las fases 1 a 4 (un archivo HTML, sin internet)

Para JSON Schema y para XML con DTD o XSD muestra:
  Fase 1  la cinta de tokens (tipo, linea y columna de cada uno)
  Fase 2  el arbol de derivacion (JSON) o el arbol del documento (XML)
  Fase 3  JSON: semaforo de palabras clave.  XML: cada elemento con su ER y
          su AFD minimo dibujado.
  Fase 4  definicion formal M, tabla delta y REPRODUCTOR paso a paso: token
          actual, fila usada, estado resaltado, pila dibujada, costo y violaciones.

Uso:
  python visor.py ESQUEMA.json DOC.json [-o visor.html]
  python visor.py --dtd ESQUEMA.dtd DOC.xml [-o visor.html]
  python visor.py --xsd ESQUEMA.xsd DOC.xml [-o visor.html]
Lo usa tambien app.py (la aplicacion local con editores).
"""
import sys
import json
import html
import shutil
import subprocess
from lexer_v4 import tokenizar, ErrorLexico
from parser_v2 import parsear_texto, simplificar, ErrorSintactico, GRAMATICA
from semantico_v1 import analizar, CLAVES
import automata_v2 as A
import xml_v1 as X

e = html.escape
COLOR_TOKEN = {"LLAVE_ABRE": "#5c6bc0", "LLAVE_CIERRA": "#5c6bc0", "CORCHETE_ABRE": "#00897b",
               "CORCHETE_CIERRA": "#00897b", "DOS_PUNTOS": "#757575", "COMA": "#757575",
               "CADENA": "#c62828", "NUMERO": "#ef6c00", "LITERAL": "#6a1b9a",
               "ETIQUETA_ABRE": "#1565c0", "ETIQUETA_CIERRA": "#1565c0", "ETIQUETA_VACIA": "#00838f",
               "TEXTO": "#5d4037", "DECLARACION": "#757575", "COMENTARIO": "#9e9e9e"}


# ------------------------------------------------------------------ utilidades
def svg_de(dot_texto):
    if not shutil.which("dot"):
        return (f"<pre class='dot'>{e(dot_texto)}</pre>"
                "<p>(instala Graphviz, comando <code>dot</code>, para ver el dibujo)</p>")
    s = subprocess.run(["dot", "-Tsvg"], input=dot_texto.encode(), capture_output=True).stdout.decode()
    return s[s.index("<svg"):] if "<svg" in s else f"<pre>{e(dot_texto)}</pre>"


def _lbl(t):
    return t.replace("\\", "\\\\").replace('"', '\\"')


def cinta(tokens):
    partes = []
    for t in tokens:
        if t.tipo == "TEXTO" and not t.texto.strip():
            continue
        c = COLOR_TOKEN.get(t.tipo, "#999")
        txt = t.texto if len(t.texto) <= 28 else t.texto[:25] + "..."
        partes.append(f"<span class='tok' data-pos='{t.linea}:{t.columna}' style='border-color:{c}'>"
                      f"<b style='color:{c}'>{e(txt)}</b><small>{t.tipo}<br>{t.linea}:{t.columna}</small></span>")
    return "".join(partes)


def veredicto(r):
    if r is None:
        return ""
    if r.valido:
        return (f"<div class='ok'><b>VALIDO</b> &mdash; costo {r.costo}, {r.pasos} pasos, "
                f"pila maxima {r.prof_max}</div>")
    errs = "".join(f"<li><code>{e(x['ruta'])}</code> {e(x['mensaje'])}"
                   + (f" <small>(linea {x['linea']}, col {x['columna']}"
                      + (f", byte {x['byte']}" if x.get("byte") is not None else "") + ")</small>" if x.get("linea") else "")
                   + "</li>" for x in r.errores)
    titulo = "LIMITE SUPERADO" if getattr(r, "limite", None) else "MAL FORMADO" if r.mal_formado else "INVALIDO"
    return (f"<div class='mal'><b>{titulo}</b> &mdash; "
            f"{r.violaciones} violacion(es), costo {r.costo}<ul>{errs}</ul></div>")


def tabla_delta(filas, tope_primero=False):
    clave = (lambda f: (f["tope"], f["de"], f["a"])) if tope_primero else (lambda f: (f["de"], f["a"], f["tope"]))
    cuerpo = "".join(
        f"<tr class='{'chk' if f['guardas'] else ''}' data-k='{e(f['de'])}|{e(f['a'])}|{e(f['tope'])}'>"
        f"<td>{e(f['de'])}</td><td>{e(f['a'])}</td><td>{e(f['tope'])}</td><td>{e(f['a_estado'])}</td>"
        f"<td>{e(f['pila'])}</td><td>{f['costo']}</td>"
        f"<td>{e(', '.join(g[0] for g in f['guardas']))}"
        f"{e(' [' + f['registro'] + ']') if f.get('registro') else ''}</td>"
        f"<td class='nota'>{e(f['nota'])}</td></tr>" for f in sorted(filas, key=clave))
    return (f"<h3>Tabla &delta; ({len(filas)} filas)</h3><div class='scroll'><table class='delta'>"
            "<tr><th>estado</th><th>lee</th><th>tope</th><th>va a</th><th>pila</th><th>w</th>"
            f"<th>comprobaciones</th><th>nota</th></tr>{cuerpo}</table></div>")


def reproductor(cinta_html, diagrama_html, ayuda):
    return f"""<h3>Reproductor paso a paso</h3>
<div class='cinta mini'>{cinta_html}</div>
<div class='controles'>
  <button onclick='ir(0)' title='inicio'>&#9198;</button><button onclick='ir(paso-1)' title='atras'>&#9664;</button>
  <button id='play' onclick='reproducir()'>&#9654; reproducir</button>
  <button onclick='ir(paso+1)' title='adelante'>&#9654;</button><button onclick='ir(T.length)' title='final'>&#9197;</button>
  <label>velocidad <input type='range' min='100' max='1500' value='700' id='vel'></label>
  <span id='cont'></span>
</div>
<div class='rep'>
  <div class='panel'><h4>Pila</h4><div id='pila'></div></div>
  <div class='panel ancho'><h4>Paso actual</h4><div id='actual'></div>
     <h4>Violaciones hasta aqui</h4><ul id='viol'></ul></div>
</div>
<div class='diagrama' id='diag'>{diagrama_html}</div>
<p class='ayuda'>{ayuda}</p>"""


CSS = """
body{font-family:Helvetica,Arial,sans-serif;margin:0;color:#222;background:#fafafa}
header{background:#1f3b5b;color:white;padding:12px 22px} header h1{margin:0;font-size:19px}
nav{display:flex;gap:4px;padding:8px 22px;background:#e8edf3;position:sticky;top:0;z-index:5;flex-wrap:wrap}
nav button{border:0;padding:8px 14px;border-radius:6px;background:#fff;cursor:pointer;font-size:14px}
nav button.activo{background:#1f3b5b;color:white}
section{display:none;padding:8px 22px 40px} section.activo{display:block}
pre{background:#fff;border:1px solid #ddd;padding:10px;overflow:auto;font-size:13px}
.entrada{display:flex;gap:12px} .entrada>div{flex:1;min-width:0} .entrada pre{white-space:pre-wrap;word-break:break-all}
.tok{display:inline-flex;flex-direction:column;align-items:center;border:2px solid;border-radius:6px;
  margin:3px;padding:3px 7px;background:white;min-width:22px;transition:transform .15s}
.tok b{font-family:monospace;font-size:14px;white-space:pre} .tok small{font-size:9px;color:#777;text-align:center}
.tok.ahora{background:#fff59d;transform:scale(1.12)} .tok.leido{opacity:.4}
table{border-collapse:collapse;background:white;font-size:13px} td,th{border:1px solid #ddd;padding:4px 8px;vertical-align:top}
th{background:#eef3fb} .delta tr.chk td{color:#b71c1c} .delta tr.ahora td{background:#fff59d} .nota{color:#666}
.scroll{max-height:420px;overflow:auto;border:1px solid #ddd}
.luz{display:inline-block;width:12px;height:12px;border-radius:50%;margin-right:6px;vertical-align:middle}
.luz.verde{background:#2e7d32} .luz.amarillo{background:#f9a825} .luz.rojo{background:#c62828} .luz.desconocida{background:#9e9e9e}
li.ERROR,li.SEGURIDAD{color:#b71c1c} li.FUERA{color:#c62828} li.AVISO{color:#8d6e00}
.ok{background:#e8f5e9;border-left:5px solid #2e7d32;padding:10px;margin:10px 0}
.mal{background:#ffebee;border-left:5px solid #c62828;padding:10px;margin:10px 0}
.diagrama{background:white;border:1px solid #ddd;overflow:auto;padding:6px} .diagrama svg{max-width:100%;height:auto}
.controles{margin:8px 0} .controles button{font-size:15px;padding:5px 11px;margin-right:3px} #cont{margin-left:10px;color:#555}
.rep{display:flex;gap:14px;margin:10px 0} .panel{background:white;border:1px solid #ddd;padding:8px 12px;min-width:160px}
.panel.ancho{flex:1} h4{margin:4px 0 8px}
#pila{display:flex;flex-direction:column-reverse;gap:3px;min-height:60px;max-height:320px;overflow:auto}
.marco{border:2px solid #4a6fa5;background:#eef3fb;padding:4px 10px;font-family:monospace;text-align:center;border-radius:4px}
.marco.tope{background:#fff59d} .marco.z0{border-color:#999;background:#eee}
.ayuda{font-size:12px;color:#555} code{background:#f1f1f1;padding:1px 4px;border-radius:3px}
g.node.ahora ellipse, g.node.ahora polygon, g.node.ahora path{fill:#fff59d !important;stroke:#f57f17 !important;stroke-width:3px}
.afds{display:flex;flex-wrap:wrap;gap:10px} .afd{background:white;border:1px solid #ddd;padding:6px;max-width:100%}
.afd.oculto{display:none} .afd h5{margin:2px 0 4px;font-size:13px}
"""

JS = r"""
let paso = 0, timer = null;
function tab(i){document.querySelectorAll('section').forEach((s,j)=>s.classList.toggle('activo',i===j));
  document.querySelectorAll('nav button').forEach((b,j)=>b.classList.toggle('activo',i===j));}
function esc(s){return String(s).replace(/[&<>]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;'})[c]);}
function marcarSvg(raiz, nombre){ if(!raiz) return; raiz.querySelectorAll('g.node').forEach(g=>{
  const t=g.querySelector('title'); const n=t?t.textContent:'';
  g.classList.toggle('ahora', n===nombre || (nombre && nombre.includes('*') && n==='JSON*'));});}
function ir(n){ if(!T.length) return; paso=Math.max(0,Math.min(T.length,n));
  const p = paso>0 ? T[paso-1] : null;
  const q = p ? p.a : INICIO;
  const pila = p ? p.pila_despues : ['Z0'];
  if (MODO==='json') marcarSvg(document.getElementById('diag'), q);
  else { // XML: mostrar el AFD del elemento del tope y su estado
    const tope = pila[pila.length-1]; const [el, s] = tope.includes('@') ? tope.split('@') : [null,null];
    let hay = false;
    document.querySelectorAll('#diag .afd').forEach(d=>{ const es = d.dataset.el===el;
       d.classList.toggle('oculto', !es); if(es){ hay = true; marcarSvg(d, s);} });
    document.getElementById('sinafd').style.display = hay ? 'none':'block';
  }
  document.getElementById('pila').innerHTML = pila.map((s,i)=>`<div class="marco ${i===pila.length-1?'tope':''} ${s==='Z0'?'z0':''}">${esc(s)}</div>`).join('');
  document.getElementById('cont').textContent = `paso ${paso} de ${T.length}`;
  document.getElementById('actual').innerHTML = p ?
    `<b>leyo:</b> <code>${esc(p.token)}</code> &rarr; simbolo <code>${esc(p.simbolo)}</code><br>
     <b>fila:</b> <code>${esc(p.fila)}</code><br><b>estado:</b> ${esc(p.de)} &rarr; <b>${esc(p.a)}</b><br>
     <b>peso de la fila:</b> ${p.costo} &nbsp; <b>costo acumulado:</b> ${p.costo_acum}<br><i>${esc(p.nota)}</i>` :
    `estado inicial <b>${esc(INICIO)}</b>, pila con Z0. Dale &#9654;`;
  document.getElementById('viol').innerHTML = T.slice(0,paso).flatMap(x=>x.violaciones.map(v=>`<li>paso ${x.paso}: ${esc(v)}</li>`)).join('') || '<li>ninguna</li>';
  document.querySelectorAll('.delta tr').forEach(tr=>tr.classList.remove('ahora'));
  if(p){ const tr=document.querySelector(`.delta tr[data-k="${CSS.escape(p.k.join('|'))}"]`); if(tr) tr.classList.add('ahora');}
  const pos = p && p.linea ? `${p.linea}:${p.columna}` : null;
  const toks = [...document.querySelectorAll('.mini .tok')];
  const i = toks.findIndex(t=>t.dataset.pos===pos);
  toks.forEach((t,j)=>{ t.classList.toggle('ahora', j===i); t.classList.toggle('leido', i>=0 && j<i); });
}
function reproducir(){ if(timer){clearTimeout(timer);timer=null;document.getElementById('play').innerHTML='&#9654; reproducir';return;}
  if(paso>=T.length) ir(0);
  document.getElementById('play').innerHTML='&#10074;&#10074; pausa';
  const tick=()=>{ if(paso>=T.length){timer=null;document.getElementById('play').innerHTML='&#9654; reproducir';return;}
     ir(paso+1); timer=setTimeout(tick, 1600 - (+document.getElementById('vel').value)); };
  tick();}
if (document.getElementById('pila')) ir(0);
"""


def pagina(titulo, subtitulo, pestanas, modo, traza, inicio):
    nav = "".join(f"<button onclick='tab({i})' class='{'activo' if i == 0 else ''}'>{e(t)}</button>"
                  for i, (t, _) in enumerate(pestanas))
    secs = "".join(f"<section class='{'activo' if i == 0 else ''}'>{c}</section>"
                   for i, (_, c) in enumerate(pestanas))
    return (f"<!DOCTYPE html><html lang='es'><head><meta charset='utf-8'><title>{e(titulo)}</title>"
            f"<style>{CSS}</style></head><body><header><h1>{e(titulo)}</h1><div>{e(subtitulo)}</div></header>"
            f"<nav>{nav}</nav>{secs}<script>const T={json.dumps(traza or [])};"
            f"const INICIO={json.dumps(inicio)};const MODO={json.dumps(modo)};{JS}</script></body></html>")


# ------------------------------------------------------------------ JSON
def dot_arbol(raiz, max_nodos=400):
    l = ['digraph arbol {', '  node [fontname="Helvetica", fontsize=10, shape=box, style="rounded,filled", fillcolor="#eef3fb"];',
         '  edge [arrowsize=0.5, color="#90a4ae"];']
    ids, pila, n = {}, [raiz], 0
    while pila and n < max_nodos:
        nodo = pila.pop()
        ids[id(nodo)] = f"n{n}"
        n += 1
        if nodo.token is not None:
            l.append(f'  {ids[id(nodo)]} [label="{nodo.simbolo}\\n{_lbl(nodo.token.texto[:30])}", fillcolor="#fde7d9"];')
        elif nodo.simbolo in GRAMATICA and not nodo.hijos:
            l.append(f'  {ids[id(nodo)]} [label="{nodo.simbolo}\\nε", fillcolor="#f2f2f2", fontcolor="#777777"];')
        else:
            l.append(f'  {ids[id(nodo)]} [label="{nodo.simbolo}"];')
        pila.extend(reversed(nodo.hijos))
    pila = [raiz]
    while pila:
        nodo = pila.pop()
        for h in nodo.hijos:
            if id(nodo) in ids and id(h) in ids:
                l.append(f"  {ids[id(nodo)]} -> {ids[id(h)]};")
        pila.extend(nodo.hijos)
    if n >= max_nodos:
        l.append('  corte [label="... (arbol recortado)", shape=plaintext];')
    l.append("}")
    return "\n".join(l)


def semaforo(esquema):
    filas, pila = [], [(esquema, "")]
    while pila:
        nodo, ruta = pila.pop()
        if not isinstance(nodo, dict):
            continue
        for k, v in nodo.items():
            filas.append((ruta or "/", k, CLAVES.get(k, "desconocida")))
            if k in ("properties", "$defs", "definitions") and isinstance(v, dict):
                for nombre, sub in v.items():
                    pila.append((sub, f"{ruta}/{k}/{nombre}"))
            elif k in ("items", "additionalProperties") and isinstance(v, dict):
                pila.append((v, f"{ruta}/{k}"))
            elif k in ("anyOf", "oneOf", "allOf") and isinstance(v, list):
                for i, sub in enumerate(v):
                    pila.append((sub, f"{ruta}/{k}/{i}"))
    return filas


def entrada(nombre_esq, texto_esquema, texto_doc, r):
    return (f"<h2>Entrada</h2><div class='entrada'><div><h3>{e(nombre_esq)}</h3><pre>{e(texto_esquema)}</pre></div>"
            f"<div><h3>Documento</h3><pre>{e(texto_doc)}</pre></div></div>"
            + (f"<h3>Resultado</h3>{veredicto(r)}<p class='ayuda'>Mira cada fase en las pestanas. "
               "En la Fase 4 esta el reproductor paso a paso.</p>" if r else ""))


def generar(texto_esquema, texto_doc, parar_en_primero=False, max_profundidad=None):
    """Visor para JSON Schema."""
    try:
        tokens, err_lex = tokenizar(texto_doc), None
    except ErrorLexico as ex:
        tokens, err_lex = [], str(ex)
    conteo = {}
    for t in tokens:
        conteo[t.tipo] = conteo.get(t.tipo, 0) + 1
    f1 = (f"<h2>Fase 1 &middot; Analisis lexico</h2><p>El lexer lee <b>bytes</b>; con los AFD de numeros, "
          "cadenas y literales arma los tokens. Los espacios no son tokens.</p>"
          + (f"<div class='mal'>{e(err_lex)}</div>" if err_lex else "")
          + f"<div class='cinta'>{cinta(tokens)}</div><p>{len(tokens)} tokens: "
          + e(", ".join(f"{k} x{v}" for k, v in conteo.items())) + "</p>")
    try:
        arbol = parsear_texto(texto_doc)
        f2 = ("<h2>Fase 2 &middot; Analisis sintactico LL(1)</h2><p>Arbol de derivacion del documento. "
              "Las hojas son tokens; &epsilon; marca las reglas vacias.</p>"
              f"<div class='diagrama'>{svg_de(dot_arbol(arbol))}</div>")
    except (ErrorSintactico, ErrorLexico) as ex:
        f2 = f"<h2>Fase 2 &middot; Analisis sintactico LL(1)</h2><div class='mal'>{e(str(ex))}</div>"
    r, traza, inicio = None, [], None
    try:
        esquema = simplificar(parsear_texto(texto_esquema))
    except (ErrorSintactico, ErrorLexico) as ex:
        error = f"<div class='mal'>El esquema no es JSON valido: {e(str(ex))}</div>"
        return pagina("Visor del validador", "JSON Schema",
                      [("Entrada", entrada("Esquema", texto_esquema, texto_doc, None) + error)], "json", [], None)
    errores3, avisos3, _ = analizar(esquema)
    filas_sem = "".join(f"<tr><td><code>{e(ru)}</code></td><td><code>{e(k)}</code></td>"
                        f"<td><span class='luz {c}'></span>{c}</td></tr>" for ru, k, c in semaforo(esquema))
    hall = "".join(f"<li class='{h.nivel}'><b>{h.nivel}</b> <code>{e(h.ruta or '/')}</code> {e(h.mensaje)}</li>"
                   for h in errores3 + avisos3) or "<li>Sin hallazgos: el esquema tiene sentido.</li>"
    f3 = ("<h2>Fase 3 &middot; Analisis semantico del esquema</h2>"
          "<p><span class='luz verde'></span>directa en el DPDA &nbsp; <span class='luz amarillo'></span>necesita registro "
          "(mascara / contador) &nbsp; <span class='luz rojo'></span>fuera del DPDA puro (se detecta y se documenta)</p>"
          f"<table><tr><th>ruta</th><th>palabra clave</th><th>semaforo</th></tr>{filas_sem}</table>"
          f"<h3>Hallazgos</h3><ul>{hall}</ul>")
    if errores3:
        f4 = "<h2>Fase 4</h2><div class='mal'>El esquema no pasa la Fase 3: no se construye el automata.</div>"
    else:
        c = A.compilar_esquema(texto_esquema)
        r = A.validar(c, texto_doc, parar_en_primero=parar_en_primero,
                      max_profundidad=max_profundidad, traza=True)
        traza, inicio = r.traza, c.M.q0
        f4 = ("<h2>Fase 4 &middot; Automata de pila determinista ponderado</h2>" + veredicto(r)
              + reproductor(cinta(tokens), svg_de(A.dot(c.M, titulo="DPDA del esquema", rutas=c.rutas)),
                            "Rojo = la fila hace comprobaciones. Etiqueta <code>lee, tope / escribe</code> y "
                            "<code>w</code> = peso. JSON* resume el sub-automata generico (valores sin regla: solo "
                            "sintaxis). El estado actual se pinta de amarillo.")
              + f"<h3>Definicion formal</h3><pre>{e(A.definicion_formal(c))}</pre>" + tabla_delta(c.M.filas()))
    return pagina("Visor del validador", "JSON Schema -> automata de pila determinista ponderado",
                  [("Entrada", entrada("Esquema (JSON Schema)", texto_esquema, texto_doc, r)),
                   ("Fase 1 · Lexico", f1), ("Fase 2 · Sintactico", f2),
                   ("Fase 3 · Semantico", f3), ("Fase 4 · DPDA", f4)], "json", traza, inicio)


# ------------------------------------------------------------------ XML
def dot_arbol_xml(raiz, max_nodos=300):
    l = ['digraph xml {', '  node [fontname="Helvetica", fontsize=10, shape=box, style="rounded,filled", fillcolor="#e3f2fd"];',
         '  edge [arrowsize=0.5, color="#90a4ae"];']
    n, pila = 0, [(raiz, None)]
    while pila and n < max_nodos:
        nodo, padre = pila.pop()
        if isinstance(nodo, str) and not nodo.strip():
            continue
        me = f"n{n}"
        n += 1
        if isinstance(nodo, str):
            l.append(f'  {me} [label="TEXTO\\n{_lbl(nodo.strip()[:24])}", fillcolor="#efebe9", shape=note];')
        else:
            attrs = " ".join(f'{k}={v}' for k, v in nodo.attrs.items())[:40]
            l.append(f'  {me} [label="<{nodo.nombre}>' + (f'\\n{_lbl(attrs)}' if attrs else "") + '"];')
            pila.extend((h, me) for h in reversed(nodo.hijos))
        if padre:
            l.append(f"  {padre} -> {me};")
    l.append("}")
    return "\n".join(l)


def generar_xml(origen, texto_esquema, texto_doc, parar_en_primero=False, max_profundidad=None):
    """Visor para XML con DTD (origen='DTD') o XSD (origen='XSD')."""
    try:
        tokens, err_lex = X.tokenizar_xml(texto_doc), None
    except ErrorLexico as ex:
        tokens, err_lex = [], str(ex)
    conteo = {}
    for t in tokens:
        if not (t.tipo == "TEXTO" and not t.texto.strip()):
            conteo[t.tipo] = conteo.get(t.tipo, 0) + 1
    f1 = ("<h2>Fase 1 &middot; Analisis lexico (XML)</h2><p>Los AFD de etiquetas y de texto arman los tokens. "
          "El texto que es solo espacios no se muestra.</p>"
          + (f"<div class='mal'>{e(err_lex)}</div>" if err_lex else "")
          + f"<div class='cinta'>{cinta(tokens)}</div><p>" + e(", ".join(f"{k} x{v}" for k, v in conteo.items())) + "</p>")
    gram = ("DOC       -> MISC* ELEMENTO MISC*\nELEMENTO  -> VACIA | ABRE CONTENIDO CIERRA   "
            "(CIERRA con el mismo nombre que ABRE)\nCONTENIDO -> (ELEMENTO | TEXTO | COMENTARIO)*\n"
            "MISC      -> COMENTARIO | DECLARACION")
    try:
        arbol = X.parsear_xml(texto_doc)
        f2 = ("<h2>Fase 2 &middot; XML bien formado</h2><p>Gramatica libre de contexto de XML bien formado; "
              f"el parser usa una pila de nombres para casar cada cierre con su apertura.</p><pre>{gram}</pre>"
              f"<div class='diagrama'>{svg_de(dot_arbol_xml(arbol))}</div>")
    except (X.ErrorXML, ErrorLexico) as ex:
        f2 = f"<h2>Fase 2 &middot; XML bien formado</h2><pre>{gram}</pre><div class='mal'>MAL FORMADO: {e(str(ex))}</div>"
    r, traza, inicio = None, [], "Q0"
    try:
        M = X.compilar(origen, texto_esquema)
    except Exception as ex:
        f3 = f"<h2>Fase 3 &middot; Esquema {origen}</h2><div class='mal'>El esquema no se pudo leer: {e(str(ex))}</div>"
        return pagina("Visor del validador", f"XML + {origen}",
                      [("Entrada", entrada(f"Esquema ({origen})", texto_esquema, texto_doc, None) + f3),
                       ("Fase 1 · Lexico", f1), ("Fase 2 · Sintactico", f2), ("Fase 3 · Semantico", f3)],
                      "xml", [], None)
    filas, afds = [], []
    for rg in M.E.reglas:
        er = X.texto_er(rg["modelo"]) if "modelo" in rg else None
        attrs = ", ".join(f"{n}{' (obligatorio)' if a['req'] else ''}: {a['tipo'].get('base')}"
                          + (f" {a['tipo']['enum']}" if 'enum' in a['tipo'] else "")
                          for n, a in rg["atributos"].items())
        tipo_txt = ", ".join(f"{k}={v}" for k, v in rg["texto"].items()) if rg["texto"] else ""
        estados = f"{rg['afd_sin_min'].n} &rarr; {rg['afd'].n}" if er else "&mdash;"
        filas.append(f"<tr><td><code>&lt;{e(rg['nombre'])}&gt;</code></td><td>{rg['contenido']}</td>"
                     f"<td>{'<code>' + e(er) + '</code>' if er else '&mdash;'}</td><td>{estados}</td>"
                     f"<td>{e(tipo_txt)}</td><td>{e(attrs)}</td></tr>")
        if er and rg["afd"].trans:
            afds.append(f"<div class='afd' data-el='{e(rg['nombre'])}'><h5>AFD minimo de &lt;{e(rg['nombre'])}&gt;</h5>"
                        f"{svg_de(X.dot_afd(rg))}</div>")
    avisos = "".join(f"<li class='{n}'><b>{n}</b> {e(m)}</li>" for n, m in M.E.avisos) or "<li>Sin avisos.</li>"
    f3 = (f"<h2>Fase 3 &middot; Semantica del esquema {origen}</h2>"
          "<p>Cada modelo de contenido es una <b>expresion regular</b> sobre los nombres de los hijos: "
          "ER &rarr; AFN (Thompson) &rarr; AFD (subconjuntos) &rarr; AFD minimo (Moore).</p>"
          "<table><tr><th>elemento</th><th>contenido</th><th>expresion regular</th><th>estados AFD &rarr; minimo</th>"
          f"<th>tipo del texto</th><th>atributos</th></tr>{''.join(filas)}</table>"
          f"<h3>Avisos</h3><ul>{avisos}</ul><h3>AFD minimos</h3><div class='afds'>{''.join(afds) or 'ninguno'}</div>")
    r = X.validar_xml(M, texto_doc, parar_en_primero=parar_en_primero,
                      max_profundidad=max_profundidad, traza=True)
    traza = r.traza
    diag = ("<div id='sinafd' class='ayuda'>(el elemento del tope no tiene hijos que revisar con un AFD)</div>"
            "<div class='afds'>" + "".join(a.replace("class='afd'", "class='afd oculto'") for a in afds) + "</div>")
    f4 = ("<h2>Fase 4 &middot; DPDA con un AFD por etiqueta abierta</h2>" + veredicto(r)
          + reproductor(cinta(tokens), diag,
                        "Cada simbolo de pila <code>e@s</code> es un elemento <code>e</code> abierto con su AFD de "
                        "contenido en el estado <code>s</code>. Arriba se ve el AFD del elemento del tope, con su "
                        "estado actual en amarillo.")
          + f"<h3>Definicion formal</h3><pre>{e(X.definicion_formal(M))}</pre>"
          + tabla_delta(list(M.delta.values()), tope_primero=True))
    return pagina("Visor del validador", f"XML + {origen} -> automata de pila con un AFD por etiqueta",
                  [("Entrada", entrada(f"Esquema ({origen})", texto_esquema, texto_doc, r)),
                   ("Fase 1 · Lexico", f1), ("Fase 2 · Sintactico", f2),
                   ("Fase 3 · Semantico", f3), ("Fase 4 · DPDA", f4)], "xml", traza, inicio)


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) < 2:
        print(__doc__)
        sys.exit(1)
    salida = a[a.index("-o") + 1] if "-o" in a else "visor.html"
    leer = lambda p: open(p, encoding="utf-8").read()
    if a[0] in ("--dtd", "--xsd"):
        pag = generar_xml(a[0][2:].upper(), leer(a[1]), leer(a[2]))
    else:
        pag = generar(leer(a[0]), leer(a[1]))
    with open(salida, "w", encoding="utf-8") as f:
        f.write(pag)
    print("  escrito", salida)

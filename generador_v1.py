r"""
generador_v1.py - Fase 5: generacion de codigo. Del DPDA (Fase 4) sale un
validador NATIVO en C y en Rust.

Que emite
  validador.c / validador.rs   un solo archivo cada uno, sin dependencias:
      - las TABLAS (datos): AFD del lexer, tabla delta densa por (estado, simbolo),
        comprobaciones (guardas) con su peso, constantes de enum/const;
      - el MOTOR (igual para todo esquema): lee bytes, arma tokens con los AFD,
        busca la fila de delta y la ejecuta. Una pasada, sin arbol.
  tablas.json                  las mismas tablas como datos (para el informe)

Garantias del codigo generado
  - Pila de profundidad ACOTADA y configurable (PILA_MAX al compilar, --prof al correr).
  - SIN memoria dinamica: no hay malloc; todo vive en un contexto de tamano fijo.
  - API C-ABI (FFI): dpda_tamano, dpda_iniciar, dpda_alimentar, dpda_terminar,
    dpda_reporte. La puede llamar cualquier lenguaje (aqui: Python con ctypes).
  - El texto del esquema NUNCA se pega como codigo: nombres y cadenas salen como
    numeros de bytes (evita inyeccion de codigo en el archivo generado).
  - Mismo veredicto, mismas violaciones, mismo costo y mismas rutas que el
    interprete en Python (se comprueba con miles de documentos).

Limites documentados del nativo (memoria fija)
  - hasta 64 propiedades declaradas por objeto (mascara de 64 bits);
  - numeros de hasta 511 caracteres; claves de hasta 63 bytes en la ruta del error;
  - claves NO declaradas repetidas no se detectan (haria falta un conjunto sin cota).
  - WASM (opcional en el enunciado) no se genera.

Uso
  python generador_v1.py                          -> pruebas (compila y compara)
  python generador_v1.py ESQUEMA.json [-o DIR]    -> escribe validador.c, .rs y tablas.json
  gcc -O2 -o validador validador.c -lm            -> compilar el C
  rustc -O --edition 2021 -o validador_rs validador.rs
  ./validador < documento.json                    -> una linea JSON con el resultado
  opciones del binario: --parar  --prof N  --max-bytes N  --max-ms N  --bloque N
                        --lote (documentos separados por el byte 0x1E)  --metricas  --silencio
"""
import os
import re
import sys
import json
import shutil
import ctypes
import subprocess
import lexer_v4 as L
import automata_v2 as A

BASE = ["{", "}", "[", "]", ":", ",", "CADENA", "NUMERO", "LITERAL"]
TIPOS = {"string": 1, "number": 2, "integer": 4, "boolean": 8, "null": 16, "object": 32, "array": 64}
OPS = ["tipo", "nunca", "enum", "const", "minimum", "maximum", "minLength", "maxLength",
       "dup", "prohibida", "requeridos", "minItems", "maxItems"]
# codigos de error: primero los de las guardas (mismo orden que OPS), luego los de forma
ERRORES = OPS + ["sintaxis", "lexico", "incompleto", "sobra", "profundidad", "tamano",
                 "tiempo", "numero_largo"]


# =========================================================================
# 1. TABLAS: del DPDA (objetos de Python) a numeros
# =========================================================================
def _natural(s):
    return [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", s)]


def _tabla_afd(afd):
    """Un AFD del lexer como arreglos: clase de cada byte, transiciones, aceptacion."""
    estados = sorted({q for q, _ in afd.tabla} | set(afd.tabla.values()) | {afd.inicial}, key=_natural)
    assert estados[0] == afd.inicial
    usadas = sorted({a for _, a in afd.tabla})
    clases = usadas + ["~otro"]
    clase = [clases.index(afd.clase(b)) if afd.clase(b) in usadas else len(usadas) for b in range(256)]
    trans = [[-1] * len(clases) for _ in estados]
    for (q, a), p in afd.tabla.items():
        trans[estados.index(q)][clases.index(a)] = estados.index(p)
    return {"estados": estados, "clases": clases, "clase": clase,
            "trans": [x for fila in trans for x in fila],
            "acepta": [1 if q in afd.aceptacion else 0 for q in estados],
            "nosigue": [1 if b in afd.no_puede_seguir else 0 for b in range(256)]}


def tablas(c, pila_max=1024):
    """Compilado (Fase 4) -> diccionario de tablas numericas, igual para C y Rust."""
    M = c.M
    det = M.verificar_determinismo()
    if det:
        raise ValueError(f"el automata no es determinista: {det}")
    estados = [M.q0] + sorted(M.Q - {M.q0}, key=_natural)
    iq = {q: i for i, q in enumerate(estados)}
    nombres = sorted({a[6:-1] for a in M.Sigma if a.startswith("CLAVE(") and a != "CLAVE(*)"})
    isim = {s: i for i, s in enumerate(BASE)}
    for i, n in enumerate(nombres):
        isim[f"CLAVE({n})"] = len(BASE) + i
    s_otra = len(BASE) + len(nombres)
    s_eps = s_otra + 1
    isim["CLAVE(*)"], isim[A.EPS] = s_otra, s_eps
    na = s_eps + 1
    gamma = ["Z0"] + sorted(M.Gamma - {"Z0"}, key=_natural)
    ig = {g: i for i, g in enumerate(gamma)}
    for g in gamma[1:]:
        if len(M.reg_pila.get(g, {}).get("bits", [])) > 64:
            raise ValueError(f"el objeto {g} declara mas de 64 propiedades (limite de la mascara)")

    octetos = bytearray()

    def texto(t):
        b = t.encode("utf-8")
        ini = len(octetos)
        octetos.extend(b)
        return ini, len(b)

    consts, guardas, filas, alts = [], [], [], []

    def const(v):
        if v is None:
            k = (0, 0.0, 0, 0)
        elif v is True:
            k = (1, 0.0, 0, 0)
        elif v is False:
            k = (2, 0.0, 0, 0)
        elif isinstance(v, (int, float)):
            try:
                k = (3, float(v), 0, 0)
            except OverflowError:
                k = (3, float("inf") if v > 0 else float("-inf"), 0, 0)
        elif isinstance(v, str):
            k = (4, 0.0) + texto(v)
        else:
            k = (5, 0.0, 0, 0)
        consts.append(k)

    max_cad = 0
    for f in sorted(M.filas(), key=lambda f: (iq[f["de"]], isim[f["a"]], f["tope"])):
        bits = M.reg_pila.get(f["tope"], {}).get("bits", [])
        g_ini = len(guardas)
        for nombre, costo, p in f["guardas"]:
            a, d, c_ini, c_n = 0, 0.0, 0, 0
            if nombre == "tipo":
                a = sum(TIPOS[t] for t in p if not t.startswith("@"))
            elif nombre in ("enum", "const"):
                vals = p if nombre == "enum" else [p]
                c_ini, c_n = len(consts), len(vals)
                for v in vals:
                    const(v)
                    if isinstance(v, str):
                        max_cad = max(max_cad, len(v.encode("utf-8")))
                a = 1 if any(isinstance(v, (dict, list)) for v in vals) else 0
            elif nombre in ("minimum", "maximum"):
                d = float(p)
            elif nombre in ("minLength", "maxLength", "minItems", "maxItems"):
                a = int(p)
            elif nombre == "dup":
                a = -1 if p is None else bits.index(p)
            elif nombre == "requeridos":
                a = sum(1 << bits.index(n) for n in set(p))
            guardas.append((OPS.index(nombre), int(costo), a, d, c_ini, c_n))
        pila, push = 0, 0
        if f["pila"] == "pop":
            pila = 1
        elif f["pila"].startswith("push:"):
            pila, push = 2, ig[f["pila"][5:]]
        reg, reg_arg = 0, 0
        if f["registro"] == "cuenta":
            reg = 1
        elif f["registro"] == "marca:*":
            reg = 3
        elif f["registro"]:
            reg, reg_arg = 2, bits.index(f["registro"][6:])
        alts.append((iq[f["de"]] * na + isim[f["a"]], -1 if f["tope"] == A.COMODIN else ig[f["tope"]],
                     len(filas)))
        filas.append((iq[f["a_estado"]], pila, push, reg, reg_arg, g_ini, len(guardas) - g_ini))
    alts.sort()
    alt_ini, k = [], 0
    for celda in range(len(estados) * na + 1):
        while k < len(alts) and alts[k][0] < celda:
            k += 1
        alt_ini.append(k)
    claves, clv_ini, es_clave = [], [], []
    for q in estados:
        clv_ini.append(len(claves))
        es_clave.append(1 if q in M.estados_clave else 0)
        for n in sorted(M.estados_clave.get(q, ())):
            claves.append(texto(n) + (isim[f"CLAVE({n})"],))
            max_cad = max(max_cad, len(n.encode("utf-8")))
    clv_ini.append(len(claves))
    return {
        "pila_max": pila_max, "buf_max": max(64, max_cad + 1),
        "estados": estados, "simbolos": BASE + [f"CLAVE({n})" for n in nombres] + ["CLAVE(*)", "EPS"],
        "gamma": gamma, "q_f": iq["qF"], "s_otra": s_otra, "s_eps": s_eps, "na": na,
        "alt_ini": alt_ini, "alt_tope": [a[1] for a in alts], "alt_fila": [a[2] for a in alts],
        "filas": filas, "guardas": guardas, "consts": consts, "bytes": list(octetos),
        "es_clave": es_clave, "clv_ini": clv_ini, "claves": claves,
        "es_arr": [1 if g.startswith("A") else 0 for g in gamma],
        "lexer": {"num": _tabla_afd(L.AFD_NUMERO), "cad": _tabla_afd(L.AFD_CADENA),
                  "lit": _tabla_afd(L.AFD_LITERAL)},
        "simbolo_byte": [BASE.index(chr(b)) if chr(b) in "{}[]:," else -1 for b in range(256)],
        "tamano": M.tamano(),
    }


# =========================================================================
# 2. EMISION: las tablas como texto C y como texto Rust
# =========================================================================
def _seguro(t):
    """Texto del esquema que va en un COMENTARIO: solo letras, digitos y . _ * ( )"""
    return re.sub(r"[^A-Za-z0-9._*()]", "?", t)[:40]


def _lista(vals, por=20):
    vals = [str(v) for v in vals] or ["0"]
    return ",\n  ".join(", ".join(vals[i:i + por]) for i in range(0, len(vals), por))


def _d_c(d):
    if d != d or d in (float("inf"), float("-inf")):
        return "HUGE_VAL" if d > 0 else "-HUGE_VAL"
    return repr(float(d))


def _d_rs(d):
    if d != d or d in (float("inf"), float("-inf")):
        return "f64::INFINITY" if d > 0 else "f64::NEG_INFINITY"
    return repr(float(d)) + "f64"


def _lexer_defs(T, define):
    cad = T["lexer"]["cad"]
    out = []
    for nombre in ("c1", "c3", "c4", "c7"):
        out.append(define(f"SC_{nombre.upper()}", cad["estados"].index(nombre)))
    for nombre in ("comilla", "barra", "u"):
        out.append(define(f"KC_{nombre.upper()}", cad["clases"].index(nombre)))
    return out


def emitir_c(T):
    o = ["/* ===== TABLAS generadas a partir del esquema (son DATOS, no logica) ===== */",
         f"/* DPDA: {len(T['estados'])} estados, {len(T['filas'])} filas de delta, "
         f"{len(T['gamma'])} simbolos de pila, {len(T['simbolos'])} simbolos de entrada */"]
    o.append("/* estados: " + " ".join(f"{i}={_seguro(q)}" for i, q in enumerate(T["estados"])) + " */")
    o.append("/* pila:    " + " ".join(f"{i}={_seguro(g)}" for i, g in enumerate(T["gamma"])) + " */")
    d = lambda n, v: f"#define {n} {v}"
    o += ["#ifndef PILA_MAX", d("PILA_MAX", T["pila_max"]) + "   /* profundidad maxima de la pila */", "#endif",
          d("BUF_MAX", T["buf_max"]), d("NQ", len(T["estados"])), d("NA", T["na"]),
          d("NFILAS", len(T["filas"])), d("Q_F", T["q_f"]), d("S_OTRA", T["s_otra"]), d("S_EPS", T["s_eps"])]
    o += _lexer_defs(T, d)
    for pref, k in (("LN", "num"), ("LC", "cad"), ("LL", "lit")):
        t = T["lexer"][k]
        o.append(d(f"{pref}_NC", len(t["clases"])))
        o.append(f"static const uint8_t {pref}_CLASE[256] = {{\n  {_lista(t['clase'], 32)}}};")
        o.append(f"static const int8_t {pref}_TRANS[] = {{\n  {_lista(t['trans'], 32)}}};")
        o.append(f"static const uint8_t {pref}_ACEPTA[] = {{{_lista(t['acepta'], 32)}}};")
        o.append(f"static const uint8_t {pref}_NOSIGUE[256] = {{\n  {_lista(t['nosigue'], 32)}}};")
    o.append(f"static const int8_t SIMBOLO[256] = {{\n  {_lista(T['simbolo_byte'], 32)}}};")
    o.append(f"static const int32_t ALT_INI[] = {{\n  {_lista(T['alt_ini'])}}};")
    o.append(f"static const int16_t ALT_TOPE[] = {{\n  {_lista(T['alt_tope'])}}};")
    o.append(f"static const int16_t ALT_FILA[] = {{\n  {_lista(T['alt_fila'])}}};")
    o.append("typedef struct { int16_t dest; uint8_t pila; int16_t push; uint8_t reg; int8_t reg_arg; "
             "int32_t g_ini; uint8_t g_n; } Fila;")
    o.append("static const Fila FILAS[] = {\n  "
             + _lista(["{%d,%d,%d,%d,%d,%d,%d}" % f for f in T["filas"]], 6) + "};")
    o.append("typedef struct { uint8_t op; uint32_t costo; int64_t a; double d; int32_t c_ini, c_n; } Guarda;")
    o.append("static const Guarda GUARDAS[] = {\n  "
             + _lista(["{%d,%d,(int64_t)UINT64_C(%d),%s,%d,%d}" % (g[0], g[1], g[2] % 2 ** 64,
                                                                   _d_c(g[3]), g[4], g[5]) for g in T["guardas"]]
                      or ["{0,0,0,0.0,0,0}"], 4) + "};")
    o.append("typedef struct { uint8_t tipo; double d; int32_t s_ini, s_n; } Const;")
    o.append("static const Const CONSTS[] = {\n  "
             + _lista(["{%d,%s,%d,%d}" % (k[0], _d_c(k[1]), k[2], k[3]) for k in T["consts"]]
                      or ["{0,0.0,0,0}"], 6) + "};")
    o.append(f"static const unsigned char BYTES[] = {{\n  {_lista(T['bytes'], 32)}}};")
    o.append(f"static const uint8_t ES_CLAVE[] = {{{_lista(T['es_clave'], 32)}}};")
    o.append(f"static const int32_t CLV_INI[] = {{{_lista(T['clv_ini'], 32)}}};")
    o.append("typedef struct { int32_t s_ini, s_n; int16_t sim; } Clave;")
    o.append("static const Clave CLAVES[] = {\n  "
             + _lista(["{%d,%d,%d}" % k for k in T["claves"]] or ["{0,0,0}"], 8) + "};")
    o.append(f"static const uint8_t ES_ARR[] = {{{_lista(T['es_arr'], 32)}}};")
    o.append("static const char *const NOMBRE_ERR[] = {" + ", ".join(f'"{e}"' for e in ERRORES) + "};")
    return C_CABEZA + "\n".join(o) + "\n" + C_MOTOR


def emitir_rust(T):
    o = ["// ===== TABLAS generadas a partir del esquema (son DATOS, no logica) =====",
         f"// DPDA: {len(T['estados'])} estados, {len(T['filas'])} filas de delta, "
         f"{len(T['gamma'])} simbolos de pila, {len(T['simbolos'])} simbolos de entrada",
         "// estados: " + " ".join(f"{i}={_seguro(q)}" for i, q in enumerate(T["estados"])),
         "// pila:    " + " ".join(f"{i}={_seguro(g)}" for i, g in enumerate(T["gamma"]))]
    d = lambda n, v: f"const {n}: usize = {v};"
    o += [d("PILA_MAX", T["pila_max"]) + "   // profundidad maxima de la pila",
          d("BUF_MAX", T["buf_max"]), d("NQ", len(T["estados"])), d("NA", T["na"]),
          d("NFILAS", len(T["filas"])), d("Q_F", T["q_f"]), d("S_OTRA", T["s_otra"]), d("S_EPS", T["s_eps"])]
    o += _lexer_defs(T, d)

    def arr(nombre, tipo, vals, por=32):
        return f"static {nombre}: [{tipo}; {len(vals)}] = [\n  {_lista(vals, por) if vals else ''}];"
    for pref, k in (("LN", "num"), ("LC", "cad"), ("LL", "lit")):
        t = T["lexer"][k]
        o.append(d(f"{pref}_NC", len(t["clases"])))
        o += [arr(f"{pref}_CLASE", "u8", t["clase"]), arr(f"{pref}_TRANS", "i8", t["trans"]),
              arr(f"{pref}_ACEPTA", "u8", t["acepta"]), arr(f"{pref}_NOSIGUE", "u8", t["nosigue"])]
    o += [arr("SIMBOLO", "i8", T["simbolo_byte"]), arr("ALT_INI", "i32", T["alt_ini"], 20),
          arr("ALT_TOPE", "i16", T["alt_tope"], 20), arr("ALT_FILA", "i16", T["alt_fila"], 20)]
    o.append("#[derive(Clone, Copy)] struct Fila { dest: i16, pila: u8, push: i16, reg: u8, reg_arg: i8, g_ini: i32, g_n: u8 }")
    o.append("const fn f(dest: i16, pila: u8, push: i16, reg: u8, reg_arg: i8, g_ini: i32, g_n: u8) -> Fila "
             "{ Fila { dest, pila, push, reg, reg_arg, g_ini, g_n } }")
    o.append(arr("FILAS", "Fila", ["f(%d,%d,%d,%d,%d,%d,%d)" % x for x in T["filas"]], 6))
    o.append("#[derive(Clone, Copy)] struct Guarda { op: u8, costo: u32, a: i64, d: f64, c_ini: i32, c_n: i32 }")
    o.append("const fn g(op: u8, costo: u32, a: i64, d: f64, c_ini: i32, c_n: i32) -> Guarda "
             "{ Guarda { op, costo, a, d, c_ini, c_n } }")
    o.append(arr("GUARDAS", "Guarda", ["g(%d,%d,%du64 as i64,%s,%d,%d)" % (x[0], x[1], x[2] % 2 ** 64,
                                                                           _d_rs(x[3]), x[4], x[5]) for x in T["guardas"]], 4))
    o.append("#[derive(Clone, Copy)] struct Konst { tipo: u8, d: f64, s_ini: i32, s_n: i32 }")
    o.append("const fn k(tipo: u8, d: f64, s_ini: i32, s_n: i32) -> Konst { Konst { tipo, d, s_ini, s_n } }")
    o.append(arr("CONSTS", "Konst", ["k(%d,%s,%d,%d)" % (x[0], _d_rs(x[1]), x[2], x[3]) for x in T["consts"]], 6))
    o += [arr("BYTES", "u8", T["bytes"]), arr("ES_CLAVE", "u8", T["es_clave"]), arr("CLV_INI", "i32", T["clv_ini"])]
    o.append("#[derive(Clone, Copy)] struct Clave { s_ini: i32, s_n: i32, sim: i16 }")
    o.append("const fn c(s_ini: i32, s_n: i32, sim: i16) -> Clave { Clave { s_ini, s_n, sim } }")
    o.append(arr("CLAVES", "Clave", ["c(%d,%d,%d)" % x for x in T["claves"]], 8))
    o.append(arr("ES_ARR", "u8", T["es_arr"]))
    o.append(f"static NOMBRE_ERR: [&str; {len(ERRORES)}] = [" + ", ".join(f'"{e}"' for e in ERRORES) + "];")
    return RS_CABEZA + "\n".join(o) + "\n" + RS_MOTOR


# ------------------------------------------------------------------ C
C_CABEZA = r"""/* validador.c - GENERADO por generador_v1.py (Fase 5). No editar a mano.
   Validador nativo de UN esquema: automata de pila determinista ponderado.
   Compilar:  gcc -O2 -o validador validador.c -lm
   Biblioteca (FFI): gcc -O2 -shared -fPIC -DSIN_MAIN -o libvalidador.so validador.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#define ERR_MAX 16      /* errores que se guardan con su ruta (se cuentan todos) */
#define RUTA_MAX 256
#define CLAVE_MAX 64
#define NUM_MAX 512
"""

C_MOTOR = r"""
/* ===== MOTOR (el mismo para cualquier esquema) ===== */
enum { T_LLAVE_A, T_LLAVE_C, T_CORCH_A, T_CORCH_C, T_DOSP, T_COMA, T_CADENA, T_NUMERO, T_LITERAL };
enum { A_NADA, A_NUM, A_CAD, A_LIT };
enum { G_TIPO, G_NUNCA, G_ENUM, G_CONST, G_MIN, G_MAX, G_MINLEN, G_MAXLEN, G_DUP, G_PROHIBIDA,
       G_REQ, G_MINITEMS, G_MAXITEMS, E_SINTAXIS, E_LEXICO, E_INCOMPLETO, E_SOBRA, E_PROFUNDIDAD,
       E_TAMANO, E_TIEMPO, E_NUMERO_LARGO };

typedef struct { int16_t sim; uint8_t tiene_clave, clave_n; uint32_t n; uint64_t mascara;
                 unsigned char clave[CLAVE_MAX]; } Marco;          /* un simbolo de pila + sus registros */
typedef struct { char ruta[RUTA_MAX]; uint8_t codigo, con_pos; uint32_t linea, columna; uint64_t byte; } Error;
typedef struct Dpda {
  /* lexer */
  int afd, lq; uint32_t linea, columna; uint64_t pos; uint32_t ini_linea, ini_columna; uint64_t ini_pos;
  unsigned char buf[BUF_MAX]; uint32_t buf_n; uint8_t buf_des, no_coincide, u8_malo, num_des;
  uint32_t cps, hex, alto; int u8_faltan; unsigned char u8_lo, u8_hi, lit;
  char num[NUM_MAX]; uint32_t num_n; double valor; int tipo_tok;
  /* automata de pila */
  int q; uint32_t tope, max_prof, pila_max; int parar, terminado, mal_formado, limite;
  uint64_t violaciones, costo, pasos;
  uint32_t n_err; Error errores[ERR_MAX];
  Marco pila[PILA_MAX];                                   /* pila de tamano FIJO */
} Dpda;

/* ruta JSON Pointer del valor actual, leida de la pila */
static void ruta_de(const Dpda *v, int sin_tope, char *o) {
  size_t k = 0; uint32_t fin = v->tope - ((sin_tope && v->tope > 0) ? 1 : 0), i, j;
  for (i = 1; i <= fin && k + 80 < RUTA_MAX; i++) {
    const Marco *m = &v->pila[i];
    if (ES_ARR[m->sim]) { if (m->n > 0) k += (size_t)snprintf(o + k, 16, "/%u", (unsigned)(m->n - 1)); }
    else if (m->tiene_clave) {
      o[k++] = '/';
      for (j = 0; j < m->clave_n && k + 4 < RUTA_MAX; j++) {
        unsigned char c = m->clave[j];
        if (c == '~') { o[k++] = '~'; o[k++] = '0'; } else if (c == '/') { o[k++] = '~'; o[k++] = '1'; }
        else o[k++] = (char)c;
      }
    }
  }
  if (k == 0) o[k++] = '/';
  o[k] = 0;
}
static void violar(Dpda *v, int codigo, int sin_tope, int con_pos, uint32_t lin, uint32_t col, uint64_t byte) {
  v->violaciones++;
  if (v->n_err < ERR_MAX) {
    Error *e = &v->errores[v->n_err++];
    ruta_de(v, sin_tope, e->ruta);
    e->codigo = (uint8_t)codigo; e->con_pos = (uint8_t)con_pos; e->linea = lin; e->columna = col; e->byte = byte;
  }
}
static void malformado(Dpda *v, int codigo, int con_pos, uint32_t lin, uint32_t col, uint64_t byte) {
  v->mal_formado = 1; v->terminado = 1;
  violar(v, codigo, 0, con_pos, lin, col, byte);
}
static int parado(const Dpda *v) { return v->terminado || (v->parar && v->violaciones); }

static int igual_const(const Dpda *v, const Const *c, int tk) {
  if (tk == T_LITERAL) return (c->tipo == 0 && v->lit == 'n') || (c->tipo == 1 && v->lit == 't') || (c->tipo == 2 && v->lit == 'f');
  if (tk == T_NUMERO) return c->tipo == 3 && c->d == v->valor;
  return c->tipo == 4 && !v->buf_des && !v->no_coincide && (int32_t)v->buf_n == c->s_n
         && memcmp(v->buf, BYTES + c->s_ini, v->buf_n) == 0;
}
/* una comprobacion (guarda) de la fila: devuelve 1 si se cumple */
static int guarda(const Dpda *v, const Guarda *g, int tk) {
  const Marco *t = &v->pila[v->tope]; int32_t i;
  switch (g->op) {
    case G_TIPO: return (g->a & v->tipo_tok) != 0;
    case G_NUNCA: case G_PROHIBIDA: return 0;
    case G_ENUM: case G_CONST:
      if (tk == T_LLAVE_A || tk == T_CORCH_A) return (int)g->a;
      for (i = 0; i < g->c_n; i++) if (igual_const(v, &CONSTS[g->c_ini + i], tk)) return 1;
      return 0;
    case G_MIN: return v->valor >= g->d;
    case G_MAX: return v->valor <= g->d;
    case G_MINLEN: return (int64_t)v->cps >= g->a;
    case G_MAXLEN: return (int64_t)v->cps <= g->a;
    case G_DUP: return g->a < 0 ? 1 : !((t->mascara >> g->a) & 1);
    case G_REQ: return (t->mascara & (uint64_t)g->a) == (uint64_t)g->a;
    case G_MINITEMS: return (int64_t)t->n >= g->a;
    case G_MAXITEMS: return (int64_t)t->n <= g->a;
  }
  return 1;
}
/* delta(q, a, X): tabla densa por (estado, simbolo) y lista corta por tope de pila */
static const Fila *buscar(int q, int a, int X, int comodin) {
  int32_t i; const Fila *libre = 0;
  for (i = ALT_INI[q * NA + a]; i < ALT_INI[q * NA + a + 1]; i++) {
    if (ALT_TOPE[i] == X) return &FILAS[ALT_FILA[i]];
    if (ALT_TOPE[i] < 0 && comodin) libre = &FILAS[ALT_FILA[i]];
  }
  return libre;
}
static void ejecutar(Dpda *v, const Fila *f, int a, int tk, uint32_t lin, uint32_t col, uint64_t byte) {
  Marco *t = &v->pila[v->tope]; int cierre = (f->pila == 1); uint64_t costo = (a != S_EPS) ? 1 : 0; int i;
  if (f->reg == 1) { if (t->n < 0xFFFFFFFFu) t->n++; }
  else if (f->reg >= 2) {
    t->clave_n = (uint8_t)(v->buf_n < CLAVE_MAX - 1 ? v->buf_n : CLAVE_MAX - 1);
    memcpy(t->clave, v->buf, t->clave_n); t->tiene_clave = 1;
  }
  for (i = 0; i < f->g_n; i++) {                           /* comprobaciones: de la mas barata a la mas cara */
    const Guarda *g = &GUARDAS[f->g_ini + i];
    costo += g->costo;
    if (!guarda(v, g, tk)) {
      violar(v, g->op, cierre, 1, lin, col, byte);
      if (g->op == G_TIPO || g->op == G_NUNCA || v->parar) break;      /* fallo temprano */
    }
  }
  v->costo += costo;
  if (f->reg == 2) t->mascara |= (uint64_t)1 << f->reg_arg;
  if (f->pila == 1) v->tope--;
  else if (f->pila == 2) {
    Marco *m;
    if (v->tope + 1 >= v->max_prof) { v->limite = E_PROFUNDIDAD; malformado(v, E_PROFUNDIDAD, 1, lin, col, byte); return; }
    m = &v->pila[++v->tope];
    m->sim = f->push; m->mascara = 0; m->n = 0; m->tiene_clave = 0; m->clave_n = 0;
    if (v->tope + 1 > v->pila_max) v->pila_max = v->tope + 1;
  }
  v->q = f->dest; v->pasos++;
}
/* un token llega al automata */
static void paso(Dpda *v, int tk, uint32_t lin, uint32_t col, uint64_t byte) {
  const Fila *f; int a = tk;
  if (parado(v)) return;
  if (v->q == Q_F) { malformado(v, E_SOBRA, 1, lin, col, byte); return; }
  if (tk == T_CADENA && ES_CLAVE[v->q]) {                  /* la cadena es una clave: cual? */
    int32_t i; a = S_OTRA;
    if (!v->buf_des && !v->no_coincide)
      for (i = CLV_INI[v->q]; i < CLV_INI[v->q + 1]; i++)
        if (CLAVES[i].s_n == (int32_t)v->buf_n && memcmp(v->buf, BYTES + CLAVES[i].s_ini, v->buf_n) == 0) { a = CLAVES[i].sim; break; }
  }
  f = buscar(v->q, a, v->pila[v->tope].sim, 1);
  if (!f) { malformado(v, E_SINTAXIS, 1, lin, col, byte); return; }
  ejecutar(v, f, a, tk, lin, col, byte);
  while (!v->terminado && (f = buscar(v->q, S_EPS, v->pila[v->tope].sim, 0)) != 0)
    ejecutar(v, f, S_EPS, tk, lin, col, byte);             /* transiciones epsilon (estado R) */
}

/* ---- lexer: los AFD de la Fase 1, byte a byte ---- */
static void hundir(Dpda *v, unsigned char b) { if (v->buf_n < BUF_MAX) v->buf[v->buf_n++] = b; else v->buf_des = 1; }
static void hundir_cp(Dpda *v, uint32_t c) {
  if (c < 0x80) hundir(v, (unsigned char)c);
  else if (c < 0x800) { hundir(v, (unsigned char)(0xC0 | (c >> 6))); hundir(v, (unsigned char)(0x80 | (c & 63))); }
  else if (c < 0x10000) { hundir(v, (unsigned char)(0xE0 | (c >> 12))); hundir(v, (unsigned char)(0x80 | ((c >> 6) & 63))); hundir(v, (unsigned char)(0x80 | (c & 63))); }
  else { hundir(v, (unsigned char)(0xF0 | (c >> 18))); hundir(v, (unsigned char)(0x80 | ((c >> 12) & 63))); hundir(v, (unsigned char)(0x80 | ((c >> 6) & 63))); hundir(v, (unsigned char)(0x80 | (c & 63))); }
}
static void soltar_alto(Dpda *v) { if (v->alto) { v->alto = 0; v->no_coincide = 1; } }
static void unidad(Dpda *v, uint32_t u) {                  /* llego un \uXXXX completo */
  if (v->alto && u >= 0xDC00 && u <= 0xDFFF) { uint32_t c = 0x10000 + ((v->alto - 0xD800) << 10) + (u - 0xDC00); v->alto = 0; hundir_cp(v, c); return; }
  soltar_alto(v); v->cps++;
  if (u >= 0xD800 && u <= 0xDBFF) v->alto = u;
  else if (u >= 0xDC00 && u <= 0xDFFF) v->no_coincide = 1;
  else hundir_cp(v, u);
}
static void utf8(Dpda *v, unsigned char b) {                /* AFD de UTF-8 bien formado */
  if (v->u8_faltan == 0) {
    if (b < 0x80) return;
    v->u8_lo = 0x80; v->u8_hi = 0xBF;
    if (b >= 0xC2 && b <= 0xDF) v->u8_faltan = 1;
    else if (b == 0xE0) { v->u8_faltan = 2; v->u8_lo = 0xA0; }
    else if (b == 0xED) { v->u8_faltan = 2; v->u8_hi = 0x9F; }
    else if (b >= 0xE1 && b <= 0xEF) v->u8_faltan = 2;
    else if (b == 0xF0) { v->u8_faltan = 3; v->u8_lo = 0x90; }
    else if (b == 0xF4) { v->u8_faltan = 3; v->u8_hi = 0x8F; }
    else if (b >= 0xF1 && b <= 0xF3) v->u8_faltan = 3;
    else v->u8_malo = 1;
  } else if (b < v->u8_lo || b > v->u8_hi) { v->u8_malo = 1; v->u8_faltan = 0; }
  else { v->u8_faltan--; v->u8_lo = 0x80; v->u8_hi = 0xBF; }
}
static int hexval(unsigned char b) { return b <= '9' ? b - '0' : (b | 32) - 'a' + 10; }
static void accion(Dpda *v, unsigned char b, int cl) {       /* lo que se guarda del token mientras se lee */
  if (v->afd == A_NUM) { if (v->num_n < NUM_MAX - 1) v->num[v->num_n++] = (char)b; else v->num_des = 1; return; }
  if (v->afd == A_LIT) { if (v->lq == 0) v->lit = b; return; }
  utf8(v, b);
  if (v->lq == SC_C1) {
    if (cl == KC_COMILLA) soltar_alto(v);
    else if (cl != KC_BARRA) { soltar_alto(v); if ((b & 0xC0) != 0x80) v->cps++; hundir(v, b); }
  } else if (v->lq == SC_C3) {
    if (cl == KC_U) v->hex = 0;
    else { soltar_alto(v); v->cps++;
           hundir(v, (unsigned char)(b == 'b' ? 8 : b == 'f' ? 12 : b == 'n' ? 10 : b == 'r' ? 13 : b == 't' ? 9 : b)); }
  } else if (v->lq >= SC_C4 && v->lq <= SC_C7) {
    v->hex = v->hex * 16 + (uint32_t)hexval(b);
    if (v->lq == SC_C7) unidad(v, v->hex);
  }
}
static void lexico(Dpda *v) { if (!parado(v)) malformado(v, E_LEXICO, 1, v->linea, v->columna, v->pos); v->terminado = 1; }
static void emitir(Dpda *v) {
  int afd = v->afd, tk; v->afd = A_NADA;
  if (afd == A_CAD) { if (v->u8_malo || v->u8_faltan) { lexico(v); return; } tk = T_CADENA; v->tipo_tok = 1; }
  else if (afd == A_NUM) {
    uint32_t i; int entero = 1;
    if (v->num_des) { v->limite = E_NUMERO_LARGO; malformado(v, E_NUMERO_LARGO, 1, v->ini_linea, v->ini_columna, v->ini_pos); return; }
    v->num[v->num_n] = 0; v->valor = strtod(v->num, 0);
    for (i = 0; i < v->num_n; i++) if (v->num[i] == '.' || v->num[i] == 'e' || v->num[i] == 'E') entero = 0;
    if (!entero) entero = (v->valor - v->valor == 0.0) && floor(v->valor) == v->valor;   /* finito y sin decimales */
    tk = T_NUMERO; v->tipo_tok = 2 | (entero ? 4 : 0);
  } else { tk = T_LITERAL; v->tipo_tok = (v->lit == 'n') ? 16 : 8; }
  paso(v, tk, v->ini_linea, v->ini_columna, v->ini_pos);
}
static void avanzar(Dpda *v, unsigned char b) { v->pos++; if (b == '\n') { v->linea++; v->columna = 1; } else v->columna++; }
static void un_byte(Dpda *v, unsigned char b) {
  for (;;) {
    int cl, sig, acepta, nosigue;
    if (v->afd == A_NADA) {                                  /* entre tokens */
      if (b == ' ' || b == '\t' || b == '\n' || b == '\r') { avanzar(v, b); return; }
      if (SIMBOLO[b] >= 0) {
        v->tipo_tok = SIMBOLO[b] == T_LLAVE_A ? 32 : SIMBOLO[b] == T_CORCH_A ? 64 : 0;
        paso(v, SIMBOLO[b], v->linea, v->columna, v->pos); avanzar(v, b); return;
      }
      if (b == '"') v->afd = A_CAD; else if (b == '-' || (b >= '0' && b <= '9')) v->afd = A_NUM;
      else if (b == 't' || b == 'f' || b == 'n') v->afd = A_LIT; else { lexico(v); return; }
      v->lq = 0; v->ini_linea = v->linea; v->ini_columna = v->columna; v->ini_pos = v->pos;
      v->buf_n = 0; v->buf_des = 0; v->no_coincide = 0; v->u8_malo = 0; v->u8_faltan = 0;
      v->cps = 0; v->alto = 0; v->num_n = 0; v->num_des = 0;
    }
    if (v->afd == A_NUM) { cl = LN_CLASE[b]; sig = LN_TRANS[v->lq * LN_NC + cl]; acepta = LN_ACEPTA[v->lq]; nosigue = LN_NOSIGUE[b]; }
    else if (v->afd == A_CAD) { cl = LC_CLASE[b]; sig = LC_TRANS[v->lq * LC_NC + cl]; acepta = LC_ACEPTA[v->lq]; nosigue = LC_NOSIGUE[b]; }
    else { cl = LL_CLASE[b]; sig = LL_TRANS[v->lq * LL_NC + cl]; acepta = LL_ACEPTA[v->lq]; nosigue = LL_NOSIGUE[b]; }
    if (sig >= 0) { accion(v, b, cl); v->lq = sig; avanzar(v, b); return; }     /* hay flecha */
    if (!acepta || nosigue) { lexico(v); return; }
    emitir(v);                                               /* token completo: va al automata */
    if (parado(v)) return;
  }                                                          /* y se vuelve a mirar el mismo byte */
}

/* ===== API C-ABI (FFI) ===== */
size_t dpda_tamano(void) { return sizeof(Dpda); }            /* la memoria la pone quien llama */
void dpda_iniciar(Dpda *v, uint32_t max_prof, int parar) {
  memset(v, 0, sizeof *v);
  v->linea = 1; v->columna = 1; v->pila_max = 1; v->parar = parar;
  v->max_prof = (max_prof == 0 || max_prof > PILA_MAX) ? PILA_MAX : max_prof;
}
int dpda_alimentar(Dpda *v, const unsigned char *d, size_t n) {    /* un bloque de bytes; 1 = ya no hace falta mas */
  size_t i;
  for (i = 0; i < n; i++) { if (parado(v)) return 1; un_byte(v, d[i]); }
  return parado(v);
}
void dpda_cortar(Dpda *v, int por_tiempo) {                  /* limite de tamano o de tiempo superado */
  if (parado(v)) return;
  v->limite = por_tiempo ? E_TIEMPO : E_TAMANO; malformado(v, v->limite, 0, 0, 0, 0);
}
int dpda_terminar(Dpda *v) {                                 /* 0 valido, 1 invalido, 2 mal formado */
  if (!parado(v) && v->afd != A_NADA) {
    int acepta = v->afd == A_NUM ? LN_ACEPTA[v->lq] : v->afd == A_CAD ? LC_ACEPTA[v->lq] : LL_ACEPTA[v->lq];
    if (!acepta) lexico(v); else emitir(v);
  }
  if (!parado(v) && v->q != Q_F) malformado(v, E_INCOMPLETO, 0, 0, 0, 0);
  return v->violaciones == 0 ? 0 : (v->mal_formado ? 2 : 1);
}
uint64_t dpda_costo(const Dpda *v) { return v->costo; }
uint64_t dpda_violaciones(const Dpda *v) { return v->violaciones; }
uint64_t dpda_bytes(const Dpda *v) { return v->pos; }
uint32_t dpda_pila_max(const Dpda *v) { return v->pila_max; }
uint32_t dpda_estados(void) { return NQ; }
uint32_t dpda_transiciones(void) { return NFILAS; }

typedef struct { char *p; size_t cap, n; } Sal;
static void pon(Sal *s, const char *t) { for (; *t; t++) if (s->n + 1 < s->cap) s->p[s->n++] = *t; }
static void pon_u(Sal *s, uint64_t x) { char b[24]; snprintf(b, sizeof b, "%llu", (unsigned long long)x); pon(s, b); }
static void pon_esc(Sal *s, const char *t) {
  for (; *t; t++) { unsigned char c = (unsigned char)*t; char b[8];
    if (c == '"' || c == '\\') { b[0] = '\\'; b[1] = (char)c; b[2] = 0; } else if (c < 0x20) snprintf(b, sizeof b, "\\u%04x", c);
    else { b[0] = (char)c; b[1] = 0; }
    pon(s, b); }
}
size_t dpda_reporte(const Dpda *v, char *salida, size_t cap) {   /* el resultado como una linea JSON */
  Sal s; uint32_t i; s.p = salida; s.cap = cap; s.n = 0;
  pon(&s, "{\"valido\":"); pon(&s, v->violaciones ? "false" : "true");
  pon(&s, ",\"mal_formado\":"); pon(&s, v->mal_formado ? "true" : "false");
  pon(&s, ",\"limite\":"); if (v->limite) { pon(&s, "\""); pon(&s, NOMBRE_ERR[v->limite]); pon(&s, "\""); } else pon(&s, "null");
  pon(&s, ",\"violaciones\":"); pon_u(&s, v->violaciones); pon(&s, ",\"costo\":"); pon_u(&s, v->costo);
  pon(&s, ",\"pasos\":"); pon_u(&s, v->pasos); pon(&s, ",\"pila_max\":"); pon_u(&s, v->pila_max);
  pon(&s, ",\"bytes\":"); pon_u(&s, v->pos); pon(&s, ",\"errores\":[");
  for (i = 0; i < v->n_err; i++) {
    const Error *e = &v->errores[i];
    pon(&s, i ? ",{\"ruta\":\"" : "{\"ruta\":\""); pon_esc(&s, e->ruta);
    pon(&s, "\",\"codigo\":\""); pon(&s, NOMBRE_ERR[e->codigo]); pon(&s, "\"");
    if (e->con_pos) { pon(&s, ",\"linea\":"); pon_u(&s, e->linea); pon(&s, ",\"columna\":"); pon_u(&s, e->columna); pon(&s, ",\"byte\":"); pon_u(&s, e->byte); }
    else pon(&s, ",\"linea\":null,\"columna\":null,\"byte\":null");
    pon(&s, "}");
  }
  pon(&s, "]}");
  if (cap) salida[s.n < cap ? s.n : cap - 1] = 0;
  return s.n;
}

#ifndef SIN_MAIN
/* ===== programa de linea de comandos (con instrumentacion de la Fase 6) ===== */
#include <time.h>
#ifdef _WIN32
#include <io.h>
#include <fcntl.h>
#endif
#ifdef CONTAR_MALLOC    /* gcc ... -DCONTAR_MALLOC -static -Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc */
static unsigned long N_MALLOC = 0;
void *__real_malloc(size_t); void *__real_calloc(size_t, size_t); void *__real_realloc(void *, size_t);
void *__wrap_malloc(size_t n) { N_MALLOC++; return __real_malloc(n); }
void *__wrap_calloc(size_t a, size_t b) { N_MALLOC++; return __real_calloc(a, b); }
void *__wrap_realloc(void *p, size_t n) { N_MALLOC++; return __real_realloc(p, n); }
#endif
#define LAT_MAX 65536
static Dpda V; static unsigned char ENT[65536]; static char SAL[ERR_MAX * (RUTA_MAX * 6 + 160) + 512];
static char SBUF[65536]; static uint64_t LAT[LAT_MAX];
static uint64_t ahora_ns(void) { struct timespec t; timespec_get(&t, TIME_UTC); return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec; }
static uint64_t ciclos(void) {
#if defined(__x86_64__) || defined(__i386__)
  return __builtin_ia32_rdtsc();
#else
  return 0;
#endif
}
static void ordenar(uint64_t *a, size_t n) {                 /* shell sort: sin memoria extra */
  size_t h, i, j; uint64_t x;
  for (h = n / 2; h > 0; h /= 2) for (i = h; i < n; i++) { x = a[i]; for (j = i; j >= h && a[j - h] > x; j -= h) a[j] = a[j - h]; a[j] = x; }
}
int main(int argc, char **argv) {
  int parar = 0, lote = 0, metricas = 0, silencio = 0, i, peor = 0, abierto = 0;
  uint32_t prof = 0; uint64_t max_bytes = 0, max_ms = 0, t_ns = 0, t_cic = 0, total = 0, n_docs = 0, cnt[3] = {0, 0, 0};
  uint64_t doc_bytes = 0, doc_ns = 0, doc_t0 = 0; size_t bloque = sizeof ENT, n, n_lat = 0; unsigned long m0 = 0, m1 = 0;
  for (i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--parar")) parar = 1; else if (!strcmp(argv[i], "--lote")) lote = 1;
    else if (!strcmp(argv[i], "--metricas")) metricas = 1; else if (!strcmp(argv[i], "--silencio")) silencio = 1;
    else if (!strcmp(argv[i], "--prof") && i + 1 < argc) prof = (uint32_t)strtoul(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "--max-bytes") && i + 1 < argc) max_bytes = strtoull(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "--max-ms") && i + 1 < argc) max_ms = strtoull(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "--bloque") && i + 1 < argc) { bloque = (size_t)strtoul(argv[++i], 0, 10); if (bloque < 1 || bloque > sizeof ENT) bloque = sizeof ENT; }
    else { fprintf(stderr, "uso: %s [--parar] [--prof N] [--max-bytes N] [--max-ms N] [--bloque N] [--lote] [--metricas] [--silencio] < documento\n", argv[0]); return 3; }
  }
#ifdef _WIN32
  _setmode(_fileno(stdin), _O_BINARY);
#endif
  setvbuf(stdin, 0, _IONBF, 0); setvbuf(stdout, SBUF, _IOFBF, sizeof SBUF);
#ifdef CONTAR_MALLOC
  m0 = N_MALLOC;
#endif
  dpda_iniciar(&V, prof, parar);
  for (;;) {
    size_t a = 0; int fin;
    n = fread(ENT, 1, bloque, stdin);
    fin = (n == 0);
    while (a < n || fin) {
      size_t b = a; int cerrar = fin; uint64_t t0, c0;
      if (!fin) {
        if (lote) { while (b < n && ENT[b] != 0x1E) b++; cerrar = (b < n); } else b = n;
        if (!abierto) { abierto = 1; doc_t0 = ahora_ns(); }
        t0 = ahora_ns(); c0 = ciclos();
        if (max_bytes && doc_bytes + (b - a) > max_bytes) { dpda_alimentar(&V, ENT + a, (size_t)(max_bytes - doc_bytes)); dpda_cortar(&V, 0); }
        else dpda_alimentar(&V, ENT + a, b - a);
        doc_bytes += b - a; total += b - a;
        t_cic += ciclos() - c0; t0 = ahora_ns() - t0; t_ns += t0; doc_ns += t0;
        if (max_ms && (ahora_ns() - doc_t0) / 1000000ull > max_ms) dpda_cortar(&V, 1);
      }
      if (cerrar && (abierto || !lote)) {                    /* fin de un documento */
        uint64_t t0b = ahora_ns(), c0b = ciclos(); int r = dpda_terminar(&V);
        t_cic += ciclos() - c0b; t0b = ahora_ns() - t0b; t_ns += t0b; doc_ns += t0b;
        cnt[r]++; n_docs++; if (r > peor) peor = r;
        if (n_lat < LAT_MAX) LAT[n_lat++] = doc_ns;
        if (!silencio) { dpda_reporte(&V, SAL, sizeof SAL); fputs(SAL, stdout); fputc('\n', stdout); }
        dpda_iniciar(&V, prof, parar); doc_bytes = 0; doc_ns = 0; abierto = 0;
      }
      if (fin) break;
      a = b + (cerrar ? 1 : 0);
    }
    if (fin) break;
  }
#ifdef CONTAR_MALLOC
  m1 = N_MALLOC;
#endif
  fflush(stdout);
  if (metricas) {
    ordenar(LAT, n_lat);
    fprintf(stderr, "{\"docs\":%llu,\"validos\":%llu,\"invalidos\":%llu,\"mal_formados\":%llu,\"bytes\":%llu,\"ns\":%llu,"
            "\"mb_s\":%.2f,\"ciclos_byte\":%.2f,\"asignaciones\":%ld,\"mem_validador\":%llu,\"estados\":%d,\"transiciones\":%d,"
            "\"lat_p50_ns\":%llu,\"lat_p99_ns\":%llu,\"lat_max_ns\":%llu}\n",
            (unsigned long long)n_docs, (unsigned long long)cnt[0], (unsigned long long)cnt[1], (unsigned long long)cnt[2],
            (unsigned long long)total, (unsigned long long)t_ns, t_ns ? (double)total / 1048576.0 / ((double)t_ns / 1e9) : 0.0,
            (total && t_cic) ? (double)t_cic / (double)total : -1.0,
#ifdef CONTAR_MALLOC
            (long)(m1 - m0),
#else
            (long)-1 + (long)(m1 - m0),
#endif
            (unsigned long long)sizeof(Dpda), NQ, NFILAS,
            (unsigned long long)(n_lat ? LAT[n_lat / 2] : 0), (unsigned long long)(n_lat ? LAT[(n_lat * 99) / 100] : 0),
            (unsigned long long)(n_lat ? LAT[n_lat - 1] : 0));
  }
  return peor;
}
#endif
"""

# ------------------------------------------------------------------ Rust
RS_CABEZA = r"""// validador.rs - GENERADO por generador_v1.py (Fase 5). No editar a mano.
// Validador nativo de UN esquema: automata de pila determinista ponderado.
// Compilar:   rustc -O --edition 2021 -o validador_rs validador.rs
// Biblioteca: rustc -O --edition 2021 --crate-type cdylib -o libvalidador_rs.so validador.rs
#![allow(dead_code, unused_unsafe, non_upper_case_globals, clippy::all)]
const ERR_MAX: usize = 16;      // errores que se guardan con su ruta (se cuentan todos)
const RUTA_MAX: usize = 256;
const CLAVE_MAX: usize = 64;
const NUM_MAX: usize = 512;
"""

RS_MOTOR = r"""
// ===== MOTOR (el mismo para cualquier esquema) =====
const T_LLAVE_A: usize = 0; const T_CORCH_A: usize = 2; const T_CADENA: usize = 6; const T_NUMERO: usize = 7; const T_LITERAL: usize = 8;
const A_NADA: u8 = 0; const A_NUM: u8 = 1; const A_CAD: u8 = 2; const A_LIT: u8 = 3;
const G_TIPO: u8 = 0; const G_NUNCA: u8 = 1; const G_ENUM: u8 = 2; const G_CONST: u8 = 3; const G_MIN: u8 = 4; const G_MAX: u8 = 5;
const G_MINLEN: u8 = 6; const G_MAXLEN: u8 = 7; const G_DUP: u8 = 8; const G_PROHIBIDA: u8 = 9; const G_REQ: u8 = 10;
const G_MINITEMS: u8 = 11; const G_MAXITEMS: u8 = 12; const E_SINTAXIS: u8 = 13; const E_LEXICO: u8 = 14; const E_INCOMPLETO: u8 = 15;
const E_SOBRA: u8 = 16; const E_PROFUNDIDAD: u8 = 17; const E_TAMANO: u8 = 18; const E_TIEMPO: u8 = 19; const E_NUMERO_LARGO: u8 = 20;

#[derive(Clone, Copy)]
struct Marco { sim: i16, tiene_clave: bool, clave_n: u8, n: u32, mascara: u64, clave: [u8; CLAVE_MAX] }   // un simbolo de pila + sus registros
#[derive(Clone, Copy)]
struct ErrorV { ruta: [u8; RUTA_MAX], ruta_n: usize, codigo: u8, con_pos: bool, linea: u32, columna: u32, byte: u64 }
pub struct Dpda {
    // lexer
    afd: u8, lq: usize, linea: u32, columna: u32, pos: u64, ini_linea: u32, ini_columna: u32, ini_pos: u64,
    buf: [u8; BUF_MAX], buf_n: usize, buf_des: bool, no_coincide: bool, u8_malo: bool, num_des: bool,
    cps: u32, hex: u32, alto: u32, u8_faltan: u8, u8_lo: u8, u8_hi: u8, lit: u8,
    num: [u8; NUM_MAX], num_n: usize, valor: f64, tipo_tok: i64,
    // automata de pila
    q: usize, tope: usize, max_prof: usize, pila_max: u32, parar: bool, terminado: bool, mal_formado: bool, limite: u8,
    violaciones: u64, costo: u64, pasos: u64,
    n_err: usize, errores: [ErrorV; ERR_MAX],
    pila: [Marco; PILA_MAX],                                 // pila de tamano FIJO
}
const MARCO0: Marco = Marco { sim: 0, tiene_clave: false, clave_n: 0, n: 0, mascara: 0, clave: [0; CLAVE_MAX] };
const ERROR0: ErrorV = ErrorV { ruta: [0; RUTA_MAX], ruta_n: 0, codigo: 0, con_pos: false, linea: 0, columna: 0, byte: 0 };

fn hexval(b: u8) -> u32 { if b <= b'9' { (b - b'0') as u32 } else { ((b | 32) - b'a') as u32 + 10 } }

impl Dpda {
    pub fn nuevo(max_prof: u32, parar: bool) -> Dpda {
        let mp = if max_prof == 0 || max_prof as usize > PILA_MAX { PILA_MAX } else { max_prof as usize };
        Dpda { afd: A_NADA, lq: 0, linea: 1, columna: 1, pos: 0, ini_linea: 0, ini_columna: 0, ini_pos: 0,
               buf: [0; BUF_MAX], buf_n: 0, buf_des: false, no_coincide: false, u8_malo: false, num_des: false,
               cps: 0, hex: 0, alto: 0, u8_faltan: 0, u8_lo: 0, u8_hi: 0, lit: 0,
               num: [0; NUM_MAX], num_n: 0, valor: 0.0, tipo_tok: 0,
               q: 0, tope: 0, max_prof: mp, pila_max: 1, parar, terminado: false, mal_formado: false, limite: 0,
               violaciones: 0, costo: 0, pasos: 0, n_err: 0, errores: [ERROR0; ERR_MAX], pila: [MARCO0; PILA_MAX] }
    }
    // ruta JSON Pointer del valor actual, leida de la pila
    fn ruta_de(&self, sin_tope: bool, o: &mut [u8; RUTA_MAX]) -> usize {
        let mut k = 0usize;
        let fin = self.tope - if sin_tope && self.tope > 0 { 1 } else { 0 };
        let mut i = 1;
        while i <= fin && k + 80 < RUTA_MAX {
            let m = &self.pila[i];
            if ES_ARR[m.sim as usize] != 0 {
                if m.n > 0 {
                    o[k] = b'/'; k += 1;
                    let mut d = [0u8; 12]; let mut x = m.n - 1; let mut n = 0;
                    loop { d[n] = b'0' + (x % 10) as u8; n += 1; x /= 10; if x == 0 { break; } }
                    while n > 0 { n -= 1; o[k] = d[n]; k += 1; }
                }
            } else if m.tiene_clave {
                o[k] = b'/'; k += 1;
                let mut j = 0;
                while j < m.clave_n as usize && k + 4 < RUTA_MAX {
                    let c = m.clave[j];
                    if c == b'~' { o[k] = b'~'; o[k + 1] = b'0'; k += 2; } else if c == b'/' { o[k] = b'~'; o[k + 1] = b'1'; k += 2; }
                    else { o[k] = c; k += 1; }
                    j += 1;
                }
            }
            i += 1;
        }
        if k == 0 { o[0] = b'/'; k = 1; }
        k
    }
    fn violar(&mut self, codigo: u8, sin_tope: bool, con_pos: bool, lin: u32, col: u32, byte: u64) {
        self.violaciones += 1;
        if self.n_err < ERR_MAX {
            let mut r = [0u8; RUTA_MAX];
            let n = self.ruta_de(sin_tope, &mut r);
            self.errores[self.n_err] = ErrorV { ruta: r, ruta_n: n, codigo, con_pos, linea: lin, columna: col, byte };
            self.n_err += 1;
        }
    }
    fn malformado(&mut self, codigo: u8, con_pos: bool, lin: u32, col: u32, byte: u64) {
        self.mal_formado = true; self.terminado = true;
        self.violar(codigo, false, con_pos, lin, col, byte);
    }
    fn parado(&self) -> bool { self.terminado || (self.parar && self.violaciones > 0) }

    fn igual_const(&self, c: &Konst, tk: usize) -> bool {
        if tk == T_LITERAL { return (c.tipo == 0 && self.lit == b'n') || (c.tipo == 1 && self.lit == b't') || (c.tipo == 2 && self.lit == b'f'); }
        if tk == T_NUMERO { return c.tipo == 3 && c.d == self.valor; }
        c.tipo == 4 && !self.buf_des && !self.no_coincide && self.buf_n == c.s_n as usize
            && self.buf[..self.buf_n] == BYTES[c.s_ini as usize..(c.s_ini + c.s_n) as usize]
    }
    // una comprobacion (guarda) de la fila: true si se cumple
    fn guarda(&self, g: &Guarda, tk: usize) -> bool {
        let t = &self.pila[self.tope];
        match g.op {
            G_TIPO => (g.a & self.tipo_tok) != 0,
            G_NUNCA | G_PROHIBIDA => false,
            G_ENUM | G_CONST => {
                if tk == T_LLAVE_A || tk == T_CORCH_A { return g.a != 0; }
                let mut i = 0;
                while i < g.c_n { if self.igual_const(&CONSTS[(g.c_ini + i) as usize], tk) { return true; } i += 1; }
                false
            }
            G_MIN => self.valor >= g.d,
            G_MAX => self.valor <= g.d,
            G_MINLEN => self.cps as i64 >= g.a,
            G_MAXLEN => self.cps as i64 <= g.a,
            G_DUP => g.a < 0 || (t.mascara >> g.a) & 1 == 0,
            G_REQ => (t.mascara & g.a as u64) == g.a as u64,
            G_MINITEMS => t.n as i64 >= g.a,
            G_MAXITEMS => t.n as i64 <= g.a,
            _ => true,
        }
    }
    // delta(q, a, X): tabla densa por (estado, simbolo) y lista corta por tope de pila
    fn buscar(q: usize, a: usize, x: i16, comodin: bool) -> Option<usize> {
        let mut libre = None;
        let mut i = ALT_INI[q * NA + a] as usize;
        let fin = ALT_INI[q * NA + a + 1] as usize;
        while i < fin {
            if ALT_TOPE[i] == x { return Some(ALT_FILA[i] as usize); }
            if ALT_TOPE[i] < 0 && comodin { libre = Some(ALT_FILA[i] as usize); }
            i += 1;
        }
        libre
    }
    fn ejecutar(&mut self, fi: usize, a: usize, tk: usize, lin: u32, col: u32, byte: u64) {
        let f = FILAS[fi];
        let cierre = f.pila == 1;
        let mut costo: u64 = if a != S_EPS { 1 } else { 0 };
        if f.reg == 1 { let t = &mut self.pila[self.tope]; if t.n < u32::MAX { t.n += 1; } }
        else if f.reg >= 2 {
            let n = if self.buf_n < CLAVE_MAX - 1 { self.buf_n } else { CLAVE_MAX - 1 };
            let t = &mut self.pila[self.tope];
            t.clave[..n].copy_from_slice(&self.buf[..n]); t.clave_n = n as u8; t.tiene_clave = true;
        }
        let mut i = 0;
        while i < f.g_n as i32 {                               // comprobaciones: de la mas barata a la mas cara
            let g = GUARDAS[(f.g_ini + i) as usize];
            costo += g.costo as u64;
            if !self.guarda(&g, tk) {
                self.violar(g.op, cierre, true, lin, col, byte);
                if g.op == G_TIPO || g.op == G_NUNCA || self.parar { break; }      // fallo temprano
            }
            i += 1;
        }
        self.costo += costo;
        if f.reg == 2 { self.pila[self.tope].mascara |= 1u64 << f.reg_arg; }
        if f.pila == 1 { self.tope -= 1; }
        else if f.pila == 2 {
            if self.tope + 1 >= self.max_prof { self.limite = E_PROFUNDIDAD; self.malformado(E_PROFUNDIDAD, true, lin, col, byte); return; }
            self.tope += 1;
            self.pila[self.tope] = MARCO0; self.pila[self.tope].sim = f.push;
            if self.tope as u32 + 1 > self.pila_max { self.pila_max = self.tope as u32 + 1; }
        }
        self.q = f.dest as usize; self.pasos += 1;
    }
    // un token llega al automata
    fn paso(&mut self, tk: usize, lin: u32, col: u32, byte: u64) {
        if self.parado() { return; }
        if self.q == Q_F { self.malformado(E_SOBRA, true, lin, col, byte); return; }
        let mut a = tk;
        if tk == T_CADENA && ES_CLAVE[self.q] != 0 {           // la cadena es una clave: cual?
            a = S_OTRA;
            if !self.buf_des && !self.no_coincide {
                let mut i = CLV_INI[self.q] as usize;
                while i < CLV_INI[self.q + 1] as usize {
                    let c = CLAVES[i];
                    if c.s_n as usize == self.buf_n && self.buf[..self.buf_n] == BYTES[c.s_ini as usize..(c.s_ini + c.s_n) as usize] { a = c.sim as usize; break; }
                    i += 1;
                }
            }
        }
        match Dpda::buscar(self.q, a, self.pila[self.tope].sim, true) {
            None => { self.malformado(E_SINTAXIS, true, lin, col, byte); return; }
            Some(fi) => self.ejecutar(fi, a, tk, lin, col, byte),
        }
        while !self.terminado {                                // transiciones epsilon (estado R)
            match Dpda::buscar(self.q, S_EPS, self.pila[self.tope].sim, false) {
                Some(fi) => self.ejecutar(fi, S_EPS, tk, lin, col, byte),
                None => break,
            }
        }
    }

    // ---- lexer: los AFD de la Fase 1, byte a byte ----
    fn hundir(&mut self, b: u8) { if self.buf_n < BUF_MAX { self.buf[self.buf_n] = b; self.buf_n += 1; } else { self.buf_des = true; } }
    fn hundir_cp(&mut self, c: u32) {
        if c < 0x80 { self.hundir(c as u8); }
        else if c < 0x800 { self.hundir((0xC0 | (c >> 6)) as u8); self.hundir((0x80 | (c & 63)) as u8); }
        else if c < 0x10000 { self.hundir((0xE0 | (c >> 12)) as u8); self.hundir((0x80 | ((c >> 6) & 63)) as u8); self.hundir((0x80 | (c & 63)) as u8); }
        else { self.hundir((0xF0 | (c >> 18)) as u8); self.hundir((0x80 | ((c >> 12) & 63)) as u8); self.hundir((0x80 | ((c >> 6) & 63)) as u8); self.hundir((0x80 | (c & 63)) as u8); }
    }
    fn soltar_alto(&mut self) { if self.alto != 0 { self.alto = 0; self.no_coincide = true; } }
    fn unidad(&mut self, u: u32) {                             // llego un \uXXXX completo
        if self.alto != 0 && (0xDC00..=0xDFFF).contains(&u) { let c = 0x10000 + ((self.alto - 0xD800) << 10) + (u - 0xDC00); self.alto = 0; self.hundir_cp(c); return; }
        self.soltar_alto(); self.cps += 1;
        if (0xD800..=0xDBFF).contains(&u) { self.alto = u; }
        else if (0xDC00..=0xDFFF).contains(&u) { self.no_coincide = true; }
        else { self.hundir_cp(u); }
    }
    fn utf8(&mut self, b: u8) {                                // AFD de UTF-8 bien formado
        if self.u8_faltan == 0 {
            if b < 0x80 { return; }
            self.u8_lo = 0x80; self.u8_hi = 0xBF;
            if (0xC2..=0xDF).contains(&b) { self.u8_faltan = 1; }
            else if b == 0xE0 { self.u8_faltan = 2; self.u8_lo = 0xA0; }
            else if b == 0xED { self.u8_faltan = 2; self.u8_hi = 0x9F; }
            else if (0xE1..=0xEF).contains(&b) { self.u8_faltan = 2; }
            else if b == 0xF0 { self.u8_faltan = 3; self.u8_lo = 0x90; }
            else if b == 0xF4 { self.u8_faltan = 3; self.u8_hi = 0x8F; }
            else if (0xF1..=0xF3).contains(&b) { self.u8_faltan = 3; }
            else { self.u8_malo = true; }
        } else if b < self.u8_lo || b > self.u8_hi { self.u8_malo = true; self.u8_faltan = 0; }
        else { self.u8_faltan -= 1; self.u8_lo = 0x80; self.u8_hi = 0xBF; }
    }
    fn accion(&mut self, b: u8, cl: usize) {                   // lo que se guarda del token mientras se lee
        if self.afd == A_NUM { if self.num_n < NUM_MAX - 1 { self.num[self.num_n] = b; self.num_n += 1; } else { self.num_des = true; } return; }
        if self.afd == A_LIT { if self.lq == 0 { self.lit = b; } return; }
        self.utf8(b);
        if self.lq == SC_C1 {
            if cl == KC_COMILLA { self.soltar_alto(); }
            else if cl != KC_BARRA { self.soltar_alto(); if (b & 0xC0) != 0x80 { self.cps += 1; } self.hundir(b); }
        } else if self.lq == SC_C3 {
            if cl == KC_U { self.hex = 0; }
            else { self.soltar_alto(); self.cps += 1;
                   self.hundir(match b { b'b' => 8, b'f' => 12, b'n' => 10, b'r' => 13, b't' => 9, _ => b }); }
        } else if self.lq >= SC_C4 && self.lq <= SC_C7 {
            self.hex = self.hex * 16 + hexval(b);
            if self.lq == SC_C7 { let h = self.hex; self.unidad(h); }
        }
    }
    fn lexico(&mut self) { if !self.parado() { let (l, c, p) = (self.linea, self.columna, self.pos); self.malformado(E_LEXICO, true, l, c, p); } self.terminado = true; }
    fn emitir(&mut self) {
        let afd = self.afd; self.afd = A_NADA;
        let tk;
        if afd == A_CAD { if self.u8_malo || self.u8_faltan != 0 { self.lexico(); return; } tk = T_CADENA; self.tipo_tok = 1; }
        else if afd == A_NUM {
            if self.num_des { self.limite = E_NUMERO_LARGO; let (l, c, p) = (self.ini_linea, self.ini_columna, self.ini_pos); self.malformado(E_NUMERO_LARGO, true, l, c, p); return; }
            let txt = &self.num[..self.num_n];
            self.valor = core::str::from_utf8(txt).ok().and_then(|s| s.parse::<f64>().ok()).unwrap_or(0.0);
            let mut entero = !txt.iter().any(|&c| c == b'.' || c == b'e' || c == b'E');
            if !entero { entero = self.valor.is_finite() && self.valor.floor() == self.valor; }   // finito y sin decimales
            tk = T_NUMERO; self.tipo_tok = 2 | if entero { 4 } else { 0 };
        } else { tk = T_LITERAL; self.tipo_tok = if self.lit == b'n' { 16 } else { 8 }; }
        let (l, c, p) = (self.ini_linea, self.ini_columna, self.ini_pos);
        self.paso(tk, l, c, p);
    }
    fn avanzar(&mut self, b: u8) { self.pos += 1; if b == b'\n' { self.linea += 1; self.columna = 1; } else { self.columna += 1; } }
    fn un_byte(&mut self, b: u8) {
        loop {
            if self.afd == A_NADA {                              // entre tokens
                if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' { self.avanzar(b); return; }
                let s = SIMBOLO[b as usize];
                if s >= 0 {
                    let s = s as usize;
                    self.tipo_tok = if s == T_LLAVE_A { 32 } else if s == T_CORCH_A { 64 } else { 0 };
                    let (l, c, p) = (self.linea, self.columna, self.pos);
                    self.paso(s, l, c, p); self.avanzar(b); return;
                }
                if b == b'"' { self.afd = A_CAD; } else if b == b'-' || b.is_ascii_digit() { self.afd = A_NUM; }
                else if b == b't' || b == b'f' || b == b'n' { self.afd = A_LIT; } else { self.lexico(); return; }
                self.lq = 0; self.ini_linea = self.linea; self.ini_columna = self.columna; self.ini_pos = self.pos;
                self.buf_n = 0; self.buf_des = false; self.no_coincide = false; self.u8_malo = false; self.u8_faltan = 0;
                self.cps = 0; self.alto = 0; self.num_n = 0; self.num_des = false;
            }
            let (cl, sig, acepta, nosigue);
            if self.afd == A_NUM { cl = LN_CLASE[b as usize] as usize; sig = LN_TRANS[self.lq * LN_NC + cl]; acepta = LN_ACEPTA[self.lq]; nosigue = LN_NOSIGUE[b as usize]; }
            else if self.afd == A_CAD { cl = LC_CLASE[b as usize] as usize; sig = LC_TRANS[self.lq * LC_NC + cl]; acepta = LC_ACEPTA[self.lq]; nosigue = LC_NOSIGUE[b as usize]; }
            else { cl = LL_CLASE[b as usize] as usize; sig = LL_TRANS[self.lq * LL_NC + cl]; acepta = LL_ACEPTA[self.lq]; nosigue = LL_NOSIGUE[b as usize]; }
            if sig >= 0 { self.accion(b, cl); self.lq = sig as usize; self.avanzar(b); return; }     // hay flecha
            if acepta == 0 || nosigue != 0 { self.lexico(); return; }
            self.emitir();                                       // token completo: va al automata
            if self.parado() { return; }
        }                                                        // y se vuelve a mirar el mismo byte
    }

    pub fn alimentar(&mut self, d: &[u8]) -> bool {             // un bloque de bytes; true = ya no hace falta mas
        for &b in d { if self.parado() { return true; } self.un_byte(b); }
        self.parado()
    }
    pub fn cortar(&mut self, por_tiempo: bool) {                // limite de tamano o de tiempo superado
        if self.parado() { return; }
        self.limite = if por_tiempo { E_TIEMPO } else { E_TAMANO };
        let l = self.limite; self.malformado(l, false, 0, 0, 0);
    }
    pub fn terminar(&mut self) -> i32 {                         // 0 valido, 1 invalido, 2 mal formado
        if !self.parado() && self.afd != A_NADA {
            let acepta = if self.afd == A_NUM { LN_ACEPTA[self.lq] } else if self.afd == A_CAD { LC_ACEPTA[self.lq] } else { LL_ACEPTA[self.lq] };
            if acepta == 0 { self.lexico(); } else { self.emitir(); }
        }
        if !self.parado() && self.q != Q_F { self.malformado(E_INCOMPLETO, false, 0, 0, 0); }
        if self.violaciones == 0 { 0 } else if self.mal_formado { 2 } else { 1 }
    }
    pub fn reporte(&self, salida: &mut [u8]) -> usize {         // el resultado como una linea JSON
        let mut s = Sal { p: salida, n: 0 };
        s.pon(b"{\"valido\":"); s.pon(if self.violaciones > 0 { b"false" } else { b"true" });
        s.pon(b",\"mal_formado\":"); s.pon(if self.mal_formado { b"true" } else { b"false" });
        s.pon(b",\"limite\":"); if self.limite != 0 { s.pon(b"\""); s.pon(NOMBRE_ERR[self.limite as usize].as_bytes()); s.pon(b"\""); } else { s.pon(b"null"); }
        s.pon(b",\"violaciones\":"); s.pon_u(self.violaciones); s.pon(b",\"costo\":"); s.pon_u(self.costo);
        s.pon(b",\"pasos\":"); s.pon_u(self.pasos); s.pon(b",\"pila_max\":"); s.pon_u(self.pila_max as u64);
        s.pon(b",\"bytes\":"); s.pon_u(self.pos); s.pon(b",\"errores\":[");
        for i in 0..self.n_err {
            let e = &self.errores[i];
            s.pon(if i > 0 { b",{\"ruta\":\"" } else { b"{\"ruta\":\"" }); s.pon_esc(&e.ruta[..e.ruta_n]);
            s.pon(b"\",\"codigo\":\""); s.pon(NOMBRE_ERR[e.codigo as usize].as_bytes()); s.pon(b"\"");
            if e.con_pos { s.pon(b",\"linea\":"); s.pon_u(e.linea as u64); s.pon(b",\"columna\":"); s.pon_u(e.columna as u64); s.pon(b",\"byte\":"); s.pon_u(e.byte); }
            else { s.pon(b",\"linea\":null,\"columna\":null,\"byte\":null"); }
            s.pon(b"}");
        }
        s.pon(b"]}");
        s.n
    }
}
struct Sal<'a> { p: &'a mut [u8], n: usize }
impl<'a> Sal<'a> {
    fn pon(&mut self, t: &[u8]) { for &c in t { if self.n < self.p.len() { self.p[self.n] = c; self.n += 1; } } }
    fn pon_u(&mut self, mut x: u64) { let mut d = [0u8; 20]; let mut n = 0; loop { d[n] = b'0' + (x % 10) as u8; n += 1; x /= 10; if x == 0 { break; } } while n > 0 { n -= 1; let c = d[n]; self.pon(&[c]); } }
    fn pon_esc(&mut self, t: &[u8]) {
        for &c in t {
            if c == b'"' || c == b'\\' { self.pon(&[b'\\', c]); }
            else if c < 0x20 { let h = b"0123456789abcdef"; self.pon(&[b'\\', b'u', b'0', b'0', h[(c >> 4) as usize], h[(c & 15) as usize]]); }
            else { self.pon(&[c]); }
        }
    }
}

// ===== API C-ABI (FFI): la memoria la pone quien llama =====
#[no_mangle] pub extern "C" fn dpda_tamano() -> usize { core::mem::size_of::<Dpda>() }
#[no_mangle] pub unsafe extern "C" fn dpda_iniciar(v: *mut Dpda, max_prof: u32, parar: i32) { core::ptr::write(v, Dpda::nuevo(max_prof, parar != 0)); }
#[no_mangle] pub unsafe extern "C" fn dpda_alimentar(v: *mut Dpda, d: *const u8, n: usize) -> i32 { (*v).alimentar(core::slice::from_raw_parts(d, n)) as i32 }
#[no_mangle] pub unsafe extern "C" fn dpda_cortar(v: *mut Dpda, por_tiempo: i32) { (*v).cortar(por_tiempo != 0) }
#[no_mangle] pub unsafe extern "C" fn dpda_terminar(v: *mut Dpda) -> i32 { (*v).terminar() }
#[no_mangle] pub unsafe extern "C" fn dpda_reporte(v: *const Dpda, salida: *mut u8, cap: usize) -> usize {
    if cap == 0 { return 0; }
    let s = core::slice::from_raw_parts_mut(salida, cap);
    let n = (*v).reporte(&mut s[..cap - 1]); s[n] = 0; n
}
#[no_mangle] pub extern "C" fn dpda_estados() -> u32 { NQ as u32 }
#[no_mangle] pub extern "C" fn dpda_transiciones() -> u32 { NFILAS as u32 }

// ===== programa de linea de comandos (con instrumentacion de la Fase 6) =====
mod cuenta {                                                   // cuenta las asignaciones de memoria
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicU64, Ordering};
    pub static N: AtomicU64 = AtomicU64::new(0);
    pub struct Contador;
    unsafe impl GlobalAlloc for Contador {
        unsafe fn alloc(&self, l: Layout) -> *mut u8 { N.fetch_add(1, Ordering::Relaxed); System.alloc(l) }
        unsafe fn dealloc(&self, p: *mut u8, l: Layout) { System.dealloc(p, l) }
    }
    pub fn total() -> u64 { N.load(Ordering::Relaxed) }
}
#[global_allocator] static ASIGNADOR: cuenta::Contador = cuenta::Contador;

fn ciclos() -> u64 {
    #[cfg(target_arch = "x86_64")] { return unsafe { core::arch::x86_64::_rdtsc() }; }
    #[cfg(not(target_arch = "x86_64"))] { return 0; }
}
const LAT_MAX: usize = 65536;
static mut LAT: [u64; LAT_MAX] = [0; LAT_MAX];
static mut ENT: [u8; 65536] = [0; 65536];
static mut SAL: [u8; ERR_MAX * (RUTA_MAX * 6 + 160) + 512] = [0; ERR_MAX * (RUTA_MAX * 6 + 160) + 512];

fn main() {
    use std::io::{Read, Write};
    use std::time::Instant;
    let (mut parar, mut lote, mut metricas, mut silencio) = (false, false, false, false);
    let (mut prof, mut max_bytes, mut max_ms, mut bloque) = (0u32, 0u64, 0u64, 65536usize);
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--parar" => parar = true, "--lote" => lote = true, "--metricas" => metricas = true, "--silencio" => silencio = true,
            "--prof" => prof = args.next().and_then(|x| x.parse().ok()).unwrap_or(0),
            "--max-bytes" => max_bytes = args.next().and_then(|x| x.parse().ok()).unwrap_or(0),
            "--max-ms" => max_ms = args.next().and_then(|x| x.parse().ok()).unwrap_or(0),
            "--bloque" => { bloque = args.next().and_then(|x| x.parse().ok()).unwrap_or(65536); if bloque < 1 || bloque > 65536 { bloque = 65536; } }
            _ => { eprintln!("uso: validador_rs [--parar] [--prof N] [--max-bytes N] [--max-ms N] [--bloque N] [--lote] [--metricas] [--silencio] < documento"); std::process::exit(3); }
        }
    }
    let ent = unsafe { &mut *core::ptr::addr_of_mut!(ENT) };
    let sal = unsafe { &mut *core::ptr::addr_of_mut!(SAL) };
    let lat = unsafe { &mut *core::ptr::addr_of_mut!(LAT) };
    let stdin = std::io::stdin(); let mut entrada = stdin.lock();
    let stdout = std::io::stdout(); let mut salida = stdout.lock();
    let mut v = Dpda::nuevo(prof, parar);
    let (mut t_ns, mut t_cic, mut total, mut n_docs, mut doc_bytes, mut doc_ns) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut cnt = [0u64; 3]; let mut n_lat = 0usize; let mut peor = 0i32; let mut abierto = false;
    let mut doc_t0 = Instant::now();
    let m0 = cuenta::total(); let mut asignaciones = 0u64;
    loop {
        let n = match entrada.read(&mut ent[..bloque]) { Ok(n) => n, Err(_) => 0 };
        let fin = n == 0;
        let mut a = 0usize;
        while a < n || fin {
            let mut b = a; let mut cerrar = fin;
            if !fin {
                if lote { while b < n && ent[b] != 0x1E { b += 1; } cerrar = b < n; } else { b = n; }
                if !abierto { abierto = true; doc_t0 = Instant::now(); }
                let (t0, c0, k0) = (Instant::now(), ciclos(), cuenta::total());
                if max_bytes != 0 && doc_bytes + (b - a) as u64 > max_bytes { v.alimentar(&ent[a..a + (max_bytes - doc_bytes) as usize]); v.cortar(false); }
                else { v.alimentar(&ent[a..b]); }
                asignaciones += cuenta::total() - k0;
                doc_bytes += (b - a) as u64; total += (b - a) as u64;
                t_cic += ciclos().wrapping_sub(c0); let d = t0.elapsed().as_nanos() as u64; t_ns += d; doc_ns += d;
                if max_ms != 0 && doc_t0.elapsed().as_millis() as u64 > max_ms { v.cortar(true); }
            }
            if cerrar && (abierto || !lote) {                    // fin de un documento
                let (t0, c0, k0) = (Instant::now(), ciclos(), cuenta::total());
                let r = v.terminar();
                asignaciones += cuenta::total() - k0;
                t_cic += ciclos().wrapping_sub(c0); let d = t0.elapsed().as_nanos() as u64; t_ns += d; doc_ns += d;
                cnt[r as usize] += 1; n_docs += 1; if r > peor { peor = r; }
                if n_lat < LAT_MAX { lat[n_lat] = doc_ns; n_lat += 1; }
                if !silencio { let k = v.reporte(&mut sal[..]); let _ = salida.write_all(&sal[..k]); let _ = salida.write_all(b"\n"); }
                v = Dpda::nuevo(prof, parar); doc_bytes = 0; doc_ns = 0; abierto = false;
            }
            if fin { break; }
            a = b + if cerrar { 1 } else { 0 };
        }
        if fin { break; }
    }
    let _ = salida.flush();
    let _ = m0;
    if metricas {
        lat[..n_lat].sort_unstable();
        let mb_s = if t_ns > 0 { total as f64 / 1048576.0 / (t_ns as f64 / 1e9) } else { 0.0 };
        let cpb = if total > 0 && t_cic > 0 { t_cic as f64 / total as f64 } else { -1.0 };
        eprintln!("{{\"docs\":{},\"validos\":{},\"invalidos\":{},\"mal_formados\":{},\"bytes\":{},\"ns\":{},\"mb_s\":{:.2},\"ciclos_byte\":{:.2},\"asignaciones\":{},\"mem_validador\":{},\"estados\":{},\"transiciones\":{},\"lat_p50_ns\":{},\"lat_p99_ns\":{},\"lat_max_ns\":{}}}",
                  n_docs, cnt[0], cnt[1], cnt[2], total, t_ns, mb_s, cpb, asignaciones, core::mem::size_of::<Dpda>(), NQ, NFILAS,
                  if n_lat > 0 { lat[n_lat / 2] } else { 0 }, if n_lat > 0 { lat[(n_lat * 99) / 100] } else { 0 }, if n_lat > 0 { lat[n_lat - 1] } else { 0 });
    }
    std::process::exit(peor);
}
"""


# =========================================================================
# 3. GENERAR, COMPILAR Y LLAMAR (sandbox: carpeta propia, tiempo limite)
# =========================================================================
def generar(texto_esquema, carpeta, pila_max=1024):
    """Escribe validador.c, validador.rs y tablas.json en la carpeta. Devuelve las tablas."""
    c = A.compilar_esquema(texto_esquema)
    T = tablas(c, pila_max)
    os.makedirs(carpeta, exist_ok=True)
    with open(os.path.join(carpeta, "validador.c"), "w", encoding="utf-8") as f:
        f.write(emitir_c(T))
    with open(os.path.join(carpeta, "validador.rs"), "w", encoding="utf-8") as f:
        f.write(emitir_rust(T))
    with open(os.path.join(carpeta, "tablas.json"), "w", encoding="utf-8") as f:
        json.dump(T, f)
    return T


def _correr(cmd, cwd, limite=120):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=limite)
    if r.returncode != 0:
        raise RuntimeError(f"fallo {' '.join(cmd)}:\n{r.stderr.decode(errors='replace')[:3000]}")


def hay(lenguaje):
    return shutil.which("gcc" if lenguaje == "c" else "rustc") is not None


def compilar(carpeta, lenguaje="c", biblioteca=False, contar=False):
    """Compila el codigo generado dentro de su carpeta. Devuelve la ruta del binario."""
    ext = ".dll" if os.name == "nt" else ".so"
    exe = ".exe" if os.name == "nt" else ""
    if lenguaje == "c":
        if biblioteca:
            sal = "libvalidador" + ext
            _correr(["gcc", "-O2", "-shared", "-fPIC", "-DSIN_MAIN", "-o", sal, "validador.c", "-lm"], carpeta)
        elif contar:
            sal = "validador_cuenta" + exe
            _correr(["gcc", "-O2", "-static", "-DCONTAR_MALLOC", "-Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc",
                     "-o", sal, "validador.c", "-lm"], carpeta)
        else:
            sal = "validador" + exe
            _correr(["gcc", "-O2", "-Wall", "-Wextra", "-o", sal, "validador.c", "-lm"], carpeta)
    else:
        if biblioteca:
            sal = "libvalidador_rs" + ext
            _correr(["rustc", "-O", "--edition", "2021", "--crate-type", "cdylib", "-o", sal, "validador.rs"], carpeta)
        else:
            sal = "validador_rs" + exe
            _correr(["rustc", "-O", "--edition", "2021", "-o", sal, "validador.rs"], carpeta)
    return os.path.join(carpeta, sal)


def _caja(segundos):
    """Limites del proceso hijo (Linux/macOS): tiempo de CPU, memoria, sin crear archivos
    ni volcados y con pocos descriptores. En Windows queda solo el limite de tiempo."""
    def poner():
        import resource
        for cual, valor in ((resource.RLIMIT_CPU, segundos + 1), (resource.RLIMIT_AS, 1 << 30),
                            (resource.RLIMIT_CORE, 0), (resource.RLIMIT_FSIZE, 0), (resource.RLIMIT_NOFILE, 16)):
            try:
                resource.setrlimit(cual, (valor, valor))
            except (ValueError, OSError):
                pass
    return poner


def ejecutar(binario, datos, args=(), limite=60):
    """Corre el validador nativo con un documento. Devuelve (resultado, metricas o None)."""
    datos = datos.encode("utf-8") if isinstance(datos, str) else datos
    binario = os.path.abspath(binario)
    extra = {}
    if os.name == "posix":                       # caja de arena: sin variables de entorno y con limites
        extra = {"env": {}, "preexec_fn": _caja(limite)}
    r = subprocess.run([binario, *args], input=datos, capture_output=True, timeout=limite,
                       cwd=os.path.dirname(binario), **extra)
    lineas = [json.loads(x) for x in r.stdout.decode("utf-8", errors="replace").splitlines() if x.strip()]
    met = None
    if "--metricas" in args and r.stderr.strip():
        met = json.loads(r.stderr.decode().strip().splitlines()[-1])
    if "--lote" in args:
        return lineas, met
    return (lineas[0] if lineas else None), met


class Nativo:
    """El validador generado, cargado como biblioteca y llamado por la API C-ABI (FFI con ctypes)."""

    def __init__(self, ruta_biblioteca):
        self.lib = ctypes.CDLL(os.path.abspath(ruta_biblioteca))
        self.lib.dpda_tamano.restype = ctypes.c_size_t
        self.lib.dpda_iniciar.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int]
        self.lib.dpda_alimentar.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_size_t]
        self.lib.dpda_terminar.argtypes = [ctypes.c_void_p]
        self.lib.dpda_reporte.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_size_t]
        self.lib.dpda_reporte.restype = ctypes.c_size_t
        self.ctx = ctypes.create_string_buffer(self.lib.dpda_tamano())     # la memoria la pone Python
        self.sal = ctypes.create_string_buffer(40000)

    def validar(self, datos, bloque=65536, parar=False, max_prof=0):
        datos = datos.encode("utf-8") if isinstance(datos, str) else datos
        self.lib.dpda_iniciar(self.ctx, max_prof, 1 if parar else 0)
        for i in range(0, len(datos), bloque):
            if self.lib.dpda_alimentar(self.ctx, datos[i:i + bloque], len(datos[i:i + bloque])):
                break
        self.lib.dpda_terminar(self.ctx)
        n = self.lib.dpda_reporte(self.ctx, self.sal, len(self.sal))
        return json.loads(self.sal.raw[:n].decode("utf-8", errors="replace"))


def como_nativo(r):
    """Resultado del interprete en Python, en la misma forma que reporta el nativo."""
    return {"valido": r.valido, "mal_formado": r.mal_formado, "violaciones": r.violaciones,
            "costo": r.costo, "pasos": r.pasos, "pila_max": r.prof_max,
            "errores": [(e["ruta"][:150], e["linea"], e["columna"], e["byte"]) for e in r.errores[:16]]}


def _clave(d):
    return {"valido": d["valido"], "mal_formado": d["mal_formado"], "violaciones": d["violaciones"],
            "costo": d["costo"], "pasos": d["pasos"], "pila_max": d["pila_max"],
            "errores": [(e["ruta"][:150], e["linea"], e["columna"], e["byte"]) for e in d["errores"]]}


# =========================================================================
# 4. PRUEBAS: el nativo debe dar EXACTAMENTE lo mismo que el interprete
# =========================================================================
ESQUEMAS_PRUEBA = [
    A.ESQ,
    '{"type":"object","properties":{"nombre":{"type":"string","minLength":2,"maxLength":5},'
    '"edad":{"type":"integer","minimum":0,"maximum":120},"activo":{"type":"boolean"},"x":{"type":"null"},'
    '"rol":{"enum":["admin","user",7,null,true]}},"required":["nombre","edad"],"additionalProperties":false}',
    '{"type":"array","items":{"type":"array","items":{"type":"number","minimum":-1.5,"maximum":100}},"minItems":1,"maxItems":4}',
    '{"$defs":{"nodo":{"type":"object","properties":{"v":{"type":"integer"},'
    '"hijos":{"type":"array","items":{"$ref":"#/$defs/nodo"}}},"required":["v"]}},"$ref":"#/$defs/nodo"}',
    '{"properties":{"a":{"const":"h\\u00e9 \\"x\\""},"b":{"type":["string","null"],"maxLength":3},"c":false},'
    '"required":["a"],"additionalProperties":{"type":"integer"}}',
    '{"required":["a","z"],"additionalProperties":{"type":"integer"},"minItems":1}',
    '{"required":["id"],"additionalProperties":false}',
    '{"type":["object","array"],"items":{"enum":[1.5,"a/b","~",[1]]},"minItems":2,"properties":{"k~/":{"const":{"x":1}}}}',
    'true',
]


def correr_pruebas():
    import random
    import tempfile
    ok = total = 0

    def chequear(nombre, cond):
        nonlocal ok, total
        total += 1
        if cond:
            ok += 1
        else:
            print("  FALLA:", nombre)

    random.seed(21)
    claves = ["id", "tags", "nombre", "edad", "activo", "x", "rol", "v", "hijos", "a", "b", "c", "z", "k~/", "é"]
    escalares = [0, 1, 7, -3, 150, 2.5, 3.0, 1e3, -1.5, 1.5, "a", "hé \"x\"", "abcdefg", "", "a/b", "~", "admin",
                 True, False, None, "x", 10 ** 20, "\U0001F600", "ñ\n\t"]

    def gen(p=0):
        r = random.random()
        if p > 3 or r < 0.45:
            return random.choice(escalares)
        if r < 0.7:
            return [gen(p + 1) for _ in range(random.randint(0, 5))]
        return {k: gen(p + 1) for k in random.sample(claves, random.randint(0, 5))}

    def danar(txt):
        t = list(txt)
        for _ in range(random.randint(1, 2)):
            pos = random.randrange(len(t)) if t else 0
            op = random.choice("bis")
            if op == "b" and t:
                del t[pos]
            elif op == "i":
                t.insert(pos, random.choice('{}[]:,"7a\\u -.e'))
            elif t:
                t[pos] = random.choice('{}[]:,"7a\\u -.e')
        return "".join(t)

    docs = []
    for _ in range(700):
        d = json.dumps(gen(), ensure_ascii=random.random() < 0.5)
        docs.append(d if random.random() < 0.7 else danar(d))
    docs += ['', ' ', '{"id":7} x', '{"id":7}{', '[' * 2000 + ']' * 2000, '{"id":"\\ud83d\\ude00\\ud83dx"}',
             '{"\\u0069d":7,"id":8}', '{"nombre":"\\u00e9\\u00e9","edad":1e2}', '[1e400,-0.0,1E2,12.0]',
             '{"a":"h\\u00e9 \\"x\\"","z":1,"b":"\\ud83d\\ude00\\ud83d\\ude00\\ud83d\\ude00"}']
    docs_b = [d.encode("utf-8") for d in docs] + [b'{"id":7,"t":"\xff"}', b'{"id":"\xc3"}', b'"\xed\xa0\x80"',
                                                  b'{"nombre":"\xc3\\n\xa9","edad":1}', b'"\xf4\x90\x80\x80"', b'["\xe2\x82\xac"]']
    if not hay("c") and not hay("rust"):
        print("  (no hay gcc ni rustc: solo se prueba la generacion)")
    with tempfile.TemporaryDirectory() as tmp:
        for n, esq in enumerate(ESQUEMAS_PRUEBA):
            carpeta = os.path.join(tmp, f"e{n}")
            T = generar(esq, carpeta, pila_max=1024)
            c = A.compilar_esquema(esq)
            chequear(f"esquema {n}: tablas con todas las filas", len(T["filas"]) == len(c.M.delta))
            ref = [como_nativo(A.validar(c, d, max_profundidad=1024, memoria_fija=True)) for d in docs_b]
            ref_parar = [como_nativo(A.validar(c, d, max_profundidad=1024, parar_en_primero=True, memoria_fija=True))
                         for d in docs_b[:200]]
            lote = b"\x1e".join(docs_b)
            for leng in ("c", "rust"):
                if not hay(leng):
                    continue
                binario = compilar(carpeta, leng)
                res, _ = ejecutar(binario, lote, ["--lote"])
                malos = [i for i, (a, b) in enumerate(zip(ref, res)) if a != _clave(b)]
                if malos or len(res) != len(ref):
                    i = malos[0] if malos else -1
                    print(f"   DIF {leng} esquema {n} doc {docs_b[i][:90]!r}\n     python {str(ref[i])[:400]}\n     nativo {str(_clave(res[i]) if i >= 0 else len(res))[:400]}")
                chequear(f"esquema {n}: {leng} = Python en {len(ref)} documentos", not malos and len(res) == len(ref))
                res1, _ = ejecutar(binario, b"\x1e".join(docs_b[:200]), ["--lote", "--bloque", "1", "--parar"])
                chequear(f"esquema {n}: {leng} con bloques de 1 byte y fallo temprano",
                         [_clave(x) for x in res1] == ref_parar)
            if n == 0:
                r, _ = ejecutar(binario, "[" * 50 + "]" * 50, ["--prof", "10"]) if hay("c") or hay("rust") else (None, None)
                if r:
                    chequear("limite de profundidad en el nativo", r["limite"] == "profundidad")
                    r, _ = ejecutar(binario, '{"id":7,"tags":["a","b"]}', ["--max-bytes", "10"])
                    chequear("limite de tamano en el nativo", r["limite"] == "tamano")
                for leng in ("c", "rust"):
                    if hay(leng):
                        nat = Nativo(compilar(carpeta, leng, biblioteca=True))
                        iguales = all(_clave(nat.validar(d, bloque=7)) == r0 for d, r0 in zip(docs_b[:300], ref[:300]))
                        chequear(f"FFI ({leng}): la biblioteca llamada desde Python da lo mismo", iguales)
                if hay("c"):
                    try:
                        cuenta = compilar(carpeta, "c", contar=True)
                        _, met = ejecutar(cuenta, lote, ["--lote", "--metricas", "--silencio"])
                        chequear("C: 0 asignaciones de memoria al validar", met["asignaciones"] == 0)
                    except RuntimeError:
                        print("  (sin libc estatica: no se cuenta malloc)")
                if hay("rust"):
                    _, met = ejecutar(compilar(carpeta, "rust"), lote, ["--lote", "--metricas", "--silencio"])
                    chequear("Rust: 0 asignaciones de memoria al validar", met["asignaciones"] == 0)
        # el texto del esquema no puede colarse como codigo
        malo = '{"properties":{"*/ int main(){} /*":{"type":"string"},"\\"; system(\\"x\\"); //":{"const":"*/"}}}'
        T = generar(malo, os.path.join(tmp, "iny"))
        fuente = open(os.path.join(tmp, "iny", "validador.c"), encoding="utf-8").read()
        chequear("sin inyeccion: el esquema no aparece como texto en el C",
                 'system("x")' not in fuente and "int main(){}" not in fuente and fuente.count("*/ int") == 0)
        if hay("c"):
            b = compilar(os.path.join(tmp, "iny"), "c")
            r, _ = ejecutar(b, '{"*/ int main(){} /*": 5}')
            chequear("el esquema hostil compila y valida", r["valido"] is False and r["errores"][0]["codigo"] == "tipo")
            # limite documentado: una clave NO declarada repetida solo la detecta el interprete
            c = A.compilar_esquema('{"type":"object"}')
            r, _ = ejecutar(compilar(os.path.join(tmp, "e9"), "c") if generar('{"type":"object"}', os.path.join(tmp, "e9")) else "", '{"x":1,"x":2}')
            chequear("clave no declarada repetida: Python la detecta, el nativo no (documentado)",
                     r["valido"] and not A.validar(c, '{"x":1,"x":2}').valido)
    print(f"\n  Pruebas: {ok} de {total} pasaron")
    return ok == total


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        correr_pruebas()
    else:
        carpeta = a[a.index("-o") + 1] if "-o" in a else "generado"
        T = generar(open(a[0], encoding="utf-8").read(), carpeta)
        print(f"  escritos {carpeta}/validador.c, validador.rs y tablas.json")
        print(f"  DPDA: {len(T['estados'])} estados, {len(T['filas'])} filas, {len(T['gamma'])} simbolos de pila")
        print("  compilar:  gcc -O2 -o validador validador.c -lm")
        print("             rustc -O --edition 2021 -o validador_rs validador.rs")

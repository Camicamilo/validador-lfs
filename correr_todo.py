r"""
correr_todo.py - Corre TODAS las pruebas del proyecto, fase por fase

Uso:  python correr_todo.py
"""
import sys
import os
import re
import time
import subprocess

AQUI = os.path.dirname(os.path.abspath(__file__))
SUITES = [("Fase 1  lexer (AFD)", ["lexer_v4.py"]), ("Fase 2  parser (GLC)", ["parser_v2.py"]),
          ("Fase 3  semantico", ["semantico_v1.py"]), ("Fase 4  DPDA ponderado (JSON)", ["automata_v2.py"]),
          ("Fase 4  DPDA para XML (DTD y XSD)", ["xml_v1.py"]), ("Fase 5  generador de C y Rust", ["generador_v1.py"]),
          ("Fase 5  generador de payloads", ["payloads_v1.py"]), ("Fase 6  tiempo real e instrumentacion", ["tiempo_real_v1.py"]),
          ("Casos de prueba (coleccion local)", ["casos_v1.py"]), ("Fase 7  aplicacion web", ["prueba_app.py"])]

if __name__ == "__main__":
    todo_bien, t_total = True, time.time()
    print(f"  {'suite':<40}{'pasaron':>12}{'segundos':>10}")
    for nombre, cmd in SUITES:
        t0 = time.time()
        r = subprocess.run([sys.executable] + cmd, cwd=AQUI, capture_output=True, text=True, encoding="utf-8", errors="replace")
        m = re.findall(r"Pruebas: (\d+) de (\d+) pasaron", r.stdout)
        if m:
            a, b = m[-1]
            bien = a == b
            print(f"  {nombre:<40}{a + ' de ' + b:>12}{time.time() - t0:>10.1f}" + ("" if bien else "   <-- REVISAR"))
        else:
            bien = False
            print(f"  {nombre:<40}{'no corrio':>12}{time.time() - t0:>10.1f}   <-- " + (r.stdout + r.stderr).strip().splitlines()[-1][:90])
        todo_bien = todo_bien and bien
    print(f"\n  {'TODO PASA' if todo_bien else 'HAY FALLAS'}  ({time.time() - t_total:.0f} s en total)")

"""ejemplos.py - Ejemplos que carga la aplicacion web (tipo, esquema, documento)."""
import xml_v1 as X
import automata_v2 as A

EJEMPLOS = {
    "JSON: enunciado (valido)": ("json",
        '{\n  "type": "object",\n  "properties": {\n    "id":   {"type": "integer"},\n'
        '    "tags": {"type": "array", "items": {"type": "string"}}\n  },\n  "required": ["id"]\n}',
        '{"id": 7, "tags": ["a"]}'),
    "JSON: enunciado (invalido)": ("json",
        '{\n  "type": "object",\n  "properties": {\n    "id":   {"type": "integer"},\n'
        '    "tags": {"type": "array", "items": {"type": "string"}}\n  },\n  "required": ["id"]\n}',
        '{"tags": [5]}'),
    "JSON: mal formado (falta una coma)": ("json",
        '{"type":"object","properties":{"id":{"type":"integer"}}}', '{"id": 7 "x": 1}'),
    "JSON: rangos, enum y additionalProperties": ("json",
        '{\n  "type": "object",\n  "properties": {\n    "nombre": {"type": "string", "minLength": 2, "maxLength": 10},\n'
        '    "edad":   {"type": "integer", "minimum": 0, "maximum": 120},\n'
        '    "rol":    {"enum": ["admin", "user"]},\n'
        '    "notas":  {"type": "array", "items": {"type": "number"}, "maxItems": 3}\n  },\n'
        '  "required": ["nombre", "edad"],\n  "additionalProperties": false\n}',
        '{"nombre": "A", "edad": 150, "rol": "root", "notas": [1, 2, 3, 4], "extra": true}'),
    "JSON: recursivo con $ref (arbol)": ("json",
        '{\n  "$defs": {\n    "nodo": {\n      "type": "object",\n      "properties": {\n'
        '        "valor": {"type": "integer"},\n        "hijos": {"type": "array", "items": {"$ref": "#/$defs/nodo"}}\n'
        '      },\n      "required": ["valor"]\n    }\n  },\n  "$ref": "#/$defs/nodo"\n}',
        '{"valor": 1, "hijos": [{"valor": 2}, {"valor": 3, "hijos": [{"valor": "x"}]}]}'),
    "JSON: palabra roja (uniqueItems)": ("json",
        '{"type": "array", "items": {"type": "string"}, "uniqueItems": true, "minItems": 1}',
        '["a", "a"]'),
    "XML + DTD: biblioteca (valido)": ("dtd", X.DTD_EJ,
        '<?xml version="1.0"?>\n<biblioteca>\n  <libro id="1" estado="nuevo">\n    <titulo>Automatas</titulo>\n'
        '    <autor>Brena</autor>\n    <anio>2003</anio>\n    <resumen>Un <b>buen</b> libro</resumen>\n'
        '    <nota/>\n  </libro>\n</biblioteca>'),
    "XML + DTD: biblioteca (invalido)": ("dtd", X.DTD_EJ,
        '<biblioteca>\n  <libro estado="viejo">\n    <autor>Brena</autor>\n    <titulo>Automatas</titulo>\n'
        '    <nota>texto</nota>\n  </libro>\n</biblioteca>'),
    "XML: mal formado (cierre cruzado)": ("dtd", X.DTD_EJ,
        '<biblioteca><libro id="1"><titulo>A</autor></libro></biblioteca>'),
    "XML + XSD: pedido (valido)": ("xsd", X.XSD_EJ,
        '<pedido id="7" moneda="COP">\n  <cliente>Ana</cliente>\n  <item sku="A1">\n    <nombre>pan</nombre>\n'
        '    <cantidad>2</cantidad>\n    <precio>3.5</precio>\n  </item>\n  <urgente/>\n</pedido>'),
    "XML + XSD: pedido (invalido)": ("xsd", X.XSD_EJ,
        '<pedido id="siete" moneda="EUR">\n  <cliente>Ana</cliente>\n  <item>\n    <nombre>p</nombre>\n'
        '    <cantidad>0</cantidad>\n    <precio>5000</precio>\n  </item>\n</pedido>'),
    "XML + DTD: <!ENTITY> rechazada (seguridad)": ("dtd",
        '<!ENTITY risa "jajaja">\n<!ELEMENT chiste (#PCDATA)>', '<chiste>&risa;</chiste>'),
}

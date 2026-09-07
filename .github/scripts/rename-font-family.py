#!/usr/bin/env python3
"""Rewrite every "name" table string in a font that contains OLD_SUBSTR,
replacing OLD_SUBSTR with NEW_SUBSTR (e.g. to fix a font whose family name
doesn't match the name a document expects).

Usage: rename-font-family.py <old-substr> <new-substr> <in-file> <out-file>
"""

import sys

from fontTools.ttLib import TTFont

old_substr, new_substr, path_in, path_out = sys.argv[1:5]

font = TTFont(path_in)
name_table = font["name"]

for record in list(name_table.names):
    old = record.toUnicode()
    if old_substr in old:
        new = old.replace(old_substr, new_substr)
        name_table.setName(new, record.nameID, record.platformID, record.platEncID, record.langID)

font.save(path_out)

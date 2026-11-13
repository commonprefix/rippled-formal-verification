#!/usr/bin/env python3
"""Branch coverage report: manifest from instrument.py + stderr of an instrumented xrpld run."""
import json
import re
import sys
from collections import defaultdict

manifest = json.load(open(sys.argv[1]))
hits = set()
for line in open(sys.argv[2], errors="replace"):
    for m in re.finditer(r"COV (\d+)", line):
        hits.add(int(m.group(1)))

by_file = defaultdict(list)
for m in manifest:
    by_file[m["file"]].append(m)

branch_total = branch_hit = entry_total = entry_hit = 0
rows = []
unhit = defaultdict(list)
unentered = defaultdict(list)
for f, ms in sorted(by_file.items()):
    bt = bh = et = eh = 0
    for m in ms:
        if m["kind"] == "entry":
            et += 1
            if m["id"] in hits:
                eh += 1
            else:
                unentered[f].append(m)
        else:
            bt += 1
            if m["id"] in hits:
                bh += 1
            else:
                unhit[f].append(m)
    branch_total += bt
    branch_hit += bh
    entry_total += et
    entry_hit += eh
    rows.append((f, bt, bh, et, eh))

print("# Lean model branch coverage\n")
print(f"Branch arms hit: {branch_hit}/{branch_total} ({100.0 * branch_hit / max(1, branch_total):.1f}%)")
print(f"Do-block entries hit: {entry_hit}/{entry_total}\n")
print("| File | Arms | Hit | % | Entries hit |")
print("|---|---|---|---|---|")
for f, bt, bh, et, eh in rows:
    pct = f"{100.0 * bh / bt:.0f}%" if bt else "-"
    print(f"| {f.replace('XRPL/Model/', '')} | {bt} | {bh} | {pct} | {eh}/{et} |")

print("\n## Branch arms never hit\n")
for f, ms in sorted(unhit.items()):
    print(f"### {f.replace('XRPL/Model/', '')}")
    for m in ms:
        print(f"- L{m['line']} ({m['kind']}): `{m['text'][:110]}`")
    print()

if unentered:
    print("\n## Do-blocks never entered\n")
    for f, ms in sorted(unentered.items()):
        for m in ms:
            print(f"- {f.replace('XRPL/Model/', '')} L{m['line']}: `{m['text'][:100]}`")

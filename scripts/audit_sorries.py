#!/usr/bin/env python3
"""List the open proof obligations (`sorry`) and forbidden escape hatches in EntropyLean/."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"^\s*(axiom|opaque|unsafe)\b|\bnative_decide\b|\badmit\b")
bad = False
total = 0
for path in sorted((root / "EntropyLean").glob("*.lean")):
    text = path.read_text()
    # drop block and line comments before scanning
    code = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    code = re.sub(r"--.*", "", code)
    lines = code.splitlines()
    hits = [i for i, line in enumerate(lines, 1) if re.search(r"\bsorry\b", line)]
    total += len(hits)
    print(f"{path.name}: {len(hits)} open proof obligations"
          + (f" (lines {', '.join(map(str, hits))})" if hits else ""))
    for i, line in enumerate(lines, 1):
        if FORBIDDEN.search(line):
            print(f"  FORBIDDEN at {path.name}:{i}: {line.strip()}")
            bad = True
print(f"total: {total}")
sys.exit(1 if bad else 0)

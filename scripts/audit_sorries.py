#!/usr/bin/env python3
from pathlib import Path
root = Path(__file__).resolve().parents[1]
for path in sorted((root / 'EntropyLean').glob('*.lean')):
    lines = [(i, line.strip()) for i, line in enumerate(path.read_text().splitlines(), 1)
             if line.strip() == 'sorry']
    print(f'{path.name}: {len(lines)} open proof obligations' +
          (f' (lines {", ".join(str(n) for n, _ in lines)})' if lines else ''))

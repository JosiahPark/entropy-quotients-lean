import re, glob, collections
stats = []; refs = collections.Counter()
files = sorted(glob.glob('/workspace/entropy-quotients-lean/EntropyLean/*.lean'))
alltext = {f: open(f).read() for f in files}
for f, t in alltext.items():
    for m in re.finditer(r'^(theorem|lemma)\s+(\S+)(.*?)(?=^(?:theorem|lemma|noncomputable def|def|structure|end |/--|omit|section|namespace|open|variable|attribute)\b|\Z)', t, re.S | re.M):
        name = m.group(2); body = m.group(3)
        proof = body.split(':=', 1)[1] if ':=' in body else ''
        lines = [l for l in proof.strip().splitlines() if l.strip() and not l.strip().startswith('--')]
        if lines and lines[0].strip() == 'by': lines = lines[1:]
        stats.append((f.split('/')[-1], name, len(lines), proof.strip()[:60].replace('\n', ' ')))
big = ' '.join(alltext.values())
short = [s for s in stats if s[2] <= 1]
unref = [s for s in stats if len(re.findall(r'\b' + re.escape(s[1].split('.')[-1]) + r'\b', big)) <= 1]
print('theorems:', len(stats), ' <=1-line proofs:', len(short), ' never referenced elsewhere:', len(unref))
rfl = [s for s in stats if re.match(r'^(by\s+)?(rfl|trivial|simp|exact rfl)\s*$', s[3])]
print('rfl/trivial/simp-only proofs:', len(rfl), [s[1] for s in rfl][:20])
for fn in ['MartonStep.lean', 'SparsePosterior.lean']:
    print(fn, [(s[1], s[2]) for s in stats if s[0] == fn])

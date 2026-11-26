# Untrusted preprocessor: JSONL certificate -> preorder token stream read by Davidson/Checker.lean.
# Format (whitespace separated integers), node := nU (k p q)*nU nL (k p q)*nL nKids (tau node)*nKids
# The Lean soundness theorem quantifies over every tree, so nothing here needs to be trusted.
import sys, json, gzip
from fractions import Fraction as Fr
src, dst = sys.argv[1], sys.argv[2]
nodes = {}; order = []
with gzip.open(src, 'rt') as fh:
    for line in fh:
        e = json.loads(line); key = tuple(e['w'])
        assert e['t'] == 'I'
        nodes[key] = e; order.append(key)
kids = {k: [] for k in order}
for k in order:
    if k: kids[k[:-1]].append(k)
out = []
def ys(d):
    items = sorted((int(k), Fr(v)) for k, v in d.items())
    toks = [str(len(items))]
    for k, v in items:
        toks += [str(k), str(v.numerator), str(v.denominator)]
    return ' '.join(toks)
stack = [((), None)]
while stack:
    key, t = stack.pop()
    e = nodes[key]
    pre = '' if t is None else str(t) + ' '
    out.append(pre + ys(e['yu']) + ' ' + ys(e['yl']) + ' ' + str(len(kids[key])))
    for c in reversed(kids[key]):
        stack.append((c, c[-1]))
with open(dst, 'w') as fh:
    fh.write('\n'.join(out) + '\n')
print('nodes', len(order))

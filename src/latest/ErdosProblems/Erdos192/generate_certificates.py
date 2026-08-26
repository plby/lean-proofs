"""Generate untrusted data; every certificate is checked by the Lean kernel."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
text = (ROOT / 'Core.lean').read_text()
word = list(map(int, re.findall(r'\d+', text.split('def keranenG₀')[1]
    .split(':=')[1].split('private')[0])))
assert len(word) == 85
weights = [-701, -531, 4059, -2316]
prefixes = []
for a in range(4):
    row = [0]
    for c in word:
        row.append(row[-1] + weights[(a + c) % 4])
    prefixes.append(row)

modulus = 43435
def mask(values):
    result = 0
    for v in values:
        result |= 1 << v
    return result

positive = [mask(v % modulus for v in row[:85]) for row in prefixes]
negative = [mask(-v % modulus for v in row[:85]) for row in prefixes]
out = 'import ErdosProblems.Erdos192.BoundaryFast\nimport ErdosProblems.Erdos192.Bitset\n\nnamespace Erdos192\n\n'
for name, data in [('positiveMasks', positive), ('negativeMasks', negative)]:
    out += 'def ' + name + ' : Array Nat :=\n  #[' + ',\n    '.join(hex(x) for x in data) + ']\n\n'
rows = []
total = 0
for a in range(4):
    for b in range(4):
        for e in range(4):
            entries = []
            for s in range(85):
                candidates = [r for r in range(85) if
                    (prefixes[a][r] + prefixes[e][(2*s-r) % 85] -
                     2*prefixes[b][s]) % modulus == 0]
                total += len(candidates)
                entries.append('[' + ', '.join(map(str, candidates)) + ']')
            rows.append('    #[' + ', '.join(entries) + ']')
out += 'def boundaryCandidates : Array (Array (List Nat)) :=\n  #[\n' + ',\n'.join(rows) + '\n  ]\n\n'
out += 'end Erdos192\n'
(ROOT / 'BoundaryMaskData.lean').write_text(out)
print(f'{total} boundary candidates in {len(rows)} rows')

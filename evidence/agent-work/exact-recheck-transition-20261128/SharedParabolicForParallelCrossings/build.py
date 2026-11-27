import json
from pathlib import Path
d = json.loads(Path('context.json').read_text())
item = d['item']
opening = ''.join(f'import {module}\n' for module in
    d['input']['imports'] + [f'Proofs.{dep}' for dep in item['deps']])
support = Path('support.txt')
Path('Check.lean').write_text(opening + '\nset_option maxHeartbeats 2000000\n\n' +
    (support.read_text() + '\n\n' if support.exists() else '') +
    f"theorem {item['id']} : (\n{d['translation']['type']}\n) :=\n" +
    f"({Path('proof.txt').read_text().rstrip()})\n\n#print axioms {item['id']}\n")

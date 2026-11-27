import json
from pathlib import Path
data=json.load(open('context.json'))
ids=[i['id'] for i in data['plan']['items']]
template=Path('InspectTemplate.txt').read_text()
for n in range(0,len(ids),40):
 batch=ids[n:n+40]
 Path(f'Inspect{n//40}.lean').write_text('import Lean\n'+''.join(f'import Proofs.{i}\n' for i in batch)+template+''.join(f'#inspect {i}\n' for i in batch))

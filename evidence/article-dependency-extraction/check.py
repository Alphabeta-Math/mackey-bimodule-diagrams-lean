"""Check extracted compiled references and local source imports, without granting review credit."""
from pathlib import Path
import datetime
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
state_hash = sha(ROOT / 'state.json')
state = json.loads((ROOT / 'state.json').read_text())
items = {i['id']: i for i in state['plan']['items']}

def dependencies(name, seen=None):
    seen = set() if seen is None else seen
    for dep in items[name]['deps']:
        if dep not in seen:
            seen.add(dep)
            dependencies(dep, seen)
    return seen

main = {n for n, i in items.items() if i['main']}
required = main | set().union(*(dependencies(n) for n in main))
assert all(n in state['proved'] for n in required)
assert (ROOT / 'lean-toolchain').read_text().strip() == state['input']['lean']
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
assert any(p['name'] == 'mathlib' and p.get('rev') == state['input']['mathlib'] for p in manifest['packages'])

refs = {}
current = None
for line in (HERE / 'current-graph-audit.tsv').read_text().splitlines():
    assert 'error:' not in line and line not in ('NO BODY', 'MISSING'), line
    t = line.split('\t')
    if len(t) == 2 and t[0] == 'BEGIN':
        current = t[1]
        assert current not in refs
        refs[current] = set()
    elif len(t) == 5 and current and t[1] in items and t[1] != current:
        refs[current].add(t[1])
assert set(refs) == required
missing = [(n, d) for n, ds in refs.items() for d in ds - dependencies(n)]
assert not missing, missing

axiom_text = (HERE / 'current-axioms-audit.log').read_text()
assert 'sorryAx' not in axiom_text and 'error:' not in axiom_text
axioms = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_text):
    axioms[m[1]] = [a.strip() for a in m[2].split(',') if a.strip()]
for m in re.finditer(r"'([^']+)' does not depend on any axioms", axiom_text):
    axioms[m[1]] = []
assert set(axioms) == required
snapshots = {}
for n in sorted(required):
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    source_claim = items[n].get('article') or items[n].get('portal') or {}
    if re.search(r'\bno choice (?:is|are) used\b', source_claim.get('statement', ''), re.I):
        allowed.remove('Classical.choice')
    assert set(axioms[n]) <= allowed, n
    src = ROOT / 'Proofs' / (n + '.lean')
    obj = ROOT / '.lake/build/lib/lean/Proofs' / (n + '.olean')
    receipt_file = ROOT / 'evidence' / (n + '-compile.json')
    receipt = json.loads(receipt_file.read_text())
    assert sha(src) == state['proved'][n] == receipt['source_sha256'], n
    assert receipt['ok'] and receipt['build']['code'] == receipt['axioms']['code'] == 0, n
    assert sha(obj) == receipt['olean_sha256'], n
    snapshots[n] = {'source_sha256': sha(src), 'olean_sha256': sha(obj), 'receipt_sha256': sha(receipt_file)}

modules = {}
active = set()
external_prefixes = {'Mathlib', 'Lean', 'Init', 'Batteries', 'Aesop', 'Qq', 'Plausible', 'ProofWidgets'}
def imports(module):
    if module in active:
        raise AssertionError('Local source import cycle: ' + module)
    if module in modules or module.split('.')[0] in external_prefixes:
        return
    file = ROOT.joinpath(*module.split('.')).with_suffix('.lean')
    assert file.is_file(), 'Unresolved local source: ' + module
    assert module not in {'Proofs.WattsFreePresentation', 'Proofs.ProjectiveGeneratorModuleReconstruction'}
    active.add(module)
    deps = []
    for line in file.read_text().splitlines():
        m = re.match(r'^\s*(?:public\s+)?import\s+(.+)', line)
        if m:
            text = m[1].split('--', 1)[0].strip()
            assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*(?:\s+[A-Za-z_][A-Za-z0-9_.]*)*', text), line
            deps.extend(text.split())
    for dep in deps:
        imports(dep)
    active.remove(module)
    modules[module] = {'source_sha256': sha(file), 'imports': deps}
for n in sorted(required):
    imports('Proofs.' + n)
assert state_hash == sha(ROOT / 'state.json'), 'State changed during audit'
report = {
    'timestamp_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Mechanical compiled named-supplier, source-import, source/artifact/receipt and fresh axiom checks. This does not replace the unfinished coordinator review.',
    'coordinator_review_complete': False,
    'article_count': len(main), 'checked_proof_count': len(required),
    'excluded_auxiliaries': sorted(set(items) - required),
    'named_supplier_references': {n: sorted(ds) for n, ds in sorted(refs.items())},
    'missing_named_suppliers': missing,
    'source_import_graph_acyclic': True,
    'open_auxiliary_imports': [],
    'axioms': axioms, 'snapshots': snapshots, 'local_source_modules': modules,
    'audit_files': {p.name: sha(p) for p in [HERE / 'GraphAudit.lean', HERE / 'AxiomsAudit.lean', HERE / 'current-graph-audit.tsv', HERE / 'current-axioms-audit.log']},
}
(HERE / 'mechanical-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(f"Passed: {len(main)} article statements; {len(required)} proof sources/artifacts/receipts and fresh axiom audits; {len(modules)} local source modules; no missing named suppliers or open-auxiliary imports.")

#!/usr/bin/env python3
"""Offline source/diagnostic regression check. This does not run Lean."""
from pathlib import Path
import ast, json, hashlib, zipfile

repo=Path(__file__).resolve().parent.parent
code=(repo/'validation/run_controls.py').read_text()
frozen=(repo/'provenance/FROZEN_run_controls.py').read_text()

def forbidden_tokens(source):
    node=ast.parse(source)
    a=next(n for n in node.body if isinstance(n, ast.Assign) and any(isinstance(t,ast.Name) and t.id=='forbidden' for t in n.targets))
    return ast.literal_eval(a.value)

def evaluated(source, rel, exit_code, output, positive=False):
    bad=forbidden_tokens(source)
    return exit_code==0 if positive else (exit_code==1 and rel+':' in output and 'error:' in output and not any(s in output.lower() for s in bad))

legit_rel='validation/controls_angular/RejectConjugation.lean'
legit=f'{legit_rel}:3:46: error: unsolved goals\n⊢ -I = I\n'
missing=f'{legit_rel}:1:1: error: failed to read file /tmp/missing/KN.olean\n'
assert evaluated(code,legit_rel,1,legit)
assert evaluated(frozen,legit_rel,1,legit)
assert evaluated(frozen,legit_rel,1,missing), 'The original weakness was not reproduced'
assert not evaluated(code,legit_rel,1,missing), 'Missing-object error was counted as a good negative'
for marker in ['unknown module','file not found','object file','no such file or directory','failed to import','could not find module']:
    assert not evaluated(code,legit_rel,1,f'{legit_rel}:1:1: error: {marker} KN\n'),marker
assert evaluated(code,legit_rel,0,'',positive=True)
assert not evaluated(code,legit_rel,1,legit,positive=True)

# Replay captured original Codex author controls (no Lean execution) if reference ZIP is present next to package.
external=Path('/mnt/data/KN_UHP_C002_CODEX_INDEPENDENT_AUDIT_REPRODUCIBILITY_20261022.zip')
count=0
if external.exists():
    with zipfile.ZipFile(external) as z:
        root='KN_UHP_C002_CODEX_AUDIT_REPRODUCIBILITY_20261022/independent/main/logs/all_author_controls/'
        x=json.loads(z.read(root+'summary.json'))
        for rec in x['cases']:
            log=z.read(root+rec['log']).decode(errors='replace')
            ok=evaluated(code,rec['source'],rec['exit_code'],log,rec['expected']=='pass')
            assert ok == rec['passed'], rec['source']
            assert ok, rec['source']
            count+=1
assert count in (0,30)
print(json.dumps({'static_regressions':'PASS','archived_case_replay_count':count,'note':'No native Lean execution in this environment'},indent=2))

#!/usr/bin/env python3
"""Portable frozen author contract controls, never an independent adversarial audit."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', type=Path, required=True)
p.add_argument('--lean-bin-dir', type=Path, required=True)
p.add_argument('--results', type=Path, required=True)
a = p.parse_args()
root, out = a.project.resolve(), a.results.resolve()
out.mkdir(parents=True, exist_ok=False)
env = os.environ.copy()
env['PATH'] = str(a.lean_bin_dir.resolve()) + os.pathsep + env.get('PATH','')
positive = {'Positive','PositiveControls','Counterexamples','SignedChargeAndSpin'}
forbidden = ['unknown module', 'object file', 'unknown package', 'file not found', 'failed to synthesize instance']
records=[]
for src in sorted((root/'validation').glob('controls_*/*.lean')):
    rel = src.relative_to(root).as_posix()
    expect = src.stem in positive
    argv = [str(a.lean_bin_dir.resolve()/'lake'),'env','lean','-j1','-DwarningAsError=true',rel]
    start = time.monotonic()
    try:
        run = subprocess.run(argv,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300)
        code, output = run.returncode, run.stdout
    except subprocess.TimeoutExpired as exc:
        code, output = 124, str(exc)
    # Negative success requires a diagnostic in the intended fixture, not failed imports/runtime.
    correct = code == 0 if expect else (code == 1 and rel+':' in output and 'error:' in output
        and not any(bad in output.lower() for bad in forbidden))
    if expect and 'sorryAx' in output:
        correct=False
    name = src.parent.name+'_'+src.stem
    log=out/(name+'.log')
    log.write_text(output)
    record={'source':rel,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
            'argv':argv,'exit_code':code,'expected':'pass' if expect else 'reject',
            'passed':correct,'seconds':time.monotonic()-start,
            'log':log.name,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
    records.append(record)
    print(name,code,'PASS' if correct else 'FAIL',flush=True)
summary={'category':'author controls, not independent audits','timestamp_utc':datetime.now(timezone.utc).isoformat(),
         'all_pass':bool(records) and all(r['passed'] for r in records),'cases':records}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
raise SystemExit(0 if summary['all_pass'] else 1)

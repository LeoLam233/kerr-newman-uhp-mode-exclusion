#!/usr/bin/env python3
"""Author regression controls, not independent adversarial audits."""
import json, os, pathlib, subprocess, sys, datetime
root = pathlib.Path(__file__).resolve().parents[2]
out = root / 'reports/radial_controls'
out.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['PATH'] = '/workspace/scratch/e6e0818fcb8f/ht_cloud_toolchain/lean-4.34.1-linux/bin:' + env['PATH']
cases = [('Positive', True), ('MissingDelta', False), ('WrongDeltaSign', False), ('PoleAsNonresonant', False), ('OneChiralBlock', False), ('BoundaryWithoutEquation', False), ('SwappedHorizonWeight', False)]
expected_diagnostics = {
 'MissingDelta': 'Type mismatch', 'WrongDeltaSign': 'Type mismatch',
 'PoleAsNonresonant': '⊢ False', 'OneChiralBlock': 'Application type mismatch',
 'BoundaryWithoutEquation': 'OriginalSelectedPair',
 'SwappedHorizonWeight': 'Application type mismatch',
}
results = []
for name, expected_success in cases:
    cmd = ['lake','env','lean','-j1','-DwarningAsError=true',f'validation/controls_radial/{name}.lean']
    p = subprocess.run(cmd,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (out / (name + '.log')).write_text('$ ' + ' '.join(cmd) + '\n' + p.stdout + f'\nEXIT_CODE={p.returncode}\n')
    passed = (p.returncode == 0) == expected_success
    if not expected_success:
        passed = passed and expected_diagnostics[name] in p.stdout
    else:
        passed = passed and 'sorryAx' not in p.stdout
    results.append(dict(name=name,expected_success=expected_success,exit_code=p.returncode,passed=passed))
    print(name, 'PASS' if passed else 'FAIL', flush=True)
(out/'summary.json').write_text(json.dumps(dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),category='author regression controls, not independent audits',results=results),indent=2)+'\n')
sys.exit(0 if all(r['passed'] for r in results) else 1)

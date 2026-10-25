#!/usr/bin/env python3
"""Author contract controls, not one of the required independent audits."""
import datetime, hashlib, json, os, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / 'reports/energy_controls'
OUT.mkdir(parents=True, exist_ok=True)
PIN = '/workspace/scratch/e6e0818fcb8f/ht_cloud_toolchain/lean-4.34.1-linux/bin'
env = dict(os.environ, PATH=PIN+':'+os.environ.get('PATH',''))
cases = [('Counterexamples',True),('SignedChargeAndSpin',True),
 ('RejectNonUHP',False),('RejectNegativeK',False),('RejectWrongWeightDomain',False),
 ('RejectUnsignedSpin',False),('RejectMissingCorrection',False),
 ('RejectVanishingCorrectionDenominator',False),('RejectNoOriginalHorizon',False),
 ('RejectUnboundedAngularAverage',False)]
markers = {
 'RejectMissingCorrection': ['Type mismatch', 'deltaValue 0 1', 'but is expected'],
 'RejectNoOriginalHorizon': ['Tactic `assumption` failed', 'HorizonRegular', 'high', 'low'],
}
results=[]
for name, expected in cases:
    src=ROOT / 'validation/controls_energy' / (name+'.lean')
    cmd=['lake','env','lean','-j1','-DwarningAsError=true',str(src.relative_to(ROOT))]
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
    log=OUT/(name+'.log');log.write_text(p.stdout)
    passed=(p.returncode==0)==expected
    if not expected:
        required=markers.get(name, ['unsolved goals', '⊢ False'])
        passed=passed and 'error:' in p.stdout and all(m in p.stdout for m in required)
        passed=passed and 'object file' not in p.stdout and 'unknown module' not in p.stdout
    row=dict(name=name,expected='compile-pass' if expected else 'compile-fail',
      command=cmd,started_utc=started,exit_code=p.returncode,matched_expectation=passed,
      source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),log=str(log.relative_to(ROOT)))
    results.append(row)
    print(name,p.returncode,'PASS' if passed else 'UNEXPECTED',flush=True)
(OUT/'results.json').write_text(json.dumps(results,indent=2)+'\n')
sys.exit(0 if all(r['matched_expectation'] for r in results) else 1)

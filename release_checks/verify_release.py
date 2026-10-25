#!/usr/bin/env python3
"""Verify publication derivative against the frozen 342-file mathematical/Lean source manifest."""
import hashlib, json, sys, importlib.util
from pathlib import Path
repo=Path(sys.argv[1] if len(sys.argv)>1 else '.').resolve()
orig=json.loads((repo/'provenance/ORIGINAL_SOURCE_MANIFEST.json').read_text())
mod=repo/'validation/source_identity.py'
spec=importlib.util.spec_from_file_location('kn_source_identity',mod)
src=importlib.util.module_from_spec(spec);spec.loader.exec_module(src)
now=src.snapshot(repo)
changes=sorted(f for f in orig['files'] if now['files'].get(f)!=orig['files'][f])
extra=sorted(set(now['files'])-set(orig['files']))
missing=sorted(set(orig['files'])-set(now['files']))
assert len(orig['files'])==342
assert changes==['README.md','validation/run_controls.py'],changes
assert not extra,extra
assert not missing,missing
assert now['source_id']!=orig['source_id']
assert all(orig['files'][f]==now['files'][f] for f in orig['files'] if f.endswith('.lean'))
assert all(orig['files'][f]==now['files'][f] for f in orig['files'] if f.startswith('manuscript/'))
assert hashlib.sha256((repo/'provenance/FROZEN_run_controls.py').read_bytes()).hexdigest()==orig['files']['validation/run_controls.py']
print(json.dumps({'status':'PASS','frozen_source_id':orig['source_id'],'release_source_id':now['source_id'],'frozen_files':len(orig['files']),'changed':changes,'new_source_scope_files':extra,'lean_and_manuscript_unchanged':True},indent=2))

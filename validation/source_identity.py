#!/usr/bin/env python3
"""Identity of KN production source, pins, and verification scripts (not caches)."""
import hashlib
import json
from pathlib import Path

def sha256(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def snapshot(project):
    project = Path(project)
    selected = [project / n for n in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'KN.lean', 'AuditKN.lean')]
    selected += list((project / 'KN').rglob('*.lean'))
    selected += [p for p in (project / 'validation').rglob('*') if p.is_file() and p.suffix in ('.py','.sh','.lean','.md')]
    selected += [project / n for n in ('EXTERNAL_INTERFACES.md','COVERAGE.md','README.md')]
    selected += [p for p in (project / 'manuscript').rglob('*') if p.is_file()]
    files = {p.relative_to(project).as_posix(): sha256(p) for p in sorted(selected) if p.is_file()}
    payload = json.dumps(files, sort_keys=True, separators=(',', ':')).encode()
    return {'source_id': hashlib.sha256(payload).hexdigest(), 'files': files}

def verify(project, expected):
    actual = snapshot(project)
    return {'pass': actual == expected, 'actual_source_id': actual['source_id'],
            'missing': sorted(set(expected['files']) - set(actual['files'])),
            'extra': sorted(set(actual['files']) - set(expected['files'])),
            'changed': [n for n in actual['files'] if n in expected['files'] and actual['files'][n] != expected['files'][n]]}

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('project', type=Path)
    a = p.parse_args()
    print(json.dumps(snapshot(a.project.resolve()), indent=2))

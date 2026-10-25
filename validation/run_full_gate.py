#!/usr/bin/env python3
"""Frozen clean KN build and DISTINCT official fresh kernel replay.
This author verification is not one of the three independent adversarial audits.
Never use the mutable development project as the --project argument.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import time
from source_identity import sha256, snapshot, verify

def write(p, x):
    p.write_text(json.dumps(x, indent=2) + '\n')

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, required=True)
    p.add_argument('--lean-bin-dir', type=Path, required=True)
    p.add_argument('--source-manifest', type=Path, required=True)
    p.add_argument('--expected-source-id', required=True)
    p.add_argument('--runtime-manifest', type=Path, required=True)
    p.add_argument('--results', type=Path, required=True)
    p.add_argument('--isolated-candidate', action='store_true', required=True)
    p.add_argument('--timeout', type=int, default=14400)
    a = p.parse_args()
    project, bindir, results = a.project.resolve(), a.lean_bin_dir.resolve(), a.results.resolve()
    results.mkdir(parents=True, exist_ok=False)
    expected = json.loads(a.source_manifest.read_text())
    env = os.environ.copy()
    for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_HOME','LAKE_PKG_URL_MAP'):
        env.pop(key, None)
    env['PATH'] = str(bindir) + os.pathsep + env.get('PATH','')
    env['LEAN_NUM_THREADS'] = '1'
    state = {'started_utc': datetime.now(timezone.utc).isoformat(), 'all_pass': False,
             'fresh_kernel_replay_pass': False, 'independent_adversarial_rounds': 0, 'stages': []}
    def stage(name, argv, cwd=project):
        start = time.monotonic()
        out, err = results / (name+'.stdout.log'), results / (name+'.stderr.log')
        with out.open('wb') as o, err.open('wb') as e:
            try:
                code = subprocess.run(argv, cwd=cwd, env=env, stdout=o, stderr=e, timeout=a.timeout).returncode
            except subprocess.TimeoutExpired:
                code = 124
        record = {'name': name, 'argv': argv, 'cwd': str(cwd), 'exit_code': code,
                  'seconds': time.monotonic()-start, 'stdout_sha256': sha256(out), 'stderr_sha256': sha256(err)}
        state['stages'].append(record)
        write(results/(name+'.json'), record)
        write(results/'summary.json', state)
        if code:
            raise RuntimeError('Stage failed: '+name)
        return out.read_text(errors='replace').strip()
    try:
        if expected['source_id'] != a.expected_source_id or not verify(project, expected)['pass']:
            raise RuntimeError('Frozen source identity mismatch')
        write(results/'source_before.json', snapshot(project))
        if not all((project/n).is_file() for n in ('KN.lean','AuditKN.lean','lean-toolchain','lakefile.toml','lake-manifest.json')):
            raise RuntimeError('Incomplete candidate roots or pins')
        build = project/'.lake/build'
        if build.exists() and any(build.rglob('*')):
            raise RuntimeError('Project build directory not empty; use a new clean candidate')
        for path in project.rglob('*.olean'):
            if '.lake/packages/' not in path.as_posix():
                raise RuntimeError('Pre-existing project object: '+str(path))
        binaries = {n: sha256(bindir/n) for n in ('lean','lake','leanchecker')}
        if binaries != json.loads(a.runtime_manifest.read_text()):
            raise RuntimeError('Pinned runtime binary hashes differ')
        state['runtime_hashes'] = binaries
        state['lean_version'] = stage('lean_version',[str(bindir/'lean'),'--version'])
        state['lake_version'] = stage('lake_version',[str(bindir/'lake'),'--version'])
        if (project/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
            raise RuntimeError('Toolchain pin mismatch')
        pins = json.loads((project/'lake-manifest.json').read_text())
        dependencies = []
        for pin in pins['packages']:
            dep = project/pins.get('packagesDir','.lake/packages')/pin['name']
            if pin['type'] != 'git' or not dep.is_dir() or dep.is_symlink():
                raise RuntimeError('Missing or shared dependency: '+pin['name'])
            head = stage('dep_'+pin['name']+'_head',['git','rev-parse','HEAD'],dep)
            dirty = stage('dep_'+pin['name']+'_tracked',['git','status','--porcelain','--untracked-files=no'],dep)
            other = stage('dep_'+pin['name']+'_untracked',['git','ls-files','--others','--exclude-standard'],dep)
            if head != pin['rev'] or dirty or any(x.endswith(('.lean','.toml','.json')) for x in other.splitlines()):
                raise RuntimeError('Dependency source mismatch: '+pin['name'])
            cache = dep/'.lake/build/lib/lean'
            if cache.exists() and any(cache.glob('KN*')):
                raise RuntimeError('KN namespace in dependency cache')
            dependencies.append({'name':pin['name'],'rev':head,'url':pin['url'],
                                 'cache_hashes': {x.relative_to(cache).as_posix():sha256(x) for x in sorted(cache.rglob('*')) if x.is_file()}})
        write(results/'dependencies_before.json', dependencies)
        lake = [str(bindir/'lake')]
        stage('complete_clean_build', lake+['-R','-H','build','KN','AuditKN'])
        stage('exact_types_and_axioms',lake+['env','lean','-j1','-DwarningAsError=true','AuditKN.lean'])
        stage('fresh_official_kernel_replay',lake+['env','leanchecker','--fresh','--verbose','KN'])
        state['fresh_kernel_replay_pass'] = True
        stage('author_negative_controls', [os.sys.executable, str(project/'validation/run_controls.py'),
              '--project', str(project), '--lean-bin-dir', str(bindir), '--results', str(results/'controls')])
        state['source_after'] = verify(project,expected)
        if not state['source_after']['pass']:
            raise RuntimeError('Production source changed during verification')
        state['all_pass'] = True
    except Exception as exc:
        state['failure'] = str(exc)
        state['source_after'] = verify(project,expected)
    finally:
        state['finished_utc'] = datetime.now(timezone.utc).isoformat()
        write(results/'summary.json',state)
    print(json.dumps(state,indent=2))
    return 0 if state['all_pass'] else 1

if __name__ == '__main__':
    raise SystemExit(main())

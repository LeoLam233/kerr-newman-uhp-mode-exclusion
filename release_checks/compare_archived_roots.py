#!/usr/bin/env python3
"""Compare the current AuditKN native output with its existing archived output."""
import hashlib
import json
import re
import sys
from pathlib import Path

base = Path(__file__).resolve().parent
baseline = json.loads((base / 'archived_root_baseline.json').read_text(encoding='utf-8'))
native_path = Path(sys.argv[1]).resolve()
native = native_path.read_text(encoding='utf-8')
parts = re.split(r"(?=^(?:KN\.|structure KN\.|'KN\.))", native, flags=re.M)
types, structures, axioms = {}, {}, {}
for block in parts:
    if not block.strip():
        continue
    if block.startswith("'KN."):
        match = re.match(r"'([^']+)' depends on axioms: \[(.*?)\]\s*$", block, re.S)
        if not match:
            raise ValueError('Unexpected axiom output: ' + block)
        axioms[match[1]] = sorted(re.sub(r'\.\{[^}]+\}', '', name.strip())
                                  for name in match[2].split(','))
    else:
        match = re.match(r'(?:structure )?(KN\.[A-Za-z0-9_.]+)', block)
        if not match:
            raise ValueError('Unexpected native output: ' + block)
        target = structures if block.startswith('structure ') else types
        target[match[1].rstrip('.')] = ' '.join(block.split())

checks = {}
for group, current in [('root_types', types), ('entry_structures', structures)]:
    checks[group] = {name: current.get(name) == expected['normalized']
                     for name, expected in baseline[group].items()}
checks['axioms'] = {name: axioms.get(name) == expected['canonical']
                    for name, expected in baseline['axioms'].items()}
all_pass = all(all(items.values()) for items in checks.values())
receipt = {'all_pass': all_pass, 'comparison': 'Native theorem types, entry structure outputs and custom/standard axiom sets against preserved successful Codex audit log',
           'native_output_sha256': hashlib.sha256(native_path.read_bytes()).hexdigest(),
           'archived_output_sha256': baseline['archive_log_sha256'],
           'archived_zip_sha256': baseline['archive_sha256'], 'checks': checks}
print(json.dumps(receipt, indent=2))
raise SystemExit(0 if all_pass else 1)

#!/usr/bin/env python3
"""Validate native author controls against the retained Codex intended diagnostics.

This is final release engineering. It does not rerun a mathematical audit and
does not replace native Lean execution. Only logs from --results are evaluated.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import zipfile

ARCHIVE_SHA256 = 'b63abf88234062d5430cfe09eff26b1e24dc1b976c907567b6195596980cfb33'
LOG_ROOT = ('KN_UHP_C002_CODEX_AUDIT_REPRODUCIBILITY_20261022/'
            'independent/main/logs/all_author_controls/')
POSITIVE_STEMS = {'Positive', 'PositiveControls', 'Counterexamples', 'SignedChargeAndSpin'}
BAD = ('unknown module', 'object file', 'unknown package', 'file not found',
       'failed to read file', 'failed to import', 'no such file or directory',
       'could not find module', 'cannot find module', 'failed to synthesize instance',
       'unknown identifier', 'unknown constant', 'unexpected token', 'sorryax',
       'declaration uses', 'stack overflow', 'out of memory', 'segmentation fault',
       'maximum recursion depth', 'interrupted', 'timed out')
# These markers were read against the literal fixtures and archived diagnostics.
# Whitespace is removed for matching; Lean line wrapping and CRLF are immaterial.
MARKERS = {
 'RejectArbitraryLpBoundary': ['OriginalSourceBoundary', 'high low'],
 'RejectConjugation': ['⊢ -Complex.I = Complex.I'],
 'RejectOrdinaryEigenbasis': ['⊢ False'],
 'RejectPositiveBetaForSignedQ': ['⊢ False'],
 'RejectUnconjugatedPrimal': ['reduced_eigenvector_of_chiral_adjoint', 'star z • u', 'z • u', 'StaticGraph'],
 'RejectUnpairedSign': ['⊢ False'],
 'RejectMissingCorrection': ['zeroExtension_second_source', 'deltaValue 0 1', 'but is expected to have type'],
 'RejectNegativeK': ['⊢ False'],
 'RejectNonUHP': ['⊢ False'],
 'RejectNoOriginalHorizon': ['HorizonRegular', '(-2 * 1) high', '(-1) low'],
 'RejectUnboundedAngularAverage': ['⊢ False'],
 'RejectUnsignedSpin': ['⊢ False'],
 'RejectVanishingCorrectionDenominator': ['⊢ False'],
 'RejectWrongWeightDomain': ['⊢ False'],
 'RejectHorizonAsNonSpecial': ['HorizonRegular', 'NonSpecialIngoing'],
 'RejectPositiveWhiting': ['⊢ False'],
 'RejectResonantFuchs': ['⊢ False'],
 'RejectSeparatedAsFullField': ['AngularH', 'ℝ → ℂ', 'kerr_separated_exclusion'],
 'RejectZeroLeadingCoefficient': ['⊢ False'],
 'BoundaryWithoutEquation': ['OriginalSelectedPair', '→ EqOn', 'charged_original_eigenmode_exclusion'],
 'MissingDelta': ['derivative_zeroExtension', '+ deltaValue 0 1', 'but is expected to have type'],
 'OneChiralBlock': ['(sourceTransform positive b r t u).1 = 0', 'sourceTransform positive b r t u = 0'],
 'PoleAsNonresonant': ['finitePartAt r (-1)', '⊢ False'],
 'SwappedHorizonWeight': ['HorizonRegular', '3 * spinSign positive / 4', '- 1 / 2'],
 'WrongDeltaSign': ['corrected_zeroExtension_second', '+ deltaValue 0 (1 / 1)', '- deltaValue 0 (1 / 1)'],
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def compact(s):
    return re.sub(r'\s+', '', s)


def category(message):
    for prefix in ('Application type mismatch', 'Type mismatch', 'unsolved goals',
                   'Tactic `assumption` failed'):
        if message.startswith(prefix):
            return prefix
    return message.strip()


def diagnostics(text, rel):
    # Match every error header, including errors outside the intended fixture.
    headers = re.findall(r'^([^\r\n]+?):(\d+):(\d+): error: ([^\r\n]*)',
                         text.replace('\\', '/'), re.MULTILINE)
    return [{'source': path, 'line': int(line), 'column': int(col), 'category': category(msg)}
            for path, line, col, msg in headers]


def judge(base, code, text):
    issues = []
    if code != base['exit_code']:
        issues.append('native_exit_code_mismatch')
    lowered = text.lower()
    issues += ['forbidden_diagnostic:' + s for s in BAD if s in lowered]
    actual_headers = diagnostics(text, base['source'])
    if actual_headers != base['diagnostics']:
        issues.append('intended_fixture_line_column_or_error_category_mismatch')
    # Any unparsed error is also a failure, even when intended errors coexist.
    if text.count('error:') != len(actual_headers):
        issues.append('unparsed_or_external_error')
    packed = compact(text)
    issues += ['missing_intended_diagnostic_marker:' + m
               for m in base['required_markers'] if compact(m) not in packed]
    return issues


def load_baseline(archive, project):
    archive_hash = file_digest(archive)
    if archive_hash != ARCHIVE_SHA256:
        raise ValueError('Retained Codex archive SHA-256 differs from handoff')
    cases, archived_text = [], {}
    with zipfile.ZipFile(archive) as z:
        summary = json.loads(z.read(LOG_ROOT + 'summary.json'))
        if not summary['all_pass'] or len(summary['cases']) != 30:
            raise ValueError('Archived control baseline is incomplete')
        for record in summary['cases']:
            rel = record['source']
            path = project / rel
            data = z.read(LOG_ROOT + record['log'])
            text = data.decode('utf-8')
            if digest(data) != record['log_sha256']:
                raise ValueError('Archived log hash mismatch: ' + rel)
            if file_digest(path) != record['source_sha256']:
                raise ValueError('Current fixture differs from audited fixture: ' + rel)
            positive = path.stem in POSITIVE_STEMS
            if record['expected'] != ('pass' if positive else 'reject'):
                raise ValueError('Archived expectation mismatch: ' + rel)
            base = {'source': rel, 'source_sha256': record['source_sha256'],
                    'expected': record['expected'], 'exit_code': 0 if positive else 1,
                    'log': record['log'], 'archived_log_sha256': record['log_sha256'],
                    'diagnostics': diagnostics(text, rel),
                    'required_markers': [] if positive else MARKERS[path.stem]}
            if positive and base['diagnostics'] or not positive and not base['diagnostics']:
                raise ValueError('Archived diagnostic presence mismatch: ' + rel)
            source_lines = path.read_text(encoding='utf-8').splitlines()
            base['fixture_error_lines'] = {str(d['line']): source_lines[d['line']-1]
                                           for d in base['diagnostics']}
            if any(d['source'] != rel or source_lines[d['line']-1].lstrip().startswith('import ')
                   for d in base['diagnostics']):
                raise ValueError('Baseline does not point to intended proof claim: ' + rel)
            issues = judge(base, record['exit_code'], text)
            if issues:
                raise ValueError('Baseline classification failure: ' + rel + ': ' + repr(issues))
            cases.append(base)
            archived_text[rel] = text
    fixtures = {p.relative_to(project).as_posix()
                for p in (project / 'validation').glob('controls_*/*.lean')}
    if fixtures != {b['source'] for b in cases} or len(fixtures) != 30:
        raise ValueError('Current fixture inventory differs from 30 archived controls')
    rejects = [b for b in cases if b['expected'] == 'reject']
    if len(rejects) != 25:
        raise ValueError('Expected exactly five accepts and 25 intended rejects')
    probes = 0
    for base in rejects:
        text = archived_text[base['source']]
        # Reject native missing-object errors, unrelated line/category errors,
        # extra infrastructure failures and a zero exit masquerading as rejection.
        mutations = [
            (1, base['source'] + ':1:1: error: failed to read file missing/KN.olean\n'),
            (1, re.sub(r':(\d+):(\d+): error:', ':1:1: error:', text, count=1)),
            (1, text.replace('error: ', 'error: unknown module ', 1)),
            (1, text + '\nerror: failed to import KN\n'),
            (0, text),
        ]
        for code, mutated in mutations:
            if not judge(base, code, mutated):
                raise ValueError('Independent validator accepted malformed negative: ' + base['source'])
            probes += 1
    return {'schema': 1, 'kind': 'archived intended author-control diagnostic baseline',
            'archive_sha256': archive_hash, 'cases': cases,
            'negative_classifier_selftest_rejections': probes}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--project', type=Path, required=True)
    p.add_argument('--results', type=Path)
    p.add_argument('--baseline-out', type=Path)
    p.add_argument('--receipt', type=Path)
    a = p.parse_args()
    baseline = load_baseline(a.archive.resolve(), a.project.resolve())
    if a.baseline_out:
        a.baseline_out.write_text(json.dumps(baseline, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    report = {'kind': 'independent intended-diagnostic validation, not mathematical re-audit',
              'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'archive_sha256': baseline['archive_sha256'],
              'baseline_case_count': 30, 'positive_count': 5, 'negative_count': 25,
              'classifier_selftest_rejections': baseline['negative_classifier_selftest_rejections'],
              'native_results_checked': False}
    if a.results:
        results = a.results.resolve()
        summary_path = results / 'summary.json'
        summary = json.loads(summary_path.read_text(encoding='utf-8'))
        records = summary['cases']
        by_source = {r['source']: r for r in records}
        issues = []
        if len(records) != 30 or len(by_source) != 30:
            issues.append('native_summary_does_not_contain_30_unique_cases')
        if set(by_source) != {b['source'] for b in baseline['cases']}:
            issues.append('native_fixture_inventory_mismatch')
        details = []
        for base in baseline['cases']:
            rec = by_source.get(base['source'])
            case_issues = []
            if rec is None:
                details.append({'source': base['source'], 'passed': False, 'issues': ['missing_native_case']})
                continue
            for field in ('source_sha256', 'expected'):
                if rec[field] != base[field]:
                    case_issues.append('native_' + field + '_mismatch')
            log = (results / rec['log']).resolve()
            if not log.is_relative_to(results):
                raise ValueError('Native log path escapes results directory')
            raw = log.read_bytes()
            log_hash = digest(raw)
            if log_hash != rec['log_sha256']:
                case_issues.append('native_log_hash_mismatch')
            text = raw.decode('utf-8')
            case_issues += judge(base, rec['exit_code'], text)
            details.append({'source': base['source'], 'native_exit_code': rec['exit_code'],
                            'intended_diagnostics': diagnostics(text, base['source']),
                            'log_sha256': log_hash, 'passed': not case_issues, 'issues': case_issues})
        report.update(native_results_checked=True, native_summary_sha256=file_digest(summary_path),
                      cases=details, issues=issues,
                      all_pass=not issues and all(d['passed'] for d in details))
    else:
        report['status'] = 'BASELINE_READY_NATIVE_RESULTS_NOT_CHECKED'
    if a.receipt:
        a.receipt.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if not a.results or report['all_pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

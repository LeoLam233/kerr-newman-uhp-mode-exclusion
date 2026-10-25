#!/usr/bin/env bash
set -u
cd "$(dirname "$0")/../.."
export PATH=/workspace/scratch/e6e0818fcb8f/ht_cloud_toolchain/lean-4.34.1-linux/bin:$PATH
mkdir -p reports/kerr_controls
status=0
lake env lean -DwarningAsError=true validation/controls_kerr/PositiveControls.lean > reports/kerr_controls/PositiveControls.log 2>&1
rc=$?
printf 'PositiveControls expected=0 actual=%s\n' "$rc" | tee reports/kerr_controls/results.log
[[ $rc == 0 ]] || status=1
for name in RejectPositiveWhiting RejectHorizonAsNonSpecial RejectResonantFuchs RejectZeroLeadingCoefficient RejectSeparatedAsFullField; do
  lake env lean validation/controls_kerr/"$name".lean > reports/kerr_controls/"$name".log 2>&1
  rc=$?
  printf '%s expected=nonzero actual=%s\n' "$name" "$rc" | tee -a reports/kerr_controls/results.log
  [[ $rc != 0 ]] || status=1
done
exit "$status"

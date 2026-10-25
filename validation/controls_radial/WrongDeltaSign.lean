import KN.ChargedRadial.RegularDistribution
open KN.ChargedRadial
-- EXPECTED FAILURE: the actual second-equation source has plus, not minus, delta.
example : Distribution.lineDerivCLM (1:ℝ) (zeroExtension 0 (fun _ => (1:ℂ))) =
    mulComplexDist (fun _ => (1:ℂ)) contDiff_const
      (zeroExtension 0 (fun _ => (0:ℂ)) - deltaValue 0 (1/1)) := by
  exact corrected_zeroExtension_second 0 (fun _ => 0) (fun _ => 1) (fun _ => 1)
    continuous_const contDiff_const contDiff_const (by norm_num) (by simp)

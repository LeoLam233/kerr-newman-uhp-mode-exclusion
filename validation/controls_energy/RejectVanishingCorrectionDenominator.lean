import KN.ChargedRadial.RegularDistribution
open TopologicalSpace
open scoped Distributions
-- The exceptional correction cannot silently divide by a vanishing coupling B(r).
example : Distribution.lineDerivCLM (1:ℝ)
    (KN.ChargedRadial.zeroExtension 0 (fun _ => (1:ℂ)))=
    KN.ChargedRadial.mulComplexDist (fun _ => (0:ℂ)) contDiff_const
      (KN.ChargedRadial.zeroExtension 0 (fun _ => (0:ℂ))+KN.ChargedRadial.deltaValue 0 (1/0)) := by
  exact KN.ChargedRadial.corrected_zeroExtension_second 0 (fun _ => 0) (fun _ => 1) (fun _ => 0)
    continuous_const contDiff_const contDiff_const (by norm_num) (by intros; simp)

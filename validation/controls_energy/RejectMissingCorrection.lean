import KN.ChargedRadial.RegularDistribution
open TopologicalSpace
open scoped Distributions
-- The genuine zero-extension theorem retains a delta; dropping it does not typecheck.
example : Distribution.lineDerivCLM (1:ℝ)
    (KN.ChargedRadial.zeroExtension 0 (fun _ => (1:ℂ)))=
    KN.ChargedRadial.mulComplexDist (fun _ => (1:ℂ)) contDiff_const
      (KN.ChargedRadial.zeroExtension 0 (fun _ => (0:ℂ))) := by
  exact KN.ChargedRadial.zeroExtension_second_source 0 (fun _ => 0) (fun _ => 1) (fun _ => 1)
    continuous_const contDiff_const contDiff_const (by intros; simp)

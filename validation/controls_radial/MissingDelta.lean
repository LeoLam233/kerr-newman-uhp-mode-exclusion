import KN.ChargedRadial.ZeroExtension
open KN.ChargedRadial
-- EXPECTED FAILURE: a nonzero horizon value cannot discard the delta source.
example : Distribution.lineDerivCLM (1:ℝ) (zeroExtension 0 (fun _ => (1:ℂ))) = (0:CDist) := by
  exact derivative_zeroExtension 0 (fun _ => (1:ℂ)) contDiff_const

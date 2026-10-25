import KN.ChargedRadial.ExteriorInjectivity
open KN.ChargedRadial Set
-- EXPECTED FAILURE: the actual nonresonant continuation API rejects alpha = -1,
-- even when every other hypothesis is provided.
example (r : ℝ) (f v : ℝ → ℂ) (hf : Smooth f)
    (hv : ContinuousOn v (Ioi r))
    (he : ∀ t > r, v t = ((t-r):ℂ)^(-1:ℂ)*f t)
    (hz : finitePartAt r (-1) f = 0) : EqOn v 0 (Ioi r) := by
  exact finitePartAt_exterior_injective r (-1) (by norm_num) (by norm_num) f v hf hv he hz

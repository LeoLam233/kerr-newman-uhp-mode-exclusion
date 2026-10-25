import KN.ChargedRadial.EigenmodeExclusion
open KN.ChargedRadial KN.Boundary KN.Angular KN.Energy Set
-- EXPECTED FAILURE: all genuine angular/boundary data still do not replace the original radial ODE.
example (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ)
    (omega lam : ℂ) (hw : 0 < omega.im) (u v : AngularHilbert) (hu : ‖u‖ = 1)
    (hg : StaticGraph (spinSign positive) b.beta m u v)
    (he : v + omega • reducedFrequencyMultiplier b (spinSign positive) u = lam • u)
    (y z : ℝ → ℂ)
    (hy : HorizonRegular b m omega (-(3*spinSign positive/4)) y)
    (hz : HorizonRegular b m omega (-(3*spinSign positive/4-1/2)) z)
    (ho : Outgoing b m omega y) : EqOn y 0 (Ioi b.rPlus) ∧ EqOn z 0 (Ioi b.rPlus) := by
  exact charged_original_eigenmode_exclusion positive b hQ m omega lam hw u v hu hg he y z hy hz ho

import KN.Kerr.FullFieldExclusion
open KN.Kerr Set
open scoped ContDiff
/-- EXPECTED FAILURE: the scalar separated theorem is not itself a theorem
about arbitrary angular-Hilbert-valued fields. -/
example (b : KN.Background) (hQ : b.Q=0) (m s : ℤ) (omega : ℂ)
    (hs : s=1 ∨ s=2 ∨ s= -1 ∨ s= -2) (homega : 0<omega.im)
    (F : ℝ → AngularH) (hF : ContDiffOn ℝ ∞ F (Ioi b.rPlus))
    (heq : FullFieldEquation b m s omega F)
    (hh : KN.Boundary.HorizonRegular b m omega (-(s:ℝ)) F)
    (ho : KN.Boundary.Outgoing b m omega F) :
    ∀ r ∈ Ioi b.rPlus, F r=0 :=
  kerr_separated_exclusion b hQ m s omega 0 hs homega F F hF hF heq hh ho

import KN.Kerr.PositiveExclusion

namespace KN.Kerr
open Set
open scoped ContDiff

/-- All four nonzero integer spins on rotating or nonrotating subextremal Kerr.
This theorem concerns actual separated angular/radial functions and physical
boundary classes. Full-field spectral extraction is a separate theorem. -/
theorem kerr_separated_exclusion
    (b : KN.Background) (hQ : b.Q = 0) (m s : ℤ) (omega Λ : ℂ)
    (hs : s = 1 ∨ s = 2 ∨ s = -1 ∨ s = -2) (homega : 0 < omega.im)
    (u R : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m s omega Λ u)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (hphysical : PhysicalRadialEquation b m omega Λ s R)
    (hhor : KN.Boundary.HorizonRegular b m omega (-(s : ℝ)) R)
    (hout : KN.Boundary.Outgoing b m omega R) :
    ∀ r ∈ Ioi b.rPlus, R r = 0 := by
  rcases hs with h | h | h | h
  · exact positive_spin_separated_exclusion b hQ m s omega Λ (Or.inl h) homega u R hu hR hphysical hhor hout
  · exact positive_spin_separated_exclusion b hQ m s omega Λ (Or.inr h) homega u R hu hR hphysical hhor hout
  · exact negative_spin_separated_exclusion b hQ m s omega Λ (Or.inl h) homega u R hu hR hphysical hhor hout
  · exact negative_spin_separated_exclusion b hQ m s omega Λ (Or.inr h) homega u R hu hR hphysical hhor hout

end KN.Kerr

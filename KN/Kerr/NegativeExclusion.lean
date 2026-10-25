import KN.Kerr.PhysicalConjugation
import KN.Kerr.NegativeBridge

namespace KN.Kerr
open Set
open scoped ContDiff

/-- Complete separated negative-spin Kerr exclusion with physical weighted-smooth
horizon data. Only the named general Fuchs and classical negative-spin Whiting
interfaces are external; the smooth-to-non-special bridge is proved above.
This theorem is not presented as full-field or positive-spin coverage. -/
theorem negative_spin_separated_exclusion
    (b : KN.Background) (hQ : b.Q = 0) (m s : ℤ) (omega Λ : ℂ)
    (hs : s = -1 ∨ s = -2) (homega : 0 < omega.im)
    (u R : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m s omega Λ u)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (hphysical : PhysicalRadialEquation b m omega Λ s R)
    (hhor : KN.Boundary.HorizonRegular b m omega (-(s : ℝ)) R)
    (hout : KN.Boundary.Outgoing b m omega R) :
    ∀ r ∈ Ioi b.rPlus, R r = 0 := by
  obtain ⟨f, hf, hrep⟩ := hhor
  have hrep' : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r := by
    intro r hr
    exact hrep r hr
  have hconj := physical_to_conjugated b m s omega Λ R f hf hrep' hphysical
  exact negative_exclusion_of_conjugated_equation b hQ m s omega Λ hs homega u R f hu hR
    hphysical hf hconj hrep' hout

end KN.Kerr

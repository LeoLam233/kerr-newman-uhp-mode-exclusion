import KN.Kerr.NegativeExclusion
import KN.Kerr.SpinReversalCore
import KN.Kerr.OutgoingInjectivity
import KN.Kerr.ReversedSmoothness
import KN.Kerr.OutgoingPreservation

namespace KN.Kerr
open Set
open scoped ContDiff

/-- Complete positive-spin separated Kerr exclusion. The differential map,
horizon preservation, outgoing preservation, and injectivity are proved above;
only classical negative-spin exclusion and general Fuchs theory are external. -/
theorem positive_spin_separated_exclusion
    (b : KN.Background) (hQ : b.Q = 0) (m s : ℤ) (omega Λ : ℂ)
    (hs : s = 1 ∨ s = 2) (homega : 0 < omega.im)
    (u R : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m s omega Λ u)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (hphysical : PhysicalRadialEquation b m omega Λ s R)
    (hhor : KN.Boundary.HorizonRegular b m omega (-(s : ℝ)) R)
    (hout : KN.Boundary.Outgoing b m omega R) :
    ∀ r ∈ Ioi b.rPlus, R r = 0 := by
  obtain ⟨f, hf, hrep⟩ := hhor
  have hrep' : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r :=
    fun r hr => hrep r hr
  have hk : (s.natAbs : ℝ) = (s : ℝ) := by rcases hs with rfl | rfl <;> norm_num
  have hrepN : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s.natAbs r * f r := by
    simpa only [hk] using hrep'
  obtain ⟨hangular, heq, hboundary⟩ := spin_reversal_core b hQ m s omega Λ hs u R f hu hphysical hf hrep'
  have hsneg : -s = -1 ∨ -s = -2 := by rcases hs with rfl | rfl <;> norm_num
  have hsm := reversedRadial_contDiffOn b m omega s.natAbs (2*s.natAbs) f hf
  have houtRev := reversedRadial_outgoing b m omega s.natAbs (2*s.natAbs) R f hR hf hrepN hout
  rw [hk] at hsm houtRev
  have hboundary' : KN.Boundary.HorizonRegular b m omega (-((-s : ℤ) : ℝ))
      (reversedRadial b m omega s (2*s.natAbs) f) := by simpa using hboundary
  have hz := negative_spin_separated_exclusion b hQ m (-s) omega Λ hsneg homega
    (angularReflect u) (reversedRadial b m omega s (2*s.natAbs) f)
    hangular hsm heq hboundary' houtRev
  intro r hr
  by_contra hne
  obtain ⟨x, hx, hnx⟩ := reversedRadial_nonzero_of_outgoing b m omega homega
    s.natAbs (2*s.natAbs) R f hf hrepN ⟨r,hr,hne⟩ hout
  rw [hk] at hnx
  exact hnx (hz x hx)

end KN.Kerr

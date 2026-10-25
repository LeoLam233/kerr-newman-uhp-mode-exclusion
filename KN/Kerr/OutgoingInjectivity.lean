import KN.Kerr.HorizonPreservation
import KN.Kerr.GaugeConjugation
import KN.Kerr.OutgoingDecay
import KN.Energy.ConormalInjectivity

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

/-- Injectivity of the reversed radial map on coefficients decaying at infinity.
This replaces the differentiated nonzero-leading-coefficient asymptotic argument
by a proved polynomial-kernel theorem. The remaining outgoing-to-decay bridge
uses the actual gauge's exponential growth, not a new ODE interface. -/
theorem reversedRadial_injective_of_decay
    (b : KN.Background) (m : ℤ) (omega : ℂ) (s : ℝ) (n : ℕ)
    (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hdecay : Tendsto f atTop (𝓝 0))
    (hzero : ∀ r ∈ Ioi b.rPlus, reversedRadial b m omega s n f r = 0) :
    ∀ r ∈ Ioi b.rPlus, f r = 0 := by
  apply KN.Energy.iteratedDeriv_injective_on_decaying n b.rPlus f
    (hf.mono Ioi_subset_Ici_self) _ hdecay
  intro r hr
  have hz := hzero r hr
  have hq : KN.Boundary.gauge b m omega r * (Real.rpow (b.Delta r) s : ℂ) ≠ 0 := by
    apply mul_ne_zero (KN.Boundary.gauge_ne_zero b m omega r)
    exact_mod_cast ne_of_gt (Real.rpow_pos_of_pos (b.Delta_pos hr) s)
  unfold reversedRadial at hz
  have hg := (mul_eq_zero.mp hz).resolve_left hq
  rwa [horizon_coefficient_derivatives_exterior hf n hr] at hg

/-- A nonzero physical field with a decaying ingoing coefficient has nonzero image. -/
theorem reversedRadial_nonzero_of_decay
    (b : KN.Background) (m : ℤ) (omega : ℂ) (s : ℝ) (n : ℕ)
    (R f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r)
    (hne : ∃ r ∈ Ioi b.rPlus, R r ≠ 0)
    (hdecay : Tendsto f atTop (𝓝 0)) :
    ∃ r ∈ Ioi b.rPlus, reversedRadial b m omega s n f r ≠ 0 := by
  by_contra h
  push Not at h
  have hfzero := reversedRadial_injective_of_decay b m omega s n f hf hdecay h
  obtain ⟨r, hr, hR⟩ := hne
  apply hR
  rw [hrep r hr, hfzero r hr, mul_zero]

/-- Outgoing upper-half-plane fields have nonzero reversed image whenever the
original field is nonzero. This includes all exceptional frequencies. -/
theorem reversedRadial_nonzero_of_outgoing
    (b : KN.Background) (m : ℤ) (omega : ℂ) (homega : 0 < omega.im)
    (k n : ℕ) (R f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega (k : ℝ) r * f r)
    (hne : ∃ r ∈ Ioi b.rPlus, R r ≠ 0)
    (hout : KN.Boundary.Outgoing b m omega R) :
    ∃ r ∈ Ioi b.rPlus, reversedRadial b m omega (k : ℝ) n f r ≠ 0 :=
  reversedRadial_nonzero_of_decay b m omega k n R f hf hrep hne
    (outgoing_coefficient_tendsto_zero b m omega homega k R f hrep hout)

end KN.Kerr

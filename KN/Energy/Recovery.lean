import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter Set
open scoped Topology
namespace KN.Energy

/-- Recovery of the second radial unknown from A w♯=0 is valid even at
an isolated zero of the affine coefficient; no division by A is made there. -/
theorem affine_mul_vanishes (a c : ℂ) (ha : a ≠ 0) (r₀ : ℝ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi r₀))
    (heq : ∀ r > r₀, (a*(r:ℂ)+c)*f r = 0) : ∀ r > r₀, f r = 0 := by
  intro r hr
  by_cases hA : a*(r:ℂ)+c = 0
  · let xs : ℕ → ℝ := fun n => r+1/(n+1:ℝ)
    have ht : Tendsto xs atTop (𝓝 r) := by
      simpa [xs] using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hfx : ∀ n, f (xs n) = 0 := by
      intro n
      have hp : 0 < 1/(n+1:ℝ) := by positivity
      have hxr : r < xs n := by dsimp [xs]; linarith
      have hAn : a*(xs n : ℂ)+c ≠ 0 := by
        intro hz
        have he : a*((xs n : ℂ)-(r:ℂ)) = 0 := by linear_combination hz-hA
        have he' := (mul_eq_zero.mp he).resolve_left ha
        have he'' : xs n = r := Complex.ofReal_injective (sub_eq_zero.mp he')
        linarith
      exact (mul_eq_zero.mp (heq (xs n) (lt_trans hr hxr))).resolve_left hAn
    have hc := (hf r hr).continuousAt (Ioi_mem_nhds hr)
    exact tendsto_nhds_unique (hc.tendsto.comp ht)
      (by simpa only [Function.comp_def, hfx] using (tendsto_const_nhds (x := (0:ℂ))))
  · exact (mul_eq_zero.mp (heq r hr)).resolve_left hA

/-- The nonzero exponential/gauge multiplier loses no radial information. -/
theorem recover_of_nonzero_multiplier (p w v : ℝ → ℂ) (s : Set ℝ)
    (hp : ∀ r ∈ s, p r ≠ 0) (hv : ∀ r ∈ s, v r = p r*w r)
    (hz : ∀ r ∈ s, v r = 0) : ∀ r ∈ s, w r = 0 := by
  intro r hr
  exact (mul_eq_zero.mp ((hv r hr).symm.trans (hz r hr))).resolve_left (hp r hr)

end KN.Energy

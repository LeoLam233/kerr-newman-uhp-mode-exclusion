import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open MeasureTheory Filter Set
open scoped Topology
namespace KN.Energy

/-- Improper fundamental theorem with limits at both open endpoints.
The value of f at the finite endpoint is immaterial. -/
theorem integral_Iio_derivative_zero {f f' : ℝ → ℝ} {b : ℝ}
    (hd : ∀ x < b, HasDerivAt f (f' x) x)
    (hi : IntegrableOn f' (Iio b))
    (hb : Tendsto f (𝓝[<] b) (𝓝 0)) (hbot : Tendsto f atBot (𝓝 0)) :
    ∫ x in Iio b, f' x = 0 := by
  let g := Function.update f b 0
  have hg : ContinuousWithinAt g (Iic b) b := by
    apply continuousWithinAt_update_same.mpr
    simpa only [Iic_sdiff_right] using hb
  have hgd : ∀ x ∈ Iio b, HasDerivAt g (f' x) x := by
    intro x hx
    apply (hd x hx).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Function.update_of_ne (ne_of_lt hy) 0 f
  have hgb : Tendsto g atBot (𝓝 0) := by
    apply hbot.congr'
    filter_upwards [Iio_mem_atBot b] with x hx
    exact (Function.update_of_ne (ne_of_lt hx) 0 f).symm
  have hii : IntegrableOn f' (Iic b) := by
    rwa [integrableOn_Iic_iff_integrableOn_Iio]
  have he := integral_Iic_of_hasDerivAt_of_tendsto hg hgd hii hgb
  simpa [g, integral_Iic_eq_integral_Iio] using he

/-- A continuous complex function with zero integral against a strictly positive
weight vanishes throughout the open integration interval. Integrability is
explicit, so the totalized Bochner integral cannot cause a vacuous conclusion. -/
theorem eq_zero_of_weighted_mass_zero {U : ℝ → ℂ} {W : ℝ → ℝ} {b : ℝ}
    (hU : ContinuousOn U (Iio b)) (hW : ∀ x < b, 0 < W x)
    (hi : IntegrableOn (fun x => W x * Complex.normSq (U x)) (Iio b))
    (hz : ∫ x in Iio b, W x * Complex.normSq (U x) = 0) :
    ∀ x < b, U x = 0 := by
  have hp : 0 ≤ᵐ[volume.restrict (Iio b)] fun x => W x * Complex.normSq (U x) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact mul_nonneg (hW x hx).le (Complex.normSq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hp hi).mp hz
  have hu : U =ᵐ[volume.restrict (Iio b)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Iio] with x hx hxb
    have hn : Complex.normSq (U x) = 0 := (mul_eq_zero.mp hx).resolve_left (ne_of_gt (hW x hxb))
    exact Complex.normSq_eq_zero.mp hn
  exact Measure.eqOn_open_of_ae_eq hu isOpen_Iio hU continuousOn_const

end KN.Energy

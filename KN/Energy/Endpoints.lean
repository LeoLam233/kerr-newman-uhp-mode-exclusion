import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

open MeasureTheory Filter Set Asymptotics
open scoped Topology
namespace KN.Energy

/-- The endpoint powers appearing in (47) are integrable for every γ>0,
without requiring a positive lower bound on γ. -/
theorem horizon_power_integrable (b M γ : ℝ) (hM : 0 < M) (hγ : 0 < γ) :
    IntegrableOn (fun x : ℝ => (b-x)^(4*M*γ-1)) (Ioo (b-1) b) := by
  have hp : -1 < 4*M*γ-1 := by nlinarith [mul_pos hM hγ]
  have hi := (intervalIntegral.intervalIntegrable_rpow' hp (a := (0:ℝ)) (b := 1)).comp_sub_left b
  have hi' : IntervalIntegrable (fun x : ℝ => (b-x)^(4*M*γ-1)) volume (b-1) b := by
    simpa using hi.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : b-1 ≤ b)).mp hi'

/-- A direct endpoint criterion for the energy density: power-integrable at
the finite endpoint, exponentially integrable at minus infinity. -/
theorem integrable_energy_of_endpoint_bounds (f : ℝ → ℝ) (b M γ δ : ℝ)
    (hM : 0 < M) (hγ : 0 < γ) (hδ : 0 < δ)
    (hf : ContinuousOn f (Iio b))
    (hfinite : f =O[𝓝[<] b] fun x : ℝ => (b-x)^(4*M*γ-1))
    (hinfty : f =O[atBot] fun x : ℝ => Real.exp ((γ*δ)*x)) :
    IntegrableOn f (Iio b) := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Iio b)) :=
    hf.aestronglyMeasurable measurableSet_Iio
  apply integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin.mpr
  refine ⟨hinfty.integrableAtFilter ⟨Iio b, Iio_mem_atBot b, hmeas⟩ ?_,
    hfinite.integrableAtFilter ⟨Iio b, self_mem_nhdsWithin, hmeas⟩ ?_,
    hf.locallyIntegrableOn measurableSet_Iio⟩
  · exact ⟨Iic b, Iic_mem_atBot b, integrableOn_exp_mul_Iic (mul_pos hγ hδ) b⟩
  · exact ⟨Ioo (b-1) b, Ioo_mem_nhdsLT (by linarith), horizon_power_integrable b M γ hM hγ⟩

/-- Vanishing of the finite-endpoint flux from its strictly positive power. -/
theorem horizon_flux_zero (J : ℝ → ℝ) (b M γ : ℝ) (hM : 0 < M) (hγ : 0 < γ)
    (hJ : J =O[𝓝[<] b] fun x : ℝ => (b-x)^(4*M*γ)) :
    Tendsto J (𝓝[<] b) (𝓝 0) := by
  have hp : 0 < 4*M*γ := by positivity
  have ht : Tendsto (fun x : ℝ => (b-x)^(4*M*γ)) (𝓝[<] b) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => (b-x)^(4*M*γ)) b := by
      exact (Real.continuousAt_rpow_const (b-b) (4*M*γ) (Or.inr hp.le)).comp
        (continuousAt_const.sub continuousAt_id)
    simpa [Real.zero_rpow hp.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact hJ.trans_tendsto ht

/-- Vanishing of the infinity flux after exponential domination. -/
theorem infinity_flux_zero (J : ℝ → ℝ) (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hJ : J =O[atBot] fun x : ℝ => Real.exp ((γ*δ)*x)) :
    Tendsto J atBot (𝓝 0) := by
  apply hJ.trans_tendsto
  exact Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atBot (mul_pos hγ hδ) tendsto_id)
end KN.Energy

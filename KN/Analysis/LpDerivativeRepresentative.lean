import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add

open Filter MeasureTheory Set
open scoped Topology

namespace KN.Analysis

/-- An independently established Lp derivative agrees almost everywhere with a
pointwise derivative. No domination or uniform pointwise estimate is assumed. -/
theorem lp_derivative_representative
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {U : ℝ → Lp E 2 μ} {u : ℝ → α → E} {U' : Lp E 2 μ}
    {r rp : ℝ} (hr : rp < r) (hU : HasDerivAt U U' r)
    (hrep : ∀ x, rp < x → (U x : α → E) =ᵐ[μ] u x)
    (hu : ∀ᵐ θ ∂μ, DifferentiableAt ℝ (fun x => u x θ) r) :
    (U' : α → E) =ᵐ[μ] fun θ => deriv (fun x => u x θ) r := by
  have ht := hU.tendsto_slope_zero_right
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae'
  have hpos : ∀ᶠ n in atTop, 0 < ns n := hns.eventually self_mem_nhdsWithin
  have hreps : ∀ n, ∀ᵐ θ ∂μ, 0 < ns n →
      ((ns n)⁻¹ • (U (r + ns n) - U r) : Lp E 2 μ) θ =
        (ns n)⁻¹ • (u (r + ns n) θ - u r θ) := by
    intro n
    by_cases hn : 0 < ns n
    · filter_upwards [Lp.coeFn_smul ((ns n)⁻¹) (U (r + ns n) - U r),
        Lp.coeFn_sub (U (r + ns n)) (U r), hrep (r + ns n) (by linarith),
        hrep r hr] with θ h1 h2 h3 h4
      intro _
      rw [h1]
      change (ns n)⁻¹ • ((U (r + ns n) - U r) θ) = _
      rw [h2]
      change (ns n)⁻¹ • (U (r + ns n) θ - U r θ) = _
      rw [h3, h4]
    · exact Filter.Eventually.of_forall (fun _ h => (hn h).elim)
  filter_upwards [hae, hu, ae_all_iff.mpr hreps] with θ hθ hd heq
  have hpoint := hd.hasDerivAt.tendsto_slope_zero_right.comp hns
  have hevent : (fun n => ((ns n)⁻¹ • (U (r + ns n) - U r) : Lp E 2 μ) θ)
      =ᶠ[atTop] (fun n => (ns n)⁻¹ • (u (r + ns n) θ - u r θ)) := by
    filter_upwards [hpos] with n hn
    exact heq n hn
  exact tendsto_nhds_unique (hθ.congr' hevent) hpoint

end KN.Analysis

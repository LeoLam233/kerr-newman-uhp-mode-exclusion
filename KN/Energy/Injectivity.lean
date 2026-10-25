import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Tactic

open Set Filter
open scoped Topology FourierTransform SchwartzMap
namespace KN.Energy

/-- A holomorphic function vanishing along a nonzero interior ray vanishes on
its whole lower half-plane. The ray inclusion is an explicit strict inequality. -/
theorem holomorphic_zero_of_ray (F : ℂ → ℂ) (ω : ℂ) (b c : ℝ)
    (hω : ω ≠ 0) (hF : AnalyticOnNhd ℂ F {z | z.im < c})
    (hray : ∀ x < b, (ω * (x : ℂ)).im < c)
    (hzero : ∀ x < b, F (ω * (x : ℂ)) = 0) :
    ∀ z : ℂ, z.im < c → F z = 0 := by
  let x₀ : ℝ := b-1
  let xs : ℕ → ℝ := fun n => x₀ - 1/(n+1:ℝ)
  have hx₀ : x₀ < b := by dsimp [x₀]; linarith
  have ht : Tendsto xs atTop (𝓝 x₀) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [xs] using tendsto_const_nhds.sub h
  have hzt : Tendsto (fun n => ω*(xs n : ℂ)) atTop (𝓝 (ω*(x₀ : ℂ))) :=
    tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto _ |>.comp ht)
  have hcl : ω*(x₀ : ℂ) ∈ closure ({z | F z = (0:ℂ)} \ {ω*(x₀ : ℂ)}) := by
    apply mem_closure_of_tendsto hzt
    apply Filter.Eventually.of_forall
    intro n
    have hp : 0 < 1/(n+1:ℝ) := by positivity
    have hx : xs n < b := by dsimp [xs]; linarith
    refine ⟨hzero (xs n) hx, ?_⟩
    simp only [mem_singleton_iff]
    intro he
    have he' : (xs n : ℂ) = (x₀ : ℂ) := mul_left_cancel₀ hω he
    have he'' : xs n = x₀ := Complex.ofReal_injective he'
    dsimp [xs] at he''
    linarith
  exact hF.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
    (convex_halfSpace_im_lt c).isPreconnected (hray x₀ hx₀) hcl

/-- Fourier injectivity for actual tempered distributions, using Mathlib's
verified Fourier inversion rather than a new external interface. -/
theorem tempered_eq_zero_of_fourier_eq_zero (T : TemperedDistribution ℝ ℂ)
    (hT : 𝓕 T = 0) : T = 0 := by
  have hi := congrArg (fun S : TemperedDistribution ℝ ℂ => 𝓕⁻ S) hT
  simpa using hi

/-- Exact horizontal-line uniqueness with Mathlib's 2π Fourier normalization.
The transform pairing is explicit for every Schwartz test function; it must be
proved by the Fourier--Laplace construction, not postulated as Fourier zero. -/
theorem damped_distribution_eq_zero (T : TemperedDistribution ℝ ℂ)
    (F : ℂ → ℂ) (c τ : ℝ) (hτ : τ < c)
    (hzero : ∀ z : ℂ, z.im < c → F z = 0)
    (hpair : ∀ φ : SchwartzMap ℝ ℂ, (𝓕 T) φ =
      ∫ x : ℝ, F ((2*Real.pi*x : ℝ) + Complex.I*τ) * φ x) : T = 0 := by
  apply tempered_eq_zero_of_fourier_eq_zero
  ext φ
  rw [hpair]
  have hz : ∀ x : ℝ, F ((2*Real.pi*x : ℝ) + Complex.I*τ) = 0 := by
    intro x
    apply hzero
    simpa using hτ
  simp only [hz, zero_mul, MeasureTheory.integral_zero]
  rfl

end KN.Energy

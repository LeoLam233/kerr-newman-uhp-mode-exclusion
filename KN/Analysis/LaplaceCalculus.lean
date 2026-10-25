import KN.Analysis.LaplaceInterface

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions SchwartzMap FourierTransform
namespace KN.Analysis
open KN.ChargedRadial

theorem laplace_zero (c : ℝ) : IsFourierLaplaceTransform (0:CDist) c (fun _ => 0) := by
  intro beta hb
  refine ⟨0, ?_, ?_⟩
  · intro phi; simp
  · intro phi
    constructor
    · simp
    · simp

theorem IsFourierLaplaceTransform.add {T S : CDist} {c : ℝ} {F G : ℂ → ℂ}
    (hF : IsFourierLaplaceTransform T c F) (hG : IsFourierLaplaceTransform S c G) :
    IsFourierLaplaceTransform (T+S) c (fun z => F z+G z) := by
  intro beta hb
  obtain ⟨U,hU,hUF⟩ := hF beta hb
  obtain ⟨V,hV,hVG⟩ := hG beta hb
  refine ⟨U+V, ?_, ?_⟩
  · intro phi
    change U (testSchwartz phi)+V (testSchwartz phi) =
      T (mulTest (damping beta) (damping_smooth beta) phi)+
      S (mulTest (damping beta) (damping_smooth beta) phi)
    rw [hU phi,hV phi]; rfl
  · intro phi
    constructor
    · simpa only [add_mul, Pi.add_def] using (hUF phi).1.add (hVG phi).1
    · change (𝓕 U) phi + (𝓕 V) phi = _
      rw [(hUF phi).2,(hVG phi).2]
      simp only [add_mul]
      exact (integral_add (hUF phi).1 (hVG phi).1).symm

theorem IsFourierLaplaceTransform.smul {T : CDist} {c : ℝ} {F : ℂ → ℂ}
    (hF : IsFourierLaplaceTransform T c F) (a : ℂ) :
    IsFourierLaplaceTransform (a • T) c (fun z => a*F z) := by
  intro beta hb
  obtain ⟨U,hU,hUF⟩ := hF beta hb
  refine ⟨a • U, ?_, ?_⟩
  · intro phi
    change a*U (testSchwartz phi) = a*T (mulTest (damping beta) (damping_smooth beta) phi)
    rw [hU phi]; rfl
  · intro phi
    constructor
    · simpa only [mul_assoc] using (hUF phi).1.const_mul a
    · change a*((𝓕 U) phi) = _
      rw [(hUF phi).2]
      simp only [mul_assoc]
      exact (integral_const_mul a _).symm

/-- A homogeneous distributional equation gives a genuine zero analytic transform. -/
theorem transform_zero_of_distribution_zero {T : CDist} {c : ℝ} {F : ℂ → ℂ}
    (hF : IsFourierLaplaceTransform T c F)
    (ha : AnalyticOnNhd ℂ F {z : ℂ | z.im < c}) (hT : T=0) :
    ∀ z : ℂ, z.im < c → F z=0 := by
  subst T
  exact External.fourier_laplace_single_valued 0 c F (fun _ => 0) hF (laplace_zero c) ha analyticOnNhd_const

end KN.Analysis

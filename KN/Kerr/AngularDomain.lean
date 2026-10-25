import KN.Kerr.AngularReflection
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace KN.Kerr
open Set
open scoped ContDiff

/-- Regular fixed-m spin sections in a polar trivialization. The smooth coefficient
is a function of cos θ, and the two regular pole powers are imposed explicitly.
This excludes the logarithmic scalar branch when either pole order is zero.
This is a smooth core representation, not an assertion about the closed L² domain. -/
def CanonicalSmoothAngular (m s : ℤ) (u : ℝ → ℂ) : Prop :=
  ∃ F : ℝ → ℂ, ContDiffOn ℝ ∞ F (Icc (-1) 1) ∧
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
      u θ = ((Real.sin (θ / 2) : ℂ) ^ (m + s).natAbs *
        (Real.cos (θ / 2) : ℂ) ^ (m - s).natAbs) * F (Real.cos θ)

private theorem sin_half_reflection (θ : ℝ) :
    Real.sin ((Real.pi - θ) / 2) = Real.cos (θ / 2) := by
  rw [sub_div, Real.sin_pi_div_two_sub]

private theorem cos_half_reflection (θ : ℝ) :
    Real.cos ((Real.pi - θ) / 2) = Real.sin (θ / 2) := by
  rw [sub_div, Real.cos_pi_div_two_sub]

/-- Reflection preserves the regular spin core, including zero pole exponents.
No maximal scalar L² domain is substituted for canonical regularity. -/
theorem CanonicalSmoothAngular.reflect {m s : ℤ} {u : ℝ → ℂ}
    (hu : CanonicalSmoothAngular m s u) :
    CanonicalSmoothAngular m (-s) (angularReflect u) := by
  obtain ⟨F, hF, hu⟩ := hu
  refine ⟨fun x => F (-x), ?_, ?_⟩
  · apply hF.comp contDiff_neg.contDiffOn
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · intro θ hθ
    have hθ' : Real.pi - θ ∈ Ioo (0 : ℝ) Real.pi := by
      constructor <;> linarith [hθ.1, hθ.2]
    rw [angularReflect, hu (Real.pi - θ) hθ']
    simp only [sin_half_reflection, cos_half_reflection, Real.cos_pi_sub,
      sub_neg_eq_add, ← sub_eq_add_neg]
    ring

/-- The regularity correspondence is two-way. -/
theorem canonicalSmoothAngular_reflect_iff (m s : ℤ) (u : ℝ → ℂ) :
    CanonicalSmoothAngular m (-s) (angularReflect u) ↔ CanonicalSmoothAngular m s u := by
  constructor
  · intro h
    simpa only [neg_neg, angularReflect_involutive] using h.reflect
  · exact CanonicalSmoothAngular.reflect

end KN.Kerr

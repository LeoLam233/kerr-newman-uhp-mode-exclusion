import KN.ChargedRadial.PowerCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial

lemma power_factor_derivative (alpha : ℂ) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (t : ℝ) (ht : 0 < t) :
    (t:ℂ)*deriv (fun x : ℝ => (x:ℂ)^alpha*f x) t =
      (t:ℂ)^alpha*(alpha*f t+(t:ℂ)*deriv f t) := by
  have ht0 : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  by_cases ha : alpha = 0
  · subst alpha
    simp
  have hp := hasDerivAt_ofReal_cpow_const (ne_of_gt ht) ha
  have hprod : HasDerivAt (fun x : ℝ => (x:ℂ)^alpha*f x)
      (alpha*(t:ℂ)^(alpha-1)*f t+(t:ℂ)^alpha*deriv f t) t := by
    convert hp.mul (hf t).hasDerivAt using 1
  rw [hprod.deriv]
  have he : (t:ℂ)* (t:ℂ)^(alpha-1) = (t:ℂ)^alpha := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
    field_simp
  calc
    _ = ((t:ℂ)*(t:ℂ)^(alpha-1))*alpha*f t+
      (t:ℂ)^alpha*((t:ℂ)*deriv f t) := by ring
    _ = _ := by rw [he]; ring

lemma raised_power_factor_derivative (alpha : ℂ) (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (t : ℝ) (ht : 0 < t) :
    deriv (fun x : ℝ => (x:ℂ)^(alpha+1)*g x) t =
      (t:ℂ)^alpha*((alpha+1)*g t+(t:ℂ)*deriv g t) := by
  have ht0 : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : (t:ℂ)^(alpha+1) = (t:ℂ)^alpha*(t:ℂ) := by
    rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
  have hh := power_factor_derivative (alpha+1) g hg t ht
  rw [he] at hh
  apply mul_left_cancel₀ ht0
  linear_combination hh

/-- The two residual equations used for canonical continuation follow from
actual derivatives of the original power-factorized pair, not from assumed
vanishing boundary terms. -/
theorem power_pair_residuals
    (alpha : ℂ) (f g d L A B : ℝ → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfirst : ∀ (t : ℝ), t > 0 →
      ((t:ℂ)*d t)*deriv (fun x : ℝ => (x:ℂ)^alpha*f x) t+
        L t*((t:ℂ)^alpha*f t) = A t*((t:ℂ)^(alpha+1)*g t))
    (hsecond : ∀ (t : ℝ), t > 0 →
      deriv (fun x : ℝ => (x:ℂ)^(alpha+1)*g x) t = B t*((t:ℂ)^alpha*f t)) :
    (∀ (t : ℝ), t > 0 → d t*(alpha*f t+(t:ℂ)*deriv f t)+L t*f t = A t*((t:ℂ)*g t)) ∧
    (∀ (t : ℝ), t > 0 → (alpha+1)*g t+(t:ℂ)*deriv g t = B t*f t) := by
  have hn (t : ℝ) (ht : 0 < t) : (t:ℂ)^alpha ≠ 0 :=
    (Complex.cpow_ne_zero_iff).2 (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)))
  constructor
  · intro t ht
    have h := hfirst t ht
    have hp := power_factor_derivative alpha f hf t ht
    have he : (t:ℂ)^(alpha+1) = (t:ℂ)^alpha*(t:ℂ) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)), Complex.cpow_one]
    rw [he] at h
    apply mul_left_cancel₀ (hn t ht)
    linear_combination h - d t*hp
  · intro t ht
    have h := hsecond t ht
    rw [raised_power_factor_derivative alpha g hg t ht] at h
    apply mul_left_cancel₀ (hn t ht)
    linear_combination h

end KN.ChargedRadial

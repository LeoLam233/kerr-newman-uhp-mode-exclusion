import KN.ChargedRadial.TranslatedCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial

lemma translated_power_factor_derivative (r : ℝ) (alpha : ℂ) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (t : ℝ) (ht : r < t) :
    ((t-r : ℝ):ℂ)*deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^alpha*f x) t =
      ((t-r : ℝ):ℂ)^alpha*(alpha*f t+((t-r : ℝ):ℂ)*deriv f t) := by
  have ht0 : ((t-r : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr ht))
  by_cases ha : alpha = 0
  · subst alpha
    simp
  have hp0 := hasDerivAt_ofReal_cpow_const (ne_of_gt (sub_pos.mpr ht)) ha
  have hp : HasDerivAt (fun x : ℝ => ((x-r : ℝ):ℂ)^alpha)
      (alpha*((t-r : ℝ):ℂ)^(alpha-1)) t := by
    have hs : HasDerivAt (fun x : ℝ => x-r) 1 t := by
      simpa using (hasDerivAt_id t).sub_const r
    convert! hp0.scomp t hs using 1
    simp
  have hprod : HasDerivAt (fun x : ℝ => ((x-r : ℝ):ℂ)^alpha*f x)
      (alpha*((t-r : ℝ):ℂ)^(alpha-1)*f t+((t-r : ℝ):ℂ)^alpha*deriv f t) t := by
    convert hp.mul (hf t).hasDerivAt using 1
  rw [hprod.deriv]
  have he : ((t-r : ℝ):ℂ)* ((t-r : ℝ):ℂ)^(alpha-1) = ((t-r : ℝ):ℂ)^alpha := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
    field_simp
  calc
    _ = (((t-r : ℝ):ℂ)*((t-r : ℝ):ℂ)^(alpha-1))*alpha*f t+
      ((t-r : ℝ):ℂ)^alpha*(((t-r : ℝ):ℂ)*deriv f t) := by ring
    _ = _ := by rw [he]; ring

lemma raised_translated_power_factor_derivative (r : ℝ) (alpha : ℂ) (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (t : ℝ) (ht : r < t) :
    deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^(alpha+1)*g x) t =
      ((t-r : ℝ):ℂ)^alpha*((alpha+1)*g t+((t-r : ℝ):ℂ)*deriv g t) := by
  have ht0 : ((t-r : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr ht))
  have he : ((t-r : ℝ):ℂ)^(alpha+1) = ((t-r : ℝ):ℂ)^alpha*((t-r : ℝ):ℂ) := by
    rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
  have hh := translated_power_factor_derivative r (alpha+1) g hg t ht
  rw [he] at hh
  apply mul_left_cancel₀ ht0
  linear_combination hh

/-- The two residual equations used for canonical continuation follow from
actual derivatives of the original power-factorized pair, not from assumed
vanishing boundary terms. -/
theorem translated_power_pair_residuals
    (r : ℝ) (alpha : ℂ) (f g d L A B : ℝ → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfirst : ∀ (t : ℝ), t > r →
      (((t-r : ℝ):ℂ)*d t)*deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^alpha*f x) t+
        L t*(((t-r : ℝ):ℂ)^alpha*f t) = A t*(((t-r : ℝ):ℂ)^(alpha+1)*g t))
    (hsecond : ∀ (t : ℝ), t > r →
      deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^(alpha+1)*g x) t = B t*(((t-r : ℝ):ℂ)^alpha*f t)) :
    (∀ (t : ℝ), t > r → d t*(alpha*f t+((t-r : ℝ):ℂ)*deriv f t)+L t*f t = A t*(((t-r : ℝ):ℂ)*g t)) ∧
    (∀ (t : ℝ), t > r → (alpha+1)*g t+((t-r : ℝ):ℂ)*deriv g t = B t*f t) := by
  have hn (t : ℝ) (ht : r < t) : ((t-r : ℝ):ℂ)^alpha ≠ 0 :=
    (Complex.cpow_ne_zero_iff).2 (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr ht))))
  constructor
  · intro t ht
    have h := hfirst t ht
    have hp := translated_power_factor_derivative r alpha f hf t ht
    have he : ((t-r : ℝ):ℂ)^(alpha+1) = ((t-r : ℝ):ℂ)^alpha*((t-r : ℝ):ℂ) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr ht))), Complex.cpow_one]
    rw [he] at h
    apply mul_left_cancel₀ (hn t ht)
    linear_combination h - d t*hp
  · intro t ht
    have h := hsecond t ht
    rw [raised_translated_power_factor_derivative r alpha g hg t ht] at h
    apply mul_left_cancel₀ (hn t ht)
    linear_combination h

end KN.ChargedRadial

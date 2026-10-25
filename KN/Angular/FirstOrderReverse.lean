import KN.Angular.JacobiFirstOrder
import KN.Angular.JacobiRealization
import KN.Angular.StaticSquare
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace KN.Angular.Jacobi
noncomputable section
open scoped ContDiff

def coefficient (k θ : ℝ) : ℝ := ((3/2)*Real.cos θ+k)/Real.sin θ

theorem coefficient_hasDerivAt (k θ : ℝ) (hs : Real.sin θ ≠ 0) :
    HasDerivAt (coefficient k) ((-3/2-k*Real.cos θ)/(Real.sin θ)^2) θ := by
  have h := (((Real.hasDerivAt_cos θ).const_mul (3/2)).add_const k).div
    (Real.hasDerivAt_sin θ) hs
  convert h using 1
  · rfl
  · have ht := Real.sin_sq_add_cos_sq θ
    field_simp
    nlinarith [ht]

/-- First-order factorization on actual twice differentiable functions. -/
theorem lowering_reverse (f : ℝ → ℝ) (k μ θ : ℝ)
    (hf : HasDerivAt f (deriv f θ) θ)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ)
    (hs : Real.sin θ ≠ 0)
    (hDE : -deriv (deriv f) θ +
      ((coefficient k θ)^2+(-3/2-k*Real.cos θ)/(Real.sin θ)^2)*f θ = μ*f θ) :
    deriv (lowering k f) θ + coefficient k θ*lowering k f θ = -μ*f θ := by
  have hd := hf'.sub ((coefficient_hasDerivAt k θ hs).mul hf)
  have heq : lowering k f = fun t => deriv f t-coefficient k t*f t := rfl
  rw [heq]
  change deriv (deriv f-coefficient k*f) θ + coefficient k θ*(deriv f θ-coefficient k θ*f θ)=_
  rw [hd.deriv]
  nlinarith [hDE]

/-- The reverse first-order expression on every upper Jacobi function is
fixed by its proved scalar equation, without invoking a square domain. -/
theorem upper_reverse (k θ : ℝ) (n : ℕ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    deriv (lowering k (upper k n)) θ + coefficient k θ*lowering k (upper k n) θ =
      -(((n : ℝ)+max |k| 1)*((n : ℝ)+max |k| 1+1)-2)*upper k n θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hf : ContDiffOn ℝ ∞ (upper k n) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) n
  have hf' : ContDiffOn ℝ ∞ (deriv (upper k n)) (Set.Ioo 0 Real.pi) :=
    (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hf |>.2
  apply lowering_reverse _ _ _ _
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt
    ((hf'.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt
    (ne_of_gt hs)
  have hDE := scalar_jacobi_eigenfunction 1 k 1 (by norm_num) (by norm_num) n θ hθ
  have hpot := static_square_upper 1 k (Real.cos θ) (Real.sin θ) (by norm_num)
    (by nlinarith [Real.sin_sq_add_cos_sq θ]) (ne_of_gt hs)
  simp only [one_mul] at hDE hpot
  change -deriv (deriv (upper k n)) θ + _= _
  simpa only [coefficient,upper,scalarPotential,← hpot] using hDE

end
end KN.Angular.Jacobi

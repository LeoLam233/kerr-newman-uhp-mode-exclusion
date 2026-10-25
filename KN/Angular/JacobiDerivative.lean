import KN.Angular.JacobiRecurrences
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp

namespace KN.Angular.Jacobi
noncomputable section

/-- Ordinary differentiation of the actual half-angle Jacobi representative.
All singular factors are retained; cancellation is performed separately. -/
theorem regular_hasDerivAt (α β θ p : ℝ) (n : ℕ)
    (hs : Real.sin (θ/2) ≠ 0) (hc : Real.cos (θ/2) ≠ 0)
    (hP : HasDerivAt (polynomial α β n) p (Real.cos θ)) :
    HasDerivAt (regularFunction α β n)
      (((Real.cos (θ/2)/2)*(α+1/2)*Real.rpow (Real.sin (θ/2)) (α-1/2)*
        Real.rpow (Real.cos (θ/2)) (β+1/2) +
        Real.rpow (Real.sin (θ/2)) (α+1/2)*
        ((-Real.sin (θ/2)/2)*(β+1/2)*Real.rpow (Real.cos (θ/2)) (β-1/2))) *
        polynomial α β n (Real.cos θ) -
        Real.rpow (Real.sin (θ/2)) (α+1/2)*
        Real.rpow (Real.cos (θ/2)) (β+1/2)*Real.sin θ*p) θ := by
  have hhalf := (hasDerivAt_id θ).div_const (2 : ℝ)
  have h1 := hhalf.sin.rpow_const (p := α+1/2) (Or.inl hs)
  have h2 := hhalf.cos.rpow_const (p := β+1/2) (Or.inl hc)
  have h3 := hP.comp θ (Real.hasDerivAt_cos θ)
  convert (h1.mul h2).mul h3 using 1
  · rfl
  · dsimp
    simp only [show α+1/2-1=α-1/2 by ring, show β+1/2-1=β-1/2 by ring]
    ring

/-- Logarithmic differentiation with all divisions justified away from poles. -/
theorem regular_deriv_log (α β θ p : ℝ) (n : ℕ)
    (hs : Real.sin (θ/2) ≠ 0) (hc : Real.cos (θ/2) ≠ 0)
    (hP : HasDerivAt (polynomial α β n) p (Real.cos θ)) :
    deriv (regularFunction α β n) θ =
      ((α+1/2)*Real.cos (θ/2)/(2*Real.sin (θ/2)) -
       (β+1/2)*Real.sin (θ/2)/(2*Real.cos (θ/2)))*regularFunction α β n θ -
      Real.rpow (Real.sin (θ/2)) (α+1/2)*
        Real.rpow (Real.cos (θ/2)) (β+1/2)*Real.sin θ*p := by
  rw [(regular_hasDerivAt α β θ p n hs hc hP).deriv]
  simp only [regularFunction, Real.rpow_eq_pow]
  rw [show α-1/2=(α+1/2)-1 by ring, Real.rpow_sub_one hs,
    show β-1/2=(β+1/2)-1 by ring, Real.rpow_sub_one hc]
  field_simp
  ring

/-- Algebra behind the first-order cancellation after half-angle conjugation. -/
theorem half_angle_log_algebra (α β k S C : ℝ) (hS : S ≠ 0) (hC : C ≠ 0)
    (hSC : S^2+C^2=1) :
    (α+1/2)*C/(2*S)-(β+1/2)*S/(2*C) -
      ((3/2)*(C^2-S^2)+k)/(2*S*C) =
      (α-β-2*k+(α+β-2)*(C^2-S^2))/(4*S*C) := by
  field_simp
  linear_combination 4*(α-β)*hSC

/-- The actual first-order expression on a Jacobi representative, before
choosing endpoint indices. This formula displays the critical cancellation. -/
theorem regular_lowering_formula (α β k θ p : ℝ) (n : ℕ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hP : HasDerivAt (polynomial α β n) p (Real.cos θ)) :
    deriv (regularFunction α β n) θ -
      ((3/2)*Real.cos θ+k)/Real.sin θ*regularFunction α β n θ =
      (α-β-2*k+(α+β-2)*Real.cos θ)/(2*Real.sin θ)*regularFunction α β n θ -
      Real.rpow (Real.sin (θ/2)) (α+1/2)*
        Real.rpow (Real.cos (θ/2)) (β+1/2)*Real.sin θ*p := by
  have hS : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hC : Real.cos (θ/2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hsin : Real.sin θ=2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.sin_two_mul (θ/2)
  have hcos : Real.cos θ=(Real.cos (θ/2))^2-(Real.sin (θ/2))^2 := by
    simpa only [show θ/2+θ/2=θ by ring, ← pow_two] using Real.cos_add (θ/2) (θ/2)
  have halg := half_angle_log_algebra α β k (Real.sin (θ/2)) (Real.cos (θ/2))
    hS hC (Real.sin_sq_add_cos_sq (θ/2))
  rw [regular_deriv_log α β θ p n hS hC hP]
  have hcanc :
      (α+1/2)*Real.cos (θ/2)/(2*Real.sin (θ/2)) -
       (β+1/2)*Real.sin (θ/2)/(2*Real.cos (θ/2)) -
       ((3/2)*Real.cos θ+k)/Real.sin θ =
      (α-β-2*k+(α+β-2)*Real.cos θ)/(2*Real.sin θ) := by
    rw [hsin,hcos]
    convert halg using 1
    congr 1
    ring
  linear_combination regularFunction α β n θ*hcanc

/-- The lowest upper Jacobi function is in the kernel of the off-diagonal
first-order expression whenever its two endpoint indices sum to two. -/
theorem regular_ground_lowering_zero (α β k θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hsum : α+β=2) (hdiff : α-β=2*k) :
    deriv (regularFunction α β 0) θ -
      ((3/2)*Real.cos θ+k)/Real.sin θ*regularFunction α β 0 θ = 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have ht := Real.sin_sq_add_cos_sq θ
  have hx : Real.cos θ ∈ Set.Ioo (-1) 1 := by
    constructor <;> nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_pos_of_pos hs]
  rw [regular_lowering_formula α β k θ 0 0 hθ (polynomial_zero_hasDerivAt α β _ hx)]
  rw [hsum,hdiff]
  ring

/-- Exact central-index first-order image, including the normalization
constant. The target is an already known L² Jacobi function. -/
theorem regular_central_lowering (α β k θ : ℝ) (n : ℕ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hsum : α+β=2) (hdiff : α-β=2*k) :
    deriv (regularFunction α β (n+1)) θ -
      ((3/2)*Real.cos θ+k)/Real.sin θ*regularFunction α β (n+1) θ =
      -((n : ℝ)+4)*regularFunction (α+1) (β+1) n θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have ht := Real.sin_sq_add_cos_sq θ
  have hx : Real.cos θ ∈ Set.Ioo (-1) 1 := by
    constructor <;> nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_pos_of_pos hs]
  have hS : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hC : Real.cos (θ/2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hsin : Real.sin θ=2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.sin_two_mul (θ/2)
  rw [regular_lowering_formula α β k θ _ (n+1) hθ (dlmf_18_9_15 α β _ n hx)]
  rw [hsum,hdiff]
  simp only [sub_self, zero_mul, zero_add, zero_div, zero_sub, regularFunction,
    Real.rpow_eq_pow]
  rw [show α+1+1/2=(α+1/2)+1 by ring, Real.rpow_add_one hS,
      show β+1+1/2=(β+1/2)+1 by ring, Real.rpow_add_one hC,hsin]
  push_cast
  have hn : (n : ℝ)+1+α+β+1=(n : ℝ)+4 := by linarith
  rw [hn]
  ring

/-- Right-end parameter ladder for the noncentral positive Fourier indices. -/
theorem regular_right_lowering (β θ : ℝ) (n : ℕ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    deriv (regularFunction (β+2) β n) θ -
      ((3/2)*Real.cos θ+(β+1))/Real.sin θ*regularFunction (β+2) β n θ =
      -((n : ℝ)+β)*regularFunction (β+3) (β-1) n θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have ht := Real.sin_sq_add_cos_sq θ
  have hx : Real.cos θ ∈ Set.Ioo (-1) 1 := by
    constructor <;> nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_pos_of_pos hs]
  have hS : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hC : Real.cos (θ/2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hsin : Real.sin θ=2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.sin_two_mul (θ/2)
  have hcos : Real.cos θ=2*(Real.cos (θ/2))^2-1 := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.cos_two_mul (θ/2)
  have hcos' : Real.cos θ=1-2*(Real.sin (θ/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  have hL := derivative_shift_right (β+2) β (Real.cos θ) n hx
  rw [regular_lowering_formula (β+2) β (β+1) θ _ n hθ
    (polynomial_hasDerivAt (β+2) β _ n hx)]
  have hcoef : ((β+2)-β-2*(β+1)+((β+2)+β-2)*Real.cos θ)/(2*Real.sin θ) =
      -β*Real.sin (θ/2)/Real.cos (θ/2) := by
    rw [hcos',hsin]
    field_simp
    ring
  rw [hcoef]
  simp only [regularFunction, Real.rpow_eq_pow]
  rw [show β+3+1/2=(β+2+1/2)+1 by ring,Real.rpow_add_one hS,
    show β-1+1/2=(β+1/2)-1 by ring,Real.rpow_sub_one hC]
  rw [show β+3=(β+2)+1 by ring]
  have hcx : 1+Real.cos θ=2*(Real.cos (θ/2))^2 := by linarith [hcos]
  rw [hcx] at hL
  rw [hsin]
  field_simp
  linear_combination -Real.sin (θ/2)^((2*(β+2)+1)/2)*Real.cos (θ/2)^((β*2+1)/2)*hL

/-- Left-end parameter ladder for the noncentral negative Fourier indices. -/
theorem regular_left_lowering (α θ : ℝ) (n : ℕ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    deriv (regularFunction α (α+2) n) θ -
      ((3/2)*Real.cos θ+(-α-1))/Real.sin θ*regularFunction α (α+2) n θ =
      ((n : ℝ)+α)*regularFunction (α-1) (α+3) n θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have ht := Real.sin_sq_add_cos_sq θ
  have hx : Real.cos θ ∈ Set.Ioo (-1) 1 := by
    constructor <;> nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_pos_of_pos hs]
  have hS : Real.sin (θ/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hC : Real.cos (θ/2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hsin : Real.sin θ=2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.sin_two_mul (θ/2)
  have hcos : Real.cos θ=2*(Real.cos (θ/2))^2-1 := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.cos_two_mul (θ/2)
  have hcos' : Real.cos θ=1-2*(Real.sin (θ/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  have hL := derivative_shift_left α (α+2) (Real.cos θ) n hx
  rw [regular_lowering_formula α (α+2) (-α-1) θ _ n hθ
    (polynomial_hasDerivAt α (α+2) _ n hx)]
  have hcoef : (α-(α+2)-2*(-α-1)+(α+(α+2)-2)*Real.cos θ)/(2*Real.sin θ) =
      α*Real.cos (θ/2)/Real.sin (θ/2) := by
    rw [hcos,hsin]
    field_simp
    ring
  rw [hcoef]
  simp only [regularFunction, Real.rpow_eq_pow]
  rw [show α-1+1/2=(α+1/2)-1 by ring,Real.rpow_sub_one hS,
    show α+3+1/2=(α+2+1/2)+1 by ring,Real.rpow_add_one hC]
  rw [show α+3=(α+2)+1 by ring]
  have hcx : 1-Real.cos θ=2*(Real.sin (θ/2))^2 := by linarith [hcos']
  rw [hcx] at hL
  rw [hsin]
  field_simp
  linear_combination -Real.sin (θ/2)^((α*2+1)/2)*Real.cos (θ/2)^((2*(α+2)+1)/2)*hL

end
end KN.Angular.Jacobi

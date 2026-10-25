import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace KN.Angular
open scoped ComplexInnerProductSpace
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Passage from pointwise static spectral multipliers to the quadratic form
on the entire first-order domain. The basis is for the static operator only;
no eigenbasis is postulated at complex frequency. -/
theorem spectral_form_nonneg (basis : HilbertBasis ι ℂ E) (ν : ι → ℝ)
    (u x : E) (hcoeff : ∀ i, ⟪basis i,x⟫ = (ν i : ℂ)*⟪basis i,u⟫)
    (β t σ : ℝ) (hscalar : ∀ i, 0 ≤ (ν i)^2-β^2+t*(ν i-σ*β)) :
    0 ≤ ‖x‖^2-β^2*‖u‖^2+t*((⟪u,x⟫).re-σ*β*‖u‖^2) := by
  have hxx := basis.hasSum_inner_mul_inner x x
  have huu := basis.hasSum_inner_mul_inner u u
  have hux := basis.hasSum_inner_mul_inner u x
  have hc := (hxx.sub (huu.mul_left ((β : ℂ)^2))).add
    ((hux.sub (huu.mul_left ((σ : ℂ)*β))).mul_left (t : ℂ))
  have hr := Complex.hasSum_re hc
  have hnonneg : ∀ i, 0 ≤
      ((⟪x,basis i⟫*⟪basis i,x⟫-(β : ℂ)^2*(⟪u,basis i⟫*⟪basis i,u⟫))+
      (t : ℂ)*(⟪u,basis i⟫*⟪basis i,x⟫-(σ : ℂ)*β*(⟪u,basis i⟫*⟪basis i,u⟫))).re := by
    intro i
    rw [← inner_conj_symm x (basis i), ← inner_conj_symm u (basis i), hcoeff]
    simp only [map_mul, Complex.conj_ofReal]
    have heq :
        ((starRingEnd ℂ) ⟪basis i,u⟫*(ν i : ℂ)*((ν i : ℂ)*⟪basis i,u⟫)-
        (β : ℂ)^2*((starRingEnd ℂ) ⟪basis i,u⟫*⟪basis i,u⟫))+
        (t : ℂ)*((starRingEnd ℂ) ⟪basis i,u⟫*((ν i : ℂ)*⟪basis i,u⟫)-
        (σ : ℂ)*β*((starRingEnd ℂ) ⟪basis i,u⟫*⟪basis i,u⟫)) =
        (((ν i)^2-β^2+t*(ν i-σ*β) : ℝ) : ℂ)*
          ((starRingEnd ℂ) ⟪basis i,u⟫*⟪basis i,u⟫) := by
      push_cast
      ring
    rw [mul_comm (ν i : ℂ) ((starRingEnd ℂ) ⟪basis i,u⟫), heq,
      Complex.conj_mul']
    norm_cast
    exact mul_nonneg (hscalar i) (sq_nonneg ‖⟪basis i,u⟫‖)
  have hsum := HasSum.nonneg hnonneg hr
  simp only [inner_self_eq_norm_sq_to_K, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    ← Complex.ofReal_pow, sub_zero, zero_mul, mul_zero, add_zero] at hsum
  norm_cast at hsum

end KN.Angular

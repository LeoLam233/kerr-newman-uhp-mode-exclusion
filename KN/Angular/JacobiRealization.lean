import KN.Angular.JacobiParameters
import Mathlib.Tactic.Positivity

namespace KN.Angular
noncomputable section

def scalarPotential (σ m s θ : ℝ) : ℝ :=
  (m^2+s^2-1/4+2*σ*m*s*Real.cos θ)/(Real.sin θ)^2-9/4

theorem jacobi_potential_specialization (σ m s θ : ℝ) (hσ : σ^2=1)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Jacobi.potential |σ*m+s| |σ*m-s| θ = scalarPotential σ m s θ+9/4 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have htrig := Real.sin_sq_add_cos_sq θ
  have hm : 1-Real.cos θ ≠ 0 := by intro h; nlinarith [sq_pos_of_pos hs]
  have hp : 1+Real.cos θ ≠ 0 := by intro h; nlinarith [sq_pos_of_pos hs]
  have htwo : 2*(θ/2)=θ := by ring
  have hsin : 4*(Real.sin (θ/2))^2 = 2*(1-Real.cos θ) := by
    rw [Real.sin_sq_eq_half_sub, htwo]; ring
  have hcos : 4*(Real.cos (θ/2))^2 = 2*(1+Real.cos θ) := by
    rw [Real.cos_sq, htwo]; ring
  unfold Jacobi.potential
  rw [hsin,hcos,jacobi_potential_algebra σ m s (Real.cos θ) hσ hm hp]
  unfold scalarPotential
  rw [show 1-(Real.cos θ)^2=(Real.sin θ)^2 by nlinarith]
  ring

/-- Actual smooth scalar Jacobi functions solve the manuscript's (11), with
exact eigenvalue ell(ell+1)-2. First-order graph membership is separate. -/
theorem scalar_jacobi_eigenfunction (σ m s : ℝ) (hσ : |σ|=1) (hs : 0 ≤ s)
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    -deriv (deriv (Jacobi.regularFunction |σ*m+s| |σ*m-s| n)) θ +
      scalarPotential σ m s θ*Jacobi.regularFunction |σ*m+s| |σ*m-s| n θ =
      (((n : ℝ)+max |m| s)*((n : ℝ)+max |m| s+1)-2)*
        Jacobi.regularFunction |σ*m+s| |σ*m-s| n θ := by
  have hσ2 : σ^2=1 := by nlinarith [sq_abs σ]
  have hDE := Jacobi.regular_differential_equation |σ*m+s| |σ*m-s|
    (abs_nonneg _) (abs_nonneg _) n θ hθ
  rw [jacobi_potential_specialization σ m s θ hσ2 hθ] at hDE
  have heig := jacobi_spectral_shift σ m s (n : ℝ) hσ hs
  calc
    _ = (((n : ℝ)+(|σ*m+s|+|σ*m-s|+1)/2)^2-9/4)*
        Jacobi.regularFunction |σ*m+s| |σ*m-s| n θ := by nlinarith [hDE]
    _ = _ := by rw [heig]

/-- The imported complete regular family is a genuine Hilbert basis, not an
assumed eigenbasis of any complex-frequency angular operator. -/
def scalarJacobiBasis (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    HilbertBasis ℕ ℂ Jacobi.H :=
  HilbertBasis.mk (Jacobi.orthonormal_complete α β hα hβ).1
    (by rw [Submodule.dense_iff_topologicalClosure_eq_top.mp
          (Jacobi.orthonormal_complete α β hα hβ).2])

end
end KN.Angular

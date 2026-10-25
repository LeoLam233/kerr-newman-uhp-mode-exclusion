import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace KN.Angular
noncomputable section

/-- The frequency multiplier in the original Pauli basis of (9). -/
def multiplier (σ a κ c θ : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  (-σ*a*((c*Real.cos θ : ℝ) - Complex.I*(κ*Real.sin θ : ℝ))*u.2,
   -σ*a*((c*Real.cos θ : ℝ) + Complex.I*(κ*Real.sin θ : ℝ))*u.1)

/-- Pointwise Pauli algebra underlying equation (19). -/
theorem multiplier_sq (σ a κ c θ : ℝ) (hσ : σ^2=1) (hκ : κ^2-c^2=1)
    (u : ℂ × ℂ) :
    multiplier σ a κ c θ (multiplier σ a κ c θ u) =
      ((a^2*(c^2+(Real.sin θ)^2) : ℝ) : ℂ) • u := by
  have hr : σ^2*a^2*(c^2*(Real.cos θ)^2+κ^2*(Real.sin θ)^2) =
      a^2*(c^2+(Real.sin θ)^2) := by
    rw [hσ, one_mul]
    have ht := Real.sin_sq_add_cos_sq θ
    have hk : κ^2 = c^2+1 := by linarith
    rw [hk]
    have ht2 : (Real.cos θ)^2 = 1-(Real.sin θ)^2 := by linarith
    rw [ht2]
    ring
  have hc : ((σ : ℂ)^2*(a : ℂ)^2*((c : ℂ)^2*(Real.cos θ : ℂ)^2+
      (κ : ℂ)^2*(Real.sin θ : ℂ)^2)) =
      ((a^2*(c^2+(Real.sin θ)^2) : ℝ) : ℂ) := by
    exact_mod_cast hr
  ext <;> simp only [multiplier, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> rw [← hc] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end
end KN.Angular

import KN.Analysis.ResolventSelfAdjoint
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

namespace KN.Analysis
noncomputable section
open KN.Angular.External

def raySlope (j : Fin 8) : ℝ := |Real.sin (Real.pi/8+(j.val:ℝ)*Real.pi/4)|

theorem raySlope_pos (j : Fin 8) : 0<raySlope j := by
  apply abs_pos.mpr
  have hθ : (0<Real.pi/8+(j.val:ℝ)*Real.pi/4 ∧ Real.pi/8+(j.val:ℝ)*Real.pi/4<Real.pi) ∨
      (Real.pi<Real.pi/8+(j.val:ℝ)*Real.pi/4 ∧ Real.pi/8+(j.val:ℝ)*Real.pi/4<2*Real.pi) := by
    fin_cases j <;> norm_num <;>
      first | (left; constructor <;> linarith [Real.pi_pos]) | (right; constructor <;> linarith [Real.pi_pos])
  rcases hθ with h | h
  · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h.1 h.2)
  · let θ := Real.pi/8+(j.val:ℝ)*Real.pi/4
    change Real.sin θ ≠ 0
    rw [show θ=(θ-Real.pi)+Real.pi by ring, Real.sin_add_pi]
    apply neg_ne_zero.mpr
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by dsimp [θ]; linarith) (by dsimp [θ]; linarith))

theorem completenessRay_abs_im (j : Fin 8) (r : ℝ) (hr : 0≤r) :
    |(completenessRay j r).im|=r*raySlope j := by
  simp [completenessRay, Complex.mul_im, Complex.exp_im, abs_mul, abs_of_nonneg hr, raySlope]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- All eight actual nonreal rays meet the resolvent-set hypothesis of the
Mityagin--Siegl interface, with the stronger uniform bound C=1 and N=0. -/
theorem boundedPerturbation_eight_rays (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (B : E →L[ℂ] E) :
    ∀ j : Fin 8, ∃ (C R : ℝ) (N : ℕ), 0<C ∧ 0<R ∧
      ∀ r : ℝ, R≤r → ∃ Q : ResolventAt (boundedPerturbation T B) (completenessRay j r),
        ‖Q.inverse‖≤C*(1+r)^N := by
  intro j
  have hc := raySlope_pos j
  refine ⟨1,(‖B‖+1)/raySlope j,0,by norm_num,by positivity,?_⟩
  intro r hr
  have hr0 : 0≤r := le_trans (by positivity) hr
  have hbig : ‖B‖+1 ≤ |(completenessRay j r).im| := by
    rw [completenessRay_abs_im j r hr0]
    exact (div_le_iff₀ hc).mp hr
  have hz : (completenessRay j r).im ≠ 0 := by
    intro hz
    rw [hz,abs_zero] at hbig
    linarith [norm_nonneg B]
  obtain ⟨R,hR⟩ := selfAdjoint_exists_resolvent T hT (completenessRay j r) hz
  obtain ⟨Q,hQ⟩ := exists_perturbed_resolvent T (completenessRay j r) B R
    |(completenessRay j r).im| (by linarith) hR
  refine ⟨Q,?_⟩
  simp only [pow_zero,mul_one]
  apply hQ.trans
  exact (div_le_one (by linarith)).mpr (by linarith)

end
end KN.Analysis

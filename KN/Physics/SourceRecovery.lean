import KN.Background.Parameters
import KN.Physics.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
namespace KN.Physics
open Matrix

def rho (b : Background) (r θ : ℝ) : ℂ := (r:ℂ) + Complex.I * b.a * Real.cos θ
def rhoStar (b : Background) (r θ : ℝ) : ℂ := (r:ℂ) - Complex.I * b.a * Real.cos θ

theorem rho_ne_zero (b : Background) {r : ℝ} (hr : b.rPlus < r) (θ : ℝ) :
    rho b r θ ≠ 0 := by
  intro h
  have hz := congrArg Complex.re h
  simp [rho] at hz
  linarith [b.rPlus_pos]
theorem rhoStar_ne_zero (b : Background) {r : ℝ} (hr : b.rPlus < r) (θ : ℝ) :
    rhoStar b r θ ≠ 0 := by
  intro h
  have hz := congrArg Complex.re h
  simp [rhoStar] at hz
  linarith [b.rPlus_pos]

def physicalSourceMatrix (b : Background) (r θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sourceMatrix b.M b.Q b.a r (Real.sqrt (b.Delta r)) (Real.sin θ) (Real.cos θ)

theorem physicalSourceMatrix_det (b : Background) {r : ℝ} (hr : b.rPlus < r) (θ : ℝ) :
    (physicalSourceMatrix b r θ).det = -(b.d : ℂ) := by
  unfold physicalSourceMatrix
  rw [sourceMatrix_det]
  · simp [Background.d]
  · exact rho_ne_zero b hr θ
  · exact rhoStar_ne_zero b hr θ
  · have hs := Real.sq_sqrt (le_of_lt (b.Delta_pos hr))
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hs
    simpa [Background.Delta] using hc
  · exact_mod_cast Real.sin_sq_add_cos_sq θ

theorem physicalSourceMatrix_det_ne_zero (b : Background) {r : ℝ}
    (hr : b.rPlus < r) (θ : ℝ) : (physicalSourceMatrix b r θ).det ≠ 0 := by
  rw [physicalSourceMatrix_det b hr θ]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr b.d_ne)

/-- The actual adjugate source map is injective, without division by any PDE coefficient. -/
theorem adjugate_mulVec_eq_zero_iff {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det ≠ 0)
    (v : Fin 2 → ℂ) : A.adjugate *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have h := congrArg (fun z => A *ᵥ z) hv
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h
    exact (smul_eq_zero.mp h).resolve_left hA
  · intro hv; subst v; simp

/-- Nonzero background Maxwell coefficient makes the phantom gauge legitimate at signed charge. -/
theorem phantomMaxwell_ne_zero (b : Background) (hQ : b.Q ≠ 0)
    {r : ℝ} (hr : b.rPlus < r) (θ : ℝ) :
    (b.Q : ℂ) / (2 * rhoStar b r θ ^ 2) ≠ 0 := by
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr hQ)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (rhoStar_ne_zero b hr θ)))

/-- Recover two original components from both chiral combinations. -/
theorem recover_chiral_pair {u v α : ℂ} (hα : α ≠ 0)
    (hp : u + α*v = 0) (hm : u - α*v = 0) : u = 0 ∧ v = 0 := by
  have hu : u = 0 := by linear_combination (hp + hm) / 2
  have hv : α*v = 0 := by simpa [hu] using hp
  exact ⟨hu, (mul_eq_zero.mp hv).resolve_left hα⟩

end KN.Physics

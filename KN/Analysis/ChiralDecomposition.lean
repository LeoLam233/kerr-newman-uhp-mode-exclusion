import KN.Angular.ChiralEmbedding
import KN.Physics.MatrixAlgebra

noncomputable section
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
namespace KN.Analysis
open Matrix KN.Angular KN.Physics

theorem chiral_orthogonal_partner :
    chiralEmbedding.conjTranspose * I4 * chiralEmbedding = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralEmbedding,I4,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,
      Matrix.conjTranspose_apply,Complex.conj_I,Complex.I_sq,map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem chiral_complete_pair :
    chiralEmbedding * chiralEmbedding.conjTranspose +
      I4 * chiralEmbedding * chiralEmbedding.conjTranspose * I4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralEmbedding,I4,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,
      Matrix.conjTranspose_apply,Complex.conj_I,Complex.I_sq,map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem I4_conjTranspose : I4.conjTranspose=I4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [I4,Matrix.conjTranspose_apply]

/-- Explicit recovery of an arbitrary full fiber from the two chiral sectors. -/
theorem full_fiber_chiral_reconstruction (v : Fin 4 → ℂ) :
    chiralEmbedding *ᵥ (chiralEmbedding.conjTranspose *ᵥ v) +
      I4 *ᵥ (chiralEmbedding *ᵥ (chiralEmbedding.conjTranspose *ᵥ (I4 *ᵥ v))) = v := by
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.add_mulVec]
  have hm : chiralEmbedding * chiralEmbedding.conjTranspose +
      I4 * (chiralEmbedding * (chiralEmbedding.conjTranspose * I4)) = 1 := by
    simpa only [Matrix.mul_assoc] using chiral_complete_pair
  rw [hm, Matrix.one_mulVec]

end KN.Analysis

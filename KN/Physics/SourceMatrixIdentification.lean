import KN.Physics.PhysicalTransform

noncomputable section
namespace KN.Physics
open Matrix
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem sourceMatrix_adjugate (M Q a r t sn cs : ℂ) :
    (sourceMatrix M Q a r t sn cs).adjugate = sourceAdj M Q a r t sn cs := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceMatrix,sourceAdj,Matrix.adjugate_fin_two]

theorem sourceMatrix_conjTranspose_real (M Q a r t sn cs : ℝ) :
    (sourceMatrix M Q a r t sn cs).conjTranspose = sourceStar M Q a r t sn cs := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceMatrix,sourceStar,Matrix.conjTranspose_apply,Complex.conj_I,
      map_add,map_sub,map_mul,map_div,map_pow] <;> ring

end KN.Physics

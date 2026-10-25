import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace KN.Physics
open Matrix

def I4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
def J4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]
def derivativeMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![Complex.I,0,0,0; 0,Complex.I,0,0; 0,0,-Complex.I,0; 0,0,0,-Complex.I]
def angularMatrix (W T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,Complex.I*W,Complex.I*T; 0,0,Complex.I*T,-Complex.I*W;
     -Complex.I*W,-Complex.I*T,0,0; -Complex.I*T,Complex.I*W,0,0]

theorem I4_sq : I4 * I4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [I4, Matrix.mul_apply, Fin.sum_univ_succ]
theorem J4_sq : J4 * J4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [J4, Matrix.mul_apply, Fin.sum_univ_succ]
theorem IJ_anticommute : I4 * J4 = -(J4 * I4) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [I4, J4, Matrix.mul_apply, Fin.sum_univ_succ]
theorem derivative_I_anticommute : derivativeMatrix * I4 = -(I4 * derivativeMatrix) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [I4, derivativeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
theorem derivative_J_anticommute : derivativeMatrix * J4 = -(J4 * derivativeMatrix) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [J4, derivativeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
theorem angular_I_anticommute (W T : ℂ) : angularMatrix W T * I4 = -(I4 * angularMatrix W T) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [I4, angularMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
theorem angular_J_anticommute (W T : ℂ) : angularMatrix W T * J4 = -(J4 * angularMatrix W T) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J4, angularMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Source matrix (6), with independent complex algebraic coordinate parameters. -/
def sourceMatrix (M Q a r t sn cs : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Q*(t+a*sn)/(r+Complex.I*a*cs), -Complex.I*(M-Q^2/(r+Complex.I*a*cs));
    Complex.I*(M-Q^2/(r-Complex.I*a*cs)), Q*(t-a*sn)/(r-Complex.I*a*cs)]

theorem sourceMatrix_det (M Q a r t sn cs : ℂ)
    (hp : r + Complex.I*a*cs ≠ 0) (hm : r - Complex.I*a*cs ≠ 0)
    (ht : t^2 = r^2 - 2*M*r + a^2 + Q^2) (htrig : sn^2 + cs^2 = 1) :
    (sourceMatrix M Q a r t sn cs).det = -(M^2-Q^2) := by
  rw [Matrix.det_fin_two]
  change (Q*(t+a*sn)/(r+Complex.I*a*cs)) * (Q*(t-a*sn)/(r-Complex.I*a*cs)) -
    (-Complex.I*(M-Q^2/(r+Complex.I*a*cs))) * (Complex.I*(M-Q^2/(r-Complex.I*a*cs))) = -(M^2-Q^2)
  have hp' : r + a*Complex.I*cs ≠ 0 := by simpa only [mul_comm a Complex.I] using hp
  have hm' : r - a*Complex.I*cs ≠ 0 := by simpa only [mul_comm a Complex.I] using hm
  field_simp [hp', hm']
  simp only [Complex.I_sq]
  linear_combination (norm := ring_nf) Q^2 * ht - Q^2*a^2*htrig
  simp [Complex.I_sq]

end KN.Physics

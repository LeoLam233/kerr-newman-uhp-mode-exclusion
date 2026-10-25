import KN.Physics.MatrixAlgebra
import Mathlib.Tactic.Module

noncomputable section
namespace KN.Physics
open Matrix

/-- Explicit conjugate-transpose expression for real background coordinates. -/
def sourceStar (M Q a r t sn cs : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Q*(t+a*sn)/(r-Complex.I*a*cs), -Complex.I*(M-Q^2/(r+Complex.I*a*cs));
    Complex.I*(M-Q^2/(r-Complex.I*a*cs)), Q*(t-a*sn)/(r+Complex.I*a*cs)]
def sourceAdj (M Q a r t sn cs : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Q*(t-a*sn)/(r-Complex.I*a*cs), Complex.I*(M-Q^2/(r+Complex.I*a*cs));
    -Complex.I*(M-Q^2/(r-Complex.I*a*cs)), Q*(t+a*sn)/(r+Complex.I*a*cs)]

def horizonEven (Q a r cs : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2*Q/(r-Complex.I*a*cs),0;0,2*Q/(r+Complex.I*a*cs)]
def horizonOdd (M Q a r sn cs : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-2*Q*a*sn/(r-Complex.I*a*cs),2*Complex.I*(M-Q^2/(r+Complex.I*a*cs));
    -2*Complex.I*(M-Q^2/(r-Complex.I*a*cs)),2*Q*a*sn/(r+Complex.I*a*cs)]

/-- The sum contains exactly one sqrt-Delta factor; its remaining matrix is horizon smooth. -/
theorem source_sum_factor (M Q a r t sn cs : ℂ) :
    sourceAdj M Q a r t sn cs + sourceStar M Q a r t sn cs = t • horizonEven Q a r cs := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sourceAdj, sourceStar, horizonEven] <;> ring
/-- The difference has no sqrt-Delta dependence. -/
theorem source_difference (M Q a r t sn cs : ℂ) :
    sourceAdj M Q a r t sn cs - sourceStar M Q a r t sn cs = horizonOdd M Q a r sn cs := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sourceAdj, sourceStar, horizonOdd] <;> ring

/-- Positive-spin projected horizon coefficients: the even projection gains sqrt Delta. -/
theorem positive_horizon_sum (A B E O : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (U V : Fin 2 → ℂ) (hs : A+B=t • E) (hd : A-B=O) :
    A *ᵥ (U + (Complex.I*t) • V) + B *ᵥ (U - (Complex.I*t) • V) =
    t • (E *ᵥ U + Complex.I • (O *ᵥ V)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hs' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ U) hs
  have hd' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ V) hd
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec] at hs' hd'
  rw [← hd']
  rw [smul_add, smul_smul, mul_comm t Complex.I, ← hs']
  module

/-- Negative-spin odd projection gains sqrt Delta; the other projection does not. -/
theorem negative_horizon_difference (A B E O : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (U V : Fin 2 → ℂ) (hs : A+B=t • E) (hd : A-B=O) :
    A *ᵥ (t • U - Complex.I • V) - B *ᵥ (t • U + Complex.I • V) =
    t • (O *ᵥ U - Complex.I • (E *ᵥ V)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hs' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ V) hs
  have hd' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ U) hd
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec] at hs' hd'
  rw [← hd']
  rw [smul_sub, smul_smul, mul_comm t Complex.I, ← smul_smul, ← hs']
  module

theorem positive_horizon_difference (A B E O : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (U V : Fin 2 → ℂ) (hs : A+B=t • E) (hd : A-B=O) :
    A *ᵥ (U + (Complex.I*t) • V) - B *ᵥ (U - (Complex.I*t) • V) =
    O *ᵥ U + (Complex.I*t^2) • (E *ᵥ V) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hs' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ V) hs
  have hd' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ U) hd
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec] at hs' hd'
  rw [← hd']
  have ht : (Complex.I*t^2) • (E *ᵥ V) = (Complex.I*t) • (A *ᵥ V+B *ᵥ V) := by
    rw [hs',smul_smul]; congr 1; ring
  rw [ht]; module

theorem negative_horizon_sum (A B E O : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (U V : Fin 2 → ℂ) (hs : A+B=t • E) (hd : A-B=O) :
    A *ᵥ (t • U - Complex.I • V) + B *ᵥ (t • U + Complex.I • V) =
    t^2 • (E *ᵥ U) - Complex.I • (O *ᵥ V) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hs' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ U) hs
  have hd' := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℂ => C *ᵥ V) hd
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec] at hs' hd'
  rw [← hd']
  have ht : t^2 • (E *ᵥ U) = t • (A *ᵥ U+B *ᵥ U) := by
    rw [hs',smul_smul,pow_two]
  rw [ht]; module

end KN.Physics

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace KN.Angular
open scoped ComplexInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The first-order eigenvector identity uses no square-operator domain. -/
theorem eigenvalue_expectation (u x y : E) (ω lam : ℂ)
    (hu : ⟪u,u⟫ = 1) (he : x + ω • y = lam • u) :
    lam = ⟪u,x⟫ + ω*⟪u,y⟫ := by
  have h := congrArg (fun z => ⟪u,z⟫) he
  rw [inner_add_right, inner_smul_right, inner_smul_right, hu, mul_one] at h
  exact h.symm

/-- Equation (18), in first-domain form: x=B₀u and y=Vu. Reality of the
expectations is exactly the symmetry assumption, not self-adjointness at ω. -/
theorem squared_eigenvalue_expectation (u x y : E) (ω lam : ℂ)
    (hu : ⟪u,u⟫ = 1) (he : x + ω • y = lam • u)
    (hx : starRingEnd ℂ ⟪u,x⟫ = ⟪u,x⟫)
    (hy : starRingEnd ℂ ⟪u,y⟫ = ⟪u,y⟫) :
    lam^2 = ⟪x,x⟫ + ω*(⟪x,y⟫ + ⟪y,x⟫) + ω^2*⟪y,y⟫ := by
  have hlam := eigenvalue_expectation u x y ω lam hu he
  have hleft : ⟪x + (starRingEnd ℂ ω) • y, u⟫ = lam := by
    rw [inner_add_left, inner_smul_left]
    simp only [starRingEnd_self_apply]
    rw [← inner_conj_symm x u, ← inner_conj_symm y u, hx, hy]
    exact hlam.symm
  have hprod : ⟪x + (starRingEnd ℂ ω) • y, x + ω • y⟫ = lam^2 := by
    rw [he, inner_smul_right, hleft, pow_two]
  rw [inner_add_left, inner_add_right, inner_add_right,
    inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right] at hprod
  simp only [starRingEnd_self_apply] at hprod
  calc
    lam^2 = _ := hprod.symm
    _ = _ := by ring

end KN.Angular

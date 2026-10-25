import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace KN.Angular

/-- The two diagonal second-order potentials are exactly (11); x=cos θ,
y=sin θ. This algebra separates the first-order graph problem from the
Jacobi Sturm–Liouville spectral theorem. -/
theorem static_square_upper (σ m x y : ℝ) (hσ : σ^2=1)
    (hxy : x^2+y^2=1) (hy : y ≠ 0) :
    ((3/2*x+σ*m)/y)^2 + (-3/2-σ*m*x)/y^2 =
      (m^2+(1 : ℝ)^2-1/4+2*σ*m*1*x)/y^2-9/4 := by
  field_simp
  nlinarith [hσ, hxy]

theorem static_square_lower (σ m x y : ℝ) (hσ : σ^2=1)
    (hxy : x^2+y^2=1) (hy : y ≠ 0) :
    ((3/2*x+σ*m)/y)^2 - (-3/2-σ*m*x)/y^2 =
      (m^2+(2 : ℝ)^2-1/4+2*σ*m*2*x)/y^2-9/4 := by
  field_simp
  nlinarith [hσ, hxy]

/-- The static Jacobi eigenvalue gives the stated gap on the paired sector. -/
theorem jacobi_gap (ell : ℝ) (hell : 2 ≤ ell) :
    4 ≤ (ell-1)*(ell+2) := by nlinarith

theorem jacobi_eigenvalue (ell : ℝ) :
    ell*(ell+1)-2 = (ell-1)*(ell+2) := by ring

/-- Only ell=1 can carry a zero mode among ell≥1. -/
theorem zero_branch_unique (ell : ℝ) (hell : 1 ≤ ell) :
    (ell-1)*(ell+2)=0 ↔ ell=1 := by
  constructor
  · intro h; rcases mul_eq_zero.mp h with h | h <;> linarith
  · intro h; subst ell; norm_num

end KN.Angular

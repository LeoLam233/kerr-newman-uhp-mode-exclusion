import KN.Angular.ExternalJacobi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace KN.Angular

/-- Exact Jacobi index shift, including m=0 and the critical pole exponents. -/
theorem jacobi_abs_sum (x s : ℝ) (hs : 0 ≤ s) :
    |x+s|+|x-s| = 2*max |x| s := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (add_nonneg hx hs)]
    by_cases hxs : s ≤ x
    · rw [abs_of_nonneg (sub_nonneg.mpr hxs), max_eq_left hxs]; ring
    · have hxs' : x ≤ s := le_of_lt (lt_of_not_ge hxs)
      rw [abs_of_nonpos (sub_nonpos.mpr hxs'), max_eq_right hxs']; ring
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonpos hx', abs_of_nonpos (by linarith : x-s ≤ 0)]
    by_cases hxs : 0 ≤ x+s
    · rw [abs_of_nonneg hxs, max_eq_right (by linarith : -x ≤ s)]; ring
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hxs)),
        max_eq_left (by linarith : s ≤ -x)]; ring

theorem jacobi_index_sum (σ m s : ℝ) (hσ : |σ|=1) (hs : 0 ≤ s) :
    |σ*m+s|+|σ*m-s| = 2*max |m| s := by
  rw [jacobi_abs_sum _ _ hs, abs_mul, hσ, one_mul]

/-- General trigonometric Jacobi spectral parameter specializes exactly to (12). -/
theorem jacobi_spectral_shift (σ m s n : ℝ) (hσ : |σ|=1) (hs : 0 ≤ s) :
    (n+(|σ*m+s|+|σ*m-s|+1)/2)^2-9/4 =
      (n+max |m| s)*(n+max |m| s+1)-2 := by
  rw [jacobi_index_sum σ m s hσ hs]
  ring

/-- Partial-fraction potential identity needed to specialize the general
Jacobi Sturm–Liouville theorem. -/
theorem jacobi_potential_algebra (σ m s x : ℝ) (hσ : σ^2=1)
    (hm : 1-x ≠ 0) (hp : 1+x ≠ 0) :
    ((|σ*m+s|)^2-1/4)/(2*(1-x)) + ((|σ*m-s|)^2-1/4)/(2*(1+x)) =
      (m^2+s^2-1/4+2*σ*m*s*x)/(1-x^2) := by
  rw [sq_abs, sq_abs]
  have hd : 1-x^2 ≠ 0 := by
    have he : 1-x^2=(1-x)*(1+x) := by ring
    rw [he]; exact mul_ne_zero hm hp
  field_simp
  ring_nf
  rw [hσ]
  ring

end KN.Angular

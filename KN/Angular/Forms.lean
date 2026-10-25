import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace KN.Angular

/-- Static paired angular eigenvalues lie strictly above the possible unpaired branch. -/
theorem paired_gap (q b v : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hbq : b*q = 3/2)
    (hgap : b^2 + 4 ≤ v^2) : b + q < v := by
  have hq2 : q^2 < 1 := by nlinarith
  have hsq : (b+q)^2 < v^2 := by nlinarith
  nlinarith

/-- Both paired branches have a positive lower bound, for either sign of charge. -/
theorem paired_form_pos (q b v : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hbq : b*q = 3/2)
    (hgap : b^2 + 4 ≤ v^2) : 0 < v^2-b^2-q*(v+b) := by
  have h := paired_gap q b v hq hq1 hb hv hbq hgap
  have hp : 0 < v+b := by linarith
  nlinarith [mul_pos hp (show 0 < v-b-q by linarith)]

/-- Signed-charge spectral multiplier positivity; no eigenvalue is presumed real
at nonzero frequency. This theorem is applied only to the static spectrum. -/
theorem signed_static_form_pos (q β ν t σ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hbq : |β| * q = 3/2)
    (hgap : β^2 + 4 ≤ ν^2) (ht : |t| ≤ q) (hσ : |σ| = 1) :
    0 < ν^2 - β^2 + t*(ν-σ*β) := by
  have base := paired_form_pos q |β| |ν| hq hq1 (abs_nonneg _) (abs_nonneg _)
    hbq (by simpa only [sq_abs] using hgap)
  have hnorm : |ν-σ*β| ≤ |ν|+|β| := by
    calc
      |ν-σ*β| ≤ |ν|+|σ*β| := abs_sub _ _
      _ = |ν|+|β| := by rw [abs_mul, hσ, one_mul]
  have hprod : |t*(ν-σ*β)| ≤ q*(|ν|+|β|) := by
    rw [abs_mul]
    exact mul_le_mul ht hnorm (abs_nonneg _) (le_of_lt hq)
  have hlo := neg_abs_le (t*(ν-σ*β))
  rw [sq_abs, sq_abs] at base
  linarith

/-- The actual unpaired branch is −β, not +β. -/
theorem unpaired_minus (β t : ℝ) :
    (-β)^2-β^2+t*(-β-(-1)*β)=0 := by ring

theorem unpaired_plus (β t : ℝ) (ht : β*t < 0) :
    0 < (-β)^2-β^2+t*(-β-1*β) := by nlinarith

/-- Exact rationalized coercivity constant, with no extremal uniformity. -/
theorem epsilon_positive (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < (5 - Real.sqrt (9+16*q^2))/2 := by
  have hs := Real.sq_sqrt (show 0 ≤ 9+16*q^2 by positivity)
  have hn := Real.sqrt_nonneg (9+16*q^2)
  have hq2 : q^2 < 1 := by nlinarith
  nlinarith

theorem epsilon_rationalization (q : ℝ) :
    (5 - Real.sqrt (9+16*q^2))/2 =
      8*(1-q^2)/(5+Real.sqrt (9+16*q^2)) := by
  have hs := Real.sq_sqrt (show 0 ≤ 9+16*q^2 by positivity)
  have hd : 5+Real.sqrt (9+16*q^2) ≠ 0 := by positivity
  field_simp
  nlinarith

end KN.Angular

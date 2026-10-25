import KN.Angular.Forms

namespace KN.Angular

theorem paired_epsilon_bound (q b v : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hbq : b*q=3/2)
    (hgap : b^2+4 ≤ v^2) :
    (5-Real.sqrt (9+16*q^2))/2 ≤ v^2-b^2-q*(v+b) := by
  let s := Real.sqrt (b^2+4)
  have hs : s^2=b^2+4 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hvs : s ≤ v := by nlinarith
  have hsq := paired_gap q b s hq hq1 hb hs0 hbq (by linarith)
  have hmon : s^2-b^2-q*(s+b) ≤ v^2-b^2-q*(v+b) := by
    have := mul_nonneg (sub_nonneg.mpr hvs) (show 0 ≤ v+s-q by linarith)
    nlinarith
  have hsqrt := Real.sq_sqrt (show 0 ≤ 9+16*q^2 by positivity)
  have hsqrt0 := Real.sqrt_nonneg (9+16*q^2)
  have hqs : 2*q*s = Real.sqrt (9+16*q^2) := by
    have h1 : (2*q*s)^2 = 9+16*q^2 := by
      calc
        (2*q*s)^2 = 4*q^2*s^2 := by ring
        _ = 4*q^2*(b^2+4) := by rw [hs]
        _ = 4*(b*q)^2+16*q^2 := by ring
        _ = _ := by rw [hbq]; ring
    nlinarith [mul_nonneg (le_of_lt hq) hs0]
  nlinarith

/-- Sharp static minus-sector bound in (16), before summing spectral weights. -/
theorem signed_minus_epsilon_bound (q β ν t : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hbq : |β| *q=3/2)
    (hgap : β^2+4 ≤ ν^2) (ht : |t| ≤ q) :
    (5-Real.sqrt (9+16*q^2))/2 ≤ ν^2-β^2+t*(ν+β) := by
  have hbase := paired_epsilon_bound q |β| |ν| hq hq1 (abs_nonneg _)
    (abs_nonneg _) hbq (by simpa only [sq_abs] using hgap)
  have hprod : |t*(ν+β)| ≤ q*(|ν|+|β|) := by
    rw [abs_mul]
    exact mul_le_mul ht (abs_add_le _ _) (abs_nonneg _) (le_of_lt hq)
  have := neg_abs_le (t*(ν+β))
  rw [sq_abs,sq_abs] at hbase
  linarith

/-- Sharp paired plus-sector lower bound of (17), including signed β. -/
theorem signed_plus_epsilon_bound (q β ν t : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hbq : |β| *q=3/2)
    (hgap : β^2+4 ≤ ν^2) (ht : |t| ≤ q) (htβ : t*β ≤ 0) :
    (11-Real.sqrt (9+16*q^2))/2 ≤ ν^2-β^2+t*(ν-β) := by
  have hbase := paired_epsilon_bound q |β| |ν| hq hq1 (abs_nonneg _)
    (abs_nonneg _) hbq (by simpa only [sq_abs] using hgap)
  have hν : |β| ≤ |ν| := by nlinarith [sq_abs β,sq_abs ν,abs_nonneg β,abs_nonneg ν]
  have htb : t*β = -(|t| *|β|) := by
    rw [← abs_mul, abs_of_nonpos htβ, neg_neg]
  have htn : -(|t| *|ν|) ≤ t*ν := by simpa only [abs_mul] using neg_abs_le (t*ν)
  have hbound := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hν)
  rw [sq_abs,sq_abs] at hbase
  nlinarith

end KN.Angular

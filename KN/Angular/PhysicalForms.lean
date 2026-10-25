import KN.Background.Parameters
import KN.Angular.Forms

namespace KN.Angular
noncomputable section

/-- Charge ratio of a signed subextremal background. -/
def chargeRatio (b : KN.Background) : ℝ := |b.Q| / b.M

theorem chargeRatio_pos (b : KN.Background) (hQ : b.Q ≠ 0) :
    0 < chargeRatio b := div_pos (abs_pos.mpr hQ) b.mass_pos

theorem chargeRatio_lt_one (b : KN.Background) : chargeRatio b < 1 := by
  unfold chargeRatio
  rw [div_lt_one b.mass_pos]
  have hsq : |b.Q|^2 < b.M^2 := by
    rw [sq_abs]
    nlinarith [b.subextremal, sq_nonneg b.a]
  nlinarith [abs_nonneg b.Q, b.mass_pos]

theorem beta_chargeRatio (b : KN.Background) (hQ : b.Q ≠ 0) :
    |b.beta| * chargeRatio b = 3/2 := by
  unfold KN.Background.beta chargeRatio
  rw [abs_div, abs_mul, abs_mul, abs_of_pos b.mass_pos]
  norm_num
  field_simp [ne_of_gt b.mass_pos, abs_ne_zero.mpr hQ]

theorem multiplier_bound (b : KN.Background) (x : ℝ) (hx : x ≤ -b.h) :
    |b.c/x| ≤ chargeRatio b := by
  have hxneg : x < 0 := lt_of_le_of_lt hx (neg_neg_of_pos b.h_pos)
  have hxabs : b.h ≤ |x| := by rw [abs_of_neg hxneg]; linarith
  have hc : |b.c| = chargeRatio b * b.h := by
    rw [KN.Background.c, abs_div, abs_mul, abs_mul,
      abs_of_pos b.mass_pos, abs_of_pos b.d_pos, b.h_eq]
    norm_num
    unfold chargeRatio
    field_simp [ne_of_gt b.mass_pos, b.d_ne]
  rw [abs_div, hc]
  apply (div_le_iff₀ (abs_pos.mpr (ne_of_lt hxneg))).mpr
  exact mul_le_mul_of_nonneg_left hxabs
    (div_nonneg (abs_nonneg _) (le_of_lt b.mass_pos))

end
end KN.Angular

namespace KN.Angular

theorem physical_paired_form_pos (b : KN.Background) (hQ : b.Q ≠ 0)
    (x ν σ : ℝ) (hx : x ≤ -b.h) (hσ : |σ|=1)
    (hν : b.beta^2+4 ≤ ν^2) :
    0 < ν^2-b.beta^2+(b.c/x)*(ν-σ*b.beta) := by
  exact signed_static_form_pos (chargeRatio b) b.beta ν (b.c/x) σ
    (chargeRatio_pos b hQ) (chargeRatio_lt_one b) (beta_chargeRatio b hQ)
    hν (multiplier_bound b x hx) hσ

theorem physical_unpaired_plus (b : KN.Background) (hQ : b.Q ≠ 0)
    (x : ℝ) (hx : x ≤ -b.h) :
    0 < (-b.beta)^2-b.beta^2+(b.c/x)*(-b.beta-b.beta) := by
  have hxneg : x < 0 := lt_of_le_of_lt hx (neg_neg_of_pos b.h_pos)
  have hc : b.beta*(b.c/x) < 0 := by
    rw [← mul_div_assoc, b.beta_mul_c hQ]
    exact div_neg_of_pos_of_neg (by positivity [b.h_pos]) hxneg
  simpa using unpaired_plus b.beta (b.c/x) hc

end KN.Angular

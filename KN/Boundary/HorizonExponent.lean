import KN.Boundary.GaugeDerivative

noncomputable section
namespace KN.Boundary

def horizonAlpha (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ) : ℂ :=
  -(1+3*(σ:ℂ))/2 + Complex.I*b.frequencyK m ω b.rPlus/(b.delta:ℂ)

theorem horizonAlpha_re (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ) :
    (horizonAlpha b m ω σ).re = -(1+3*σ)/2 +
      (b.rPlus^2+b.a^2)*ω.im/b.delta := by
  simp [horizonAlpha, Background.frequencyK, Complex.div_re, Complex.normSq_ofReal,
    Complex.mul_re, Complex.mul_im]
  field_simp [ne_of_gt b.delta_pos]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem horizonAlpha_positive_gt_neg_two (b : Background) (m : ℤ) (ω : ℂ)
    (hω : 0 < ω.im) : -2 < (horizonAlpha b m ω 1).re := by
  rw [horizonAlpha_re]
  have hB : 0 < b.rPlus^2+b.a^2 := by nlinarith [b.rPlus_pos, sq_nonneg b.a]
  have hp := div_pos (mul_pos hB hω) b.delta_pos
  linarith

theorem horizonAlpha_negative_gt_one (b : Background) (m : ℤ) (ω : ℂ)
    (hω : 0 < ω.im) : 1 < (horizonAlpha b m ω (-1)).re := by
  rw [horizonAlpha_re]
  have hB : 0 < b.rPlus^2+b.a^2 := by nlinarith [b.rPlus_pos, sq_nonneg b.a]
  have hp := div_pos (mul_pos hB hω) b.delta_pos
  linarith

end KN.Boundary

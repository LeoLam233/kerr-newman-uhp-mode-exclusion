import KN.Boundary.GaugeDerivative

noncomputable section
open Set MeasureTheory
namespace KN.Boundary

theorem gaugeIntegrand_intervalIntegrable (b : Background) (m : ℤ) (ω : ℂ)
    {r : ℝ} (hr : b.rPlus < r) :
    IntervalIntegrable (gaugeIntegrand b m ω) volume (2*b.rPlus) r := by
  apply ContinuousOn.intervalIntegrable
  apply (gaugeIntegrand_continuousOn b m ω).mono
  intro x hx
  change min (2*b.rPlus) r ≤ x ∧ x ≤ max (2*b.rPlus) r at hx
  exact lt_of_lt_of_le (lt_min (by linarith [b.rPlus_pos]) hr) hx.1

theorem neg_gaugeIntegrand_im (b : Background) (m : ℤ) (ω : ℂ) (r : ℝ) :
    -(gaugeIntegrand b m ω r).im = ω.im*((r^2+b.a^2)/b.Delta r) := by
  simp [gaugeIntegrand, Background.frequencyK, ← Complex.ofReal_pow]
  ring

theorem gauge_norm_formula (b : Background) (m : ℤ) (ω : ℂ) {r : ℝ}
    (hr : b.rPlus < r) :
    ‖gauge b m ω r‖ = Real.exp (∫ x in (2*b.rPlus)..r,
      ω.im*((x^2+b.a^2)/b.Delta x)) := by
  have hi := gaugeIntegrand_intervalIntegrable b m ω hr
  have him := Complex.imCLM.intervalIntegral_comp_comm hi
  simp only [Complex.imCLM_apply] at him
  rw [gauge, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  change Real.exp (-(∫ x in (2*b.rPlus)..r, gaugeIntegrand b m ω x).im) = _
  rw [← him]
  rw [← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact neg_gaugeIntegrand_im b m ω x

/-- A direct global exponential lower bound for H, with its exact normalization.
No asymptotic expansion or separated-mode assumption is used. -/
theorem gauge_exp_lower_bound (b : Background) (m : ℤ) (ω : ℂ) (hω : 0 < ω.im)
    {r : ℝ} (hr : 2*b.rPlus ≤ r) :
    Real.exp (ω.im*(r-2*b.rPlus)) ≤ ‖gauge b m ω r‖ := by
  have hre : b.rPlus < r := by linarith [b.rPlus_pos]
  rw [gauge_norm_formula b m ω hre]
  apply Real.exp_le_exp.mpr
  have hc : ContinuousOn (fun x => ω.im*((x^2+b.a^2)/b.Delta x)) (uIcc (2*b.rPlus) r) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.div
    · fun_prop
    · unfold Background.Delta; fun_prop
    · intro x hx
      apply ne_of_gt; apply b.Delta_pos
      rw [uIcc_of_le hr] at hx
      linarith [hx.1, b.rPlus_pos]
  have hb : ∀ x ∈ Icc (2*b.rPlus) r, ω.im ≤ ω.im*((x^2+b.a^2)/b.Delta x) := by
    intro x hx
    have hxext : b.rPlus < x := by linarith [hx.1, b.rPlus_pos]
    have hxM : b.M < x := by
      have := b.delta_pos
      dsimp [Background.rPlus] at hxext; linarith
    have hrat : 1 ≤ (x^2+b.a^2)/b.Delta x := by
      apply (le_div_iff₀ (b.Delta_pos hxext)).mpr
      dsimp [Background.Delta]
      nlinarith [b.subextremal, b.mass_pos, sq_nonneg b.a]
    nlinarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hr intervalIntegrable_const hc.intervalIntegrable hb
  simpa [intervalIntegral.integral_const, mul_comm] using hi

end KN.Boundary

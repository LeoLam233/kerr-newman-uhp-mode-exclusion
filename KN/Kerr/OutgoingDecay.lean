import KN.Kerr.GaugeConjugation
import KN.Boundary.GaugeGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace KN.Kerr
open Set Filter
open scoped Topology

/-- Positive-spin ingoing coefficients decay at infinity from the physical
outgoing conormal condition alone. No radial asymptotic expansion is imported. -/
theorem outgoing_coefficient_tendsto_zero
    (b : KN.Background) (m : ℤ) (omega : ℂ) (homega : 0 < omega.im)
    (n : ℕ) (R f : ℝ → ℂ)
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega (n : ℝ) r * f r)
    (hout : KN.Boundary.Outgoing b m omega R) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨N, C, R₀, hC, hR₀, hbound⟩ := hout 0
  let D : ℝ := 1 + b.a ^ 2 + b.Q ^ 2
  let A : ℝ := C * 2 ^ N * D ^ n
  have hD : 0 < D := by dsimp [D]; nlinarith [sq_nonneg b.a, sq_nonneg b.Q]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmajor : ∀ᶠ r : ℝ in atTop,
      ‖f r‖ ≤ (A * Real.exp (4 * omega.im * b.rPlus)) *
        (r ^ (N + 2 * n) * Real.exp (-(2 * omega.im) * r)) := by
    filter_upwards [eventually_ge_atTop (max R₀ (max (2 * b.rPlus) 1))] with r hr
    have hrR : R₀ ≤ r := le_trans (le_max_left _ _) hr
    have hrH : 2 * b.rPlus ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
    have hr1 : 1 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr1
    have hre : b.rPlus < r := by linarith [b.rPlus_pos]
    have hd : 0 < b.Delta r := b.Delta_pos hre
    have hdp : 0 < b.Delta r ^ n := pow_pos hd n
    have hpoly : b.Delta r ≤ D * r ^ 2 := by
      dsimp [Background.Delta, D]
      have har := mul_nonneg (sq_nonneg b.a) (show 0 ≤ r^2-1 by nlinarith)
      have hqr := mul_nonneg (sq_nonneg b.Q) (show 0 ≤ r^2-1 by nlinarith)
      nlinarith [b.mass_pos]
    have hpolyN : b.Delta r ^ n ≤ D ^ n * r ^ (2 * n) := by
      simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (le_of_lt hd) hpoly n
    have hU : ‖KN.Boundary.gauge b m omega r * R r‖ ≤ C * 2 ^ N * r ^ N := by
      have h := hbound r hrR
      simp only [Function.iterate_zero_apply, smul_eq_mul, abs_of_nonneg hr0] at h
      have hp := pow_le_pow_left₀ (show 0 ≤ 1 + r by linarith) (show 1 + r ≤ 2 * r by linarith) N
      calc
        _ ≤ C * (1 + r)^N := h
        _ ≤ C * (2*r)^N := mul_le_mul_of_nonneg_left hp hC
        _ = _ := by rw [mul_pow]; ring
    have hweight : (Real.rpow (b.Delta r) (-(n : ℝ)) : ℂ) * (b.Delta r : ℂ)^n = 1 := by
      change ((b.Delta r ^ (-(n : ℝ)) : ℝ) : ℂ) * (b.Delta r : ℂ)^n = 1
      rw [Real.rpow_neg (le_of_lt hd), Real.rpow_natCast]
      push_cast
      exact inv_mul_cancel₀ (pow_ne_zero n (by exact_mod_cast ne_of_gt hd))
    have hidentity : (KN.Boundary.gauge b m omega r * R r) * (b.Delta r : ℂ)^n =
        KN.Boundary.gauge b m omega r ^ 2 * f r := by
      rw [hrep r hre]
      unfold ingoingFactor
      calc
        _ = (KN.Boundary.gauge b m omega r ^ 2 * f r) *
          ((Real.rpow (b.Delta r) (-(n : ℝ)) : ℂ) * (b.Delta r : ℂ)^n) := by ring
        _ = _ := by rw [hweight, mul_one]
    have hnorm := congrArg norm hidentity
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at hnorm
    have hgauge := KN.Boundary.gauge_exp_lower_bound b m omega homega hrH
    have hexp : Real.exp (2 * omega.im * (r - 2 * b.rPlus)) ≤ ‖KN.Boundary.gauge b m omega r‖ ^ 2 := by
      calc
        _ = Real.exp (omega.im * (r - 2 * b.rPlus)) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ _ := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hgauge 2
    have hprod : Real.exp (2 * omega.im * (r - 2 * b.rPlus)) * ‖f r‖ ≤ A * r ^ (N + 2 * n) := by
      calc
        _ ≤ ‖KN.Boundary.gauge b m omega r‖ ^ 2 * ‖f r‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
        _ = ‖KN.Boundary.gauge b m omega r * R r‖ * b.Delta r ^ n := by simpa only [norm_mul] using hnorm.symm
        _ ≤ (C * 2 ^ N * r ^ N) * (D ^ n * r ^ (2 * n)) :=
          mul_le_mul hU hpolyN (le_of_lt hdp) (by positivity)
        _ = _ := by dsimp [A]; rw [pow_add]; ring
    have hquot := (le_div_iff₀ (Real.exp_pos (2 * omega.im * (r - 2 * b.rPlus)))).mpr
      (show ‖f r‖ * Real.exp (2 * omega.im * (r - 2 * b.rPlus)) ≤ A * r ^ (N + 2 * n) by nlinarith [hprod])
    calc
      ‖f r‖ ≤ A * r ^ (N + 2 * n) / Real.exp (2 * omega.im * (r - 2 * b.rPlus)) := hquot
      _ = _ := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        rw [show -(2 * omega.im * (r - 2 * b.rPlus)) = 4 * omega.im * b.rPlus + -(2 * omega.im) * r by ring,
          Real.exp_add]
        ring
  have hlim : Tendsto (fun r : ℝ => (A * Real.exp (4 * omega.im * b.rPlus)) *
      (r ^ (N + 2 * n) * Real.exp (-(2 * omega.im) * r))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (N + 2 * n : ℕ) (2 * omega.im) (by linarith)).const_mul (A * Real.exp (4 * omega.im * b.rPlus))
    simpa only [Real.rpow_natCast, mul_zero] using h
  exact squeeze_zero_norm' hmajor hlim

end KN.Kerr

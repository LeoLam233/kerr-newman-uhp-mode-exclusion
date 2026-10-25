import KN.Boundary.GaugeDerivative

noncomputable section
namespace KN.Boundary

/-- Extracting a square-root factor shifts precisely the horizon exponent by one half. -/
theorem sqrt_shift (b : Background) {r : ℝ} (hr : b.rPlus < r) (q : ℝ) :
    (Real.rpow (b.Delta r) q : ℂ) * (Real.sqrt (b.Delta r) : ℂ) =
      (Real.rpow (b.Delta r) (q+1/2) : ℂ) := by
  norm_cast
  change b.Delta r ^ q * Real.sqrt (b.Delta r) = b.Delta r ^ (q+1/2)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (b.Delta_pos hr)]

theorem positive_horizon_shift (b : Background) {r : ℝ} (hr : b.rPlus < r) :
    (Real.rpow (b.Delta r) ((-3:ℝ)/4) : ℂ) * (Real.sqrt (b.Delta r) : ℂ) =
      (Real.rpow (b.Delta r) ((-1:ℝ)/4) : ℂ) := by
  convert sqrt_shift b hr ((-3:ℝ)/4) using 1; norm_num

theorem negative_horizon_shift (b : Background) {r : ℝ} (hr : b.rPlus < r) :
    (Real.rpow (b.Delta r) ((3:ℝ)/4) : ℂ) * (Real.sqrt (b.Delta r) : ℂ) =
      (Real.rpow (b.Delta r) ((5:ℝ)/4) : ℂ) := by
  convert sqrt_shift b hr ((3:ℝ)/4) using 1; norm_num

end KN.Boundary

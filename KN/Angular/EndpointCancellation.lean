import KN.Angular.EndpointIndices
import Mathlib.Tactic.Ring

namespace KN.Angular

/-- Leading first-order coefficients at the two poles, in local inward
coordinates. These explicitly retain the critical exponent 1/2. -/
theorem upper_north_coefficient (k : ℝ) :
    (|k+1|+1/2)-(3/2+k) = |k+1|-(k+1) := by ring

theorem lower_north_coefficient (k : ℝ) :
    (|k+2|+1/2)+(3/2+k) = |k+2|+(k+2) := by ring

theorem upper_south_coefficient (k : ℝ) :
    -(|k-1|+1/2)-(-3/2+k) = -(|k-1|+(k-1)) := by ring

theorem lower_south_coefficient (k : ℝ) :
    -(|k-2|+1/2)+(-3/2+k) = (k-2)-|k-2| := by ring

theorem upper_north_critical_cancels (k : ℝ) (h : |k+1|=0) :
    (|k+1|+1/2)-(3/2+k)=0 := by
  have hk := abs_eq_zero.mp h
  rw [upper_north_coefficient,h,hk]; ring

theorem lower_north_critical_cancels (k : ℝ) (h : |k+2|=0) :
    (|k+2|+1/2)+(3/2+k)=0 := by
  have hk := abs_eq_zero.mp h
  rw [lower_north_coefficient,h,hk]; ring

theorem upper_south_critical_cancels (k : ℝ) (h : |k-1|=0) :
    -(|k-1|+1/2)-(-3/2+k)=0 := by
  have hk := abs_eq_zero.mp h
  rw [upper_south_coefficient,h,hk]; ring

theorem lower_south_critical_cancels (k : ℝ) (h : |k-2|=0) :
    -(|k-2|+1/2)+(-3/2+k)=0 := by
  have hk := abs_eq_zero.mp h
  rw [lower_south_coefficient,h,hk]; ring

/-- Away from the critical pole order zero, differentiating loses one power
but still leaves exponent at least 1/2. -/
theorem noncritical_image_exponent (k : ℤ) (hk : k ≠ 0) :
    (1/2 : ℝ) ≤ |(k : ℝ)|+1/2-1 := by
  have hkZ : 1 ≤ |k| := by
    by_cases hp : 0 ≤ k
    · rw [abs_of_nonneg hp]; omega
    · rw [abs_of_nonpos (by omega : k ≤ 0)]; omega
  have hkR : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkZ
  linarith

end KN.Angular

import KN.ChargedRadial.OriginalPair
import KN.Angular.FullField

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial

theorem angular_radialR1_eq (b : KN.Background) (sigma : ℝ) (omega : ℂ) (r : ℝ) :
    KN.Angular.radialR1 b sigma omega r=physicalR1 b sigma omega r := by
  dsimp [KN.Angular.radialR1,physicalR1,KN.Background.c,KN.Background.eta]
  push_cast
  field_simp
  ring

theorem angular_radialR0_div (b : KN.Background) (m : ℤ) (sigma : ℝ) (omega : ℂ)
    {r : ℝ} (hr : b.rPlus<r) :
    KN.Angular.radialR0 b sigma m omega r/(Real.sqrt (b.Delta r):ℂ)=
      (3:ℂ)/4*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ)-
        Complex.I*sigma*(b.frequencyK m omega r-(b.eta:ℂ)*omega*(b.Delta r:ℂ))/(b.Delta r:ℂ) := by
  have hd : (b.Delta r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (b.Delta_pos hr))
  have ht : (Real.sqrt (b.Delta r):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  have ht2 : (Real.sqrt (b.Delta r):ℂ)^2=(b.Delta r:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (b.Delta_pos hr).le
  dsimp [KN.Angular.radialR0]
  rw [(KN.Boundary.delta_hasDerivAt b r).deriv]
  push_cast
  field_simp
  rw [ht2]
  ring

/-- The exact radial basis equations extracted by the angular projection imply
(24) in the selected component ordering for each sign. -/
theorem selected_pair_of_radial_basis
    (positive : Bool) (b : KN.Background) (m : ℤ) (omega lam : ℂ)
    (z1 z2 : ℝ → ℂ)
    (h1 : DifferentiableOn ℝ z1 (Ioi b.rPlus))
    (h2 : DifferentiableOn ℝ z2 (Ioi b.rPlus))
    (he1 : ∀ r>b.rPlus, (Real.sqrt (b.Delta r):ℂ)*deriv z1 r=
      KN.Angular.radialR0 b (if positive then 1 else -1) m omega r*z1 r+
      (KN.Angular.radialR1 b (if positive then 1 else -1) omega r-Complex.I*lam)*z2 r)
    (he2 : ∀ r>b.rPlus, (Real.sqrt (b.Delta r):ℂ)*deriv z2 r=
      -KN.Angular.radialR0 b (if positive then 1 else -1) m omega r*z2 r+
      (KN.Angular.radialR1 b (if positive then 1 else -1) omega r+Complex.I*lam)*z1 r) :
    OriginalSelectedPair b m (if positive then 1 else -1) omega lam
      (if positive then z2 else z1) (if positive then z1 else z2) := by
  intro r hr
  have ht : (Real.sqrt (b.Delta r):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  have hh1 := (eq_div_iff ht).2 (by simpa only [mul_comm] using he1 r hr)
  have hh2 := (eq_div_iff ht).2 (by simpa only [mul_comm] using he2 r hr)
  have hR := angular_radialR0_div b m (if positive then 1 else -1) omega hr
  rw [angular_radialR1_eq] at hh1 hh2
  have hd1 := (h1.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  have hd2 := (h2.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  rw [hh1] at hd1
  rw [hh2] at hd2
  cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
  · push_cast at hR
    constructor
    · convert hd1 using 1
      push_cast
      linear_combination -(z1 r)*hR
    · convert hd2 using 1
      push_cast
      linear_combination (z2 r)*hR
  · push_cast at hR
    constructor
    · convert hd2 using 1
      push_cast
      linear_combination (z2 r)*hR
    · convert hd1 using 1
      push_cast
      linear_combination -(z1 r)*hR

end KN.ChargedRadial

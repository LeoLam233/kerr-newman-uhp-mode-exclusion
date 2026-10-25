import KN.ChargedRadial.PhysicalElimination
import KN.ChargedRadial.HorizonResonance
import KN.Boundary.HorizonExponent

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KN.ChargedRadial

lemma physicalDelta_horizon_zero (b : KN.Background) : (b.Delta b.rPlus:ℂ) = 0 := by
  rw [b.delta_factor]
  simp

lemma physicalDelta_horizon_derivative (b : KN.Background) :
    deriv (fun r => (b.Delta r:ℂ)) b.rPlus = (2*b.delta:ℝ) := by
  rw [(KN.Boundary.delta_hasDerivAt b b.rPlus).ofReal_comp.deriv]
  simp [KN.Background.rPlus]
  ring

/-- The indicial exponent exactly measures the first equation's horizon coefficient. -/
theorem physicalL_horizon_alpha (b : KN.Background) (m : ℤ) (omega : ℂ) (sigma : ℝ) :
    physicalL b m (sigma:ℂ) omega b.rPlus =
      -2*(b.delta:ℂ)*KN.Boundary.horizonAlpha b m omega sigma := by
  unfold physicalL KN.Boundary.horizonAlpha
  rw [physicalDelta_horizon_zero]
  simp only [mul_zero, sub_zero]
  have hd : (b.delta:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt b.delta_pos)
  simp only [KN.Background.rPlus, Complex.ofReal_add]
  field_simp
  ring

/-- At α=-1 the corrected delta is annihilated by ΔD+L. -/
theorem resonance_horizon_coefficient (b : KN.Background) (m : ℤ) (omega : ℂ) (sigma : ℝ)
    (ha : KN.Boundary.horizonAlpha b m omega sigma = -1) :
    physicalL b m (sigma:ℂ) omega b.rPlus = deriv (fun r => (b.Delta r:ℂ)) b.rPlus := by
  rw [physicalL_horizon_alpha, ha, physicalDelta_horizon_derivative]
  push_cast
  ring

/-- The only possible resonance in the upper half-plane is positive spin. -/
theorem resonance_spin_positive (b : KN.Background) (m : ℤ) (omega : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma = 1 ∨ sigma = -1)
    (ha : KN.Boundary.horizonAlpha b m omega sigma = -1) : sigma = 1 := by
  rcases hs with hs | hs
  · exact hs
  subst sigma
  have hh := KN.Boundary.horizonAlpha_negative_gt_one b m omega hw
  rw [ha] at hh
  norm_num at hh

/-- The real part of the exact indicial relation fixes the exceptional frequency height. -/
theorem resonance_frequency_im (b : KN.Background) (m : ℤ) (omega : ℂ)
    (ha : KN.Boundary.horizonAlpha b m omega 1 = -1) :
    omega.im = b.delta/horizonBPlus b := by
  have hh := congrArg Complex.re ha
  rw [KN.Boundary.horizonAlpha_re] at hh
  norm_num at hh
  have hd := b.delta_pos
  have hB := horizonBPlus_pos b
  dsimp [horizonBPlus] at *
  field_simp at hh ⊢
  nlinarith

/-- Exact physical affine coupling at the outer horizon, for both charge signs. -/
theorem physicalR1_horizon (b : KN.Background) (omega : ℂ) :
    physicalR1 b 1 omega b.rPlus = -(horizonG b:ℂ)*omega+Complex.I*b.beta := by
  unfold physicalR1 horizonG KN.Background.c KN.Background.eta
  push_cast
  field_simp
  ring

/-- Full exceptional nonvanishing statement with the physical horizon coupling,
from the actual indicial resonance and genuine angular square identity. -/
theorem resonant_physical_coupling_nonzero
    (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma = 1 ∨ sigma = -1)
    (ha : KN.Boundary.horizonAlpha b m omega sigma = -1)
    (T C D : ℝ) (hT : 0 ≤ T) (hD : D ≤ b.a^2*b.kappa^2)
    (hangular : lam^2 = (b.beta:ℂ)^2+(T:ℂ)+omega*(C:ℂ)+omega^2*(D:ℂ)) :
    physicalR1 b (sigma:ℂ) omega b.rPlus-Complex.I*(sigma:ℂ)*lam ≠ 0 := by
  have hs1 := resonance_spin_positive b m omega sigma hw hs ha
  subst sigma
  simp only [Complex.ofReal_one, mul_one]
  rw [physicalR1_horizon]
  exact exceptional_coupling_nonzero b hQ omega lam T C D
    (resonance_frequency_im b m omega ha) hT hD hangular

end KN.ChargedRadial

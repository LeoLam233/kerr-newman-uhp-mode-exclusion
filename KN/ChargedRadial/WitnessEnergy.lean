import KN.ChargedRadial.PhysicalTransformWitness
import KN.Energy.RawEnergyExclusion
import KN.Energy.InfinityGauge

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial
open KN.Energy

/-- The constructed transform satisfies every regularity, endpoint and
injectivity requirement of the energy exclusion. Only its differential equation
and angular expectations remain to be supplied by the separate algebraic bridges. -/
theorem witness_exterior_zero_of_transformedEquation
    (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ)
    (hw : 0 < omega.im) (T L av C qAvg : ℝ) (hq : qAvg ≤ 1)
    (hlam : lam=(L:ℂ)+omega*av)
    (hlam2 : lam^2=(b.beta:ℂ)^2+T+omega*C+omega^2*((b.a^2*(b.c^2+qAvg):ℝ):ℂ))
    (v : ℝ → ℂ) (witness : PhysicalTransformWitness b m (spinSign positive) omega lam v)
    (hk : ∀ x < -b.h, 0 ≤ angularK b T L (spinSign positive) x)
    (heq : TransformedEquation b (backgroundPolynomialData b m (spinSign positive) omega lam)
      (fun x : ℝ => witness.F (omega*x)) (deriv (fun x : ℝ => witness.F (omega*x)))) :
    EqOn v 0 (Ioi b.rPlus) := by
  apply witness.injective
  have hc := physical_ray_finite_continuity b omega hw witness.F witness.analytic
  have hd := physical_ray_differentiable b omega hw witness.F witness.analytic
  apply raw_transformed_field_zero positive b hQ m omega lam hw T L av C qAvg hq hlam hlam2
    _ _ hd.1 (physical_ray_deriv_differentiableOn b omega hw witness.F witness.analytic)
    hc.1 hc.2 _ _ hk heq
  · convert reflected_growth_of_atBot_bound _ (omega.im*b.rPlus) 1
      (by simpa only [pow_one] using witness.bound) using 1; ring
  · convert reflected_growth_of_atBot_bound _ (omega.im*b.rPlus) 1
      (by simpa only [pow_one] using witness.deriv_bound) using 1; ring

/-- The two explicit rescaling multipliers are nonzero on the exterior. -/
theorem original_zero_of_multiplier_zero (b : KN.Background) (m : ℤ) (omega : ℂ)
    (q e : ℝ) (v w original : ℝ → ℂ)
    (hv : ∀ r ∈ Ioi b.rPlus, v r=KN.Boundary.radialMultiplier b m omega q r*w r)
    (hw : ∀ r ∈ Ioi b.rPlus, w r=KN.Boundary.rescaleFactor b m omega e r*original r)
    (hz : EqOn v 0 (Ioi b.rPlus)) : EqOn original 0 (Ioi b.rPlus) := by
  intro r hr
  have hh := hz hr
  rw [hv r hr,hw r hr] at hh
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
    (KN.Boundary.radialMultiplier_ne_zero b m omega q hr))).resolve_left
      (KN.Boundary.rescaleFactor_ne_zero b m omega e hr)

end KN.ChargedRadial

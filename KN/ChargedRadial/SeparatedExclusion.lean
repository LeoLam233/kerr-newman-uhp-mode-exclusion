import KN.ChargedRadial.WitnessEnergy
import KN.Energy.PhysicalWeylEquation
import KN.ChargedRadial.FactorRegularity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ComplexInnerProductSpace
namespace KN.ChargedRadial
open KN.Energy KN.Boundary

theorem spinSign_cases (positive : Bool) : spinSign positive=1 ∨ spinSign positive= -1 := by
  cases positive <;> simp [spinSign]

/-- A supported transform constructed from the original pair is excluded by the
actual differential equation and physical angular graph coercivity. -/
theorem physical_witness_exterior_zero
    (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ)
    (hw : 0 < omega.im)
    (angular : PhysicalAngularData b m (spinSign positive) omega lam)
    (v : ℝ → ℂ) (witness : PhysicalTransformWitness b m (spinSign positive) omega lam v) :
    EqOn v 0 (Ioi b.rPlus) := by
  apply witness_exterior_zero_of_transformedEquation positive b hQ m omega lam hw
    (‖angular.staticImage‖^2-b.beta^2) (⟪angular.u,angular.staticImage⟫).re
    angular.av angular.cross angular.sineAvg angular.sine_le_one
    angular.first_expectation angular.squared_expectation v witness
  · intro x hx
    exact angular.K_nonneg b hQ m _ (spinSign_cases positive) omega lam hx
  · apply physical_supported_pair_transformedEquation b hQ m (spinSign positive) omega lam
      _ hw witness.pair witness.F witness.transform witness.analytic
    cases positive <;> simp [spinSign]

/-- Charged separated exclusion, for both signs including alpha=-1. The input is
the actual first-order radial system with original horizon and outgoing classes;
there is no supported-pair, transform, energy identity or vanishing premise. -/
theorem charged_separated_exclusion
    (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ)
    (hw : 0 < omega.im)
    (angular : PhysicalAngularData b m (spinSign positive) omega lam)
    (w ws original v z : ℝ → ℂ)
    (hwh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus))
    (hwsh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ws (Ici b.rPlus))
    (hvdef : ∀ r ∈ Ioi b.rPlus,
      v r=radialMultiplier b m omega (-(1+3*spinSign positive)/2) r*w r)
    (hzdef : ∀ r ∈ Ioi b.rPlus,
      z r=(b.Delta r:ℂ)*radialMultiplier b m omega (-(1+3*spinSign positive)/2) r*ws r)
    (hrescale : ∀ r ∈ Ioi b.rPlus,
      w r=rescaleFactor b m omega (3*spinSign positive/4) r*original r)
    (hsmooth : ExteriorSmooth b.rPlus (fun r => gauge b m omega r*original r))
    (hout : PolynomialConormal (fun r => gauge b m omega r*original r))
    (hfirst : ∀ t > b.rPlus,
      (b.Delta t:ℂ)*deriv v t+physicalL b m (spinSign positive) omega t*v t =
      (physicalR1 b (spinSign positive) omega t+Complex.I*(spinSign positive:ℝ)*lam)*z t)
    (hsecond : ∀ t > b.rPlus,
      deriv z t=(physicalR1 b (spinSign positive) omega t-Complex.I*(spinSign positive:ℝ)*lam)*v t) :
    EqOn original 0 (Ioi b.rPlus) := by
  obtain ⟨witness⟩ := physical_transform_witness_of_angular_data b hQ m omega lam
    (spinSign positive) hw (spinSign_cases positive) angular w ws original v z
    hwh hwsh (multiplier_exterior_smooth b m omega (spinSign positive) w v hwh hvdef)
    hvdef hzdef hrescale hsmooth hout hfirst hsecond
  exact original_zero_of_multiplier_zero b m omega _ _ v w original hvdef hrescale
    (physical_witness_exterior_zero positive b hQ m omega lam hw angular v witness)

end KN.ChargedRadial

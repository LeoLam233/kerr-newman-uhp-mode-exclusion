import KN.Angular.FullCoefficientEquation
import KN.Angular.Jordan

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ComplexInnerProductSpace

def firstRadialCoefficient (v : FullAngularHilbert) : FullAngularHilbert →L[ℂ] ℂ :=
  (innerSL ℂ v).comp fullPiPlus

def secondRadialCoefficient (v : FullAngularHilbert) : FullAngularHilbert →L[ℂ] ℂ :=
  (Complex.I • innerSL ℂ v).comp fullPiMinus

theorem firstRadialCoefficient_apply (v u : FullAngularHilbert) :
    firstRadialCoefficient v u=(⟪v,u⟫+⟪fullI v,u⟫)/2 := by
  change ⟪v,(1/2 : ℂ) • (u+fullI u)⟫=_
  rw [inner_smul_right,inner_add_right,← fullI_symmetric]
  ring

theorem secondRadialCoefficient_apply (v u : FullAngularHilbert) :
    secondRadialCoefficient v u=Complex.I*(⟪v,u⟫-⟪fullI v,u⟫)/2 := by
  change Complex.I*⟪v,(1/2 : ℂ) • (u-fullI u)⟫=_
  rw [inner_smul_right,inner_sub_right,← fullI_symmetric]
  ring

theorem radialCoefficient_invert (v u : FullAngularHilbert) :
    ⟪v,u⟫=firstRadialCoefficient v u-Complex.I*secondRadialCoefficient v u ∧
    ⟪fullI v,u⟫=firstRadialCoefficient v u+Complex.I*secondRadialCoefficient v u := by
  rw [firstRadialCoefficient_apply,secondRadialCoefficient_apply]
  constructor <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem firstRadialCoefficient_horizon (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (Z : FullField b hQ σ hσ m ω) (v : FullAngularHilbert) :
    KN.Boundary.HorizonRegular b m ω ((1-2*σ)/4) (fun r => firstRadialCoefficient v (Z.field r)) :=
  Z.horizon_plus.map (innerSL ℂ v)

theorem secondRadialCoefficient_horizon (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (Z : FullField b hQ σ hσ m ω) (v : FullAngularHilbert) :
    KN.Boundary.HorizonRegular b m ω ((1-4*σ)/4) (fun r => secondRadialCoefficient v (Z.field r)) :=
  Z.horizon_minus.map (Complex.I • innerSL ℂ v)

theorem radialCoefficient_equation
    (b : KN.Background) (hQ : b.Q ≠ 0) (σ : ℝ) (hσ : σ=1 ∨ σ= -1)
    (m : ℤ) (ω z : ℂ) (Z : FullField b hQ σ hσ m ω)
    (v w : FullAngularHilbert)
    (hv : v ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain)
    (hchain : (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨v,hv⟩=z • v+w)
    (hchiral : ChiralVector v)
    (hzero : ∀ r, b.rPlus<r → ⟪w,Z.field r⟫=0 ∧ ⟪w,fullI (Z.field r)⟫=0)
    (r : ℝ) (hr : b.rPlus<r) :
    (Real.sqrt (b.Delta r) : ℂ)*deriv (fun t => firstRadialCoefficient v (Z.field t)) r =
      radialR0 b σ m ω r*firstRadialCoefficient v (Z.field r)+
        (radialR1 b σ ω r-Complex.I*(starRingEnd ℂ z))*secondRadialCoefficient v (Z.field r) ∧
    (Real.sqrt (b.Delta r) : ℂ)*deriv (fun t => secondRadialCoefficient v (Z.field t)) r =
      -radialR0 b σ m ω r*secondRadialCoefficient v (Z.field r)+
        (radialR1 b σ ω r+Complex.I*(starRingEnd ℂ z))*firstRadialCoefficient v (Z.field r) := by
  obtain ⟨hp,hq⟩ := fullField_paired_coefficient_equation b hQ σ hσ m ω z Z v w hv hchain hchiral hzero r hr
  erw [KN.Boundary.deriv_clm_on Z.smooth (innerSL ℂ v) hr] at hp
  erw [KN.Boundary.deriv_clm_on Z.smooth (innerSL ℂ (fullI v)) hr] at hq
  change (Real.sqrt (b.Delta r) : ℂ)*⟪v,deriv Z.field r⟫=_ at hp
  change (Real.sqrt (b.Delta r) : ℂ)*⟪fullI v,deriv Z.field r⟫=_ at hq
  rw [(radialCoefficient_invert v (deriv Z.field r)).1,
    (radialCoefficient_invert v (Z.field r)).1,(radialCoefficient_invert v (Z.field r)).2] at hp
  rw [(radialCoefficient_invert v (deriv Z.field r)).2,
    (radialCoefficient_invert v (Z.field r)).1,(radialCoefficient_invert v (Z.field r)).2] at hq
  erw [KN.Boundary.deriv_clm_on Z.smooth (firstRadialCoefficient v) hr,
    KN.Boundary.deriv_clm_on Z.smooth (secondRadialCoefficient v) hr]
  exact radial_basis_change _ _ _ _ _ _ _ _ hp hq

end
end KN.Angular

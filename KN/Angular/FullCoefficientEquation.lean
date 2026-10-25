import KN.Angular.FullOperatorSymmetry
import KN.Angular.ChiralPairing
import KN.Angular.FullField
import KN.Analysis.ResolventBoundaryMap

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped ComplexInnerProductSpace

theorem fullJ_partner_chiral (u : AngularHilbert) :
    fullJ (fullI (chiralLpMap u)) = -Complex.I • chiralLpMap u := by
  have hi : fullI (chiralLpMap u)= -Complex.I • fullJ (chiralLpMap u) := by
    rw [KN.Analysis.fullJ_chiral,smul_smul]
    simp
  rw [hi,map_smul,KN.Analysis.fullJ_involution]

/-- The two dual-chain coefficients satisfy the actual homogeneous paired
radial equations, including at zero spectral parameter. -/
theorem fullField_paired_coefficient_equation
    (b : KN.Background) (hQ : b.Q ≠ 0) (σ : ℝ) (hσ : σ=1 ∨ σ= -1)
    (m : ℤ) (ω z : ℂ) (Z : FullField b hQ σ hσ m ω)
    (v w : FullAngularHilbert)
    (hv : v ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain)
    (hchain : (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨v,hv⟩=z • v+w)
    (hchiral : ChiralVector v)
    (hzero : ∀ r, b.rPlus<r → ⟪w,Z.field r⟫=0 ∧ ⟪w,fullI (Z.field r)⟫=0)
    (r : ℝ) (hr : b.rPlus<r) :
    (Real.sqrt (b.Delta r) : ℂ)*deriv (fun t => ⟪v,Z.field t⟫) r =
      (starRingEnd ℂ z)*⟪v,Z.field r⟫+
        (radialR0 b σ m ω r-Complex.I*radialR1 b σ ω r)*⟪fullI v,Z.field r⟫ ∧
    (Real.sqrt (b.Delta r) : ℂ)*deriv (fun t => ⟪fullI v,Z.field t⟫) r =
      -(starRingEnd ℂ z)*⟪fullI v,Z.field r⟫+
        (radialR0 b σ m ω r+Complex.I*radialR1 b σ ω r)*⟪v,Z.field r⟫ := by
  let A := fullFrequencyOperator b hQ σ hσ m ω
  have hd : Dense (A.domain : Set FullAngularHilbert) :=
    (fullStaticOperator_selfAdjoint b hQ σ hσ m).dense_domain
  have hp := A.adjoint_isFormalAdjoint hd ⟨v,hv⟩ ⟨Z.field r,Z.mem_domain r hr⟩
  change ⟪A.adjoint ⟨v,hv⟩,Z.field r⟫=⟪v,A ⟨Z.field r,Z.mem_domain r hr⟩⟫ at hp
  rw [hchain,inner_add_left,inner_smul_left,(hzero r hr).1,add_zero] at hp
  obtain ⟨hIv,hIstep⟩ := fullFrequencyOperator_adjoint_I b hQ σ hσ m ω ⟨v,hv⟩
  have hq := A.adjoint_isFormalAdjoint hd ⟨fullI v,hIv⟩ ⟨Z.field r,Z.mem_domain r hr⟩
  change ⟪A.adjoint ⟨fullI v,hIv⟩,Z.field r⟫=⟪fullI v,A ⟨Z.field r,Z.mem_domain r hr⟩⟫ at hq
  rw [hIstep,hchain,map_add,map_smul,neg_add,inner_add_left,inner_neg_left,
    inner_smul_left,inner_neg_left,fullI_symmetric w (Z.field r),(hzero r hr).2,neg_zero,add_zero] at hq
  obtain ⟨u,hu⟩ := hchiral
  have hvJ : fullJ v=Complex.I • fullI v := by rw [hu]; exact KN.Analysis.fullJ_chiral u
  have hIvJ : fullJ (fullI v)= -Complex.I • v := by rw [hu]; exact fullJ_partner_chiral u
  have hi1 : ⟪v,fullI (Z.field r)⟫=⟪fullI v,Z.field r⟫ := (fullI_symmetric _ _).symm
  have hi2 : ⟪fullI v,fullI (Z.field r)⟫=⟪v,Z.field r⟫ := by
    rw [← fullI_symmetric,fullI_involution]
  have hj1 : ⟪v,fullJ (Z.field r)⟫= -Complex.I*⟪fullI v,Z.field r⟫ := by
    rw [← KN.Analysis.fullJ_symmetric,hvJ,inner_smul_left,Complex.conj_I]
  have hj2 : ⟪fullI v,fullJ (Z.field r)⟫=Complex.I*⟪v,Z.field r⟫ := by
    rw [← KN.Analysis.fullJ_symmetric,hIvJ,inner_smul_left,map_neg,Complex.conj_I,neg_neg]
  have he1 := congrArg (innerSL ℂ v) (Z.equation r hr)
  have he2 := congrArg (innerSL ℂ (fullI v)) (Z.equation r hr)
  simp only [innerSL_apply_apply,inner_smul_right,inner_add_right] at he1 he2
  rw [← hp,hi1,hj1] at he1
  rw [← hq,hi2,hj2] at he2
  constructor
  · erw [KN.Boundary.deriv_clm_on Z.smooth (innerSL ℂ v) hr]
    simp only [innerSL_apply_apply]
    linear_combination he1
  · erw [KN.Boundary.deriv_clm_on Z.smooth (innerSL ℂ (fullI v)) hr]
    simp only [innerSL_apply_apply]
    linear_combination he2

end
end KN.Angular

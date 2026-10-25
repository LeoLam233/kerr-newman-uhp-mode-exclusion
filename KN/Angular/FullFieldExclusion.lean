import KN.Angular.FullChainExtraction
import KN.Angular.FullCoefficientBoundary
import KN.Angular.PrimalEigenvector
import KN.ChargedRadial.AngularRadialBridge
import KN.ChargedRadial.EigenmodeExclusion

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set
open scoped ComplexInnerProductSpace

/-- Full charged UHP exclusion on the actual maximal angular domain. This theorem
performs chiral adjoint-chain detection, preserves both horizon weights, obtains
a genuine same-parameter right angular eigenvector, and invokes the proved
scalar transform-energy-injectivity argument. It assumes no separation theorem. -/
theorem charged_full_field_exclusion (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0)
    (m : ℤ) (ω : ℂ) (hω : 0<ω.im)
    (Z : FullField b hQ (KN.Energy.spinSign positive) (KN.ChargedRadial.spinSign_cases positive) m ω) :
    EqOn Z.field 0 (Ioi b.rPlus) := by
  classical
  by_contra hnot
  have hne : ∃ r : Ioi b.rPlus, Z.field r≠0 := by
    by_contra! hh
    apply hnot
    intro r hr
    exact hh ⟨r,hr⟩
  obtain ⟨z,v,w,hv,hchain,hdetect,hzero,hchiral,_,e,he,hene,hechiral,hee⟩ :=
    full_chiral_chain_extraction b hQ (KN.Energy.spinSign positive)
      (KN.ChargedRadial.spinSign_cases positive) m ω (fun r : Ioi b.rPlus => Z.field r) hne
  obtain ⟨u,staticImage,hu,hgraph,heigen⟩ :=
    normalized_reduced_eigenvector_of_chiral_adjoint b hQ (KN.Energy.spinSign positive)
      (KN.ChargedRadial.spinSign_cases positive) m ω z e he hee hene hechiral
  let z1 : ℝ → ℂ := fun r => firstRadialCoefficient v (Z.field r)
  let z2 : ℝ → ℂ := fun r => secondRadialCoefficient v (Z.field r)
  have hs1 := ((firstRadialCoefficient v).restrictScalars ℝ).contDiff.comp_contDiffOn Z.smooth
  have hs2 := ((secondRadialCoefficient v).restrictScalars ℝ).contDiff.comp_contDiffOn Z.smooth
  have hd1 : DifferentiableOn ℝ z1 (Ioi b.rPlus) := hs1.differentiableOn (by simp)
  have hd2 : DifferentiableOn ℝ z2 (Ioi b.rPlus) := hs2.differentiableOn (by simp)
  have heq := fun r hr => radialCoefficient_equation b hQ (KN.Energy.spinSign positive)
    (KN.ChargedRadial.spinSign_cases positive) m ω z Z v w hv hchain hchiral
    (fun r hr => hzero ⟨r,hr⟩) r hr
  have hpair := KN.ChargedRadial.selected_pair_of_radial_basis positive b m ω (star z)
    z1 z2 hd1 hd2 (fun r hr => (heq r hr).1) (fun r hr => (heq r hr).2)
  have hh1 := firstRadialCoefficient_horizon b hQ (KN.Energy.spinSign positive)
    (KN.ChargedRadial.spinSign_cases positive) m ω Z v
  have hh2 := secondRadialCoefficient_horizon b hQ (KN.Energy.spinSign positive)
    (KN.ChargedRadial.spinSign_cases positive) m ω Z v
  have hy : KN.Boundary.HorizonRegular b m ω (-(3*KN.Energy.spinSign positive/4))
      (if positive then z2 else z1) := by
    cases positive <;> norm_num [KN.Energy.spinSign,z1,z2] at * <;> assumption
  have hz : KN.Boundary.HorizonRegular b m ω (-(3*KN.Energy.spinSign positive/4-1/2))
      (if positive then z1 else z2) := by
    cases positive <;> norm_num [KN.Energy.spinSign,z1,z2] at * <;> assumption
  have hout : KN.Boundary.Outgoing b m ω (if positive then z2 else z1) := by
    cases positive
    · exact Z.outgoing.map Z.smooth (firstRadialCoefficient v)
    · exact Z.outgoing.map Z.smooth (secondRadialCoefficient v)
  obtain ⟨hy0,hz0⟩ := KN.ChargedRadial.charged_original_eigenmode_exclusion positive b hQ m ω
    (star z) hω u staticImage hu hgraph heigen (if positive then z2 else z1)
    (if positive then z1 else z2) hy hz hout hpair
  have hz10 : EqOn z1 0 (Ioi b.rPlus) := by cases positive <;> assumption
  have hz20 : EqOn z2 0 (Ioi b.rPlus) := by cases positive <;> assumption
  obtain ⟨r,hr⟩ := hdetect
  have hh := radialCoefficient_invert v (Z.field r)
  have h1 : firstRadialCoefficient v (Z.field r)=0 := hz10 r.property
  have h2 : secondRadialCoefficient v (Z.field r)=0 := hz20 r.property
  rw [h1,h2,mul_zero,sub_zero,add_zero] at hh
  rcases hr with hr | hr
  · exact hr hh.1
  · rw [← fullI_symmetric] at hr
    exact hr hh.2

/-- Equivalent signed formulation, with no choice of a Fourier mode bound. -/
theorem full_field_exclusion (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ) (hω : 0<ω.im)
    (Z : FullField b hQ σ hσ m ω) : EqOn Z.field 0 (Ioi b.rPlus) := by
  rcases hσ with rfl | rfl
  · exact charged_full_field_exclusion true b hQ m ω hω Z
  · exact charged_full_field_exclusion false b hQ m ω hω Z

end
end KN.Angular

import KN.Angular.FullCompleteness
import KN.Angular.FullOperatorSymmetry
import KN.Angular.ChiralPairing
import KN.Angular.DualChainExtraction

namespace KN.Angular
noncomputable section
open scoped ComplexInnerProductSpace

/-- A complete adjoint root system produces a chiral chain whose first globally
nonzero paired coefficient has zero predecessor coefficients. The same eigenvalue
also has a genuine nonzero chiral adjoint eigenvector. -/
theorem full_chiral_chain_extraction (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    {R : Type*} (Z : R → FullAngularHilbert) (hne : ∃ r, Z r≠0) :
    ∃ (z : ℂ) (v w : FullAngularHilbert)
      (hv : v ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain),
      (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨v,hv⟩=z • v+w ∧
      (∃ r, ⟪v,Z r⟫≠0 ∨ ⟪v,fullI (Z r)⟫≠0) ∧
      (∀ r, ⟪w,Z r⟫=0 ∧ ⟪w,fullI (Z r)⟫=0) ∧ ChiralVector v ∧ ChiralVector w ∧
      ∃ (e : FullAngularHilbert)
        (he : e ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain),
        e≠0 ∧ ChiralVector e ∧ (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨e,he⟩=z • e := by
  classical
  let T := (fullFrequencyOperator b hQ σ hσ m ω).adjoint
  let W : R × Bool → FullAngularHilbert := fun rs => if rs.2 then fullI (Z rs.1) else Z rs.1
  have hP : ∃ rs, chiralLpMap (chiralProjection (W rs))≠0 := by
    obtain ⟨r,hr⟩ := hne
    by_contra! hh
    apply hr
    have h0 := hh (r,false)
    have h1 := hh (r,true)
    simp only [W,Bool.false_eq_true,ite_false,ite_true] at h0 h1
    have hre := full_chiral_reconstruction (Z r)
    change chiralLpMap (chiralProjection (Z r)) + fullI (chiralLpMap (chiralProjection (fullI (Z r))))=Z r at hre
    rw [h0,h1,map_zero,add_zero] at hre
    exact hre.symm
  obtain ⟨rs,hrs⟩ := hP
  have hd := fullFrequencyOperator_dense_adjoint_roots b hQ σ hσ m ω
  have hroot : ∃ u, External.IsGeneralizedRoot T u ∧
      ⟪u,chiralLpMap (chiralProjection (W rs))⟫≠0 := by
    by_contra! hh
    apply hrs
    apply hd.eq_zero_of_inner_right ℂ
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact hh x hx
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left,ihx,ihy]
    | smul a x hx ih => simp [inner_smul_left,ih]
  obtain ⟨u,⟨z,n,c,_,hc0,hcn,hc⟩,hu⟩ := hroot
  let d : ℕ → FullAngularHilbert := fun j => chiralLpMap (chiralProjection (c j))
  have hd0 : d 0=0 := by simp [d,hc0]
  have hdchain : ∀ j, j<n → ∃ hj : d (j+1) ∈ T.domain,
      T ⟨d (j+1),hj⟩=z • d (j+1)+d j := by
    intro j hj
    obtain ⟨hcj,hstep⟩ := hc j hj
    obtain ⟨hdj,hdstep⟩ := fullFrequencyOperator_adjoint_chiral b hQ σ hσ m ω ⟨c (j+1),hcj⟩
    refine ⟨hdj,?_⟩
    change T ⟨d (j+1),hdj⟩ = _ at hdstep
    rw [hstep,map_add,map_smul,map_add,map_smul] at hdstep
    exact hdstep
  have hdS : ∀ j, ChiralVector (d j) := fun j => ⟨chiralProjection (c j),rfl⟩
  have hdetect : ⟪d n,W rs⟫≠0 := by
    change ⟪chiralLpMap (chiralProjection (c n)),W rs⟫≠0
    rw [fullChiralProjection_symmetric,hcn]
    exact hu
  obtain ⟨v,w,hv,hstep,hvne,hw,hvS,hwS,e,he,hene,heS,hee⟩ :=
    exists_first_chain_member_with_property T W z n d hd0 hdchain ChiralVector hdS rs hdetect
  refine ⟨z,v,w,hv,hstep,?_,?_,hvS,hwS,e,he,hene,heS,hee⟩
  · obtain ⟨⟨r,s⟩,hr⟩ := hvne
    refine ⟨r,?_⟩
    cases s
    · exact Or.inl hr
    · exact Or.inr hr
  · intro r
    exact ⟨hw (r,false),hw (r,true)⟩

end
end KN.Angular

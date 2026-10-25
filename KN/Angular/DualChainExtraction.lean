import KN.Angular.ExternalMityaginSiegl
import KN.Angular.RootDetection

namespace KN.Angular
noncomputable section
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Minimal nonzero chain coefficient is chosen globally on the entire parameter set.
The predecessor vanishes as a coefficient function, not just at one point. -/
theorem exists_first_detecting_chain_member {R : Type*} (T : E →ₗ.[ℂ] E)
    (hd : Dense (Submodule.span ℂ {u : E | External.IsGeneralizedRoot T u} : Set E))
    (Z : R → E) (hne : ∃ r, Z r ≠ 0) :
    ∃ (z : ℂ) (v w : E) (hv : v ∈ T.domain),
      T ⟨v,hv⟩ = z • v+w ∧ (∃ r, ⟪v,Z r⟫ ≠ 0) ∧
      (∀ r, ⟪w,Z r⟫=0) ∧
      ∃ (e : E) (he : e ∈ T.domain), e ≠ 0 ∧ T ⟨e,he⟩=z • e := by
  classical
  obtain ⟨r0,hr0⟩ := hne
  have hex : ∃ u : E, External.IsGeneralizedRoot T u ∧ ⟪u,Z r0⟫ ≠ 0 := by
    by_contra! h
    apply hr0
    apply hd.eq_zero_of_inner_right ℂ
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left,ihx,ihy]
    | smul a x hx ih => simp [inner_smul_left,ih]
  obtain ⟨u,⟨z,n,c,hn,hzero,hend,hchain⟩,hu⟩ := hex
  have hexj : ∃ j : ℕ, ∃ r, ⟪c j,Z r⟫≠0 := ⟨n,r0,by rwa [hend]⟩
  let j := Nat.find hexj
  have hj : ∃ r, ⟪c j,Z r⟫≠0 := Nat.find_spec hexj
  have hjn : j ≤ n := Nat.find_min' hexj ⟨r0,by rwa [hend]⟩
  have hjpos : 0<j := by
    by_contra hle
    have hj0 : j=0 := by omega
    obtain ⟨r,hr⟩ := hj
    rw [hj0,hzero] at hr
    simp at hr
  have hvpack := hchain (j-1) (by omega)
  have hjpred : j-1+1=j := by omega
  simp only [hjpred] at hvpack
  obtain ⟨hv,hvstep⟩ := hvpack
  have hw : ∀ r, ⟪c (j-1),Z r⟫=0 := by
    intro r
    by_contra hh
    exact Nat.find_min hexj (show j-1<j by omega) ⟨r,hh⟩
  have hexc : ∃ k : ℕ, c k ≠ 0 := by
    obtain ⟨r,hr⟩ := hj
    refine ⟨j,?_⟩
    intro hz
    rw [hz] at hr
    simp at hr
  let k := Nat.find hexc
  have hk : c k ≠ 0 := Nat.find_spec hexc
  have hkj : k≤j := Nat.find_min' hexc (by
    obtain ⟨r,hr⟩ := hj
    intro hz
    rw [hz] at hr
    simp at hr)
  have hkpos : 0<k := by
    by_contra hh
    have hk0 : k=0 := by omega
    exact hk (hk0 ▸ hzero)
  have hepack := hchain (k-1) (by omega)
  have hkpred : k-1+1=k := by omega
  simp only [hkpred] at hepack
  obtain ⟨he,hestep⟩ := hepack
  have hprev : c (k-1)=0 := by
    by_contra hh
    exact Nat.find_min hexc (show k-1<k by omega) hh
  refine ⟨z,c j,c (j-1),hv,hvstep,hj,hw,c k,he,hk,?_⟩
  simpa only [hprev,add_zero] using hestep

/-- Chain selection with an invariant property, used for a fixed chiral range.
The invariant is retained by both the detecting vector and the genuine eigenvector. -/
theorem exists_first_chain_member_with_property {R : Type*} (T : E →ₗ.[ℂ] E)
    (Z : R → E) (z : ℂ) (n : ℕ) (c : ℕ → E)
    (hzero : c 0=0)
    (hchain : ∀ j, j<n → ∃ hj : c (j+1) ∈ T.domain,
      T ⟨c (j+1),hj⟩=z • c (j+1)+c j)
    (S : E → Prop) (hS : ∀ j, S (c j)) (r0 : R) (hr0 : ⟪c n,Z r0⟫≠0) :
    ∃ (v w : E) (hv : v ∈ T.domain),
      T ⟨v,hv⟩=z • v+w ∧ (∃ r, ⟪v,Z r⟫≠0) ∧ (∀ r, ⟪w,Z r⟫=0) ∧
      S v ∧ S w ∧ ∃ (e : E) (he : e ∈ T.domain), e≠0 ∧ S e ∧ T ⟨e,he⟩=z • e := by
  classical
  have hexj : ∃ j : ℕ, ∃ r, ⟪c j,Z r⟫≠0 := ⟨n,r0,hr0⟩
  let j := Nat.find hexj
  have hj : ∃ r, ⟪c j,Z r⟫≠0 := Nat.find_spec hexj
  have hjn : j ≤ n := Nat.find_min' hexj ⟨r0,hr0⟩
  have hjpos : 0<j := by
    by_contra hle
    have hj0 : j=0 := by omega
    obtain ⟨r,hr⟩ := hj
    rw [hj0,hzero] at hr
    simp at hr
  have hvpack := hchain (j-1) (by omega)
  have hjpred : j-1+1=j := by omega
  simp only [hjpred] at hvpack
  obtain ⟨hv,hvstep⟩ := hvpack
  have hw : ∀ r, ⟪c (j-1),Z r⟫=0 := by
    intro r
    by_contra hh
    exact Nat.find_min hexj (show j-1<j by omega) ⟨r,hh⟩
  have hexc : ∃ k : ℕ, c k ≠ 0 := by
    obtain ⟨r,hr⟩ := hj
    refine ⟨j,?_⟩
    intro hz
    rw [hz] at hr
    simp at hr
  let k := Nat.find hexc
  have hk : c k ≠ 0 := Nat.find_spec hexc
  have hkj : k≤j := Nat.find_min' hexc (by
    obtain ⟨r,hr⟩ := hj
    intro hz
    rw [hz] at hr
    simp at hr)
  have hkpos : 0<k := by
    by_contra hh
    have hk0 : k=0 := by omega
    exact hk (hk0 ▸ hzero)
  have hepack := hchain (k-1) (by omega)
  have hkpred : k-1+1=k := by omega
  simp only [hkpred] at hepack
  obtain ⟨he,hestep⟩ := hepack
  have hprev : c (k-1)=0 := by
    by_contra hh
    exact Nat.find_min hexc (show k-1<k by omega) hh
  refine ⟨c j,c (j-1),hv,hvstep,hj,hw,hS j,hS (j-1),c k,he,hk,hS k,?_⟩
  simpa only [hprev,add_zero] using hestep

end
end KN.Angular

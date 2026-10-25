import KN.Physics.SourceHilbertBoundaryRegularConormal

noncomputable section
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace KN.Physics
open KN.Angular KN.Boundary

lemma SourceSC.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {rp : ℝ} {f g : ℝ → E} (hf : SourceSC rp f) (he : ∀r>rp, f r=g r) : SourceSC rp g := by
  exact ⟨hf.1.congr (fun r hr => (he r hr).symm),hf.2.congr_exterior rp he⟩

lemma transformMix_sourceSC (positive : Bool) (b : KN.Background) :
    SourceSC b.rPlus (transformMix positive b) := by
  cases positive
  · exact (deltaSqrt_sourceSC b).const_smul (-1) |>.congr (fun r _ => by simp [transformMix])
  · apply (deltaPower_sourceSC b ((-1:ℝ)/2)).congr
    intro r hr
    dsimp [transformMix]
    have he : Real.rpow (b.Delta r) ((-1:ℝ)/2)=(Real.sqrt (b.Delta r))⁻¹ := by
      rw [Real.sqrt_eq_rpow]
      convert Real.rpow_neg (le_of_lt (b.Delta_pos hr)) ((1:ℝ)/2) using 1 <;> norm_num
    exact_mod_cast he

lemma sourceHilbertTransform_sourceSC (positive : Bool) (b : KN.Background)
    (high low : ℝ → SourceAngularHilbert)
    (hh : SourceSC b.rPlus high) (hl : SourceSC b.rPlus low) :
    SourceSC b.rPlus (fun r => (sourceHilbertTransform positive b r (high r) (low r)).1) ∧
    SourceSC b.rPlus (fun r => (sourceHilbertTransform positive b r (high r) (low r)).2) := by
  have hU := (hh.map sourceAngularEmbedding.toContinuousLinearMap).map (sourceChargeL (transformCharge positive b))
  have hV := (hl.map sourceAngularEmbedding.toContinuousLinearMap).map (sourceChargeL (transformCharge positive b))
  have hmix : SourceSC b.rPlus (fun r => Complex.I*transformMix positive b r) :=
    (transformMix_sourceSC positive b).const_smul Complex.I
  have hscale := deltaPower_sourceSC b (if positive then (5:ℝ)/4 else (-3:ℝ)/4)
  exact ⟨hscale.smul (sourceAdjL_sourceSC b _ (hU.add (hmix.smul hV))),
    hscale.smul (sourceStarL_sourceSC b _ (hU.sub (hmix.smul hV)))⟩

lemma sourceHilbertTransform_smul (positive : Bool) (b : KN.Background) (r : ℝ)
    (high low : SourceAngularHilbert) (c : ℂ) :
    sourceHilbertTransform positive b r (c • high) (c • low)=c • sourceHilbertTransform positive b r high low := by
  apply Prod.ext <;>
    simp only [sourceHilbertTransform,map_smul,map_add,map_sub,Prod.smul_fst,Prod.smul_snd] <;>
    module

/-- Original outgoing boundary data imply the outgoing class of both actual
transformed blocks, with every Euler radial derivative controlled. -/
theorem source_hilbert_outgoing (positive : Bool) (b : KN.Background) (m : ℤ) (omega : ℂ)
    (sigma : ℝ) (high low : ℝ → SourceAngularHilbert)
    (h : OriginalSourceBoundary b m omega sigma high low) :
    Outgoing b m omega (fun r => (sourceHilbertTransform positive b r (high r) (low r)).1) ∧
    Outgoing b m omega (fun r => (sourceHilbertTransform positive b r (high r) (low r)).2) ∧
    ContDiffOn ℝ ∞ (fun r => (sourceHilbertTransform positive b r (high r) (low r)).1) (Ioi b.rPlus) ∧
    ContDiffOn ℝ ∞ (fun r => (sourceHilbertTransform positive b r (high r) (low r)).2) (Ioi b.rPlus) := by
  have hh : SourceSC b.rPlus (fun r => gauge b m omega r • high r) :=
    ⟨(gauge_contDiffOn b m omega).fun_smul h.high_smooth,h.high_outgoing⟩
  have hl : SourceSC b.rPlus (fun r => gauge b m omega r • low r) :=
    ⟨(gauge_contDiffOn b m omega).fun_smul h.low_smooth,h.low_outgoing⟩
  obtain ⟨hP,hM⟩ := sourceHilbertTransform_sourceSC positive b _ _ hh hl
  have heP : (fun r => (sourceHilbertTransform positive b r (gauge b m omega r • high r)
      (gauge b m omega r • low r)).1)=fun r => gauge b m omega r •
      (sourceHilbertTransform positive b r (high r) (low r)).1 := by
    funext r
    rw [sourceHilbertTransform_smul]
    rfl
  have heM : (fun r => (sourceHilbertTransform positive b r (gauge b m omega r • high r)
      (gauge b m omega r • low r)).2)=fun r => gauge b m omega r •
      (sourceHilbertTransform positive b r (high r) (low r)).2 := by
    funext r
    rw [sourceHilbertTransform_smul]
    rfl
  rw [heP] at hP
  rw [heM] at hM
  have hi := (gauge_contDiffOn b m omega).fun_inv (fun r _ => gauge_ne_zero b m omega r)
  have hsP := hi.fun_smul hP.1
  have hsM := hi.fun_smul hM.1
  simp only [smul_smul,inv_mul_cancel₀ (gauge_ne_zero b m omega _),one_smul] at hsP hsM
  exact ⟨hP.2,hM.2,hsP,hsM⟩

end KN.Physics

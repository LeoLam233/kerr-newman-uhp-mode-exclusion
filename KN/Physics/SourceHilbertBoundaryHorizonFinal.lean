import KN.Physics.SourceHilbertBoundaryNormalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace KN.Physics
open KN.Angular KN.Boundary

lemma horizonRegular_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {b : KN.Background} {m : ℤ} {omega : ℂ} {q : ℝ} {f g : ℝ → E}
    (hf : HorizonRegular b m omega q f) (he : ∀r>b.rPlus, f r=g r) :
    HorizonRegular b m omega q g := by
  obtain ⟨v,hv,heq⟩ := hf
  exact ⟨v,hv,fun r hr => (he r hr).symm.trans (heq r hr)⟩

theorem source_hilbert_horizon_positive (b : KN.Background) (m : ℤ) (omega : ℂ)
    (high low : ℝ → SourceAngularHilbert)
    (h : OriginalSourceBoundary b m omega 1 high low) :
    HorizonRegular b m omega ((-1:ℝ)/4)
      (fun r => (sourceHilbertTransform true b r (high r) (low r)).1+
        (sourceHilbertTransform true b r (high r) (low r)).2) ∧
    HorizonRegular b m omega ((-3:ℝ)/4)
      (fun r => (sourceHilbertTransform true b r (high r) (low r)).1-
        (sourceHilbertTransform true b r (high r) (low r)).2) := by
  let L := (sourceChargeL (transformCharge true b)).comp sourceAngularEmbedding.toContinuousLinearMap
  obtain ⟨U,hU,hUE⟩ := h.high_horizon.map L
  obtain ⟨V,hV,hVE⟩ := h.low_horizon.map L
  norm_num only [mul_one,neg_mul,one_mul] at hUE hVE
  have hP : ∀r>b.rPlus, (sourceHilbertTransform true b r (high r) (low r)).1=
      (gauge b m omega r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
      sourceAdjL b r (U r+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r) := by
    intro r hr
    change (Real.rpow (b.Delta r) ((5:ℝ)/4):ℂ) • sourceAdjL b r
      (L (high r)+(Complex.I*(Real.sqrt (b.Delta r):ℂ)⁻¹) • L (low r))=_
    rw [hUE r hr,hVE r hr]
    simpa only [one_mul] using source_normalization_positive b m omega r hr (U r) (V r) (sourceAdjL b r) 1
  have hM : ∀r>b.rPlus, (sourceHilbertTransform true b r (high r) (low r)).2=
      (gauge b m omega r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
      sourceStarL b r (U r-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r) := by
    intro r hr
    change (Real.rpow (b.Delta r) ((5:ℝ)/4):ℂ) • sourceStarL b r
      (L (high r)-(Complex.I*(Real.sqrt (b.Delta r):ℂ)⁻¹) • L (low r))=_
    rw [hUE r hr,hVE r hr]
    simpa only [neg_one_mul,one_mul,neg_mul,neg_smul,sub_eq_add_neg] using
      source_normalization_positive b m omega r hr (U r) (V r) (sourceStarL b r) (-1)
  obtain ⟨hp,hm⟩ := positive_hilbert_horizon_transport b m omega U V hU hV
  constructor
  · apply horizonRegular_congr hp
    intro r hr
    rw [hP r hr,hM r hr,← smul_add]
  · apply horizonRegular_congr hm
    intro r hr
    rw [hP r hr,hM r hr,← smul_sub]

theorem source_hilbert_horizon_negative (b : KN.Background) (m : ℤ) (omega : ℂ)
    (high low : ℝ → SourceAngularHilbert)
    (h : OriginalSourceBoundary b m omega (-1) high low) :
    HorizonRegular b m omega ((3:ℝ)/4)
      (fun r => (sourceHilbertTransform false b r (high r) (low r)).1+
        (sourceHilbertTransform false b r (high r) (low r)).2) ∧
    HorizonRegular b m omega ((5:ℝ)/4)
      (fun r => (sourceHilbertTransform false b r (high r) (low r)).1-
        (sourceHilbertTransform false b r (high r) (low r)).2) := by
  let L := (sourceChargeL (transformCharge false b)).comp sourceAngularEmbedding.toContinuousLinearMap
  obtain ⟨U,hU,hUE⟩ := h.high_horizon.map L
  obtain ⟨V,hV,hVE⟩ := h.low_horizon.map L
  norm_num only [mul_neg_one,neg_neg] at hUE hVE
  have hP : ∀r>b.rPlus, (sourceHilbertTransform false b r (high r) (low r)).1=
      (gauge b m omega r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
      sourceAdjL b r ((Real.sqrt (b.Delta r):ℂ) • U r-Complex.I • V r) := by
    intro r hr
    change (Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ) • sourceAdjL b r
      (L (high r)+(Complex.I*(-(Real.sqrt (b.Delta r):ℂ))) • L (low r))=_
    rw [hUE r hr,hVE r hr]
    simpa only [neg_one_mul,one_mul,mul_neg,neg_mul,neg_smul,sub_eq_add_neg] using
      source_normalization_negative b m omega r hr (U r) (V r) (sourceAdjL b r) 1
  have hM : ∀r>b.rPlus, (sourceHilbertTransform false b r (high r) (low r)).2=
      (gauge b m omega r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
      sourceStarL b r ((Real.sqrt (b.Delta r):ℂ) • U r+Complex.I • V r) := by
    intro r hr
    change (Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ) • sourceStarL b r
      (L (high r)-(Complex.I*(-(Real.sqrt (b.Delta r):ℂ))) • L (low r))=_
    rw [hUE r hr,hVE r hr]
    simpa only [neg_neg,neg_one_mul,one_mul,mul_neg,neg_mul,neg_smul,sub_neg_eq_add] using
      source_normalization_negative b m omega r hr (U r) (V r) (sourceStarL b r) (-1)
  obtain ⟨hp,hm⟩ := negative_hilbert_horizon_transport b m omega U V hU hV
  constructor
  · apply horizonRegular_congr hp
    intro r hr
    rw [hP r hr,hM r hr,← smul_add]
  · apply horizonRegular_congr hm
    intro r hr
    rw [hP r hr,hM r hr,← smul_sub]

end KN.Physics

import KN.ChargedRadial.PhysicalElimination
import KN.Physics.SourceHilbertBoundaryTransform
import KN.Boundary.Powers

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace KN.Physics
open KN.Angular KN.Boundary

lemma positive_source_sum_L (b : KN.Background) (r : ℝ) (U V : AngularHilbert) :
    sourceAdjL b r (U+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V)+
    sourceStarL b r (U-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V)=
    (Real.sqrt (b.Delta r):ℂ) • (horizonEvenL b r U+Complex.I • horizonOddL b r V) := by
  simp only [sourceAdjL,sourceStarL,smul_apply,add_apply,
    sub_apply,map_add,map_sub,map_smul]
  module

lemma positive_source_difference_L (b : KN.Background) (r : ℝ) (U V : AngularHilbert) :
    sourceAdjL b r (U+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V)-
    sourceStarL b r (U-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V)=
    horizonOddL b r U+(Complex.I*(Real.sqrt (b.Delta r):ℂ)^2) • horizonEvenL b r V := by
  simp only [sourceAdjL,sourceStarL,smul_apply,add_apply,
    sub_apply,map_add,map_sub,map_smul]
  module

lemma negative_source_sum_L (b : KN.Background) (r : ℝ) (U V : AngularHilbert) :
    sourceAdjL b r ((Real.sqrt (b.Delta r):ℂ) • U-Complex.I • V)+
    sourceStarL b r ((Real.sqrt (b.Delta r):ℂ) • U+Complex.I • V)=
    (Real.sqrt (b.Delta r):ℂ)^2 • horizonEvenL b r U-Complex.I • horizonOddL b r V := by
  simp only [sourceAdjL,sourceStarL,smul_apply,add_apply,
    sub_apply,map_add,map_sub,map_smul]
  module

lemma negative_source_difference_L (b : KN.Background) (r : ℝ) (U V : AngularHilbert) :
    sourceAdjL b r ((Real.sqrt (b.Delta r):ℂ) • U-Complex.I • V)-
    sourceStarL b r ((Real.sqrt (b.Delta r):ℂ) • U+Complex.I • V)=
    (Real.sqrt (b.Delta r):ℂ) • (horizonOddL b r U-Complex.I • horizonEvenL b r V) := by
  simp only [sourceAdjL,sourceStarL,smul_apply,add_apply,
    sub_apply,map_add,map_sub,map_smul]
  module

lemma positive_hilbert_horizon_transport (b : KN.Background) (m : ℤ) (omega : ℂ)
    (U V : ℝ → AngularHilbert) (hU : ContDiffOn ℝ ∞ U (Ici b.rPlus))
    (hV : ContDiffOn ℝ ∞ V (Ici b.rPlus)) :
    HorizonRegular b m omega ((-1:ℝ)/4)
      (fun r => (gauge b m omega r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
        (sourceAdjL b r (U r+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r)+
         sourceStarL b r (U r-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r))) ∧
    HorizonRegular b m omega ((-3:ℝ)/4)
      (fun r => (gauge b m omega r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
        (sourceAdjL b r (U r+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r)-
         sourceStarL b r (U r-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r))) := by
  have hDelta := KN.ChargedRadial.physicalDelta_smooth b
  constructor
  · refine ⟨fun r => horizonEvenL b r (U r)+Complex.I • horizonOddL b r (V r),
      (horizonEvenL_action_smooth b U hU).add ((horizonOddL_action_smooth b V hV).const_smul Complex.I), ?_⟩
    intro r hr
    dsimp only
    rw [positive_source_sum_L,smul_smul,mul_assoc,positive_horizon_shift b hr]
  · refine ⟨fun r => horizonOddL b r (U r)+(Complex.I*(b.Delta r:ℂ)) • horizonEvenL b r (V r),
      (horizonOddL_action_smooth b U hU).add
        ((contDiffOn_const.mul hDelta.contDiffOn).fun_smul (horizonEvenL_action_smooth b V hV)), ?_⟩
    intro r hr
    dsimp only
    rw [positive_source_difference_L]
    have ht : (Real.sqrt (b.Delta r):ℂ)^2=(b.Delta r:ℂ) := by
      norm_cast
      exact Real.sq_sqrt (le_of_lt (b.Delta_pos hr))
    rw [ht]

lemma negative_hilbert_horizon_transport (b : KN.Background) (m : ℤ) (omega : ℂ)
    (U V : ℝ → AngularHilbert) (hU : ContDiffOn ℝ ∞ U (Ici b.rPlus))
    (hV : ContDiffOn ℝ ∞ V (Ici b.rPlus)) :
    HorizonRegular b m omega ((3:ℝ)/4)
      (fun r => (gauge b m omega r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
        (sourceAdjL b r ((Real.sqrt (b.Delta r):ℂ) • U r-Complex.I • V r)+
         sourceStarL b r ((Real.sqrt (b.Delta r):ℂ) • U r+Complex.I • V r))) ∧
    HorizonRegular b m omega ((5:ℝ)/4)
      (fun r => (gauge b m omega r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
        (sourceAdjL b r ((Real.sqrt (b.Delta r):ℂ) • U r-Complex.I • V r)-
         sourceStarL b r ((Real.sqrt (b.Delta r):ℂ) • U r+Complex.I • V r))) := by
  have hDelta := KN.ChargedRadial.physicalDelta_smooth b
  constructor
  · refine ⟨fun r => (b.Delta r:ℂ) • horizonEvenL b r (U r)-Complex.I • horizonOddL b r (V r),
      (hDelta.contDiffOn.fun_smul (horizonEvenL_action_smooth b U hU)).sub
        ((horizonOddL_action_smooth b V hV).const_smul Complex.I), ?_⟩
    intro r hr
    dsimp only
    rw [negative_source_sum_L]
    have ht : (Real.sqrt (b.Delta r):ℂ)^2=(b.Delta r:ℂ) := by
      norm_cast
      exact Real.sq_sqrt (le_of_lt (b.Delta_pos hr))
    rw [ht]
  · refine ⟨fun r => horizonOddL b r (U r)-Complex.I • horizonEvenL b r (V r),
      (horizonOddL_action_smooth b U hU).sub ((horizonEvenL_action_smooth b V hV).const_smul Complex.I), ?_⟩
    intro r hr
    dsimp only
    rw [negative_source_difference_L,smul_smul,mul_assoc,negative_horizon_shift b hr]

end KN.Physics

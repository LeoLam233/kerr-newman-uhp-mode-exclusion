import KN.Angular.OriginalSourceField
import KN.Physics.SourceHilbertBoundaryOutgoingFinal
import KN.Physics.SourceHilbertBoundaryHorizonFinal

namespace KN.Angular.OriginalSourceField
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set KN.Physics KN.Boundary
open scoped ContDiff
variable {positive : Bool} {b : KN.Background} {m : ℤ} {omega : ℂ}

theorem transformed_smooth (U : OriginalSourceField positive b m omega) :
    ContDiffOn ℝ ∞ U.transformed (Ioi b.rPlus) := by
  have h := source_hilbert_outgoing positive b m omega _ U.high U.low U.boundary
  exact (((sourceUpperL).restrictScalars ℝ).contDiff.comp_contDiffOn h.2.2.1).add
    (((sourceLowerL).restrictScalars ℝ).contDiff.comp_contDiffOn h.2.2.2)

theorem transformed_outgoing (U : OriginalSourceField positive b m omega) :
    Outgoing b m omega U.transformed := by
  have h := source_hilbert_outgoing positive b m omega _ U.high U.low U.boundary
  have hp := h.1.map h.2.2.1 sourceUpperL
  have hm := h.2.1.map h.2.2.2 sourceLowerL
  have hsP := (gauge_contDiffOn b m omega).smul
    (((sourceUpperL).restrictScalars ℝ).contDiff.comp_contDiffOn h.2.2.1)
  have hsM := (gauge_contDiffOn b m omega).smul
    (((sourceLowerL).restrictScalars ℝ).contDiff.comp_contDiffOn h.2.2.2)
  have hh := PolynomialConormal.add_on hp hm hsP hsM
  simpa only [Outgoing,transformed,sourcePack,smul_add] using hh

theorem transformed_horizons (U : OriginalSourceField positive b m omega) :
    HorizonRegular b m omega ((1-2*(if positive then 1 else -1))/4)
      (fun r => fullPiPlus (U.transformed r)) ∧
    HorizonRegular b m omega ((1-4*(if positive then 1 else -1))/4)
      (fun r => fullPiMinus (U.transformed r)) := by
  cases positive
  · have h := source_hilbert_horizon_negative b m omega U.high U.low U.boundary
    have hp := sourcePack_horizons b m omega _ _ ((3:ℝ)/4) ((5:ℝ)/4) h.1 h.2
    norm_num only [Bool.false_eq_true,ite_false,mul_neg_one,sub_neg_eq_add] at *
    convert hp using 1 <;> norm_num [transformed]
  · have h := source_hilbert_horizon_positive b m omega U.high U.low U.boundary
    have hp := sourcePack_horizons b m omega _ _ ((-1:ℝ)/4) ((-3:ℝ)/4) h.1 h.2
    norm_num only [ite_true,mul_one] at *
    convert hp using 1 <;> norm_num [transformed]

end
end KN.Angular.OriginalSourceField

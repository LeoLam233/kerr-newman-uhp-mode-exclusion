import KN.Angular.OriginalSourceDerivative
import KN.Angular.FullFieldConstructor
import KN.Angular.FullFieldExclusion
import KN.Physics.SourceHilbertRecovery

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set KN.Physics
open scoped ContDiff

/-- The literal published source system produces the actual maximal-domain
Hilbert-valued full field. Neither a transformed PDE nor transformed boundary
regularity is assumed. -/
def OriginalSourceField.toFullField {positive : Bool} {b : KN.Background}
    {m : ℤ} {omega : ℂ} (U : OriginalSourceField positive b m omega)
    (hQ : b.Q≠0) (hs : PublishedChiralSystem positive b m omega U.components) :
    FullField b hQ (KN.Energy.spinSign positive)
      (KN.ChargedRadial.spinSign_cases positive) m omega := by
  apply fullField_of_classical b hQ (KN.Energy.spinSign positive)
    (KN.ChargedRadial.spinSign_cases positive) m omega U.transformed
    (fun r θ => WithLp.toLp 2 (sourceFullVector positive b U.components r θ))
    U.transformed_smooth (fun r hr => U.transformed_ae hr)
    (fun r hr => U.transformed_derivative_ae hr)
    (fun r hr => sourceFullVector_angular_smooth positive b U.components hr
      (fun i => U.angular_smooth hr i))
  · intro r θ hr hθ
    have hsign : ((KN.Energy.spinSign positive : ℝ):ℂ)=sourceSign positive := by
      cases positive <;> norm_num [KN.Energy.spinSign,sourceSign]
    have h := source_four_transport_euclidean positive b hQ m omega
      (KN.Energy.spinSign positive) hsign U.components hs U.source_differentiable
      hr hθ.1 hθ.2
    rw [source_angular_action_identification] at h
    simpa only [add_assoc, derivativeMatrix, fullPrincipal] using h
  · exact U.transformed_horizons.1
  · exact U.transformed_horizons.2
  · exact U.transformed_outgoing

/-- Exclusion for the original smooth source components satisfying the literal
published chiral equations and the original physical boundary conditions. -/
theorem original_source_exclusion (positive : Bool) (b : KN.Background) (hQ : b.Q≠0)
    (m : ℤ) (omega : ℂ) (homega : 0<omega.im)
    (U : OriginalSourceField positive b m omega)
    (hs : PublishedChiralSystem positive b m omega U.components) :
    ∀ r, b.rPlus<r → EqOn (U.components r) 0 (Ioo 0 Real.pi) := by
  have hz := charged_full_field_exclusion positive b hQ m omega homega (U.toFullField hQ hs)
  intro r hr
  apply sourceFullTransform_original_pointwise_zero positive b hQ hr
    (U.high r) (U.low r) (U.components r)
    (continuousOn_pi.mpr (fun i => (U.angular_smooth hr i).continuousOn))
    (U.high_rep r hr) (U.low_rep r hr)
  exact hz hr

end
end KN.Angular

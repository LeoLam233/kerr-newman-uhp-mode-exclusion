import KN.ChargedRadial.SeparatedExclusion
import KN.ChargedRadial.OriginalHorizonRescaling
import KN.ChargedRadial.OriginalPair

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial
open KN.Energy KN.Boundary

/-- Exclusion directly from the original selected radial equation (24) and its
weighted horizon/outgoing conditions. Both rescalings, supported continuation,
exceptional delta correction, transform equation, energy and injectivity are
constructed internally. -/
theorem charged_original_selected_exclusion
    (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ)
    (hw : 0 < omega.im)
    (angular : PhysicalAngularData b m (spinSign positive) omega lam)
    (y z : ℝ → ℂ)
    (hy : HorizonRegular b m omega (-(3*spinSign positive/4)) y)
    (hz : HorizonRegular b m omega (-(3*spinSign positive/4-1/2)) z)
    (hout : Outgoing b m omega y)
    (hpair : OriginalSelectedPair b m (spinSign positive) omega lam y z) :
    EqOn y 0 (Ioi b.rPlus) := by
  obtain ⟨w,hwh,hew⟩ := horizon_rescale_representative b m omega (3*spinSign positive/4) y hy
  obtain ⟨ws,hwsh,hes⟩ := horizon_rescale_representative b m omega (3*spinSign positive/4-1/2) z hz
  let p := radialMultiplier b m omega (-(1+3*spinSign positive)/2)
  let v := fun r => p r*w r
  let zs := fun r => (b.Delta r:ℂ)*p r*ws r
  apply charged_separated_exclusion positive b hQ m omega lam hw angular w ws y v zs
    hwh hwsh (fun _ _ => rfl) (fun _ _ => rfl) hew
  · exact (gauge_contDiffOn b m omega).mul
      (horizon_original_exterior_smooth b m omega _ y hy)
  · exact hout
  · intro r hr
    exact (original_pair_transport b m (spinSign positive) omega lam y z w ws hpair hew hes hr).1
  · intro r hr
    exact (original_pair_transport b m (spinSign positive) omega lam y z w ws hpair hew hes hr).2

end KN.ChargedRadial

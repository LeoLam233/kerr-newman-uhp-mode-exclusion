import KN.ChargedRadial.OriginalExclusion
import KN.ChargedRadial.PartnerRecovery
import KN.Angular.MultiplierExpectations

noncomputable section
open Set
namespace KN.ChargedRadial
open KN.Energy KN.Boundary KN.Angular

/-- Complete charged scalar separated-mode exclusion with the actual angular
first-order graph and frequency multiplier. All expectation identities,
coercivity, radial rescalings, supported continuation, exceptional correction,
transform, energy endpoints and injectivity are derived internally. -/
theorem charged_original_eigenmode_exclusion
    (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ)
    (hw : 0 < omega.im) (u staticImage : AngularHilbert) (hu : ‖u‖=1)
    (hgraph : StaticGraph (spinSign positive) b.beta m u staticImage)
    (heigen : staticImage+omega • reducedFrequencyMultiplier b (spinSign positive) u=lam • u)
    (y z : ℝ → ℂ)
    (hy : HorizonRegular b m omega (-(3*spinSign positive/4)) y)
    (hz : HorizonRegular b m omega (-(3*spinSign positive/4-1/2)) z)
    (hout : Outgoing b m omega y)
    (hpair : OriginalSelectedPair b m (spinSign positive) omega lam y z) :
    EqOn y 0 (Ioi b.rPlus) ∧ EqOn z 0 (Ioi b.rPlus) := by
  let angular := physicalAngularData_of_eigenvector b hQ (spinSign positive)
    (spinSign_cases positive) m omega lam u staticImage hu hgraph heigen
  have hy0 := charged_original_selected_exclusion positive b hQ m omega lam hw angular
    y z hy hz hout hpair
  exact ⟨hy0,original_partner_zero b hQ m (spinSign positive) (spinSign_cases positive)
    omega lam hw y z hpair hy0⟩

end KN.ChargedRadial

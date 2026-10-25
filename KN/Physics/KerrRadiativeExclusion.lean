import KN.Kerr.FullFieldExclusion
import KN.Physics.RadiativeRecovery

noncomputable section
namespace KN.Physics
open Set
open scoped ContDiff

/-- Ordering of the four physical radiative quantities in C002 (8a). -/
inductive RadiativeComponent where
  | gravitationalPlus | gravitationalMinus | electromagneticPlus | electromagneticMinus
  deriving DecidableEq

def RadiativeComponent.spin : RadiativeComponent → ℤ
  | .gravitationalPlus => 2
  | .gravitationalMinus => -2
  | .electromagneticPlus => 1
  | .electromagneticMinus => -1

theorem RadiativeComponent.spin_cases (i : RadiativeComponent) :
    i.spin=1 ∨ i.spin=2 ∨ i.spin= -1 ∨ i.spin= -2 := by
  cases i <;> simp [RadiativeComponent.spin]

/-- The actual four canonical Kerr equations and physical endpoint classes.
This is the published necessary-system output, not an exclusion premise. -/
structure KerrRadiativeNecessarySystem (b : KN.Background) (m : ℤ) (omega : ℂ)
    (F : RadiativeComponent → ℝ → KN.Kerr.AngularH) : Prop where
  smooth : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioi b.rPlus)
  equation : ∀ i, KN.Kerr.FullFieldEquation b m i.spin omega (F i)
  horizon : ∀ i, KN.Boundary.HorizonRegular b m omega (-(i.spin:ℝ)) (F i)
  outgoing : ∀ i, KN.Boundary.Outgoing b m omega (F i)

/-- Zero charge is handled directly by four complete Kerr field theorems,
not by a limit of the singular charged source transformation. -/
theorem kerr_all_radiative_fields_zero (b : KN.Background) (hQ : b.Q=0)
    (m : ℤ) (omega : ℂ) (homega : 0<omega.im)
    (F : RadiativeComponent → ℝ → KN.Kerr.AngularH)
    (h : KerrRadiativeNecessarySystem b m omega F) :
    ∀ i r, b.rPlus<r → F i r=0 := by
  intro i r hr
  exact KN.Kerr.kerr_full_field_exclusion b hQ m i.spin omega i.spin_cases homega
    (F i) (h.smooth i) (h.equation i) (h.horizon i) (h.outgoing i) r hr

end KN.Physics

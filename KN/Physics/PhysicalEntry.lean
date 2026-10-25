import KN.Angular.OriginalSourceField
import KN.Physics.KerrRadiativeExclusion

noncomputable section
namespace KN.Physics
open KN.Angular MeasureTheory Set

/-- Background Weyl coefficient in the fixed principal tetrad. -/
def backgroundPsiTwo (b : KN.Background) (r θ : ℝ) : ℂ :=
  ((b.Q:ℂ)^2/rho b r θ-(b.M:ℂ))/(rhoStar b r θ)^3

/-- Literal gauge-invariant radiative data (8a), before any phantom-frame choice. -/
def radiativeValue (b : KN.Background) (r θ : ℝ) (v : RadiativeCurvatureMaxwell) :
    RadiativeComponent → ℂ
  | .gravitationalPlus => gravitationalPlus v
  | .gravitationalMinus => gravitationalMinus (rhoStar b r θ) v
  | .electromagneticPlus => electromagneticPlus b.M b.Q (rhoStar b r θ) (backgroundPsiTwo b r θ) v
  | .electromagneticMinus => electromagneticMinus b.M b.Q (rhoStar b r θ) (backgroundPsiTwo b r θ) v

/-- The classical phantom-frame identification, stated on the original NP
variables. It contains no transformed field, spectral assertion, or vanishing. -/
def PhantomIdentification (b : KN.Background)
    (raw phantom : ℝ → ℝ → RadiativeCurvatureMaxwell)
    (plus minus : ℝ → ℝ → Fin 4 → ℂ) : Prop :=
  ∀ r θ, b.rPlus<r → θ ∈ Ioo 0 Real.pi →
    (phantom r θ).dPhi0=0 ∧ (phantom r θ).dPhi2=0 ∧
    plus r θ 0=(phantom r θ).dPsi0 ∧
    plus r θ 1=(Real.sqrt 2:ℂ)*rhoStar b r θ*(phantom r θ).dPsi1 ∧
    minus r θ 0=(rhoStar b r θ)^4*(phantom r θ).dPsi4 ∧
    minus r θ 1=(rhoStar b r θ)^3*(phantom r θ).dPsi3/(Real.sqrt 2:ℂ) ∧
    ∀ i, radiativeValue b r θ (raw r θ) i=radiativeValue b r θ (phantom r θ) i

/-- Precisely scoped one-way classical physical input. For nonzero charge the
output is the ORIGINAL published chiral source system and original boundary
classes. For zero charge it is the four canonical Teukolsky necessary equations.
This interface does not assert exclusion, separation, transformed boundary
conditions, energy positivity, or any C002 conclusion.

Sources: Hintz arXiv:2609.33661v1, original NP equations (1), chiral variables (3),
necessary system (4), physical tetrad/axis/horizon conventions; Teukolsky 1973
for the decoupled Kerr necessary equations; Motohashi arXiv:2610.10529v1,
(5.1)–(5.2), for the four invariant mixtures. Only the physical implication is
external. All subsequent source transformation and exclusion are proved here.
-/
structure PublishedPhysicalNecessaryData (b : KN.Background) (m : ℤ) (omega : ℂ)
    (raw : ℝ → ℝ → RadiativeCurvatureMaxwell) : Prop where
  axis_continuity : ∀ i r, b.rPlus<r →
    ContinuousOn (fun θ => radiativeValue b r θ (raw r θ) i) (Icc 0 Real.pi)
  charged : b.Q≠0 → ∃ (plus : OriginalSourceField true b m omega)
      (minus : OriginalSourceField false b m omega)
      (phantom : ℝ → ℝ → RadiativeCurvatureMaxwell),
    PublishedChiralSystem true b m omega plus.components ∧
    PublishedChiralSystem false b m omega minus.components ∧
    PhantomIdentification b raw phantom plus.components minus.components
  kerr : b.Q=0 → ∃ F : RadiativeComponent → ℝ → KN.Kerr.AngularH,
    KerrRadiativeNecessarySystem b m omega F ∧
    ∀ i r, b.rPlus<r →
      ContinuousOn (fun θ => radiativeValue b r θ (raw r θ) i) (Ioo 0 Real.pi) ∧
      F i r =ᵐ[KN.Kerr.sphericalMeasure] fun θ => radiativeValue b r θ (raw r θ) i

/-- An explicit interface for a physical perturbation theory. Its carrier and
admissibility predicate belong to the imported Einstein–Maxwell theory; the
only theorem required of it is the published necessary-system implication.
Keeping this argument explicit avoids pretending the full GR field equations
were independently reimplemented in this development. -/
structure PublishedEinsteinMaxwellEntry (b : KN.Background) (m : ℤ) (omega : ℂ)
    (P : Type*) where
  curvatureMaxwell : P → ℝ → ℝ → RadiativeCurvatureMaxwell
  smoothOutgoingMode : P → Prop
  necessary : ∀ p, smoothOutgoingMode p →
    PublishedPhysicalNecessaryData b m omega (curvatureMaxwell p)

end KN.Physics

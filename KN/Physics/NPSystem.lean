import KN.Physics.SourceRecovery
import KN.Boundary.GaugeDerivative

noncomputable section
namespace KN.Physics

abbrev ScalarField := ℝ → ℝ → ℂ
structure RadiativeSystem where
  psiTwo : ScalarField
  psiOne : ScalarField
  auxTwo : ScalarField
  auxOne : ScalarField

def radialNP (b : Background) (m : ℤ) (ω : ℂ) (j σ : ℂ)
    (f : ScalarField) (r θ : ℝ) : ℂ :=
  deriv (fun x => f x θ) r +
    (σ*Complex.I*b.frequencyK m ω r/(b.Delta r : ℂ) +
      j*(2*(r:ℂ)-2*(b.M:ℂ))/(b.Delta r : ℂ))*f r θ

def angularNP (b : Background) (m : ℤ) (ω : ℂ) (j σ : ℂ)
    (f : ScalarField) (r θ : ℝ) : ℂ :=
  deriv (f r) θ +
    (σ*(-(b.a:ℂ)*ω*Real.sin θ + (m:ℂ)/(Real.sin θ:ℂ)) +
      j*(Real.cos θ:ℂ)/(Real.sin θ:ℂ))*f r θ

def curvatureFactor (b : Background) (sign : ℂ) (r θ : ℝ) : ℂ :=
  3*((b.M:ℂ)-(b.Q:ℂ)^2/rho b r θ) +
    sign*(b.Q:ℂ)^2*rhoStar b r θ/(rho b r θ)^2

/-- Precisely Hintz (1a)-(1d), not an assumed transformed no-mode result. -/
def PositiveNPSystem (b : Background) (m : ℤ) (ω : ℂ) (u : RadiativeSystem) : Prop :=
  ∀ r θ, b.rPlus < r → 0 < θ → θ < Real.pi →
    (angularNP b m ω 2 1 u.psiTwo r θ -
      3*Complex.I*b.a*Real.sin θ/rhoStar b r θ*u.psiTwo r θ -
      (radialNP b m ω 0 1 u.psiOne r θ + 3/rhoStar b r θ*u.psiOne r θ) =
        -2*u.auxTwo r θ*curvatureFactor b 1 r θ) ∧
    ((b.Delta r:ℂ)*(radialNP b m ω 2 (-1) u.psiTwo r θ -
      3/rhoStar b r θ*u.psiTwo r θ) +
      angularNP b m ω (-1) (-1) u.psiOne r θ +
      3*Complex.I*b.a*Real.sin θ/rhoStar b r θ*u.psiOne r θ =
        2*u.auxOne r θ*curvatureFactor b (-1) r θ) ∧
    (radialNP b m ω 0 1 u.auxOne r θ + 3/rhoStar b r θ*u.auxOne r θ -
      (angularNP b m ω (-1) (-1) u.auxTwo r θ +
      3*Complex.I*b.a*Real.sin θ/rhoStar b r θ*u.auxTwo r θ) =
        rho b r θ/(rhoStar b r θ)^2*u.psiTwo r θ) ∧
    ((b.Delta r:ℂ)*(radialNP b m ω 2 (-1) u.auxTwo r θ -
      3/rhoStar b r θ*u.auxTwo r θ) +
      angularNP b m ω 2 1 u.auxOne r θ -
      3*Complex.I*b.a*Real.sin θ/rhoStar b r θ*u.auxOne r θ =
        2*rho b r θ/(rhoStar b r θ)^2*u.psiOne r θ)

/-- Physical radiative invariants (8a) before phantom-gauge specialization. -/
structure RadiativeCurvatureMaxwell where
  dPsi0 : ℂ
  dPsi1 : ℂ
  dPsi3 : ℂ
  dPsi4 : ℂ
  dPhi0 : ℂ
  dPhi2 : ℂ

def gravitationalPlus (v : RadiativeCurvatureMaxwell) : ℂ := v.dPsi0
def gravitationalMinus (ρstar : ℂ) (v : RadiativeCurvatureMaxwell) : ℂ := ρstar^4*v.dPsi4
def electromagneticPlus (M Q ρstar backgroundPsi2 : ℂ) (v : RadiativeCurvatureMaxwell) : ℂ :=
  ρstar/(3*M)*(Q*v.dPsi1-3*ρstar^2*backgroundPsi2*v.dPhi0)
def electromagneticMinus (M Q ρstar backgroundPsi2 : ℂ) (v : RadiativeCurvatureMaxwell) : ℂ :=
  ρstar^3/(3*M)*(Q*v.dPsi3-3*ρstar^2*backgroundPsi2*v.dPhi2)

/-- The null-rotation mixtures are invariant; the coefficients are exactly the NP gauge laws. -/
theorem mixed_null_rotation_invariant (Q ρstar backgroundPsi2 z Psi Phi : ℂ)
    (hρ : ρstar ≠ 0) :
    Q*(Psi+3*z*backgroundPsi2) - 3*ρstar^2*backgroundPsi2*(Phi+z*Q/ρstar^2) =
      Q*Psi-3*ρstar^2*backgroundPsi2*Phi := by
  field_simp
  ring

end KN.Physics

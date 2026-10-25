import KN.Angular.FullOperator
import KN.Boundary.Radial

namespace KN.Angular
noncomputable section

/-- Literal scalar coefficients (3), prior to any radial division. -/
def radialR0 (b : KN.Background) (σ : ℝ) (m : ℤ) (ω : ℂ) (r : ℝ) : ℂ :=
  (3 : ℂ)*((deriv b.Delta r : ℝ) : ℂ)/(4*(Real.sqrt (b.Delta r) : ℂ)) -
    Complex.I*(σ : ℂ)*(Real.sqrt (b.Delta r) : ℂ)*
      (b.frequencyK m ω r/(b.Delta r : ℂ)-(b.eta : ℂ)*ω)

def radialR1 (b : KN.Background) (σ : ℝ) (ω : ℂ) (r : ℝ) : ℂ :=
  -(σ : ℂ)*2*ω*(b.Q : ℂ)*((b.M*r-b.Q^2 : ℝ) : ℂ)/(b.d : ℂ)+Complex.I*(b.beta : ℂ)

/-- The actual full angular PDE and exact physical transformed boundary
classes. There is no assumed separation, expansion or extraction conclusion. -/
structure FullField (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ) where
  field : ℝ → FullAngularHilbert
  smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) field (Set.Ioi b.rPlus)
  mem_domain : ∀ r, b.rPlus < r → field r ∈ (fullFrequencyOperator b hQ σ hσ m ω).domain
  equation : ∀ r (hr : b.rPlus < r),
    (Real.sqrt (b.Delta r) : ℂ) • deriv field r =
      fullFrequencyOperator b hQ σ hσ m ω ⟨field r,mem_domain r hr⟩ +
      radialR0 b σ m ω r • fullI (field r) + radialR1 b σ ω r • fullJ (field r)
  horizon_plus : KN.Boundary.HorizonRegular b m ω ((1-2*σ)/4)
    (fun r => fullPiPlus (field r))
  horizon_minus : KN.Boundary.HorizonRegular b m ω ((1-4*σ)/4)
    (fun r => fullPiMinus (field r))
  outgoing : KN.Boundary.Outgoing b m ω field

def FullField.Nonzero {b : KN.Background} {hQ : b.Q ≠ 0}
    {σ : ℝ} {hσ : σ=1 ∨ σ= -1} {m : ℤ} {ω : ℂ}
    (Z : FullField b hQ σ hσ m ω) : Prop :=
  ∃ r, b.rPlus < r ∧ Z.field r ≠ 0

end
end KN.Angular

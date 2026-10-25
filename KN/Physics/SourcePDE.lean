import KN.Physics.SourcePDEProduct
import KN.Physics.SourcePDECoupling

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal source variables in Hintz (3), for both positive and negative systems. -/
def sourceY (positive : Bool) (sign : ℂ) (b : Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) (r θ : ℝ) : Fin 2 → ℂ :=
  chiralInput (transformScale positive b r θ) (transformCharge positive b)
    (transformMix positive b r) sign (u r θ)

def sourceSign (positive : Bool) : ℂ := if positive then 1 else -1

/-- Precisely the pre-integrating-factor chiral necessary system, Hintz
arXiv:2609.33661v1, equation (4), with actual equation (3) source variables.
All coefficients are complex algebraic in omega: dagger in the original NP
notation changes signs, and does not conjugate omega. This is not the separated
or transformed equation (8), and contains no mode-exclusion premise. -/
def PublishedChiralSystem (positive : Bool) (b : Background) (m : ℤ) (omega : ℂ)
    (u : ℝ → ℝ → Fin 4 → ℂ) : Prop :=
  ∀ r θ, b.rPlus<r → 0<θ → θ<Real.pi →
    (sourceVectorD (Real.sqrt (b.Delta r)) (-1) (sourceY positive 1 b u) r θ =
      sourceA b r θ *ᵥ sourceY positive 1 b u r θ +
      physicalOriginalCoupling b m omega (sourceSign positive) r θ *ᵥ sourceY positive (-1) b u r θ) ∧
    (sourceVectorD (Real.sqrt (b.Delta r)) 1 (sourceY positive (-1) b u) r θ =
      -sourceA b r θ *ᵥ sourceY positive (-1) b u r θ +
      (physicalOriginalCoupling b m omega (sourceSign positive) r θ).adjugate *ᵥ sourceY positive 1 b u r θ)

/-- Smooth source sections give these ordinary partial derivatives before any
integrating factor is applied. No transformed equation is part of this condition. -/
def SourceChiralDifferentiable (positive : Bool) (b : Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) : Prop :=
  ∀ r θ, b.rPlus<r → 0<θ → θ<Real.pi → ∀ sign ∈ ({1,-1} : Set ℂ),
    ∀ i, SourceDifferentiableAt (fun x y => sourceY positive sign b u x y i) r θ

/-- Actual equation (4) is carried to the transformed two chiral blocks by
ordinary differentiation of adj(X), X*, and frequency-independent matrix algebra. -/
theorem source_chiral_transport (positive : Bool) (b : Background) (hQ : b.Q≠0)
    (m : ℤ) (omega : ℂ) (u : ℝ → ℝ → Fin 4 → ℂ)
    (hs : PublishedChiralSystem positive b m omega u)
    (hd : SourceChiralDifferentiable positive b u)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) :
    (sourceVectorD (Real.sqrt (b.Delta r)) (-1)
      (fun x y => (sourceTransform positive b x y (u x y)).1) r θ =
      physicalChiralCoupling b m omega (sourceSign positive) r θ *ᵥ
        (sourceTransform positive b r θ (u r θ)).2) ∧
    (sourceVectorD (Real.sqrt (b.Delta r)) 1
      (fun x y => (sourceTransform positive b x y (u x y)).2) r θ =
      (physicalChiralCoupling b m omega (sourceSign positive) r θ).adjugate *ᵥ
        (sourceTransform positive b r θ (u r θ)).1) := by
  obtain ⟨hp,hm⟩ := hs r θ hr hθ hπ
  constructor
  · have h := source_positive_transport b hr θ (sourceY positive 1 b u) (sourceY positive (-1) b u)
      (hd r θ hr hθ hπ 1 (by simp)) _ hp
    rw [←physical_source_coupling b hQ m omega (sourceSign positive) hr hθ hπ,
      ←Matrix.mulVec_mulVec] at h
    exact h
  · have h := source_negative_transport b hr θ (sourceY positive 1 b u) (sourceY positive (-1) b u)
      (hd r θ hr hθ hπ (-1) (by simp)) _ hm
    rw [←physical_source_reverse_coupling b hQ m omega (sourceSign positive) hr hθ hπ,
      ←Matrix.mulVec_mulVec] at h
    exact h

end
end KN.Physics

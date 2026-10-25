import KN.Physics.RadiativeRecovery

noncomputable section
namespace KN.Physics

def phantomPositiveValues (ρ : ℂ) (v : RadiativeCurvatureMaxwell) (k s : ℂ) : Fin 4 → ℂ :=
  ![v.dPsi0,(Real.sqrt 2:ℂ)*ρ*v.dPsi1,k,s]
def phantomNegativeValues (ρ : ℂ) (v : RadiativeCurvatureMaxwell) (n ell : ℂ) : Fin 4 → ℂ :=
  ![ρ^4*v.dPsi4,ρ^3*v.dPsi3/(Real.sqrt 2:ℂ),n,ell]

/-- Actual invertible charged source maps recover all four physical invariants
in the phantom frame, with the exact Maxwell-curvature normalization. -/
theorem physical_radiative_zero_of_source_transforms (b : KN.Background) (hQ : b.Q ≠ 0)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi)
    (Ψ₂ : ℂ) (v : RadiativeCurvatureMaxwell) (k s n ell : ℂ)
    (hg0 : v.dPhi0=0) (hg2 : v.dPhi2=0)
    (hp : sourceTransform true b r θ (phantomPositiveValues (rhoStar b r θ) v k s)=0)
    (hm : sourceTransform false b r θ (phantomNegativeValues (rhoStar b r θ) v n ell)=0) :
    gravitationalPlus v=0 ∧ gravitationalMinus (rhoStar b r θ) v=0 ∧
      electromagneticPlus b.M b.Q (rhoStar b r θ) Ψ₂ v=0 ∧
      electromagneticMinus b.M b.Q (rhoStar b r θ) Ψ₂ v=0 := by
  have hp' := sourceTransform_zero true b hQ hr hθ hπ _ hp
  have hm' := sourceTransform_zero false b hQ hr hθ hπ _ hm
  apply phantom_radiative_zero _ _ _ _ v
    (Complex.ofReal_ne_zero.mpr (ne_of_gt b.mass_pos)) (rhoStar_ne_zero b hr θ) hg0 hg2
  · exact congrFun hp' 0
  · exact congrFun hm' 0
  · exact congrFun hp' 1
  · exact congrFun hm' 1

end KN.Physics

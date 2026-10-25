import KN.Physics.ChiralTransform
import KN.Physics.NPSystem

noncomputable section
namespace KN.Physics
open Matrix

def transformScale (positive : Bool) (b : Background) (r θ : ℝ) : ℂ :=
  ((Real.rpow (b.Delta r) (if positive then (5:ℝ)/4 else (-3:ℝ)/4) *
    Real.sqrt (Real.sin θ) : ℝ) : ℂ)
def transformMix (positive : Bool) (b : Background) (r : ℝ) : ℂ :=
  if positive then ((Real.sqrt (b.Delta r) : ℂ))⁻¹ else -(Real.sqrt (b.Delta r) : ℂ)
def transformCharge (positive : Bool) (b : Background) : ℂ :=
  if positive then (b.Q : ℂ) else -(b.Q : ℂ)

def sourceTransform (positive : Bool) (b : Background) (r θ : ℝ)
    (u : Fin 4 → ℂ) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  let X := physicalSourceMatrix b r θ
  let F := transformScale positive b r θ
  let Q := transformCharge positive b
  let t := transformMix positive b r
  (X.adjugate *ᵥ chiralInput F Q t 1 u,
    X.conjTranspose *ᵥ chiralInput F Q t (-1) u)

theorem transformScale_ne_zero (positive : Bool) (b : Background) {r θ : ℝ}
    (hr : b.rPlus < r) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    transformScale positive b r θ ≠ 0 := by
  unfold transformScale
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos (b.Delta_pos hr) _)
    (Real.sqrt_pos.mpr (Real.sin_pos_of_pos_of_lt_pi hθ hπ)))
theorem transformMix_ne_zero (positive : Bool) (b : Background) {r : ℝ}
    (hr : b.rPlus < r) : transformMix positive b r ≠ 0 := by
  have ht : (Real.sqrt (b.Delta r) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  cases positive <;> simp [transformMix, ht]
theorem transformCharge_ne_zero (positive : Bool) (b : Background) (hQ : b.Q ≠ 0) :
    transformCharge positive b ≠ 0 := by
  cases positive <;> simp [transformCharge, hQ]

/-- Both manuscript source transformations are genuinely injective at every exterior point. -/
theorem sourceTransform_zero (positive : Bool) (b : Background) (hQ : b.Q ≠ 0)
    {r θ : ℝ} (hr : b.rPlus < r) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (u : Fin 4 → ℂ) (hz : sourceTransform positive b r θ u = 0) : u = 0 := by
  have hp := congrArg Prod.fst hz
  have hm := congrArg Prod.snd hz
  exact transformed_chiral_zero (physicalSourceMatrix b r θ)
    (physicalSourceMatrix_det_ne_zero b hr θ)
    (transformScale positive b r θ) (transformCharge positive b) (transformMix positive b r)
    (transformScale_ne_zero positive b hr hθ hπ) (transformCharge_ne_zero positive b hQ)
    (transformMix_ne_zero positive b hr) u hp hm

/-- The positive electromagnetic invariant in phantom gauge is exactly (8b). -/
theorem electromagneticPlus_phantom (M Q ρ Ψ Ψ₂ : ℂ) (hM : M ≠ 0) :
    ρ/(3*M)*(Q*Ψ-3*ρ^2*Ψ₂*0) =
      Q/(3*(Real.sqrt 2 : ℂ)*M) * ((Real.sqrt 2 : ℂ)*ρ*Ψ) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
  field_simp
  ring

end KN.Physics

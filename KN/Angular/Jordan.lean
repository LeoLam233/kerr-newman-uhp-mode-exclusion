import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace KN.Angular
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Pair an actual Jordan chain under the anticommuting involution. This holds
also at lam=0; no eigenvalue division appears. -/
theorem paired_jordan_step (A I : E →ₗ[ℂ] E) (lam : ℂ) (u prev : E)
    (hanti : ∀ v, A (I v) = -(I (A v)))
    (hchain : A u = lam • u + prev) :
    A (I u) = -lam • I u - I prev := by
  rw [hanti, hchain, map_add, map_smul]
  simp [sub_eq_add_neg, add_comm]

/-- The chiral eigenvalue relation IJ u = i u and I²=1 yield J u=i I u. -/
theorem chiral_J (I J : E →ₗ[ℂ] E) (u : E)
    (hI : ∀ v, I (I v) = v) (hS : I (J u) = Complex.I • u) :
    J u = Complex.I • I u := by
  have h := congrArg I hS
  simpa only [hI, map_smul] using h

/-- The paired J action has the opposite sign. -/
theorem paired_J (I J : E →ₗ[ℂ] E) (u : E)
    (hI : ∀ v, I (I v) = v) (hanti : ∀ v, J (I v) = -(I (J v)))
    (hJu : J u = Complex.I • I u) : J (I u) = -Complex.I • u := by
  rw [hanti, hJu, map_smul, hI, neg_smul]

/-- Equation (24) from the homogeneous highest Jordan coefficient, in a
polynomial form that does not divide by the radial square root. -/
theorem radial_basis_change (d lam R₀ R₁ z₁ z₂ dz₁ dz₂ : ℂ)
    (hp : d*(dz₁-Complex.I*dz₂) =
      lam*(z₁-Complex.I*z₂)+(R₀-Complex.I*R₁)*(z₁+Complex.I*z₂))
    (hq : d*(dz₁+Complex.I*dz₂) =
      -lam*(z₁+Complex.I*z₂)+(R₀+Complex.I*R₁)*(z₁-Complex.I*z₂)) :
    d*dz₁ = R₀*z₁+(R₁-Complex.I*lam)*z₂ ∧
    d*dz₂ = -R₀*z₂+(R₁+Complex.I*lam)*z₁ := by
  constructor
  · linear_combination (norm := ring_nf) (hp+hq)/2
    simp [Complex.I_sq]
  · linear_combination (norm := ring_nf) Complex.I*(hp-hq)/2
    simp [Complex.I_sq]

end KN.Angular

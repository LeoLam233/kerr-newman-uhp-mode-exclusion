import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Explicit published external interface, not a proved theorem

Source: B. Mityagin and P. Siegl, *Local form subordination without a power
decay and a criterion of Riesz basesness*, Bol. Soc. Mat. Mex. 31, 111 (2025),
published 21 August 2025, Theorem 2.2 (itself citing Dunford–Schwartz,
Corollary XI.9.31), DOI 10.1007/s40590-025-00751-7.
Verified against the published full text on 2026-10-21.

The interface below is only its general p=2 Hilbert-space specialization,
with the eight nonreal rays of C002. It does NOT assume any angular spectrum,
positivity, domain identification, PDE extraction or KN result. All those
hypotheses must be proved separately for a concrete operator.
-/
namespace KN.Angular.External
noncomputable section
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A genuine bounded two-sided inverse to T-z on its actual domain. -/
structure ResolventAt (T : E →ₗ.[ℂ] E) (z : ℂ) where
  inverse : E →L[ℂ] E
  mem_domain : ∀ u, inverse u ∈ T.domain
  right_inverse : ∀ u, T ⟨inverse u, mem_domain u⟩ - z • inverse u = u
  left_inverse : ∀ u : T.domain, inverse (T u - z • (u : E)) = u

/-- A generalized eigenvector specified by an actual finite domain-valued chain. -/
def IsGeneralizedRoot (T : E →ₗ.[ℂ] E) (u : E) : Prop :=
  ∃ (z : ℂ) (n : ℕ) (chain : ℕ → E), 0 < n ∧ chain 0 = 0 ∧ chain n = u ∧
    ∀ j, j < n → ∃ hj : chain (j+1) ∈ T.domain,
      T ⟨chain (j+1),hj⟩ = z • chain (j+1) + chain j

/-- The rays have adjacent angles pi/4, strictly below pi/2, and none is real. -/
def completenessRay (j : Fin 8) (r : ℝ) : ℂ :=
  (r : ℂ)*Complex.exp (Complex.I*((Real.pi/8+(j.val : ℝ)*Real.pi/4 : ℝ) : ℂ))

/-- Explicit trusted published spectral theorem. The Hilbert–Schmidt premise
is the standard basis sum definition; the polynomial estimate is a bound on
actual resolvents on all eight rays, not an assumed completeness conclusion. -/
axiom mityagin_siegl_2025_theorem_2_2_p2
    (T : E →ₗ.[ℂ] E) (hclosed : T.IsClosed)
    (hdense : Dense (T.domain : Set E))
    (basis : HilbertBasis ℕ ℂ E) (z₀ : ℂ) (R₀ : ResolventAt T z₀)
    (hHS : Summable (fun n : ℕ => ‖R₀.inverse (basis n)‖^2))
    (hrays : ∀ j : Fin 8, ∃ (C R : ℝ) (N : ℕ), 0 < C ∧ 0 < R ∧
      ∀ r : ℝ, R ≤ r → ∃ Q : ResolventAt T (completenessRay j r),
        ‖Q.inverse‖ ≤ C*(1+r)^N) :
    Dense (Submodule.span ℂ {u : E | IsGeneralizedRoot T u} : Set E)

end
end KN.Angular.External

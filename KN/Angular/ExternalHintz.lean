import KN.Angular.WeakGraphTransform
import KN.Angular.ExternalMityaginSiegl
import KN.Background.Parameters
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Explicit published real-frequency angular input

P. Hintz, *Perturbations of Kerr–Newman black holes: separation and mode
stability*, arXiv:2609.33661v1, 27 September 2026, Lemma 1 and its proof.
https://arxiv.org/html/2609.33661v1 . The input is used ONLY at frequency zero.
The full four-component expression and maximal weak L² graph below are
explicit; the source establishes essential self-adjointness, identifies the
adjoint with that maximal graph, and proves compactness of the resolvent.
No spectral values, branch bookkeeping, coercivity, complex-frequency
completeness or upper-half-plane exclusion are included in this interface.
-/
namespace KN.Angular.External
noncomputable section

/-- Exact zero-frequency content of the published Hintz angular lemma. -/
axiom hintz_2026_v1_lemma1_zero_frequency
    (b : KN.Background) (hQ : b.Q ≠ 0) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) :
    ∃ T : FullAngularHilbert →ₗ.[ℂ] FullAngularHilbert,
      (∀ u v, (∃ hu : u ∈ T.domain, T ⟨u,hu⟩ = v) ↔ FullStaticGraph σ b.beta m u v) ∧
      IsSelfAdjoint T ∧ ∃ (z : ℂ) (R : ResolventAt T z), IsCompactOperator R.inverse

end
end KN.Angular.External

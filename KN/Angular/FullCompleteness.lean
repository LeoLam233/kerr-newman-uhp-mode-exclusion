import KN.Angular.FullResolvent
import KN.Analysis.ResolventReindex

namespace KN.Angular
noncomputable section

theorem fullFrequencyOperator_dense_adjoint_roots (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ) :
    Dense (Submodule.span ℂ {u : FullAngularHilbert |
      External.IsGeneralizedRoot (fullFrequencyOperator b hQ σ hσ m ω).adjoint u} :
      Set FullAngularHilbert) := by
  obtain ⟨R,hR⟩ := fullStaticOperator_resolvent_hilbertSchmidt b hQ σ hσ m
  exact KN.Analysis.boundedPerturbation_dense_adjoint_roots_indexed
    (fullStaticOperator b hQ σ hσ m) (fullStaticOperator_selfAdjoint b hQ σ hσ m)
    (ω • fullFrequencyMultiplier b σ) (fullStaticHilbertBasis b hQ (signedFourier σ m))
    Complex.I R hR

end
end KN.Angular

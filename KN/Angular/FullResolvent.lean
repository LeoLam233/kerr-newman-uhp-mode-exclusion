import KN.Angular.FullEigenbasis
import KN.Analysis.ResolventEigenbasis
import KN.Analysis.ResolventStaticSum

namespace KN.Angular
noncomputable section
open KN.Angular.External

theorem fullBasisEigenvalue_resolvent_sum (k : ℤ) (β : ℝ) :
    Summable (fun i : Bool × Jacobi.StaticLabel k =>
      (‖(fullBasisEigenvalue k β i : ℂ)-Complex.I‖^2)⁻¹) := by
  apply (KN.Analysis.doubled_staticEigenvalue_resolvent_sum k β).congr
  rintro ⟨s,i⟩
  cases s
  · rfl
  · change (‖(Jacobi.staticEigenvalue k β i : ℂ)-Complex.I‖^2)⁻¹ =
      (‖((-Jacobi.staticEigenvalue k β i : ℝ) : ℂ)-Complex.I‖^2)⁻¹
    rw [KN.Analysis.real_sub_I_norm_sq,KN.Analysis.real_sub_I_norm_sq,neg_sq]

theorem fullStaticOperator_resolvent_hilbertSchmidt (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) :
    ∃ R : ResolventAt (fullStaticOperator b hQ σ hσ m) Complex.I,
      Summable (fun i => ‖R.inverse (fullStaticHilbertBasis b hQ (signedFourier σ m) i)‖^2) := by
  obtain ⟨R,_⟩ := KN.Analysis.selfAdjoint_exists_resolvent
    (fullStaticOperator b hQ σ hσ m) (fullStaticOperator_selfAdjoint b hQ σ hσ m)
    Complex.I (by simp)
  refine ⟨R,?_⟩
  apply (KN.Analysis.resolvent_hilbertSchmidt_iff_eigenvalue_sum
    (fullStaticOperator b hQ σ hσ m) Complex.I R
    (fullStaticHilbertBasis b hQ (signedFourier σ m))
    (fun i => (fullBasisEigenvalue (signedFourier σ m) b.beta i : ℂ))
    (fun i => (fullStaticHilbertBasis_graph b hQ σ hσ m i).choose)
    (fun i => (fullStaticHilbertBasis_graph b hQ σ hσ m i).choose_spec)).mpr
  exact fullBasisEigenvalue_resolvent_sum _ _

end
end KN.Angular

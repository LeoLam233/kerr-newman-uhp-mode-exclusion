import KN.Analysis.ResolventRays
import KN.Analysis.ResolventClosed
import KN.Analysis.ResolventHilbertSchmidt

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- General compact-resolvent completeness bridge. The concrete base realization
must prove self-adjointness and its actual Hilbert--Schmidt resolvent basis sum.
Every bounded-perturbation and eight-ray hypothesis is then discharged here. -/
theorem boundedPerturbation_dense_generalized_roots
    (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (B : E →L[ℂ] E)
    (basis : HilbertBasis ℕ ℂ E) (z₀ : ℂ) (R₀ : ResolventAt T z₀)
    (hHS : Summable (fun n : ℕ => ‖R₀.inverse (basis n)‖^2)) :
    Dense (Submodule.span ℂ {u : E | IsGeneralizedRoot (boundedPerturbation T B) u} : Set E) := by
  let w : ℂ := (‖B‖+1 : ℝ)*Complex.I
  have hw : w.im=‖B‖+1 := by simp [w]
  have hwp : 0<w.im := by rw [hw]; linarith [norm_nonneg B]
  obtain ⟨R,hR⟩ := selfAdjoint_exists_resolvent T hT w (ne_of_gt hwp)
  obtain ⟨Q,_⟩ := exists_perturbed_resolvent T w B R |w.im| (by rw [abs_of_pos hwp,hw]; linarith) hR
  have hRHS := resolvent_hilbertSchmidt_change_parameter basis T z₀ w R₀ R hHS
  have hQHS := perturbed_resolvent_hilbertSchmidt basis T w B R Q hRHS
  exact mityagin_siegl_2025_theorem_2_2_p2 (boundedPerturbation T B)
    (boundedPerturbation_isClosed T hT.isClosed B)
    (boundedPerturbation_dense T hT.dense_domain B) basis w Q hQHS
    (boundedPerturbation_eight_rays T hT B)

end
end KN.Analysis

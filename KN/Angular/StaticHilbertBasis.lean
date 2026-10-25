import KN.Angular.StaticCompleteness
import KN.Angular.GraphLinearity

namespace KN.Angular.Jacobi
noncomputable section
open scoped ComplexInnerProductSpace

def normalizedStaticVector (k : ℤ) (β : ℝ) (i : StaticLabel k) : AngularHilbert :=
  ((‖staticEigenvector k β i‖⁻¹ : ℝ) : ℂ) • staticEigenvector k β i

theorem normalizedStaticVector_orthonormal (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ) :
    Orthonormal ℂ (normalizedStaticVector k b.beta) := by
  constructor
  · intro i
    change ‖((‖staticEigenvector k b.beta i‖⁻¹ : ℝ) : ℂ) • staticEigenvector k b.beta i‖=1
    rw [Complex.ofReal_inv]
    exact norm_smul_inv_norm (𝕜 := ℂ) (staticEigenvector_ne_zero k b.beta i)
  · intro i j hij
    simp only [normalizedStaticVector,inner_smul_left,inner_smul_right,
      staticEigenvector_orthogonal b hQ k i j hij,mul_zero]

theorem normalizedStaticVector_span (k : ℤ) (β : ℝ) :
    Submodule.span ℂ (Set.range (normalizedStaticVector k β)) =
      Submodule.span ℂ (Set.range (staticEigenvector k β)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨i,rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℂ (Set.range (normalizedStaticVector k β)))
      (‖staticEigenvector k β i‖ : ℂ) (Submodule.subset_span ⟨i,rfl⟩)
    have hc : (‖staticEigenvector k β i‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (staticEigenvector_ne_zero k β i)
    simp only [normalizedStaticVector,smul_smul,Complex.ofReal_inv,mul_inv_cancel₀ hc,one_smul] at h
    exact h

/-- The genuine static angular Hilbert basis. Its construction uses proved
first-order domain membership, real-frequency symmetry and scalar Jacobi
completeness; no complex-frequency eigenbasis is asserted. -/
def staticHilbertBasis (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ) :
    HilbertBasis (StaticLabel k) ℂ AngularHilbert :=
  HilbertBasis.mk (normalizedStaticVector_orthonormal b hQ k) (by
    rw [normalizedStaticVector_span]
    rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (staticEigenvector_dense k b.beta)])

theorem normalizedStaticVector_graph (k : ℤ) (β : ℝ) (i : StaticLabel k) :
    StaticGraph 1 β k (normalizedStaticVector k β i)
      ((staticEigenvalue k β i : ℂ) • normalizedStaticVector k β i) := by
  have h := StaticGraph.smul 1 β k (staticEigenvector_graph k β i)
    ((‖staticEigenvector k β i‖⁻¹ : ℝ) : ℂ)
  simpa only [normalizedStaticVector,smul_comm ((‖staticEigenvector k β i‖⁻¹ : ℝ) : ℂ)] using h

end
end KN.Angular.Jacobi

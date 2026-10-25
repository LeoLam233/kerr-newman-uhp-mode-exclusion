import KN.Angular.StaticEigenFamily
import KN.Angular.JacobiCoordinateBlocks

namespace KN.Angular.Jacobi
noncomputable section

theorem pairVector_mem_eigen_span (k : ℤ) (β : ℝ) (n : ℕ) (z : ℂ × ℂ) :
    pairVector k n z ∈ Submodule.span ℂ (Set.range (staticEigenvector k β)) := by
  have hc : (ladderConstant k n : ℂ) ≠ 0 := by exact_mod_cast ladderConstant_ne_zero k n
  have hr : (positiveRoot k β n : ℂ) ≠ 0 := by
    have hp : 0 < positiveRoot k β n := lt_of_le_of_lt (abs_nonneg β) (positiveRoot_gt_abs k β n)
    exact_mod_cast ne_of_gt hp
  obtain ⟨a,b,hab⟩ := pairedVector_spanning (β : ℂ) (ladderConstant k n : ℂ)
    (positiveRoot k β n : ℂ) hc hr z
  have hmap := congrArg (pairVectorLinear k n) hab
  rw [map_add,map_smul,map_smul] at hmap
  change a • pairVector k n (pairedVector (β : ℂ) (ladderConstant k n : ℂ)
      (positiveRoot k β n : ℂ)) +
    b • pairVector k n (pairedVector (β : ℂ) (ladderConstant k n : ℂ)
      (-(positiveRoot k β n : ℂ))) = pairVector k n z at hmap
  rw [← hmap]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨.inl (true,n),rfl⟩
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨.inl (false,n), ?_⟩
    simp [staticEigenvector,staticEigenvalue]

/-- Completeness of the actual first-order static eigenvectors, including
only the correctly signed ground branch. This is proved from scalar Jacobi
completeness, not assumed as an angular spectral interface. -/
theorem staticEigenvector_dense (k : ℤ) (β : ℝ) :
    Dense (Submodule.span ℂ (Set.range (staticEigenvector k β)) : Set AngularHilbert) := by
  let S := (Submodule.span ℂ (Set.range (staticEigenvector k β))).topologicalClosure
  have hp (n : ℕ) (z : ℂ × ℂ) : pairVector k n z ∈ S :=
    Submodule.le_topologicalClosure _ (pairVector_mem_eigen_span k β n z)
  have hground (hk : |k| ≤ 1) : groundVector k ∈ S := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨.inr ⟨hk⟩,rfl⟩
  have hu (n : ℕ) : injectCoordinate 0 (regularVector |(k : ℝ)+1| |(k : ℝ)-1|
      (abs_nonneg _) (abs_nonneg _) n) ∈ S := by
    by_cases hk : |k| ≤ 1
    · cases n with
      | zero => rw [inject_upper_ground]; exact hground hk
      | succ n =>
        have hi : pairedIndex k n=n+1 := by simp [pairedIndex,hk]
        rw [← hi,inject_upper_paired]
        exact hp n (1,0)
    · have hi : pairedIndex k n=n := by simp [pairedIndex,hk]
      rw [← hi,inject_upper_paired]
      exact hp n (1,0)
  have hl (n : ℕ) : injectCoordinate 1 (regularVector |(k : ℝ)+2| |(k : ℝ)-2|
      (abs_nonneg _) (abs_nonneg _) n) ∈ S := by
    rw [inject_lower]
    exact hp n (0,1)
  have htop : S=⊤ := by
    apply top_unique
    intro u _
    rw [← reconstruct_coordinates u]
    apply S.add_mem
    · exact coordinate_mem_of_jacobi S (Submodule.isClosed_topologicalClosure _) 0
        _ _ (abs_nonneg _) (abs_nonneg _) hu _
    · exact coordinate_mem_of_jacobi S (Submodule.isClosed_topologicalClosure _) 1
        _ _ (abs_nonneg _) (abs_nonneg _) hl _
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

end
end KN.Angular.Jacobi

import KN.Angular.JacobiGround
import KN.Angular.L2Coordinates

namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory

theorem inject_upper_paired (k : ℤ) (n : ℕ) :
    injectCoordinate 0 (regularVector |(k : ℝ)+1| |(k : ℝ)-1|
      (abs_nonneg _) (abs_nonneg _) (pairedIndex k n)) = pairVector k n (1,0) := by
  apply Lp.ext
  filter_upwards [injectCoordinate_ae 0 (regularVector |(k : ℝ)+1| |(k : ℝ)-1|
      (abs_nonneg _) (abs_nonneg _) (pairedIndex k n)),
    (regular_memLp |(k : ℝ)+1| |(k : ℝ)-1| (abs_nonneg _) (abs_nonneg _) (pairedIndex k n)).coeFn_toLp,
    (pairFunction_memLp k n (1,0)).coeFn_toLp] with θ h1 h2 h3
  change (regularVector _ _ (abs_nonneg _) (abs_nonneg _) _) θ = _ at h2
  change pairVector k n (1,0) θ = _ at h3
  rw [h1,h2,h3]
  ext j
  fin_cases j <;> simp [coordinateInjection,pairFunction,upper,Complex.real_smul]

theorem inject_lower (k : ℤ) (n : ℕ) :
    injectCoordinate 1 (regularVector |(k : ℝ)+2| |(k : ℝ)-2|
      (abs_nonneg _) (abs_nonneg _) n) = pairVector k n (0,1) := by
  apply Lp.ext
  filter_upwards [injectCoordinate_ae 1 (regularVector |(k : ℝ)+2| |(k : ℝ)-2|
      (abs_nonneg _) (abs_nonneg _) n),
    (regular_memLp |(k : ℝ)+2| |(k : ℝ)-2| (abs_nonneg _) (abs_nonneg _) n).coeFn_toLp,
    (pairFunction_memLp k n (0,1)).coeFn_toLp] with θ h1 h2 h3
  change (regularVector _ _ (abs_nonneg _) (abs_nonneg _) _) θ = _ at h2
  change pairVector k n (0,1) θ = _ at h3
  rw [h1,h2,h3]
  ext j
  fin_cases j <;> simp [coordinateInjection,pairFunction,lower,Complex.real_smul]

theorem inject_upper_ground (k : ℤ) :
    injectCoordinate 0 (regularVector |(k : ℝ)+1| |(k : ℝ)-1|
      (abs_nonneg _) (abs_nonneg _) 0) = groundVector k := by
  apply Lp.ext
  filter_upwards [injectCoordinate_ae 0 (regularVector |(k : ℝ)+1| |(k : ℝ)-1|
      (abs_nonneg _) (abs_nonneg _) 0),
    (regular_memLp |(k : ℝ)+1| |(k : ℝ)-1| (abs_nonneg _) (abs_nonneg _) 0).coeFn_toLp,
    (groundFunction_memLp k).coeFn_toLp] with θ h1 h2 h3
  change (regularVector _ _ (abs_nonneg _) (abs_nonneg _) _) θ = _ at h2
  change groundVector k θ = _ at h3
  rw [h1,h2,h3]
  ext j
  fin_cases j <;> simp [coordinateInjection,groundFunction,upper,Complex.real_smul]

/-- Completeness of the general scalar Jacobi family transfers through an
actual bounded coordinate embedding to any closed linear subspace. -/
theorem coordinate_mem_of_jacobi (S : Submodule ℂ AngularHilbert) (hS : IsClosed (S : Set AngularHilbert))
    (j : Fin 2) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hmem : ∀ n, injectCoordinate j (regularVector α β hα hβ n) ∈ S) (f : H) :
    injectCoordinate j f ∈ S := by
  let T : Submodule ℂ H := S.comap (injectCoordinate j).toLinearMap
  have hT : IsClosed (T : Set H) := hS.preimage (injectCoordinate j).continuous
  have hspan : Submodule.span ℂ (Set.range (normalizedVector α β hα hβ)) ≤ T := by
    apply Submodule.span_le.2
    rintro _ ⟨n,rfl⟩
    change injectCoordinate j (normalizedVector α β hα hβ n) ∈ S
    unfold normalizedVector
    rw [map_smul]
    exact S.smul_mem _ (hmem n)
  have hcl := (Submodule.span ℂ (Set.range (normalizedVector α β hα hβ))).topologicalClosure_minimal hspan hT
  rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (orthonormal_complete α β hα hβ).2] at hcl
  exact hcl (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ H))

end
end KN.Angular.Jacobi

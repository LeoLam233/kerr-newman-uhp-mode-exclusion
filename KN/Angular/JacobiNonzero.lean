import KN.Angular.JacobiVectorBlocks

namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory

theorem regularVector_ne_zero (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    regularVector α β hα hβ n ≠ 0 := by
  intro hz
  have hn := (orthonormal_complete α β hα hβ).1.ne_zero n
  apply hn
  simp [normalizedVector,hz]

theorem regular_not_ae_zero (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ¬ (fun θ => (regularFunction α β n θ : ℂ)) =ᵐ[intervalMeasure] 0 := by
  intro hz
  apply regularVector_ne_zero α β hα hβ n
  apply Lp.ext
  filter_upwards [(regular_memLp α β hα hβ n).coeFn_toLp,hz,
    Lp.coeFn_zero ℂ 2 intervalMeasure] with θ h1 h2 h3
  change (regularVector α β hα hβ n) θ = _ at h1
  rw [h1,h3]
  exact h2

theorem pairVector_ne_zero_of_second (k : ℤ) (n : ℕ) (z : ℂ × ℂ) (hz : z.2 ≠ 0) :
    pairVector k n z ≠ 0 := by
  intro hzero
  apply regular_not_ae_zero |(k : ℝ)+2| |(k : ℝ)-2| (abs_nonneg _) (abs_nonneg _) n
  have hpair := (pairFunction_memLp k n z).coeFn_toLp
  change (pairVector k n z : ℝ → AngularFiber) =ᵐ[angularMeasure] pairFunction k n z at hpair
  rw [hzero] at hpair
  filter_upwards [hpair,Lp.coeFn_zero AngularFiber 2 angularMeasure] with θ h1 h2
  have h := congrArg (fun v : AngularFiber => v 1) (h1.symm.trans h2)
  rw [pairFunction_one] at h
  simpa only [lower,Pi.zero_apply] using (mul_eq_zero.mp h).resolve_right hz

/-- The paired eigenvectors are genuinely nonzero elements of L². -/
theorem paired_eigenvector_ne_zero (k : ℤ) (n : ℕ) (β ν : ℝ) :
    pairVector k n (pairedVector (β : ℂ) (ladderConstant k n : ℂ) (ν : ℂ)) ≠ 0 := by
  apply pairVector_ne_zero_of_second
  change Complex.I*(ladderConstant k n : ℂ) ≠ 0
  apply mul_ne_zero Complex.I_ne_zero
  exact_mod_cast ladderConstant_ne_zero k n

end
end KN.Angular.Jacobi

import KN.Angular.JacobiNonzero

namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory
open scoped ContDiff

def groundFunction (k : ℤ) (θ : ℝ) : AngularFiber :=
  upper (k : ℝ) 0 θ • PiLp.single 2 0 (1 : ℂ)

theorem groundFunction_smooth (k : ℤ) :
    ContDiffOn ℝ ∞ (groundFunction k) (Set.Ioo 0 Real.pi) :=
  (regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) 0).smul contDiffOn_const

theorem groundFunction_memLp (k : ℤ) : MemLp (groundFunction k) 2 angularMeasure := by
  apply memLp_piLp_iff.2
  intro i
  fin_cases i
  · change MemLp (fun θ => groundFunction k θ 0) 2 intervalMeasure
    simpa [groundFunction,Complex.real_smul] using upper_memLp (k : ℝ) 0
  · simp [groundFunction]

def groundVector (k : ℤ) : AngularHilbert :=
  (groundFunction_memLp k).toLp (groundFunction k)

theorem groundVector_ne_zero (k : ℤ) : groundVector k ≠ 0 := by
  intro hzero
  apply regular_not_ae_zero |(k : ℝ)+1| |(k : ℝ)-1| (abs_nonneg _) (abs_nonneg _) 0
  have hpair := (groundFunction_memLp k).coeFn_toLp
  change (groundVector k : ℝ → AngularFiber) =ᵐ[angularMeasure] groundFunction k at hpair
  rw [hzero] at hpair
  filter_upwards [hpair,Lp.coeFn_zero AngularFiber 2 angularMeasure] with θ h1 h2
  have h := congrArg (fun v : AngularFiber => v 0) (h1.symm.trans h2)
  simpa [groundFunction,upper,Complex.real_smul] using h

theorem groundFunction_differential (k : ℤ) (β θ : ℝ)
    (hk : |k| ≤ 1) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    massPrincipal.toEuclideanLin (deriv (groundFunction k) θ) +
      (massPotential (staticCoefficient 1 k θ : ℂ) (β : ℂ)).toEuclideanLin
        (groundFunction k θ) = (-β : ℂ) • groundFunction k θ := by
  have hsm : ContDiffOn ℝ ∞ (upper (k : ℝ) 0) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) 0
  have hd := ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
    (by simp)).hasDerivAt.smul_const (PiLp.single 2 0 (1 : ℂ) : AngularFiber)
  have hkR : |(k : ℝ)| ≤ 1 := by exact_mod_cast hk
  have hz := upper_ground_kernel (k : ℝ) θ hkR hθ
  have hcoef : staticCoefficient 1 k θ=coefficient (k : ℝ) θ := by
    simp [staticCoefficient,coefficient,add_div]
  have hzC : ((deriv (upper (k : ℝ) 0) θ : ℝ) : ℂ) -
    (coefficient (k : ℝ) θ : ℂ)*(upper (k : ℝ) 0 θ : ℂ) = 0 := by
    exact_mod_cast hz
  change HasDerivAt (groundFunction k) _ θ at hd
  rw [hd.deriv,hcoef]
  ext i
  fin_cases i
  · simp [massPrincipal,massPotential,Matrix.toLpLin_apply,groundFunction,Complex.real_smul]
    ring
  · simp [massPrincipal,massPotential,Matrix.toLpLin_apply,groundFunction,Complex.real_smul]
    linear_combination Complex.I*hzC

/-- The actual unpaired L² eigenvector has eigenvalue -β. Its opposite sign
is never inserted by squaring the first-order operator. -/
theorem groundVector_graph (k : ℤ) (β : ℝ) (hk : |k| ≤ 1) :
    StaticGraph 1 β k (groundVector k) ((-β : ℂ) • groundVector k) := by
  have hraw : MatrixWeakGraph massPrincipal
      (fun θ => massPotential (staticCoefficient 1 k θ : ℂ) (β : ℂ))
      (groundFunction k) (fun θ => (-β : ℂ) • groundFunction k θ) := by
    apply KN.Analysis.matrixWeakGraph_of_classical
    · exact groundFunction_smooth k
    · exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (-β : ℂ))
        (Set.Ioo 0 Real.pi)).smul (groundFunction_smooth k).continuousOn
    · intro θ hθ
      exact (groundFunction_differential k β θ hk hθ).symm
  apply (MatrixWeakGraph.congr_ae massPrincipal
    (fun θ => massPotential (staticCoefficient 1 k θ : ℂ) (β : ℂ))
    (groundFunction_memLp k).coeFn_toLp ?_).mpr hraw
  filter_upwards [Lp.coeFn_smul (-β : ℂ) (groundVector k),
    (groundFunction_memLp k).coeFn_toLp] with θ h1 h2
  change groundVector k θ = _ at h2
  rw [h1]
  change (-β : ℂ) • groundVector k θ = _
  rw [h2]

end
end KN.Angular.Jacobi

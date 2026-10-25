import KN.Angular.JacobiPairing
import KN.Angular.PairedBlocks
import KN.Angular.WeakGraphTransform
import KN.Analysis.WeakGraphIBP
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory
open scoped ContDiff

/-- The actual vector-valued Jacobi block, with arbitrary complex coordinates. -/
def pairFunction (k : ℤ) (n : ℕ) (z : ℂ × ℂ) (θ : ℝ) : AngularFiber :=
  upper (k : ℝ) (pairedIndex k n) θ • PiLp.single 2 0 z.1 +
  lower (k : ℝ) n θ • PiLp.single 2 1 z.2

theorem pairFunction_zero (k : ℤ) (n : ℕ) (z : ℂ × ℂ) (θ : ℝ) :
    pairFunction k n z θ 0 = (upper (k : ℝ) (pairedIndex k n) θ : ℂ)*z.1 := by
  simp [pairFunction,Complex.real_smul]

theorem pairFunction_one (k : ℤ) (n : ℕ) (z : ℂ × ℂ) (θ : ℝ) :
    pairFunction k n z θ 1 = (lower (k : ℝ) n θ : ℂ)*z.2 := by
  simp [pairFunction,Complex.real_smul]

theorem pairFunction_smooth (k : ℤ) (n : ℕ) (z : ℂ × ℂ) :
    ContDiffOn ℝ ∞ (pairFunction k n z) (Set.Ioo 0 Real.pi) := by
  have hu : ContDiffOn ℝ ∞ (upper (k : ℝ) (pairedIndex k n)) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) _
  have hl : ContDiffOn ℝ ∞ (lower (k : ℝ) n) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) _
  exact (hu.smul contDiffOn_const).add (hl.smul contDiffOn_const)

theorem pairFunction_memLp (k : ℤ) (n : ℕ) (z : ℂ × ℂ) :
    MemLp (pairFunction k n z) 2 angularMeasure := by
  apply memLp_piLp_iff.2
  intro i
  fin_cases i
  · change MemLp (fun θ => pairFunction k n z θ 0) 2 intervalMeasure
    simpa only [pairFunction_zero,mul_comm] using
      (upper_memLp (k : ℝ) (pairedIndex k n)).const_mul z.1
  · change MemLp (fun θ => pairFunction k n z θ 1) 2 intervalMeasure
    simpa only [pairFunction_one,mul_comm] using (lower_memLp (k : ℝ) n).const_mul z.2

def pairVector (k : ℤ) (n : ℕ) (z : ℂ × ℂ) : AngularHilbert :=
  (pairFunction_memLp k n z).toLp (pairFunction k n z)

theorem pairFunction_hasDerivAt (k : ℤ) (n : ℕ) (z : ℂ × ℂ) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt (pairFunction k n z)
      (deriv (upper (k : ℝ) (pairedIndex k n)) θ • PiLp.single 2 0 z.1 +
       deriv (lower (k : ℝ) n) θ • PiLp.single 2 1 z.2) θ := by
  have hu : ContDiffOn ℝ ∞ (upper (k : ℝ) (pairedIndex k n)) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) _
  have hl : ContDiffOn ℝ ∞ (lower (k : ℝ) n) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) _
  exact (((hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
    (by simp)).hasDerivAt.smul_const _).add
    (((hl.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
    (by simp)).hasDerivAt.smul_const _)

/-- The differential expression acts on the actual L² Jacobi block by the
explicit two-by-two matrix, including the reverse first-order image. -/
theorem pairFunction_differential (k : ℤ) (n : ℕ) (β : ℝ) (z : ℂ × ℂ)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    massPrincipal.toEuclideanLin (deriv (pairFunction k n z) θ) +
      (massPotential (staticCoefficient 1 k θ : ℂ) (β : ℂ)).toEuclideanLin
        (pairFunction k n z θ) =
      pairFunction k n (pairedBlock (β : ℂ) (pairedEigenvalueSq k n : ℂ)
        (ladderConstant k n : ℂ) z) θ := by
  have hcoef : staticCoefficient 1 k θ=coefficient (k : ℝ) θ := by
    simp [staticCoefficient,coefficient,add_div]
  have hl := paired_lowering k n hθ
  have hr := paired_raising k n θ hθ
  change deriv (upper (k : ℝ) (pairedIndex k n)) θ -
    coefficient (k : ℝ) θ*upper (k : ℝ) (pairedIndex k n) θ =
    ladderConstant k n*lower (k : ℝ) n θ at hl
  have hlC : ((deriv (upper (k : ℝ) (pairedIndex k n)) θ : ℝ) : ℂ) -
    (coefficient (k : ℝ) θ : ℂ)*(upper (k : ℝ) (pairedIndex k n) θ : ℂ) =
    (ladderConstant k n : ℂ)*(lower (k : ℝ) n θ : ℂ) := by exact_mod_cast hl
  have hrC : ((deriv (lower (k : ℝ) n) θ : ℝ) : ℂ) +
    (coefficient (k : ℝ) θ : ℂ)*(lower (k : ℝ) n θ : ℂ) =
    -((pairedEigenvalueSq k n : ℂ)/(ladderConstant k n : ℂ))*
      (upper (k : ℝ) (pairedIndex k n) θ : ℂ) := by exact_mod_cast hr
  rw [(pairFunction_hasDerivAt k n z θ hθ).deriv,hcoef]
  ext i
  fin_cases i
  · simp [massPrincipal,massPotential,Matrix.toLpLin_apply,
      dotProduct,Fin.sum_univ_succ,pairFunction,Complex.real_smul,pairedBlock]
    linear_combination Complex.I*z.2*hrC
  · simp [massPrincipal,massPotential,Matrix.toLpLin_apply,
      dotProduct,Fin.sum_univ_succ,pairFunction,Complex.real_smul,pairedBlock]
    linear_combination Complex.I*z.1*hlC

/-- Every constructed Jacobi block is in the genuine maximal first-order
L² graph; the endpoint/domain assertion is now a theorem. -/
theorem pairVector_graph (k : ℤ) (n : ℕ) (β : ℝ) (z : ℂ × ℂ) :
    StaticGraph 1 β k (pairVector k n z)
      (pairVector k n (pairedBlock (β : ℂ) (pairedEigenvalueSq k n : ℂ)
        (ladderConstant k n : ℂ) z)) := by
  apply (MatrixWeakGraph.congr_ae massPrincipal
    (fun θ => massPotential (staticCoefficient 1 k θ : ℂ) (β : ℂ))
    (pairFunction_memLp k n z).coeFn_toLp
    (pairFunction_memLp k n _).coeFn_toLp).mpr
  apply KN.Analysis.matrixWeakGraph_of_classical
  · exact pairFunction_smooth k n z
  · exact (pairFunction_smooth k n _).continuousOn
  · intro θ hθ
    exact (pairFunction_differential k n β z θ hθ).symm

theorem pairFunction_smul (k : ℤ) (n : ℕ) (a : ℂ) (z : ℂ × ℂ) (θ : ℝ) :
    pairFunction k n (a • z) θ = a • pairFunction k n z θ := by
  ext i
  fin_cases i <;> simp [pairFunction,Complex.real_smul] <;> ring

theorem pairVector_smul (k : ℤ) (n : ℕ) (a : ℂ) (z : ℂ × ℂ) :
    pairVector k n (a • z) = a • pairVector k n z := by
  apply Lp.ext
  filter_upwards [(pairFunction_memLp k n (a • z)).coeFn_toLp,
    Lp.coeFn_smul a (pairVector k n z), (pairFunction_memLp k n z).coeFn_toLp] with θ h1 h2 h3
  change (pairVector k n (a • z)) θ = _ at h1
  change (pairVector k n z) θ = _ at h3
  rw [h1,h2]
  change _ = a • (pairVector k n z) θ
  rw [h3]
  exact pairFunction_smul k n a z θ

/-- Both real static spectral signs occur on every paired Jacobi block. -/
theorem pairVector_eigen_graph (k : ℤ) (n : ℕ) (β ν : ℝ)
    (hν : ν^2=β^2+pairedEigenvalueSq k n) :
    StaticGraph 1 β k
      (pairVector k n (pairedVector (β : ℂ) (ladderConstant k n : ℂ) (ν : ℂ)))
      ((ν : ℂ) • pairVector k n
        (pairedVector (β : ℂ) (ladderConstant k n : ℂ) (ν : ℂ))) := by
  have hc : (ladderConstant k n : ℂ) ≠ 0 := by
    exact_mod_cast ladderConstant_ne_zero k n
  have hνC : (ν : ℂ)^2=(β : ℂ)^2+(pairedEigenvalueSq k n : ℂ) := by exact_mod_cast hν
  have h := pairVector_graph k n β
    (pairedVector (β : ℂ) (ladderConstant k n : ℂ) (ν : ℂ))
  rw [pairedBlock_eigen _ _ _ _ hc hνC,pairVector_smul] at h
  exact h

theorem pairVector_add (k : ℤ) (n : ℕ) (z w : ℂ × ℂ) :
    pairVector k n (z+w)=pairVector k n z+pairVector k n w := by
  apply Lp.ext
  filter_upwards [(pairFunction_memLp k n (z+w)).coeFn_toLp,
    (pairFunction_memLp k n z).coeFn_toLp,(pairFunction_memLp k n w).coeFn_toLp,
    Lp.coeFn_add (pairVector k n z) (pairVector k n w)] with θ h0 h1 h2 h3
  change pairVector k n (z+w) θ = _ at h0
  change pairVector k n z θ = _ at h1
  change pairVector k n w θ = _ at h2
  rw [h0,h3]
  change _ = pairVector k n z θ+pairVector k n w θ
  rw [h1,h2]
  ext i
  fin_cases i <;> simp [pairFunction,Complex.real_smul]

def pairVectorLinear (k : ℤ) (n : ℕ) : (ℂ × ℂ) →ₗ[ℂ] AngularHilbert where
  toFun := pairVector k n
  map_add' := pairVector_add k n
  map_smul' := pairVector_smul k n

end
end KN.Angular.Jacobi

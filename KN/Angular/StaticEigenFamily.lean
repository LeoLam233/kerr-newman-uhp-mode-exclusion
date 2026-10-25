import KN.Angular.JacobiGround
import KN.Angular.StaticGraphProperties

namespace KN.Angular.Jacobi
noncomputable section

abbrev StaticLabel (k : ℤ) := (Bool × ℕ) ⊕ PLift (|k| ≤ 1)

def positiveRoot (k : ℤ) (β : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (β^2+pairedEigenvalueSq k n)

def staticEigenvalue (k : ℤ) (β : ℝ) : StaticLabel k → ℝ
  | .inl (true,n) => positiveRoot k β n
  | .inl (false,n) => -positiveRoot k β n
  | .inr _ => -β

def staticEigenvector (k : ℤ) (β : ℝ) : StaticLabel k → AngularHilbert
  | .inl (s,n) => pairVector k n
      (pairedVector (β : ℂ) (ladderConstant k n : ℂ)
        (staticEigenvalue k β (.inl (s,n)) : ℂ))
  | .inr _ => groundVector k

theorem positiveRoot_sq (k : ℤ) (β : ℝ) (n : ℕ) :
    (positiveRoot k β n)^2=β^2+pairedEigenvalueSq k n := by
  exact Real.sq_sqrt (by nlinarith [paired_gap k n,sq_nonneg β])

theorem positiveRoot_gt_abs (k : ℤ) (β : ℝ) (n : ℕ) :
    |β| < positiveRoot k β n := by
  have hpos : 0 ≤ positiveRoot k β n := Real.sqrt_nonneg _
  nlinarith [positiveRoot_sq k β n,paired_gap k n,sq_abs β]

theorem staticEigenvector_ne_zero (k : ℤ) (β : ℝ) (i : StaticLabel k) :
    staticEigenvector k β i ≠ 0 := by
  cases i with
  | inl sn => exact paired_eigenvector_ne_zero k sn.2 β _
  | inr h => exact groundVector_ne_zero k

theorem staticEigenvector_graph (k : ℤ) (β : ℝ) (i : StaticLabel k) :
    StaticGraph 1 β k (staticEigenvector k β i)
      ((staticEigenvalue k β i : ℂ) • staticEigenvector k β i) := by
  cases i with
  | inl sn =>
    obtain ⟨s,n⟩ := sn
    apply pairVector_eigen_graph
    cases s <;> simp only [staticEigenvalue,neg_sq]
      <;> exact positiveRoot_sq k β n
  | inr h => simpa [staticEigenvector,staticEigenvalue] using groundVector_graph k β h.down

theorem pairedEigenvalueSq_strictMono (k : ℤ) : StrictMono (pairedEigenvalueSq k) := by
  intro n m hnm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hmax : (1 : ℝ) ≤ max |(k : ℝ)| 1 := le_max_right _ _
  unfold pairedEigenvalueSq pairedIndex
  split_ifs <;> push_cast <;> nlinarith

theorem positiveRoot_strictMono (k : ℤ) (β : ℝ) : StrictMono (positiveRoot k β) := by
  intro n m hnm
  have hμ := pairedEigenvalueSq_strictMono k hnm
  have hn := positiveRoot_sq k β n
  have hm := positiveRoot_sq k β m
  have hnp := Real.sqrt_nonneg (β^2+pairedEigenvalueSq k n)
  have hmp := Real.sqrt_nonneg (β^2+pairedEigenvalueSq k m)
  change 0 ≤ positiveRoot k β n at hnp
  change 0 ≤ positiveRoot k β m at hmp
  nlinarith

theorem staticEigenvalue_injective (k : ℤ) (β : ℝ) :
    Function.Injective (staticEigenvalue k β) := by
  intro i j hij
  cases i with
  | inl sn =>
    obtain ⟨s,n⟩ := sn
    cases j with
    | inl tm =>
      obtain ⟨t,m⟩ := tm
      have hn := positiveRoot_gt_abs k β n
      have hm := positiveRoot_gt_abs k β m
      cases s <;> cases t
      · simp only [staticEigenvalue,neg_inj] at hij
        have hnm := (positiveRoot_strictMono k β).injective hij
        subst m
        rfl
      · simp only [staticEigenvalue] at hij
        exfalso
        linarith [abs_nonneg β]
      · simp only [staticEigenvalue] at hij
        exfalso
        linarith [abs_nonneg β]
      · simp only [staticEigenvalue] at hij
        have hnm := (positiveRoot_strictMono k β).injective hij
        subst m
        rfl
    | inr h =>
      have hn := positiveRoot_gt_abs k β n
      cases s <;> simp only [staticEigenvalue] at hij <;>
        exfalso <;> linarith [le_abs_self β,neg_le_abs β]
  | inr h =>
    cases j with
    | inl sn =>
      obtain ⟨s,n⟩ := sn
      have hn := positiveRoot_gt_abs k β n
      cases s <;> simp only [staticEigenvalue] at hij <;>
        exfalso <;> linarith [le_abs_self β,neg_le_abs β]
    | inr h' => congr 1; exact Subsingleton.elim _ _

open scoped ComplexInnerProductSpace
/-- Orthogonality uses only the real-frequency self-adjoint graph. -/
theorem staticEigenvector_orthogonal (b : KN.Background) (hQ : b.Q ≠ 0)
    (k : ℤ) (i j : StaticLabel k) (hij : i ≠ j) :
    ⟪staticEigenvector k b.beta i,staticEigenvector k b.beta j⟫ = 0 := by
  have hs := staticGraph_symmetric b hQ 1 (Or.inl rfl) k _ _ _ _
    (staticEigenvector_graph k b.beta i) (staticEigenvector_graph k b.beta j)
  simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal] at hs
  have hne : (staticEigenvalue k b.beta i : ℂ) ≠ (staticEigenvalue k b.beta j : ℂ) := by
    intro h
    apply hij
    apply staticEigenvalue_injective k b.beta
    exact_mod_cast h
  have hprod : ((staticEigenvalue k b.beta i : ℂ)-(staticEigenvalue k b.beta j : ℂ))*
      ⟪staticEigenvector k b.beta i,staticEigenvector k b.beta j⟫=0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

end
end KN.Angular.Jacobi

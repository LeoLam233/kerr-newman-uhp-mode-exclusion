import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace KN.Angular
noncomputable section

/-- Matrix induced on an upper/lower Jacobi pair when the first-order
lowering coefficient is c and the squared eigenvalue is μ. -/
def pairedBlock (β μ c : ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (-β*z.1-Complex.I*(μ/c)*z.2, Complex.I*c*z.1+β*z.2)

def pairedVector (β c ν : ℂ) : ℂ × ℂ := (ν-β,Complex.I*c)

theorem pairedBlock_eigen (β μ c ν : ℂ) (hc : c ≠ 0) (hν : ν^2=β^2+μ) :
    pairedBlock β μ c (pairedVector β c ν) = ν • pairedVector β c ν := by
  ext <;> simp only [pairedBlock,pairedVector,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  · field_simp
    ring_nf
    simp only [Complex.I_sq]
    linear_combination -hν
  · ring

/-- Both signed eigenvectors span the whole block. This does not assume
orthogonality or a basis at nonreal frequency. -/
theorem pairedVector_spanning (β c ν : ℂ) (hc : c ≠ 0) (hν : ν ≠ 0)
    (z : ℂ × ℂ) :
    ∃ a b : ℂ, a • pairedVector β c ν + b • pairedVector β c (-ν) = z := by
  refine ⟨(z.1+(ν+β)*(z.2/(Complex.I*c)))/(2*ν),
    ((ν-β)*(z.2/(Complex.I*c))-z.1)/(2*ν), ?_⟩
  ext <;> simp only [pairedVector,Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul]
    <;> field_simp <;> ring

/-- The upper unpaired line has sign -β, not +β. -/
theorem unpaired_upper_sign (β z : ℂ) : (-β*z,(0 : ℂ)) = (-β) • (z,0) := by
  simp

/-- The paired scalar gap ensures both square roots are genuinely nonzero. -/
theorem paired_root_positive (β μ : ℝ) (hμ : 4 ≤ μ) :
    0 < Real.sqrt (β^2+μ) := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg β]

end
end KN.Angular

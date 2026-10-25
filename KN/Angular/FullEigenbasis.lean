import KN.Angular.FullGraphSymmetry
import KN.Angular.PhysicalCoercivity

namespace KN.Angular
noncomputable section

def fullBasisEigenvalue (k : ℤ) (β : ℝ) (i : Bool × Jacobi.StaticLabel k) : ℝ :=
  if i.1 then -Jacobi.staticEigenvalue k β i.2 else Jacobi.staticEigenvalue k β i.2

theorem fullBasisVector_graph (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ)
    (i : Bool × Jacobi.StaticLabel k) :
    FullStaticGraph 1 b.beta k (fullBasisVector b hQ k i)
      ((fullBasisEigenvalue k b.beta i : ℂ) • fullBasisVector b hQ k i) := by
  obtain ⟨s,i⟩ := i
  have h := (fullStaticGraph_chiral_iff 1 b.beta k _ _).mpr (staticBasis_graph b hQ k i)
  rw [map_smul] at h
  cases s
  · exact h
  · have hI := fullStaticGraph_I 1 b.beta k h
    change FullStaticGraph 1 b.beta k (fullI (chiralLpMap _))
      (((-Jacobi.staticEigenvalue k b.beta i : ℝ) : ℂ) • (fullI (chiralLpMap _)))
    simpa only [Complex.ofReal_neg,map_smul,neg_smul] using hI

theorem fullStaticGraph_signedFourier (σ β : ℝ) (m : ℤ) (hσ : σ=1 ∨ σ= -1)
    (u v : FullAngularHilbert) :
    FullStaticGraph σ β m u v ↔ FullStaticGraph 1 β (signedFourier σ m) u v := by
  have hcoeff : staticCoefficient σ m = staticCoefficient 1 (signedFourier σ m) := by
    funext θ
    rcases hσ with rfl | rfl <;> norm_num [staticCoefficient,signedFourier]
  simp only [FullStaticGraph,hcoeff]

theorem fullStaticHilbertBasis_graph (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ)
    (i : Bool × Jacobi.StaticLabel (signedFourier σ m)) :
    ∃ hi : fullStaticHilbertBasis b hQ (signedFourier σ m) i ∈
      (fullStaticOperator b hQ σ hσ m).domain,
    fullStaticOperator b hQ σ hσ m ⟨_,hi⟩ =
      (fullBasisEigenvalue (signedFourier σ m) b.beta i : ℂ) •
        fullStaticHilbertBasis b hQ (signedFourier σ m) i := by
  apply (fullStaticOperator_graph b hQ σ hσ m _ _).mpr
  apply (fullStaticGraph_signedFourier σ b.beta m hσ _ _).mpr
  simpa only [fullStaticHilbertBasis,HilbertBasis.coe_mk] using fullBasisVector_graph b hQ _ i

end
end KN.Angular

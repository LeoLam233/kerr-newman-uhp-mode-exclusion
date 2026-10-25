import KN.Angular.StaticHilbertBasis
import KN.Angular.PhysicalForms
import KN.Angular.SpectralForm

namespace KN.Angular
noncomputable section
open scoped ComplexInnerProductSpace

def signedFourier (σ : ℝ) (m : ℤ) : ℤ := if σ=1 then m else -m

theorem staticGraph_signedFourier (σ β : ℝ) (m : ℤ) (hσ : σ=1 ∨ σ= -1)
    (u v : AngularHilbert) :
    StaticGraph σ β m u v ↔ StaticGraph 1 β (signedFourier σ m) u v := by
  have hcoeff : staticCoefficient σ m = staticCoefficient 1 (signedFourier σ m) := by
    funext θ
    rcases hσ with rfl | rfl <;> norm_num [staticCoefficient,signedFourier]
  simp only [StaticGraph,hcoeff]

theorem staticBasis_graph (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ)
    (i : Jacobi.StaticLabel k) :
    StaticGraph 1 b.beta k (Jacobi.staticHilbertBasis b hQ k i)
      ((Jacobi.staticEigenvalue k b.beta i : ℂ) • Jacobi.staticHilbertBasis b hQ k i) := by
  simpa only [Jacobi.staticHilbertBasis,HilbertBasis.coe_mk] using
    Jacobi.normalizedStaticVector_graph k b.beta i

theorem staticBasis_coefficient (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ)
    (u v : AngularHilbert) (hv : StaticGraph 1 b.beta k u v)
    (i : Jacobi.StaticLabel k) :
    ⟪Jacobi.staticHilbertBasis b hQ k i,v⟫ =
      (Jacobi.staticEigenvalue k b.beta i : ℂ)*⟪Jacobi.staticHilbertBasis b hQ k i,u⟫ := by
  have hs := staticGraph_symmetric b hQ 1 (Or.inl rfl) k _ _ _ _
    (staticBasis_graph b hQ k i) hv
  simpa only [inner_smul_left,Complex.conj_ofReal] using hs.symm

theorem physical_static_multiplier_nonneg (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ x : ℝ) (hσ : σ=1 ∨ σ= -1) (hx : x ≤ -b.h) (k : ℤ)
    (i : Jacobi.StaticLabel k) :
    0 ≤ (Jacobi.staticEigenvalue k b.beta i)^2-b.beta^2+
      (b.c/x)*(Jacobi.staticEigenvalue k b.beta i-σ*b.beta) := by
  cases i with
  | inl sn =>
    obtain ⟨s,n⟩ := sn
    apply le_of_lt (physical_paired_form_pos b hQ x _ σ hx
      (by rcases hσ with rfl | rfl <;> norm_num) ?_)
    cases s <;> simp only [Jacobi.staticEigenvalue,neg_sq] <;>
      rw [Jacobi.positiveRoot_sq] <;> linarith [Jacobi.paired_gap k n]
  | inr h =>
    simp only [Jacobi.staticEigenvalue]
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using (physical_unpaired_plus b hQ x hx).le
    · ring_nf
      exact le_refl 0

/-- C002 (16) on the actual maximal first-order domain, including its critical
endpoint sectors and correct unpaired branch. This is not a spectral hypothesis. -/
theorem physical_angular_form_nonneg (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (x : ℝ) (hx : x ≤ -b.h)
    (u v : AngularHilbert) (hv : StaticGraph σ b.beta m u v) :
    0 ≤ ‖v‖^2-b.beta^2*‖u‖^2+(b.c/x)*((⟪u,v⟫).re-σ*b.beta*‖u‖^2) := by
  have hv' := (staticGraph_signedFourier σ b.beta m hσ u v).mp hv
  exact spectral_form_nonneg (Jacobi.staticHilbertBasis b hQ (signedFourier σ m))
    (Jacobi.staticEigenvalue (signedFourier σ m) b.beta) u v
    (staticBasis_coefficient b hQ _ u v hv') b.beta (b.c/x) σ
    (physical_static_multiplier_nonneg b hQ σ x hσ hx _)

/-- The static first-order graph has the sharp mass gap, including the ground branch. -/
theorem physical_static_norm_gap (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ)
    (u v : AngularHilbert) (hv : StaticGraph σ b.beta m u v) :
    b.beta^2*‖u‖^2 ≤ ‖v‖^2 := by
  have hv' := (staticGraph_signedFourier σ b.beta m hσ u v).mp hv
  have h := spectral_form_nonneg (Jacobi.staticHilbertBasis b hQ (signedFourier σ m))
    (Jacobi.staticEigenvalue (signedFourier σ m) b.beta) u v
    (staticBasis_coefficient b hQ _ u v hv') b.beta 0 σ (by
      intro i
      cases i with
      | inl sn =>
        obtain ⟨s,n⟩ := sn
        cases s <;> simp only [Jacobi.staticEigenvalue,neg_sq,zero_mul,add_zero] <;>
          rw [Jacobi.positiveRoot_sq] <;> linarith [Jacobi.paired_gap (signedFourier σ m) n]
      | inr h => simp [Jacobi.staticEigenvalue])
  simpa only [zero_mul,add_zero,sub_nonneg] using h

end
end KN.Angular

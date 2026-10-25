import KN.Energy.AngularAverage
import KN.Energy.PhysicalFiniteEndpoint
import KN.Angular.PhysicalCoercivity

noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
namespace KN.Energy
open KN.Angular

def angularDensity (u : AngularHilbert) (θ : ℝ) : ℝ := ‖u θ‖^2

theorem angularDensity_integrable (u : AngularHilbert) :
    Integrable (angularDensity u) angularMeasure :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)

theorem angularDensity_integral (u : AngularHilbert) :
    ∫ θ, angularDensity u θ ∂angularMeasure = ‖u‖^2 := by
  have hh := L2.inner_def (𝕜 := ℂ) u u
  simp only [inner_self_eq_norm_sq_to_K] at hh
  exact_mod_cast hh.symm

theorem physical_sineAverage_bounds (u : AngularHilbert) (hu : ‖u‖=1) :
    0 ≤ sineAverage (angularDensity u) ∧ sineAverage (angularDensity u) ≤ 1 := by
  apply sineAverage_bounds (angularDensity u) (angularDensity_integrable u)
    (Filter.Eventually.of_forall (fun θ => sq_nonneg ‖u θ‖))
  change ∫ θ, angularDensity u θ ∂angularMeasure = 1
  rw [angularDensity_integral,hu,one_pow]

theorem physical_normalized_angularK_nonneg (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (u v : AngularHilbert)
    (hu : ‖u‖=1) (hv : StaticGraph σ b.beta m u v)
    {x : ℝ} (hx : x ≤ -b.h) :
    0 ≤ angularK b (‖v‖^2-b.beta^2) (⟪u,v⟫).re σ x := by
  simpa only [angularK,hu,one_pow,mul_one] using
    physical_angular_form_nonneg b hQ σ hσ m x hx u v hv

theorem angularSineDensity_integrable (u : AngularHilbert) :
    Integrable (fun θ => Real.sin θ^2*angularDensity u θ) angularMeasure := by
  have hi := angularDensity_integrable u
  apply hi.mono' ((Real.continuous_sin.pow 2).aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards [] with θ
  have hs : Real.sin θ^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg (Real.cos θ)]
  have hp : 0 ≤ angularDensity u θ := sq_nonneg _
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
  exact mul_le_of_le_one_left hp hs

/-- Integration of an actual pointwise multiplier-square identity. -/
theorem multiplier_norm_square_integral (u y : AngularHilbert) (a c : ℝ)
    (hy : ∀ᵐ θ ∂angularMeasure,
      ‖y θ‖^2 = a^2*(c^2+Real.sin θ^2)*‖u θ‖^2) :
    ‖y‖^2 = a^2*(c^2*‖u‖^2+sineAverage (angularDensity u)) := by
  rw [← angularDensity_integral y]
  have he : (fun θ => angularDensity y θ) =ᵐ[angularMeasure]
      (fun θ => a^2*(c^2*angularDensity u θ+Real.sin θ^2*angularDensity u θ)) := by
    filter_upwards [hy] with θ hθ
    dsimp [angularDensity]
    rw [hθ]
    ring
  rw [integral_congr_ae he,integral_const_mul,
    integral_add ((angularDensity_integrable u).const_mul (c^2)) (angularSineDensity_integrable u),
    integral_const_mul,angularDensity_integral]
  rfl

theorem multiplier_normalized_norm_square (u y : AngularHilbert) (a c : ℝ)
    (hu : ‖u‖=1)
    (hy : ∀ᵐ θ ∂angularMeasure,
      ‖y θ‖^2 = a^2*(c^2+Real.sin θ^2)*‖u θ‖^2) :
    ‖y‖^2 = a^2*(c^2+sineAverage (angularDensity u)) := by
  simpa only [hu,one_pow,mul_one] using multiplier_norm_square_integral u y a c hy

end KN.Energy

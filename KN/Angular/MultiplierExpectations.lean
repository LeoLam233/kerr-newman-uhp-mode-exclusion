import KN.Angular.MultiplierNorm
import KN.Angular.StaticGraphProperties
import KN.Angular.Expectations
import KN.ChargedRadial.PhysicalAngularData

namespace KN.Angular
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace

theorem reducedFrequencyMultiplier_symmetric (b : KN.Background) (σ : ℝ)
    (u v : AngularHilbert) :
    ⟪reducedFrequencyMultiplier b σ u,v⟫=⟪u,reducedFrequencyMultiplier b σ v⟫ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reducedFrequencyMultiplier_ae b σ u,reducedFrequencyMultiplier_ae b σ v]
    with θ hu hv
  rw [hu,hv]
  have h := massPotential_inner (-σ*b.a*b.kappa*Real.sin θ) (σ*b.a*b.c*Real.cos θ) (u θ) (v θ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_neg] using h

theorem reducedFrequencyMultiplier_expectation_real (b : KN.Background) (σ : ℝ)
    (u : AngularHilbert) :
    starRingEnd ℂ ⟪u,reducedFrequencyMultiplier b σ u⟫=⟪u,reducedFrequencyMultiplier b σ u⟫ := by
  rw [inner_conj_symm]
  exact reducedFrequencyMultiplier_symmetric b σ u u

theorem reducedFrequencyMultiplier_norm_square (b : KN.Background)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (u : AngularHilbert) (hu : ‖u‖=1) :
    ‖reducedFrequencyMultiplier b σ u‖^2 =
      b.a^2*(b.c^2+KN.Energy.sineAverage (KN.Energy.angularDensity u)) := by
  apply KN.Energy.multiplier_normalized_norm_square u _ b.a b.c hu
  filter_upwards [reducedFrequencyMultiplier_ae b σ u] with θ hθ
  rw [hθ]
  exact frequency_fiber_norm_sq b σ hσ θ (u θ)

private theorem real_cast_of_conj_eq {z : ℂ} (h : starRingEnd ℂ z=z) :
    (z.re : ℂ)=z := by
  have hi := congrArg Complex.im h
  have hz : z.im=0 := by simpa only [Complex.conj_im] using (show -z.im=z.im from hi) |> (fun h => by linarith)
  exact Complex.ext (by simp) (by simp [hz])

/-- All angular energy data derived from one actual first-domain eigenvector.
No squared-operator membership or self-adjointness at complex frequency occurs. -/
def physicalAngularData_of_eigenvector (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω lam : ℂ)
    (u v : AngularHilbert) (hu : ‖u‖=1) (hv : StaticGraph σ b.beta m u v)
    (heig : v+ω • reducedFrequencyMultiplier b σ u=lam • u) :
    KN.ChargedRadial.PhysicalAngularData b m σ ω lam where
  u := u
  staticImage := v
  normalized := hu
  graph := hv
  av := (⟪u,reducedFrequencyMultiplier b σ u⟫).re
  cross := (⟪v,reducedFrequencyMultiplier b σ u⟫+⟪reducedFrequencyMultiplier b σ u,v⟫).re
  sineAvg := KN.Energy.sineAverage (KN.Energy.angularDensity u)
  sine_le_one := (KN.Energy.physical_sineAverage_bounds u hu).2
  first_expectation := by
    have hx := static_expectation_real b hQ σ hσ m u v hv
    have hy := reducedFrequencyMultiplier_expectation_real b σ u
    rw [real_cast_of_conj_eq hx,real_cast_of_conj_eq hy]
    exact eigenvalue_expectation u v _ ω lam (by simp [inner_self_eq_norm_sq_to_K,hu]) heig
  squared_expectation := by
    have hx := static_expectation_real b hQ σ hσ m u v hv
    have hy := reducedFrequencyMultiplier_expectation_real b σ u
    have hc : starRingEnd ℂ (⟪v,reducedFrequencyMultiplier b σ u⟫+⟪reducedFrequencyMultiplier b σ u,v⟫)=
        ⟪v,reducedFrequencyMultiplier b σ u⟫+⟪reducedFrequencyMultiplier b σ u,v⟫ := by
      rw [map_add,inner_conj_symm,inner_conj_symm,add_comm]
    have h := squared_eigenvalue_expectation u v _ ω lam
      (by simp [inner_self_eq_norm_sq_to_K,hu]) heig hx hy
    rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow,← RCLike.ofReal_pow,
      reducedFrequencyMultiplier_norm_square b σ hσ u hu] at h
    rw [real_cast_of_conj_eq hc]
    change lam^2 = ((‖v‖^2 : ℝ) : ℂ) + ω*(⟪v,reducedFrequencyMultiplier b σ u⟫+
      ⟪reducedFrequencyMultiplier b σ u,v⟫) +
      ω^2*((b.a^2*(b.c^2+KN.Energy.sineAverage (KN.Energy.angularDensity u)) : ℝ) : ℂ) at h
    rw [h]
    push_cast
    ring

end
end KN.Angular

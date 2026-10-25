import KN.Angular.ExternalHintz
import KN.Physics.MatrixAlgebra
import KN.Analysis.ResolventPerturbation
import KN.Analysis.LpMultiplier

namespace KN.Angular
noncomputable section

/-- The actual zero-frequency maximal full four-component operator, fixed
by its explicitly identified weak graph in the published real-frequency lemma. -/
def fullStaticOperator (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) :
    FullAngularHilbert →ₗ.[ℂ] FullAngularHilbert :=
  Classical.choose (External.hintz_2026_v1_lemma1_zero_frequency b hQ σ hσ m)

theorem fullStaticOperator_graph (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (u v : FullAngularHilbert) :
    (∃ hu : u ∈ (fullStaticOperator b hQ σ hσ m).domain,
      fullStaticOperator b hQ σ hσ m ⟨u,hu⟩=v) ↔ FullStaticGraph σ b.beta m u v :=
  (Classical.choose_spec (External.hintz_2026_v1_lemma1_zero_frequency b hQ σ hσ m)).1 u v

theorem fullStaticOperator_selfAdjoint (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) :
    IsSelfAdjoint (fullStaticOperator b hQ σ hσ m) :=
  (Classical.choose_spec (External.hintz_2026_v1_lemma1_zero_frequency b hQ σ hσ m)).2.1

/-- Constant full-field matrices lifted to actual bounded L² operators. -/
def fullI : FullAngularHilbert →L[ℂ] FullAngularHilbert :=
  KN.Physics.I4.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure

def fullJ : FullAngularHilbert →L[ℂ] FullAngularHilbert :=
  KN.Physics.J4.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure

def fullPiPlus : FullAngularHilbert →L[ℂ] FullAngularHilbert := (1/2 : ℂ) • (1+fullI)
def fullPiMinus : FullAngularHilbert →L[ℂ] FullAngularHilbert := (1/2 : ℂ) • (1-fullI)

def fullSinMultiplier : FullAngularHilbert →L[ℂ] FullAngularHilbert :=
  KN.Analysis.boundedScalarMultiplier angularMeasure (fun θ => (Real.sin θ : ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_sin) 1 (fun θ => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ)

def fullCosMultiplier : FullAngularHilbert →L[ℂ] FullAngularHilbert :=
  KN.Analysis.boundedScalarMultiplier angularMeasure (fun θ => (Real.cos θ : ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_cos) 1 (fun θ => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ)

/-- The exact bounded frequency coefficient in the full four-component
angular differential expression (5). No frequency-dependent domain is imposed. -/
def fullFrequencyMultiplier (b : KN.Background) (σ : ℝ) :
    FullAngularHilbert →L[ℂ] FullAngularHilbert :=
  ((fullStaticPotential (-σ*b.a*b.kappa : ℂ) 0).toEuclideanLin.toContinuousLinearMap.compLpL
    2 angularMeasure).comp fullSinMultiplier +
  ((fullStaticPotential 0 (σ*b.a*b.c : ℂ)).toEuclideanLin.toContinuousLinearMap.compLpL
    2 angularMeasure).comp fullCosMultiplier

def fullFrequencyOperator (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ) :
    FullAngularHilbert →ₗ.[ℂ] FullAngularHilbert :=
  KN.Analysis.boundedPerturbation (fullStaticOperator b hQ σ hσ m)
    (ω • fullFrequencyMultiplier b σ)

def FullFrequencyGraph (b : KN.Background) (σ : ℝ) (m : ℤ) (ω : ℂ)
    (u v : FullAngularHilbert) : Prop :=
  FullStaticGraph σ b.beta m u (v-ω • fullFrequencyMultiplier b σ u)

theorem fullFrequencyOperator_graph (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ) (u v : FullAngularHilbert) :
    (∃ hu : u ∈ (fullFrequencyOperator b hQ σ hσ m ω).domain,
      fullFrequencyOperator b hQ σ hσ m ω ⟨u,hu⟩=v) ↔
      FullFrequencyGraph b σ m ω u v := by
  rw [FullFrequencyGraph,← fullStaticOperator_graph b hQ σ hσ m]
  constructor
  · rintro ⟨hu,h⟩
    refine ⟨hu, ?_⟩
    change fullStaticOperator b hQ σ hσ m ⟨u,hu⟩ + ω • fullFrequencyMultiplier b σ u=v at h
    exact eq_sub_iff_add_eq.mpr h
  · rintro ⟨hu,h⟩
    refine ⟨hu, ?_⟩
    change fullStaticOperator b hQ σ hσ m ⟨u,hu⟩ + ω • fullFrequencyMultiplier b σ u=v
    exact eq_sub_iff_add_eq.mp h

end
end KN.Angular

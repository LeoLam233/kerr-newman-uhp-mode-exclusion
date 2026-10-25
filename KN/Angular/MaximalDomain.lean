import KN.Angular.ChiralEmbedding
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Support

namespace KN.Angular
noncomputable section
open MeasureTheory

/-- Lebesgue measure on the open angular interval; endpoints are handled by
maximal distributional regularity, not by imposing pointwise Dirichlet values. -/
def angularMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 Real.pi)
abbrev AngularFiber := EuclideanSpace ℂ (Fin 2)
abbrev AngularHilbert := Lp AngularFiber 2 angularMeasure

/-- Scalar test functions supported strictly inside the angular interval. -/
def IsAngularTest (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Set.Ioo 0 Real.pi

def staticCoefficient (σ : ℝ) (m : ℤ) (θ : ℝ) : ℝ :=
  (3/2 : ℝ)*Real.cos θ/Real.sin θ + σ*(m : ℝ)/Real.sin θ

/-- Distributional graph of a matrix first-order differential expression.
Testing is vector-valued, so it is independent of a chosen component basis. -/
def MatrixWeakGraph {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ)
    (W : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (u v : ℝ → EuclideanSpace ℂ (Fin N)) : Prop :=
  ∀ φ : ℝ → ℂ, IsAngularTest φ →
    (∫ θ, φ θ • v θ ∂angularMeasure) =
    (∫ θ, -(deriv φ θ) • D.toEuclideanLin (u θ) +
      φ θ • (W θ).toEuclideanLin (u θ) ∂angularMeasure)

/-- The graph of (10), interpreted weakly. There is no square-operator domain
or logarithmic second-order extension in this definition. -/
def StaticGraph (σ β : ℝ) (m : ℤ) (u v : AngularHilbert) : Prop :=
  MatrixWeakGraph massPrincipal
    (fun θ => massPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)) u v

/-- Precisely the maximal distributional L² domain of the first-order operator. -/
def MaximalDomain (σ β : ℝ) (m : ℤ) : Set AngularHilbert :=
  {u | ∃ v, StaticGraph σ β m u v}

/-- Frequency perturbations share this first-order domain. -/
def FrequencyGraph (σ β : ℝ) (m : ℤ) (V : AngularHilbert → AngularHilbert)
    (ω : ℂ) (u v : AngularHilbert) : Prop :=
  StaticGraph σ β m u (v - ω • V u)

theorem frequency_domain_fixed (σ β : ℝ) (m : ℤ)
    (V : AngularHilbert → AngularHilbert) (ω : ℂ) (u : AngularHilbert) :
    (∃ v, FrequencyGraph σ β m V ω u v) ↔ u ∈ MaximalDomain σ β m := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v-ω • V u,hv⟩
  · rintro ⟨v,hv⟩
    refine ⟨v+ω • V u, ?_⟩
    simpa [FrequencyGraph] using hv

end
end KN.Angular

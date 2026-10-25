import KN.Background.Parameters
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
open Set MeasureTheory
namespace KN.Boundary

/-- The manuscript's fixed, nonvanishing radial gauge; integration stays in the exterior
when the evaluation radius is exterior. -/
def gauge (b : Background) (m : ℤ) (ω : ℂ) (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * ∫ x in (2*b.rPlus)..r,
    b.frequencyK m ω x / (b.Delta x : ℂ))

theorem gauge_ne_zero (b : Background) (m : ℤ) (ω : ℂ) (r : ℝ) :
    gauge b m ω r ≠ 0 := Complex.exp_ne_zero _

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Actual weighted smooth future-horizon class, not a condition on leading coefficients.
The exponent is -b for an original boost-weight b field. -/
def HorizonRegular (b : Background) (m : ℤ) (ω : ℂ) (exponent : ℝ)
    (f : ℝ → E) : Prop :=
  ∃ v : ℝ → E, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ici b.rPlus) ∧
    ∀ r, b.rPlus < r →
      f r = (gauge b m ω r * (Real.rpow (b.Delta r) exponent : ℂ)) • v r

/-- Euler radial derivative, whose iterates define conormal control. -/
def eulerDeriv (f : ℝ → E) : ℝ → E := fun r => r • deriv f r

/-- Every fixed radial Euler derivative has a polynomial norm bound. Angular
Sobolev/section derivatives are imposed by instantiating this class on their actual fields. -/
def PolynomialConormal (f : ℝ → E) : Prop :=
  ∀ j : ℕ, ∃ (N : ℕ) (C R : ℝ), 0 ≤ C ∧ 0 ≤ R ∧
    ∀ r, R ≤ r → ‖(eulerDeriv^[j]) f r‖ ≤ C * (1 + |r|)^N

def Outgoing (b : Background) (m : ℤ) (ω : ℂ) (f : ℝ → E) : Prop :=
  PolynomialConormal (fun r => gauge b m ω r • f r)

/-- A fixed bounded angular projection preserves the exact weighted smooth horizon class. -/
theorem HorizonRegular.map {b : Background} {m : ℤ} {ω : ℂ} {q : ℝ}
    {f : ℝ → E} (hf : HorizonRegular b m ω q f) (L : E →L[ℂ] F) :
    HorizonRegular b m ω q (fun r => L (f r)) := by
  obtain ⟨v, hv, heq⟩ := hf
  refine ⟨fun r => L (v r), ?_, ?_⟩
  · exact (L.restrictScalars ℝ).contDiff.comp_contDiffOn hv
  · intro r hr
    dsimp only
    rw [heq r hr, map_smul]

end KN.Boundary

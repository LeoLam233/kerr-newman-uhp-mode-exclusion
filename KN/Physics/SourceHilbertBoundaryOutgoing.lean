import KN.Physics.SourceHilbertBoundaryConormal
import KN.Physics.SourceHilbertBoundaryRhoConormal
import KN.Physics.SourceHilbertBoundaryTransform
import KN.Boundary.DeltaPowerConormal

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BoundedContinuousFunction
namespace KN.Physics
open KN.Angular KN.Boundary

lemma coefficient_action_conormal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {rp : ℝ} (μ : Measure ℝ) (f : ℝ → AngularCoefficient) (u : ℝ → Lp E 2 μ)
    (hf : PolynomialConormal f) (hu : PolynomialConormal u)
    (hfs : RadialSmooth rp f) (hus : RadialSmooth rp u) :
    PolynomialConormal (fun r => coefficientMultiplier μ (f r) (u r)) :=
  PolynomialConormal.bilinear_on ((coefficientMultiplierCLM (E:=E) μ).bilinearRestrictScalars ℝ)
    hf hu hfs hus

lemma matrixCoefficient_action_conormal {rp : ℝ}
    (a00 a01 a10 a11 : ℝ → AngularCoefficient) (u : ℝ → AngularHilbert)
    (h00 : PolynomialConormal a00) (h01 : PolynomialConormal a01)
    (h10 : PolynomialConormal a10) (h11 : PolynomialConormal a11)
    (hs00 : RadialSmooth rp a00) (hs01 : RadialSmooth rp a01)
    (hs10 : RadialSmooth rp a10) (hs11 : RadialSmooth rp a11)
    (hu : PolynomialConormal u) (hus : RadialSmooth rp u) :
    PolynomialConormal (fun r => matrixCoefficientL (a00 r) (a01 r) (a10 r) (a11 r) (u r)) := by
  have h0 := hu.map_on hus (projectCoordinate 0)
  have h1 := hu.map_on hus (projectCoordinate 1)
  have hs0 := ((projectCoordinate 0).restrictScalars ℝ).contDiff.comp_contDiffOn hus
  have hs1 := ((projectCoordinate 1).restrictScalars ℝ).contDiff.comp_contDiffOn hus
  have hA := (coefficient_action_conormal angularMeasure a00 _ h00 h0 hs00 hs0).add_on
    (coefficient_action_conormal angularMeasure a01 _ h01 h1 hs01 hs1)
    (coefficient_action_smooth angularMeasure a00 _ hs00 hs0)
    (coefficient_action_smooth angularMeasure a01 _ hs01 hs1)
  have hB := (coefficient_action_conormal angularMeasure a10 _ h10 h0 hs10 hs0).add_on
    (coefficient_action_conormal angularMeasure a11 _ h11 h1 hs11 hs1)
    (coefficient_action_smooth angularMeasure a10 _ hs10 hs0)
    (coefficient_action_smooth angularMeasure a11 _ hs11 hs1)
  have hsA := (coefficient_action_smooth angularMeasure a00 _ hs00 hs0).add
    (coefficient_action_smooth angularMeasure a01 _ hs01 hs1)
  have hsB := (coefficient_action_smooth angularMeasure a10 _ hs10 hs0).add
    (coefficient_action_smooth angularMeasure a11 _ hs11 hs1)
  exact (hA.map_on hsA (injectCoordinate 0)).add_on (hB.map_on hsB (injectCoordinate 1))
    (((injectCoordinate 0).restrictScalars ℝ).contDiff.comp_contDiffOn hsA)
    (((injectCoordinate 1).restrictScalars ℝ).contDiff.comp_contDiffOn hsB)

end KN.Physics

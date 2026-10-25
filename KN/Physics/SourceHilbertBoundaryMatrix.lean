import KN.Physics.SourceHilbertBoundaryRho
import KN.Angular.L2Coordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BoundedContinuousFunction ContDiff
namespace KN.Physics
open KN.Angular

/-- Actual two-component angular matrix multiplication assembled from scalar
coefficient multiplication and fixed coordinate maps. -/
def matrixCoefficientL (a00 a01 a10 a11 : ℝ →ᵇ ℂ) : AngularHilbert →L[ℂ] AngularHilbert :=
  (injectCoordinate 0).comp
    ((coefficientMultiplier angularMeasure a00).comp (projectCoordinate 0)+
      (coefficientMultiplier angularMeasure a01).comp (projectCoordinate 1))+
  (injectCoordinate 1).comp
    ((coefficientMultiplier angularMeasure a10).comp (projectCoordinate 0)+
      (coefficientMultiplier angularMeasure a11).comp (projectCoordinate 1))

lemma matrixCoefficientL_ae (a00 a01 a10 a11 : ℝ →ᵇ ℂ) (u : AngularHilbert) :
    matrixCoefficientL a00 a01 a10 a11 u =ᵐ[angularMeasure]
      fun t => WithLp.toLp 2 ![a00 t*(u t 0)+a01 t*(u t 1),a10 t*(u t 0)+a11 t*(u t 1)] := by
  let v0 := coefficientMultiplier angularMeasure a00 (projectCoordinate 0 u)+
    coefficientMultiplier angularMeasure a01 (projectCoordinate 1 u)
  let v1 := coefficientMultiplier angularMeasure a10 (projectCoordinate 0 u)+
    coefficientMultiplier angularMeasure a11 (projectCoordinate 1 u)
  filter_upwards [Lp.coeFn_add (injectCoordinate 0 v0) (injectCoordinate 1 v1),
    injectCoordinate_ae 0 v0,injectCoordinate_ae 1 v1,
    Lp.coeFn_add (coefficientMultiplier angularMeasure a00 (projectCoordinate 0 u))
      (coefficientMultiplier angularMeasure a01 (projectCoordinate 1 u)),
    Lp.coeFn_add (coefficientMultiplier angularMeasure a10 (projectCoordinate 0 u))
      (coefficientMultiplier angularMeasure a11 (projectCoordinate 1 u)),
    coefficientMultiplier_ae angularMeasure a00 (projectCoordinate 0 u),
    coefficientMultiplier_ae angularMeasure a01 (projectCoordinate 1 u),
    coefficientMultiplier_ae angularMeasure a10 (projectCoordinate 0 u),
    coefficientMultiplier_ae angularMeasure a11 (projectCoordinate 1 u),
    projectCoordinate_ae 0 u,projectCoordinate_ae 1 u] with t h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  change (injectCoordinate 0 v0+injectCoordinate 1 v1) t=_
  rw [h0]
  simp only [Pi.add_apply]
  rw [h1,h2]
  change coordinateInjection 0 ((coefficientMultiplier angularMeasure a00 (projectCoordinate 0 u)+
    coefficientMultiplier angularMeasure a01 (projectCoordinate 1 u)) t)+
    coordinateInjection 1 ((coefficientMultiplier angularMeasure a10 (projectCoordinate 0 u)+
    coefficientMultiplier angularMeasure a11 (projectCoordinate 1 u)) t)=_
  rw [h3,h4]
  simp only [Pi.add_apply]
  rw [h5,h6,h7,h8]
  erw [h9,h10]
  ext j
  fin_cases j <;> simp [coordinateInjection]

theorem matrixCoefficient_action_smooth {s : Set ℝ}
    (a00 a01 a10 a11 : ℝ → (ℝ →ᵇ ℂ)) (u : ℝ → AngularHilbert)
    (h00 : ContDiffOn ℝ ∞ a00 s) (h01 : ContDiffOn ℝ ∞ a01 s)
    (h10 : ContDiffOn ℝ ∞ a10 s) (h11 : ContDiffOn ℝ ∞ a11 s)
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (fun r => matrixCoefficientL (a00 r) (a01 r) (a10 r) (a11 r) (u r)) s := by
  have h0 := ((projectCoordinate 0).restrictScalars ℝ).contDiff.comp_contDiffOn hu
  have h1 := ((projectCoordinate 1).restrictScalars ℝ).contDiff.comp_contDiffOn hu
  exact (((injectCoordinate 0).restrictScalars ℝ).contDiff.comp_contDiffOn
    ((coefficient_action_smooth angularMeasure a00 _ h00 h0).add
      (coefficient_action_smooth angularMeasure a01 _ h01 h1))).add
    (((injectCoordinate 1).restrictScalars ℝ).contDiff.comp_contDiffOn
    ((coefficient_action_smooth angularMeasure a10 _ h10 h0).add
      (coefficient_action_smooth angularMeasure a11 _ h11 h1)))

end KN.Physics

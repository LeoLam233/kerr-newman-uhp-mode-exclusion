import KN.Angular.WeakGraphTransform
import KN.Angular.ExternalJacobi

namespace KN.Angular
noncomputable section
open MeasureTheory

def coordinateInjection (j : Fin 2) : ℂ →L[ℂ] AngularFiber :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (PiLp.single 2 j (1 : ℂ))

def coordinateProjection (j : Fin 2) : AngularFiber →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 2 => ℂ) j

def injectCoordinate (j : Fin 2) : Jacobi.H →L[ℂ] AngularHilbert :=
  (coordinateInjection j).compLpL 2 angularMeasure

def projectCoordinate (j : Fin 2) : AngularHilbert →L[ℂ] Jacobi.H :=
  (coordinateProjection j).compLpL 2 angularMeasure

theorem injectCoordinate_ae (j : Fin 2) (f : Jacobi.H) :
    injectCoordinate j f =ᵐ[angularMeasure] fun θ => coordinateInjection j (f θ) :=
  (coordinateInjection j).coeFn_compLpL f

theorem projectCoordinate_ae (j : Fin 2) (f : AngularHilbert) :
    projectCoordinate j f =ᵐ[angularMeasure] fun θ => f θ j :=
  (coordinateProjection j).coeFn_compLpL f

theorem reconstruct_coordinates (f : AngularHilbert) :
    injectCoordinate 0 (projectCoordinate 0 f)+injectCoordinate 1 (projectCoordinate 1 f)=f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (injectCoordinate 0 (projectCoordinate 0 f))
    (injectCoordinate 1 (projectCoordinate 1 f)),
    injectCoordinate_ae 0 (projectCoordinate 0 f),injectCoordinate_ae 1 (projectCoordinate 1 f),
    projectCoordinate_ae 0 f,projectCoordinate_ae 1 f] with θ h0 h1 h2 h3 h4
  rw [h0]
  change injectCoordinate 0 (projectCoordinate 0 f) θ + injectCoordinate 1 (projectCoordinate 1 f) θ = _
  rw [h1,h2,h3,h4]
  ext j
  fin_cases j <;> simp [coordinateInjection]

end
end KN.Angular

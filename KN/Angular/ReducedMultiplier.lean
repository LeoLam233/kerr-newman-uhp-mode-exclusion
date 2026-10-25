import KN.Angular.MaximalDomain
import KN.Background.Parameters
import KN.Analysis.LpMultiplier

namespace KN.Angular
noncomputable section
open MeasureTheory

def reducedSinMultiplier : AngularHilbert →L[ℂ] AngularHilbert :=
  KN.Analysis.boundedScalarMultiplier angularMeasure (fun θ => (Real.sin θ : ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_sin) 1 (fun θ => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ)

def reducedCosMultiplier : AngularHilbert →L[ℂ] AngularHilbert :=
  KN.Analysis.boundedScalarMultiplier angularMeasure (fun θ => (Real.cos θ : ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_cos) 1 (fun θ => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ)

def reducedFrequencyMultiplier (b : KN.Background) (σ : ℝ) :
    AngularHilbert →L[ℂ] AngularHilbert :=
  ((massPotential (-σ*b.a*b.kappa : ℂ) 0).toEuclideanLin.toContinuousLinearMap.compLpL
    2 angularMeasure).comp reducedSinMultiplier +
  ((massPotential 0 (σ*b.a*b.c : ℂ)).toEuclideanLin.toContinuousLinearMap.compLpL
    2 angularMeasure).comp reducedCosMultiplier

theorem massPotential_sin_cos (g β s t : ℂ) (u : AngularFiber) :
    (massPotential g 0).toEuclideanLin (s • u) +
      (massPotential 0 β).toEuclideanLin (t • u) =
      (massPotential (g*s) (β*t)).toEuclideanLin u := by
  rw [map_smul,map_smul,← LinearMap.smul_apply,← LinearMap.smul_apply,
    ← LinearMap.add_apply]
  congr 1
  change s • (Matrix.toLpLin 2 2) (massPotential g 0) +
    t • (Matrix.toLpLin 2 2) (massPotential 0 β) = _
  rw [← map_smul,← map_smul,← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [massPotential] <;> ring

theorem reducedFrequencyMultiplier_ae (b : KN.Background) (σ : ℝ) (u : AngularHilbert) :
    reducedFrequencyMultiplier b σ u =ᵐ[angularMeasure] fun θ =>
      (massPotential (-σ*b.a*b.kappa*Real.sin θ : ℂ)
        (σ*b.a*b.c*Real.cos θ : ℂ)).toEuclideanLin (u θ) := by
  let A := (massPotential (-σ*b.a*b.kappa : ℂ) 0).toEuclideanLin.toContinuousLinearMap
  let B := (massPotential 0 (σ*b.a*b.c : ℂ)).toEuclideanLin.toContinuousLinearMap
  have hs := KN.Analysis.boundedScalarMultiplier_ae angularMeasure
    (fun θ => (Real.sin θ : ℂ)) (Complex.continuous_ofReal.comp Real.continuous_sin)
    1 (fun θ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ) u
  have hc := KN.Analysis.boundedScalarMultiplier_ae angularMeasure
    (fun θ => (Real.cos θ : ℂ)) (Complex.continuous_ofReal.comp Real.continuous_cos)
    1 (fun θ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ) u
  filter_upwards [Lp.coeFn_add (A.compLpL 2 angularMeasure (reducedSinMultiplier u))
    (B.compLpL 2 angularMeasure (reducedCosMultiplier u)),
    A.coeFn_compLpL (reducedSinMultiplier u),B.coeFn_compLpL (reducedCosMultiplier u),hs,hc]
    with θ hadd ha hb hs hc
  simp only [Pi.add_apply] at hadd
  change (A.compLpL 2 angularMeasure (reducedSinMultiplier u) +
    B.compLpL 2 angularMeasure (reducedCosMultiplier u)) θ = _
  change reducedSinMultiplier u θ = _ at hs
  change reducedCosMultiplier u θ = _ at hc
  rw [hadd,ha,hb,hs,hc]
  exact massPotential_sin_cos _ _ _ _ _

end
end KN.Angular

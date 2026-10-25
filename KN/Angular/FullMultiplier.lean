import KN.Angular.FullGraphJ
import KN.Background.Parameters
import KN.Analysis.LpMultiplier

namespace KN.Angular
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory

theorem fullStaticPotential_sin_cos (g β s t : ℂ) (u : EuclideanSpace ℂ (Fin 4)) :
    (fullStaticPotential g 0).toEuclideanLin (s • u) +
      (fullStaticPotential 0 β).toEuclideanLin (t • u) =
      (fullStaticPotential (g*s) (β*t)).toEuclideanLin u := by
  rw [map_smul,map_smul,← LinearMap.smul_apply,← LinearMap.smul_apply,
    ← LinearMap.add_apply]
  congr 1
  change s • (Matrix.toLpLin 2 2) (fullStaticPotential g 0) +
    t • (Matrix.toLpLin 2 2) (fullStaticPotential 0 β) = _
  rw [← map_smul,← map_smul,← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fullStaticPotential] <;> ring

theorem fullFrequencyMultiplier_ae (b : KN.Background) (σ : ℝ) (u : FullAngularHilbert) :
    fullFrequencyMultiplier b σ u =ᵐ[angularMeasure] fun θ =>
      (fullStaticPotential (-σ*b.a*b.kappa*Real.sin θ : ℂ)
        (σ*b.a*b.c*Real.cos θ : ℂ)).toEuclideanLin (u θ) := by
  let A := (fullStaticPotential (-σ*b.a*b.kappa : ℂ) 0).toEuclideanLin.toContinuousLinearMap
  let B := (fullStaticPotential 0 (σ*b.a*b.c : ℂ)).toEuclideanLin.toContinuousLinearMap
  have hs := KN.Analysis.boundedScalarMultiplier_ae angularMeasure
    (fun θ => (Real.sin θ : ℂ)) (Complex.continuous_ofReal.comp Real.continuous_sin)
    1 (fun θ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ) u
  have hc := KN.Analysis.boundedScalarMultiplier_ae angularMeasure
    (fun θ => (Real.cos θ : ℂ)) (Complex.continuous_ofReal.comp Real.continuous_cos)
    1 (fun θ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ) u
  filter_upwards [Lp.coeFn_add (A.compLpL 2 angularMeasure (fullSinMultiplier u))
    (B.compLpL 2 angularMeasure (fullCosMultiplier u)),
    A.coeFn_compLpL (fullSinMultiplier u),B.coeFn_compLpL (fullCosMultiplier u),hs,hc]
    with θ hadd ha hb hs hc
  simp only [Pi.add_apply] at hadd
  change (A.compLpL 2 angularMeasure (fullSinMultiplier u) +
    B.compLpL 2 angularMeasure (fullCosMultiplier u)) θ = _
  change fullSinMultiplier u θ = _ at hs
  change fullCosMultiplier u θ = _ at hc
  rw [hadd,ha,hb,hs,hc]
  exact fullStaticPotential_sin_cos _ _ _ _ _


theorem fullFrequencyMultiplier_anticommute_matrix
    (b : KN.Background) (σ : ℝ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : ∀ g β : ℂ, fullStaticPotential g β * U = -(U*fullStaticPotential g β))
    (u : FullAngularHilbert) :
    fullFrequencyMultiplier b σ
      (U.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure u) =
    -U.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure
      (fullFrequencyMultiplier b σ u) := by
  let L := U.toEuclideanLin.toContinuousLinearMap
  apply Lp.ext
  filter_upwards [fullFrequencyMultiplier_ae b σ (L.compLpL 2 angularMeasure u),
    L.coeFn_compLpL u,L.coeFn_compLpL (fullFrequencyMultiplier b σ u),
    fullFrequencyMultiplier_ae b σ u,
    Lp.coeFn_neg (L.compLpL 2 angularMeasure (fullFrequencyMultiplier b σ u))]
    with θ hv hu hL hV hn
  rw [hn]
  change _ = -(L.compLpL 2 angularMeasure (fullFrequencyMultiplier b σ u)) θ
  rw [hv,hu,hL,hV]
  change ((fullStaticPotential _ _).toEuclideanLin.comp U.toEuclideanLin) (u θ) =
    -(U.toEuclideanLin.comp (fullStaticPotential _ _).toEuclideanLin) (u θ)
  rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,hU]
  simp only [map_neg,LinearMap.neg_apply]

theorem fullFrequencyMultiplier_I (b : KN.Background) (σ : ℝ) (u : FullAngularHilbert) :
    fullFrequencyMultiplier b σ (fullI u) = -fullI (fullFrequencyMultiplier b σ u) :=
  fullFrequencyMultiplier_anticommute_matrix b σ KN.Physics.I4 fullPotential_I u

theorem fullFrequencyMultiplier_J (b : KN.Background) (σ : ℝ) (u : FullAngularHilbert) :
    fullFrequencyMultiplier b σ (fullJ u) = -fullJ (fullFrequencyMultiplier b σ u) :=
  fullFrequencyMultiplier_anticommute_matrix b σ KN.Physics.J4 fullPotential_J u

theorem fullStaticPotential_hermitian (g β : ℝ) :
    (fullStaticPotential (g : ℂ) (β : ℂ)).conjTranspose = fullStaticPotential g β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fullStaticPotential,Matrix.conjTranspose_apply]

theorem fullFrequencyMultiplier_symmetric (b : KN.Background) (σ : ℝ)
    (u v : FullAngularHilbert) :
    @inner ℂ _ _ (fullFrequencyMultiplier b σ u) v =
      @inner ℂ _ _ u (fullFrequencyMultiplier b σ v) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fullFrequencyMultiplier_ae b σ u,fullFrequencyMultiplier_ae b σ v]
    with θ hu hv
  rw [hu,hv,← LinearMap.adjoint_inner_right,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hh := fullStaticPotential_hermitian (-σ*b.a*b.kappa*Real.sin θ) (σ*b.a*b.c*Real.cos θ)
  simp only [Complex.ofReal_mul,Complex.ofReal_neg] at hh
  rw [hh]

end
end KN.Angular

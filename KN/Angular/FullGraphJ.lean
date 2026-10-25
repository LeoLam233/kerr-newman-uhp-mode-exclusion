import KN.Angular.FullGraphSymmetry

namespace KN.Angular
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ComplexInnerProductSpace

private theorem fullJMatrix_conjTranspose : KN.Physics.J4.conjTranspose=KN.Physics.J4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [KN.Physics.J4,Matrix.conjTranspose_apply]

private theorem fullJMap_ae (u : FullAngularHilbert) :
    fullJ u =ᵐ[angularMeasure] fun θ => KN.Physics.J4.toEuclideanLin (u θ) :=
  KN.Physics.J4.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL u

def fullJFiber : EuclideanSpace ℂ (Fin 4) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4) :=
  KN.Physics.J4.toEuclideanLin.isometryOfInner (by
    intro x y
    rw [← LinearMap.adjoint_inner_right,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x,(KN.Physics.J4.conjTranspose.toEuclideanLin.comp
      KN.Physics.J4.toEuclideanLin) y⟫=⟪x,y⟫
    rw [← Matrix.toLpLin_mul 2 2 2,fullJMatrix_conjTranspose,KN.Physics.J4_sq,
      Matrix.toLpLin_one]
    rfl)

theorem fullPotential_J (g β : ℂ) :
    fullStaticPotential g β * KN.Physics.J4 = -(KN.Physics.J4*fullStaticPotential g β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullStaticPotential,KN.Physics.J4,Matrix.mul_apply,Fin.sum_univ_succ]

/-- The anticommuting involution preserves the actual full maximal graph,
including distributional vectors, not only formal differential expressions. -/
theorem fullWeakGraph_J (σ β : ℝ) (m : ℤ)
    {u v : ℝ → EuclideanSpace ℂ (Fin 4)}
    (h : MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)) u v) :
    MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
      (fun θ => fullJFiber (u θ)) (fun θ => -fullJFiber (v θ)) := by
  have hD (w : EuclideanSpace ℂ (Fin 4)) :
      fullPrincipal.toEuclideanLin (fullJFiber w) = -fullJFiber (fullPrincipal.toEuclideanLin w) := by
    change (fullPrincipal.toEuclideanLin.comp KN.Physics.J4.toEuclideanLin) w =
      -(KN.Physics.J4.toEuclideanLin.comp fullPrincipal.toEuclideanLin) w
    rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2]
    change ((Matrix.toLpLin 2 2) (KN.Physics.derivativeMatrix*KN.Physics.J4)) w = _
    rw [KN.Physics.derivative_J_anticommute]
    simp only [map_neg, LinearMap.neg_apply]
    rfl
  have hW (θ : ℝ) (w : EuclideanSpace ℂ (Fin 4)) :
      (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin (fullJFiber w) =
        -fullJFiber ((fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin w) := by
    change ((fullStaticPotential _ _).toEuclideanLin.comp KN.Physics.J4.toEuclideanLin) w =
      -(KN.Physics.J4.toEuclideanLin.comp (fullStaticPotential _ _).toEuclideanLin) w
    rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,fullPotential_J]
    simp only [map_neg, LinearMap.neg_apply]
  intro φ hφ
  have hleft (θ : ℝ) : φ θ • (-fullJFiber (v θ)) = -fullJFiber (φ θ • v θ) := by
    simp
  have hright (θ : ℝ) :
      -(deriv φ θ) • fullPrincipal.toEuclideanLin (fullJFiber (u θ)) +
        φ θ • (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin (fullJFiber (u θ)) =
      -fullJFiber (-(deriv φ θ) • fullPrincipal.toEuclideanLin (u θ) +
        φ θ • (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin (u θ)) := by
    rw [hD,hW]
    simp [add_comm]
  simp_rw [hleft,hright,integral_neg,fullJFiber.integral_comp_comm]
  rw [h φ hφ]

theorem fullStaticGraph_J (σ β : ℝ) (m : ℤ) {u v : FullAngularHilbert}
    (h : FullStaticGraph σ β m u v) : FullStaticGraph σ β m (fullJ u) (-fullJ v) := by
  apply (MatrixWeakGraph.congr_ae fullPrincipal
    (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
    (fullJMap_ae u) ?_).mpr (fullWeakGraph_J σ β m h)
  filter_upwards [Lp.coeFn_neg (fullJ v),fullJMap_ae v] with θ h1 h2
  rw [h1]
  change -fullJ v θ = _
  rw [h2]
  rfl

end
end KN.Angular

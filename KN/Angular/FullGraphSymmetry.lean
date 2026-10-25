import KN.Angular.FullChiralBasis

namespace KN.Angular
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory

theorem fullPotential_I (g β : ℂ) :
    fullStaticPotential g β * KN.Physics.I4 = -(KN.Physics.I4*fullStaticPotential g β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullStaticPotential,KN.Physics.I4,Matrix.mul_apply,Fin.sum_univ_succ]

/-- The anticommuting involution preserves the actual full maximal graph,
including distributional vectors, not only formal differential expressions. -/
theorem fullWeakGraph_I (σ β : ℝ) (m : ℤ)
    {u v : ℝ → EuclideanSpace ℂ (Fin 4)}
    (h : MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)) u v) :
    MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
      (fun θ => fullIFiber (u θ)) (fun θ => -fullIFiber (v θ)) := by
  have hD (w : EuclideanSpace ℂ (Fin 4)) :
      fullPrincipal.toEuclideanLin (fullIFiber w) = -fullIFiber (fullPrincipal.toEuclideanLin w) := by
    change (fullPrincipal.toEuclideanLin.comp KN.Physics.I4.toEuclideanLin) w =
      -(KN.Physics.I4.toEuclideanLin.comp fullPrincipal.toEuclideanLin) w
    rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2]
    change ((Matrix.toLpLin 2 2) (KN.Physics.derivativeMatrix*KN.Physics.I4)) w = _
    rw [KN.Physics.derivative_I_anticommute]
    simp only [map_neg, LinearMap.neg_apply]
    rfl
  have hW (θ : ℝ) (w : EuclideanSpace ℂ (Fin 4)) :
      (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin (fullIFiber w) =
        -fullIFiber ((fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin w) := by
    change ((fullStaticPotential _ _).toEuclideanLin.comp KN.Physics.I4.toEuclideanLin) w =
      -(KN.Physics.I4.toEuclideanLin.comp (fullStaticPotential _ _).toEuclideanLin) w
    rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,fullPotential_I]
    simp only [map_neg, LinearMap.neg_apply]
  intro φ hφ
  have hleft (θ : ℝ) : φ θ • (-fullIFiber (v θ)) = -fullIFiber (φ θ • v θ) := by
    simp
  have hright (θ : ℝ) :
      -(deriv φ θ) • fullPrincipal.toEuclideanLin (fullIFiber (u θ)) +
        φ θ • (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin (fullIFiber (u θ)) =
      -fullIFiber (-(deriv φ θ) • fullPrincipal.toEuclideanLin (u θ) +
        φ θ • (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin (u θ)) := by
    rw [hD,hW]
    simp [add_comm]
  simp_rw [hleft,hright,integral_neg,fullIFiber.integral_comp_comm]
  rw [h φ hφ]

theorem fullStaticGraph_I (σ β : ℝ) (m : ℤ) {u v : FullAngularHilbert}
    (h : FullStaticGraph σ β m u v) : FullStaticGraph σ β m (fullI u) (-fullI v) := by
  apply (MatrixWeakGraph.congr_ae fullPrincipal
    (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
    (fullI_ae u) ?_).mpr (fullWeakGraph_I σ β m h)
  filter_upwards [Lp.coeFn_neg (fullI v),fullI_ae v] with θ h1 h2
  rw [h1]
  change -fullI v θ = _
  rw [h2]

end
end KN.Angular

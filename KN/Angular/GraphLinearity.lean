import KN.Angular.WeakGraphTransform

namespace KN.Angular
noncomputable section
open MeasureTheory

theorem MatrixWeakGraph.smul {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ)
    (W : ℝ → Matrix (Fin N) (Fin N) ℂ) {u v : ℝ → EuclideanSpace ℂ (Fin N)}
    (h : MatrixWeakGraph D W u v) (a : ℂ) :
    MatrixWeakGraph D W (fun θ => a • u θ) (fun θ => a • v θ) := by
  intro φ hφ
  have hleft (θ : ℝ) : φ θ • (a • v θ) = a • (φ θ • v θ) := smul_comm _ _ _
  have hright (θ : ℝ) :
      -(deriv φ θ) • D.toEuclideanLin (a • u θ) + φ θ • (W θ).toEuclideanLin (a • u θ) =
      a • (-(deriv φ θ) • D.toEuclideanLin (u θ) + φ θ • (W θ).toEuclideanLin (u θ)) := by
    simp only [map_smul]
    module
  simp_rw [hleft,hright,integral_smul]
  rw [h φ hφ]

theorem StaticGraph.smul (σ β : ℝ) (m : ℤ) {u v : AngularHilbert}
    (h : StaticGraph σ β m u v) (a : ℂ) : StaticGraph σ β m (a • u) (a • v) := by
  apply (MatrixWeakGraph.congr_ae massPrincipal
    (fun θ => massPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
    (Lp.coeFn_smul a u) (Lp.coeFn_smul a v)).mpr
  exact MatrixWeakGraph.smul _ _ h a

end
end KN.Angular

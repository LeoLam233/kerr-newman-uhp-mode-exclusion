import KN.Angular.MaximalDomain

namespace KN.Angular
noncomputable section
open MeasureTheory

/-- Intertwining holds in the actual weak distributional graph, not just on
smooth vectors or formal matrix expressions. -/
theorem weakGraph_chiral (σ β : ℝ) (m : ℤ)
    (u v : ℝ → EuclideanSpace ℂ (Fin 2)) :
    MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
      (fun θ => chiralIsometry (u θ)) (fun θ => chiralIsometry (v θ)) ↔
    MatrixWeakGraph massPrincipal
      (fun θ => massPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)) u v := by
  have hD (w : EuclideanSpace ℂ (Fin 2)) :
      fullPrincipal.toEuclideanLin (chiralIsometry w) =
      chiralIsometry (massPrincipal.toEuclideanLin w) := by
    change (fullPrincipal.toEuclideanLin.comp chiralEmbedding.toEuclideanLin) w =
      (chiralEmbedding.toEuclideanLin.comp massPrincipal.toEuclideanLin) w
    rw [← Matrix.toLpLin_mul 2 2 2, ← Matrix.toLpLin_mul 2 2 2, chiral_principal]
  have hW (θ : ℝ) (w : EuclideanSpace ℂ (Fin 2)) :
      (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin
        (chiralIsometry w) =
      chiralIsometry ((massPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin w) := by
    change ((fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin.comp
      chiralEmbedding.toEuclideanLin) w =
      (chiralEmbedding.toEuclideanLin.comp
      (massPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin) w
    rw [← Matrix.toLpLin_mul 2 2 2, ← Matrix.toLpLin_mul 2 2 2, chiral_potential]
  unfold MatrixWeakGraph
  have hφ (φ : ℝ → ℂ) :
      (∫ θ, φ θ • chiralIsometry (v θ) ∂angularMeasure) =
        chiralIsometry (∫ θ, φ θ • v θ ∂angularMeasure) := by
    simpa only [map_smul] using chiral_integral angularMeasure (fun θ => φ θ • v θ)
  have hψ (φ : ℝ → ℂ) :
      (∫ θ, -(deriv φ θ) • fullPrincipal.toEuclideanLin (chiralIsometry (u θ)) +
        φ θ • (fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin
          (chiralIsometry (u θ)) ∂angularMeasure) =
      chiralIsometry (∫ θ, -(deriv φ θ) • massPrincipal.toEuclideanLin (u θ) +
        φ θ • (massPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)).toEuclideanLin
          (u θ) ∂angularMeasure) := by
    simp_rw [hD,hW,← map_smul,← map_add]
    exact chiral_integral angularMeasure _
  simp_rw [hφ,hψ,chiralIsometry.injective.eq_iff]

end
end KN.Angular

namespace KN.Angular
noncomputable section
open MeasureTheory

abbrev FullAngularHilbert := Lp (EuclideanSpace ℂ (Fin 4)) 2 angularMeasure

def chiralLpMap : AngularHilbert →L[ℂ] FullAngularHilbert :=
  chiralIsometry.toContinuousLinearMap.compLpL 2 angularMeasure

theorem chiralLpMap_ae (u : AngularHilbert) :
    chiralLpMap u =ᵐ[angularMeasure] fun θ => chiralIsometry (u θ) :=
  chiralIsometry.toContinuousLinearMap.coeFn_compLpL u

theorem chiralLpMap_norm (u : AngularHilbert) : ‖chiralLpMap u‖ = ‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [chiralLpMap_ae u] with θ hθ
  rw [hθ,chiralIsometry.norm_map]

def chiralLpIsometry : AngularHilbert →ₗᵢ[ℂ] FullAngularHilbert :=
  { chiralLpMap.toLinearMap with norm_map' := chiralLpMap_norm }

/-- The weak graph is independent of the choice of L² representatives. -/
theorem MatrixWeakGraph.congr_ae {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ)
    (W : ℝ → Matrix (Fin N) (Fin N) ℂ)
    {u v u' v' : ℝ → EuclideanSpace ℂ (Fin N)}
    (hu : u =ᵐ[angularMeasure] u') (hv : v =ᵐ[angularMeasure] v') :
    MatrixWeakGraph D W u v ↔ MatrixWeakGraph D W u' v' := by
  unfold MatrixWeakGraph
  have hl (φ : ℝ → ℂ) : (∫ θ, φ θ • v θ ∂angularMeasure) =
      ∫ θ, φ θ • v' θ ∂angularMeasure := by
    apply integral_congr_ae
    filter_upwards [hv] with θ hθ
    rw [hθ]
  have hr (φ : ℝ → ℂ) :
      (∫ θ, -(deriv φ θ) • D.toEuclideanLin (u θ) +
        φ θ • (W θ).toEuclideanLin (u θ) ∂angularMeasure) =
      ∫ θ, -(deriv φ θ) • D.toEuclideanLin (u' θ) +
        φ θ • (W θ).toEuclideanLin (u' θ) ∂angularMeasure := by
    apply integral_congr_ae
    filter_upwards [hu] with θ hθ
    rw [hθ]
  simp_rw [hl,hr]

def FullStaticGraph (σ β : ℝ) (m : ℤ) (u v : FullAngularHilbert) : Prop :=
  MatrixWeakGraph fullPrincipal
    (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)) u v

/-- Exact first-order graph equivalence on actual L² spaces under the
constant isometric chiral/Hadamard embedding. -/
theorem fullStaticGraph_chiral_iff (σ β : ℝ) (m : ℤ) (u v : AngularHilbert) :
    FullStaticGraph σ β m (chiralLpMap u) (chiralLpMap v) ↔ StaticGraph σ β m u v := by
  unfold FullStaticGraph StaticGraph
  rw [MatrixWeakGraph.congr_ae _ _ (chiralLpMap_ae u) (chiralLpMap_ae v)]
  exact weakGraph_chiral σ β m u v

end
end KN.Angular

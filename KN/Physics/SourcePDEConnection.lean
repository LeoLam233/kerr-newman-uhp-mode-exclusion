import KN.Physics.SourcePDEGeometry
import KN.Physics.SourcePDEFactor
import KN.Physics.SourceMatrixIdentification

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

abbrev SourceMatrix := Matrix (Fin 2) (Fin 2) ℂ

def sourceA (b : Background) (r θ : ℝ) : SourceMatrix :=
  factorConnection b.Q (rho b r θ) (rhoStar b r θ)

def sourceMatrixD (t ε : ℂ) (X : ℝ → ℝ → SourceMatrix) (r θ : ℝ) : SourceMatrix :=
  fun i j => sourceD t ε (fun x y => X x y i j) r θ

lemma source_matrix_connection (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    sourceMatrixD (Real.sqrt (b.Delta r)) (-1) (physicalSourceMatrix b) r θ =
      sourceA b r θ * physicalSourceMatrix b r θ := by
  have h1 : SourceDifferentiableAt (rho b) r θ :=
    ⟨(rho_radial_deriv b r θ).differentiableAt,(rho_angular_deriv b r θ).differentiableAt⟩
  have h3 : SourceDifferentiableAt (rhoStar b) r θ :=
    ⟨(rhoStar_radial_deriv b r θ).differentiableAt,(rhoStar_angular_deriv b r θ).differentiableAt⟩
  have h2 : SourceDifferentiableAt (sourceF2 b) r θ :=
    ⟨(sourceF2_radial_deriv b hr θ).differentiableAt,(sourceF2_angular_deriv b r θ).differentiableAt⟩
  have h4 : SourceDifferentiableAt (sourceF4 b) r θ :=
    ⟨(sourceF4_radial_deriv b hr θ).differentiableAt,(sourceF4_angular_deriv b r θ).differentiableAt⟩
  obtain ⟨hd1,hd2,hd3,hd4⟩ := source_geometry_jets b hr θ
  have hg : rho b r θ*rhoStar b r θ-sourceF2 b r θ*sourceF4 b r θ =
      (b.M:ℂ)*(rho b r θ+rhoStar b r θ)-(b.Q:ℂ)^2 := by
    apply integrating_geometry
    · have hh := congrArg Complex.ofReal (Real.sq_sqrt (le_of_lt (b.Delta_pos hr)))
      simpa [Background.Delta] using hh
    · exact_mod_cast Real.sin_sq_add_cos_sq θ
  have hdx := sourceD_factorX (Real.sqrt (b.Delta r)) (-1) b.M b.Q
    (rho b) (sourceF2 b) (rhoStar b) (sourceF4 b) r θ h1 h2 h3 h4
    (rho_ne_zero b hr θ) (rhoStar_ne_zero b hr θ) hd1 hd2 hd3 hd4
  rw [factor_connection_identity _ _ _ _ _ _ (rho_ne_zero b hr θ) (rhoStar_ne_zero b hr θ) hg] at hdx
  exact hdx

/-- Every matrix entry has the actual two partial derivatives in the exterior. -/
lemma source_matrix_differentiable (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ)
    (i j : Fin 2) : SourceDifferentiableAt (fun x y => physicalSourceMatrix b x y i j) r θ := by
  have h1 : SourceDifferentiableAt (rho b) r θ :=
    ⟨(rho_radial_deriv b r θ).differentiableAt,(rho_angular_deriv b r θ).differentiableAt⟩
  have h3 : SourceDifferentiableAt (rhoStar b) r θ :=
    ⟨(rhoStar_radial_deriv b r θ).differentiableAt,(rhoStar_angular_deriv b r θ).differentiableAt⟩
  have h2 : SourceDifferentiableAt (sourceF2 b) r θ :=
    ⟨(sourceF2_radial_deriv b hr θ).differentiableAt,(sourceF2_angular_deriv b r θ).differentiableAt⟩
  have h4 : SourceDifferentiableAt (sourceF4 b) r θ :=
    ⟨(sourceF4_radial_deriv b hr θ).differentiableAt,(sourceF4_angular_deriv b r θ).differentiableAt⟩
  have hc := SourceDifferentiableAt.const
  fin_cases i <;> fin_cases j
  · exact ((hc b.Q r θ).mul h4).div h1 (rho_ne_zero b hr θ)
  · exact (hc (-Complex.I) r θ).mul ((hc b.M r θ).sub ((hc ((b.Q:ℂ)^2) r θ).div h1 (rho_ne_zero b hr θ)))
  · exact (hc Complex.I r θ).mul ((hc b.M r θ).sub ((hc ((b.Q:ℂ)^2) r θ).div h3 (rhoStar_ne_zero b hr θ)))
  · exact ((hc b.Q r θ).mul h2).div h3 (rhoStar_ne_zero b hr θ)

end
end KN.Physics

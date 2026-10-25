import KN.Physics.SourcePDEFour
import KN.Physics.SourceHorizonRegularity

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
open KN.Physics Set Matrix
open scoped ContDiff

private theorem sourceMatrix_angular_smooth (b : KN.Background) {r : ℝ} (hr : b.rPlus<r)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (fun θ => physicalSourceMatrix b r θ i j) (Ioo 0 Real.pi) := by
  have hs : ContDiffOn ℝ ∞ (fun θ : ℝ => (Real.sin θ : ℂ)) (Ioo 0 Real.pi) :=
    (Complex.ofRealCLM.contDiff.comp Real.contDiff_sin).contDiffOn
  have hc : ContDiffOn ℝ ∞ (fun θ : ℝ => (Real.cos θ : ℂ)) (Ioo 0 Real.pi) :=
    (Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).contDiffOn
  have hconst (c : ℂ) : ContDiffOn ℝ ∞ (fun _ : ℝ => c) (Ioo 0 Real.pi) := contDiffOn_const
  have hp : ContDiffOn ℝ ∞ (rho b r) (Ioo 0 Real.pi) :=
    (hconst r).add ((hconst (Complex.I*b.a)).mul hc)
  have hm : ContDiffOn ℝ ∞ (rhoStar b r) (Ioo 0 Real.pi) :=
    (hconst r).sub ((hconst (Complex.I*b.a)).mul hc)
  have hpn : ∀ θ ∈ Ioo (0:ℝ) Real.pi, rho b r θ≠0 := fun θ _ => rho_ne_zero b hr θ
  have hmn : ∀ θ ∈ Ioo (0:ℝ) Real.pi, rhoStar b r θ≠0 := fun θ _ => rhoStar_ne_zero b hr θ
  fin_cases i <;> fin_cases j
  · exact ((hconst b.Q).mul ((hconst (Real.sqrt (b.Delta r))).add ((hconst b.a).mul hs))).mul (hp.inv hpn)
  · exact (hconst (-Complex.I)).mul ((hconst b.M).sub ((hconst ((b.Q:ℂ)^2)).mul (hp.inv hpn)))
  · exact (hconst Complex.I).mul ((hconst b.M).sub ((hconst ((b.Q:ℂ)^2)).mul (hm.inv hmn)))
  · exact ((hconst b.Q).mul ((hconst (Real.sqrt (b.Delta r))).sub ((hconst b.a).mul hs))).mul (hm.inv hmn)

private theorem transformScale_angular_smooth (positive : Bool) (b : KN.Background) (r : ℝ) :
    ContDiffOn ℝ ∞ (transformScale positive b r) (Ioo 0 Real.pi) := by
  have hs : ContDiffOn ℝ ∞ (fun θ => Real.sqrt (Real.sin θ)) (Ioo 0 Real.pi) :=
    Real.contDiff_sin.contDiffOn.sqrt (fun θ hθ => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hs)

private theorem sourceY_angular_smooth (positive : Bool) (b : KN.Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) (r : ℝ)
    (hu : ∀ i, ContDiffOn ℝ ∞ (fun θ => u r θ i) (Ioo 0 Real.pi)) (sign : ℂ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun θ => sourceY positive sign b u r θ i) (Ioo 0 Real.pi) := by
  have hF := transformScale_angular_smooth positive b r
  have hconst (c : ℂ) : ContDiffOn ℝ ∞ (fun _ : ℝ => c) (Ioo 0 Real.pi) := contDiffOn_const
  fin_cases i
  · exact hF.mul ((hu 0).add ((hconst (sign*Complex.I*transformMix positive b r)).mul (hu 1)))
  · exact hF.mul ((hconst (-2*transformCharge positive b)).mul
      ((hu 2).add ((hconst (sign*Complex.I*transformMix positive b r)).mul (hu 3))))

/-- Ordinary interior smoothness of the original angular sections gives the
actual source transform's smooth angular representative. No transformed angular
regularity or operator-domain membership is assumed. -/
theorem sourceFullVector_angular_smooth (positive : Bool) (b : KN.Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) {r : ℝ} (hr : b.rPlus<r)
    (hu : ∀ i, ContDiffOn ℝ ∞ (fun θ => u r θ i) (Ioo 0 Real.pi)) :
    ContDiffOn ℝ ∞ (fun θ => WithLp.toLp 2 (sourceFullVector positive b u r θ)) (Ioo 0 Real.pi) := by
  have hX := sourceMatrix_angular_smooth b hr
  have hA (i j : Fin 2) : ContDiffOn ℝ ∞
      (fun θ => (physicalSourceMatrix b r θ).adjugate i j) (Ioo 0 Real.pi) := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hX 1 1
    · simpa [Matrix.adjugate_fin_two] using (hX 0 1).neg
    · simpa [Matrix.adjugate_fin_two] using (hX 1 0).neg
    · simpa [Matrix.adjugate_fin_two] using hX 0 0
  have hS (i j : Fin 2) : ContDiffOn ℝ ∞
      (fun θ => (physicalSourceMatrix b r θ).conjTranspose i j) (Ioo 0 Real.pi) := by
    exact Complex.conjCLE.contDiff.comp_contDiffOn (hX j i)
  have hp (i : Fin 2) : ContDiffOn ℝ ∞
      (fun θ => (sourceTransform positive b r θ (u r θ)).1 i) (Ioo 0 Real.pi) := by
    change ContDiffOn ℝ ∞ (fun θ => ∑ j, (physicalSourceMatrix b r θ).adjugate i j*
      sourceY positive 1 b u r θ j) _
    exact ContDiffOn.sum (fun j _ => (hA i j).mul (sourceY_angular_smooth positive b u r hu 1 j))
  have hm (i : Fin 2) : ContDiffOn ℝ ∞
      (fun θ => (sourceTransform positive b r θ (u r θ)).2 i) (Ioo 0 Real.pi) := by
    change ContDiffOn ℝ ∞ (fun θ => ∑ j, (physicalSourceMatrix b r θ).conjTranspose i j*
      sourceY positive (-1) b u r θ j) _
    exact ContDiffOn.sum (fun j _ => (hS i j).mul (sourceY_angular_smooth positive b u r hu (-1) j))
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℂ)).symm.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact hp 0
  · exact hp 1
  · exact hm 0
  · exact hm 1

end
end KN.Angular

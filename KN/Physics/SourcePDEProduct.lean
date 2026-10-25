import KN.Physics.SourcePDEAdjoint

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

def sourceVectorD (t ε : ℂ) (u : ℝ → ℝ → Fin 2 → ℂ) (r θ : ℝ) : Fin 2 → ℂ :=
  fun i => sourceD t ε (fun x y => u x y i) r θ

lemma sourceVectorD_mulVec (t ε : ℂ) (X : ℝ → ℝ → SourceMatrix)
    (u : ℝ → ℝ → Fin 2 → ℂ) (r θ : ℝ)
    (hX : ∀ i j, SourceDifferentiableAt (fun x y => X x y i j) r θ)
    (hu : ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ) :
    sourceVectorD t ε (fun x y => X x y *ᵥ u x y) r θ=
      sourceMatrixD t ε X r θ *ᵥ u r θ + X r θ *ᵥ sourceVectorD t ε u r θ := by
  ext i
  simp only [sourceVectorD,sourceMatrixD,Matrix.mulVec, dotProduct,Fin.sum_univ_two,Pi.add_apply]
  rw [sourceD_add _ _ _ _ _ _ ((hX i 0).mul (hu 0)) ((hX i 1).mul (hu 1)),
    sourceD_mul _ _ _ _ _ _ (hX i 0) (hu 0),sourceD_mul _ _ _ _ _ _ (hX i 1) (hu 1)]
  ring

lemma source_adjugate_differentiable (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ)
    (i j : Fin 2) : SourceDifferentiableAt
      (fun x y => (physicalSourceMatrix b x y).adjugate i j) r θ := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using source_matrix_differentiable b hr θ 1 1
  · simpa [Matrix.adjugate_fin_two] using (source_matrix_differentiable b hr θ 0 1).neg
  · simpa [Matrix.adjugate_fin_two] using (source_matrix_differentiable b hr θ 1 0).neg
  · simpa [Matrix.adjugate_fin_two] using source_matrix_differentiable b hr θ 0 0
lemma source_star_differentiable (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ)
    (i j : Fin 2) : SourceDifferentiableAt
      (fun x y => (physicalSourceMatrix b x y).conjTranspose i j) r θ :=
  (source_matrix_differentiable b hr θ j i).conjugate

/-- Differential part of the positive source block transformation, before
using the separately verified complex-frequency coupling algebra. -/
theorem source_positive_transport (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ)
    (yplus yminus : ℝ → ℝ → Fin 2 → ℂ)
    (hy : ∀ i, SourceDifferentiableAt (fun x y => yplus x y i) r θ)
    (C : SourceMatrix)
    (heq : sourceVectorD (Real.sqrt (b.Delta r)) (-1) yplus r θ =
      sourceA b r θ *ᵥ yplus r θ + C *ᵥ yminus r θ) :
    sourceVectorD (Real.sqrt (b.Delta r)) (-1)
      (fun x y => (physicalSourceMatrix b x y).adjugate *ᵥ yplus x y) r θ =
      ((physicalSourceMatrix b r θ).adjugate*C) *ᵥ yminus r θ := by
  rw [sourceVectorD_mulVec _ _ _ _ _ _ (source_adjugate_differentiable b hr θ) hy,
    source_adjugate_connection b hr θ,heq,Matrix.mulVec_add,
    Matrix.neg_mul,Matrix.neg_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  abel

/-- Differential part of the negative source block transformation. -/
theorem source_negative_transport (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ)
    (yplus yminus : ℝ → ℝ → Fin 2 → ℂ)
    (hy : ∀ i, SourceDifferentiableAt (fun x y => yminus x y i) r θ)
    (C : SourceMatrix)
    (heq : sourceVectorD (Real.sqrt (b.Delta r)) 1 yminus r θ =
      -sourceA b r θ *ᵥ yminus r θ + C *ᵥ yplus r θ) :
    sourceVectorD (Real.sqrt (b.Delta r)) 1
      (fun x y => (physicalSourceMatrix b x y).conjTranspose *ᵥ yminus x y) r θ =
      ((physicalSourceMatrix b r θ).conjTranspose*C) *ᵥ yplus r θ := by
  rw [sourceVectorD_mulVec _ _ _ _ _ _ (source_star_differentiable b hr θ) hy,
    source_star_connection b hr θ,heq,Matrix.mulVec_add,
    Matrix.neg_mulVec,Matrix.mulVec_neg,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  abel

end
end KN.Physics

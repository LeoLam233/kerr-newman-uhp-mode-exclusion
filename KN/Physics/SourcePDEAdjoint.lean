import KN.Physics.SourcePDEConnection

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

lemma sourceD_neg (t ε : ℂ) (f : ℝ → ℝ → ℂ) (r θ : ℝ) :
    sourceD t ε (fun x y => -f x y) r θ= -sourceD t ε f r θ := by
  unfold sourceD
  have hrn : deriv (fun x => -f x θ) r= -deriv (fun x => f x θ) r := deriv.neg
  have hθn : deriv (fun y => -f r y) θ= -deriv (f r) θ := deriv.neg
  rw [hrn,hθn]
  ring

lemma sourceD_star (t : ℝ) (f : ℝ → ℝ → ℂ) (r θ : ℝ) :
    sourceD t 1 (fun x y => star (f x y)) r θ=star (sourceD t (-1) f r θ) := by
  unfold sourceD
  rw [deriv.star,deriv.star]
  simp only [Complex.star_def,map_add,map_mul,Complex.conj_ofReal,map_neg,map_one,Complex.conj_I]
  ring

lemma sourceMatrixD_adjugate (t ε : ℂ) (X : ℝ → ℝ → SourceMatrix) (r θ : ℝ) :
    sourceMatrixD t ε (fun x y => (X x y).adjugate) r θ =
      (sourceMatrixD t ε X r θ).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two,sourceMatrixD,sourceD_neg]

lemma sourceMatrixD_conjTranspose (t : ℝ) (X : ℝ → ℝ → SourceMatrix) (r θ : ℝ) :
    sourceMatrixD t 1 (fun x y => (X x y).conjTranspose) r θ =
      (sourceMatrixD t (-1) X r θ).conjTranspose := by
  ext i j
  exact sourceD_star t (fun x y => X x y j i) r θ

lemma sourceA_adjugate (b : Background) (r θ : ℝ) :
    (sourceA b r θ).adjugate= -sourceA b r θ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceA,factorConnection,Matrix.adjugate_fin_two]

lemma sourceA_conjTranspose (b : Background) (r θ : ℝ) :
    (sourceA b r θ).conjTranspose=sourceA b r θ := by
  have hrho : star (rho b r θ)=rhoStar b r θ := by
    simp only [rho,rhoStar,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    ring
  have hrhos : star (rhoStar b r θ)=rho b r θ := by
    rw [←hrho,star_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceA,factorConnection,Matrix.conjTranspose_apply,hrho,hrhos,
      star_mul,star_pow,Complex.conj_I] <;> ring

/-- Genuine differential cancellation for the adjugate source block. -/
theorem source_adjugate_connection (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    sourceMatrixD (Real.sqrt (b.Delta r)) (-1)
      (fun x y => (physicalSourceMatrix b x y).adjugate) r θ =
      -(physicalSourceMatrix b r θ).adjugate * sourceA b r θ := by
  rw [sourceMatrixD_adjugate,source_matrix_connection b hr θ,Matrix.adjugate_mul_distrib,
    sourceA_adjugate,Matrix.mul_neg,Matrix.neg_mul]

/-- Genuine differential cancellation for the conjugate-transpose source block.
Only real background coefficients are conjugated, never the frequency. -/
theorem source_star_connection (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    sourceMatrixD (Real.sqrt (b.Delta r)) 1
      (fun x y => (physicalSourceMatrix b x y).conjTranspose) r θ =
      (physicalSourceMatrix b r θ).conjTranspose * sourceA b r θ := by
  rw [sourceMatrixD_conjTranspose,source_matrix_connection b hr θ,
    Matrix.conjTranspose_mul,sourceA_conjTranspose]

end
end KN.Physics

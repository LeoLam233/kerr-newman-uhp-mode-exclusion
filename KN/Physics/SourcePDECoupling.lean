import KN.Physics.SourcePDEConnection

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

/-- In dimension two the reverse coupling follows algebraically from the
forward coupling and equal nonzero determinants. No frequency conjugation. -/
lemma reverse_source_coupling (X S C B : SourceMatrix)
    (hdet : S.det=X.det) (hne : X.det≠0) (h : C*S=X.adjugate*B) :
    C.adjugate*X.adjugate=S*B.adjugate := by
  have ha := congrArg Matrix.adjugate h
  rw [Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib] at ha
  have hxx : X.adjugate.adjugate=X := by
    simp [Matrix.adjugate_adjugate]
  rw [hxx] at ha
  have he : X.det • (C.adjugate*X.adjugate)=X.det • (S*B.adjugate) := by
    calc
      _ = S.det • (C.adjugate*X.adjugate) := by rw [hdet]
      _ = (S*S.adjugate)*(C.adjugate*X.adjugate) := by rw [Matrix.mul_adjugate,Matrix.smul_mul,one_mul]
      _ = S*(S.adjugate*C.adjugate)*X.adjugate := by simp only [Matrix.mul_assoc]
      _ = S*(B.adjugate*X)*X.adjugate := by rw [ha]
      _ = (S*B.adjugate)*(X*X.adjugate) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_adjugate,Matrix.mul_smul,mul_one]
  exact (smul_right_injective _ hne) he

def physicalChiralCoupling (b : Background) (m : ℤ) (omega σ : ℂ) (r θ : ℝ) : SourceMatrix :=
  chiralCoupling b.M b.Q b.a r (Real.sqrt (b.Delta r)) (Real.sin θ) (Real.cos θ) m omega σ

def physicalOriginalCoupling (b : Background) (m : ℤ) (omega σ : ℂ) (r θ : ℝ) : SourceMatrix :=
  originalChiralCoupling b.M b.Q b.a r (Real.sqrt (b.Delta r)) (Real.sin θ) (Real.cos θ) m omega σ

lemma physical_source_coupling (b : Background) (hQ : b.Q≠0) (m : ℤ) (omega σ : ℂ)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) :
    physicalChiralCoupling b m omega σ r θ*(physicalSourceMatrix b r θ).conjTranspose=
      (physicalSourceMatrix b r θ).adjugate*physicalOriginalCoupling b m omega σ r θ := by
  unfold physicalChiralCoupling physicalOriginalCoupling physicalSourceMatrix
  rw [sourceMatrix_adjugate,sourceMatrix_conjTranspose_real]
  apply source_coupling_identity
  · exact_mod_cast hQ
  · exact_mod_cast b.d_ne
  · exact_mod_cast ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ hπ)
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr))
  · exact rho_ne_zero b hr θ
  · exact rhoStar_ne_zero b hr θ
  · have hh := congrArg Complex.ofReal (Real.sq_sqrt (le_of_lt (b.Delta_pos hr)))
    simpa [Background.Delta] using hh
  · exact_mod_cast Real.sin_sq_add_cos_sq θ

lemma physical_source_reverse_coupling (b : Background) (hQ : b.Q≠0) (m : ℤ) (omega σ : ℂ)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) :
    (physicalChiralCoupling b m omega σ r θ).adjugate*(physicalSourceMatrix b r θ).adjugate=
      (physicalSourceMatrix b r θ).conjTranspose*(physicalOriginalCoupling b m omega σ r θ).adjugate := by
  apply reverse_source_coupling
  · rw [Matrix.det_conjTranspose,physicalSourceMatrix_det b hr θ]
    simp
  · exact physicalSourceMatrix_det_ne_zero b hr θ
  · exact physical_source_coupling b hQ m omega σ hr hθ hπ

end
end KN.Physics

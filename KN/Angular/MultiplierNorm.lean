import KN.Angular.ReducedMultiplier
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace KN.Angular
noncomputable section
open scoped ComplexInnerProductSpace

theorem massPotential_hermitian (g β : ℝ) :
    (massPotential (g : ℂ) (β : ℂ)).conjTranspose = massPotential g β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [massPotential,Matrix.conjTranspose_apply]

theorem massPotential_sq (g β : ℂ) :
    massPotential g β * massPotential g β = (g^2+β^2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massPotential,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem massPotential_inner (g β : ℝ) (u v : AngularFiber) :
    ⟪(massPotential (g : ℂ) (β : ℂ)).toEuclideanLin u,v⟫ =
      ⟪u,(massPotential (g : ℂ) (β : ℂ)).toEuclideanLin v⟫ := by
  rw [← LinearMap.adjoint_inner_right,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    massPotential_hermitian]

theorem massPotential_norm_sq (g β : ℝ) (u : AngularFiber) :
    ‖(massPotential (g : ℂ) (β : ℂ)).toEuclideanLin u‖^2 = (g^2+β^2)*‖u‖^2 := by
  have h := massPotential_inner g β u ((massPotential (g : ℂ) (β : ℂ)).toEuclideanLin u)
  rw [inner_self_eq_norm_sq_to_K] at h
  change (‖(massPotential (g : ℂ) (β : ℂ)).toEuclideanLin u‖^2 : ℂ) =
    ⟪u,((massPotential (g : ℂ) (β : ℂ)).toEuclideanLin.comp
      (massPotential (g : ℂ) (β : ℂ)).toEuclideanLin) u⟫ at h
  rw [← Matrix.toLpLin_mul 2 2 2,massPotential_sq,map_smul,Matrix.toLpLin_one,
    LinearMap.smul_apply,LinearMap.id_apply,inner_smul_right,inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  simpa [pow_two] using hr

theorem frequency_fiber_norm_sq (b : KN.Background)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (θ : ℝ) (u : AngularFiber) :
    ‖(massPotential (-σ*b.a*b.kappa*Real.sin θ : ℂ)
      (σ*b.a*b.c*Real.cos θ : ℂ)).toEuclideanLin u‖^2 =
      b.a^2*(b.c^2+Real.sin θ^2)*‖u‖^2 := by
  have he : ((-σ*b.a*b.kappa*Real.sin θ)^2+(σ*b.a*b.c*Real.cos θ)^2) =
      b.a^2*(b.c^2+Real.sin θ^2) := by
    have hk := b.kappa_sq_sub_c_sq
    have ht := Real.sin_sq_add_cos_sq θ
    have hk' : b.kappa^2=b.c^2+1 := by linarith
    have ht' : Real.cos θ^2=1-Real.sin θ^2 := by linarith
    rcases hσ with rfl | rfl <;>
      simp only [mul_pow,one_pow,one_mul,neg_sq] <;>
      rw [hk',ht'] <;> ring

  have h := massPotential_norm_sq (-σ*b.a*b.kappa*Real.sin θ) (σ*b.a*b.c*Real.cos θ) u
  simp only [Complex.ofReal_mul,Complex.ofReal_neg] at h
  rw [he] at h
  exact h

end
end KN.Angular

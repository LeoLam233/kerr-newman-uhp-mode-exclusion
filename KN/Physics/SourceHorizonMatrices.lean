import KN.Physics.SourceHorizonRegularity
import KN.Physics.SourceRecovery

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Elementwise
open Set Matrix
namespace KN.Physics

lemma rho_closed_ne_zero (b : KN.Background) {r : ℝ} (hr : b.rPlus ≤ r) (θ : ℝ) :
    rho b r θ ≠ 0 := by
  intro h
  have hz := congrArg Complex.re h
  simp [rho] at hz
  linarith [b.rPlus_pos]
lemma rhoStar_closed_ne_zero (b : KN.Background) {r : ℝ} (hr : b.rPlus ≤ r) (θ : ℝ) :
    rhoStar b r θ ≠ 0 := by
  intro h
  have hz := congrArg Complex.re h
  simp [rhoStar] at hz
  linarith [b.rPlus_pos]

lemma horizonEven_smooth (b : KN.Background) (θ : ℝ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun (r : ℝ) => horizonEven b.Q b.a r (Real.cos θ)) (Ici b.rPlus) := by
  have hp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun (r : ℝ) => (r:ℂ)+Complex.I*b.a*Real.cos θ) (Ici b.rPlus) :=
    Complex.ofRealCLM.contDiff.contDiffOn.add contDiffOn_const
  have hm : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun (r : ℝ) => (r:ℂ)-Complex.I*b.a*Real.cos θ) (Ici b.rPlus) :=
    Complex.ofRealCLM.contDiff.contDiffOn.sub contDiffOn_const
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp only [horizonEven,Matrix.of_apply,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const]
  · convert (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) _ (Ici b.rPlus) from contDiffOn_const.mul (hm.fun_inv (fun r hr => rhoStar_closed_ne_zero b hr θ))) using 1 <;> (try rfl) <;> simp_all [div_eq_mul_inv]
  · exact contDiffOn_const
  · exact contDiffOn_const
  · convert (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) _ (Ici b.rPlus) from contDiffOn_const.mul (hp.fun_inv (fun r hr => rho_closed_ne_zero b hr θ))) using 1 <;> (try rfl) <;> simp_all [div_eq_mul_inv]

lemma horizonOdd_smooth (b : KN.Background) (θ : ℝ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun (r : ℝ) => horizonOdd b.M b.Q b.a r (Real.sin θ) (Real.cos θ)) (Ici b.rPlus) := by
  have hp : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun (r : ℝ) => (r:ℂ)+Complex.I*b.a*Real.cos θ) (Ici b.rPlus) :=
    Complex.ofRealCLM.contDiff.contDiffOn.add contDiffOn_const
  have hm : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun (r : ℝ) => (r:ℂ)-Complex.I*b.a*Real.cos θ) (Ici b.rPlus) :=
    Complex.ofRealCLM.contDiff.contDiffOn.sub contDiffOn_const
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp only [horizonOdd,Matrix.of_apply,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const]
  · convert (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) _ (Ici b.rPlus) from contDiffOn_const.mul (hm.fun_inv (fun r hr => rhoStar_closed_ne_zero b hr θ))) using 1 <;> (try rfl) <;> simp_all [div_eq_mul_inv]
  · convert (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) _ (Ici b.rPlus) from contDiffOn_const.mul
      (contDiffOn_const.sub (contDiffOn_const.mul (hp.fun_inv (fun r hr => rho_closed_ne_zero b hr θ))))) using 1 <;> (try rfl) <;> simp_all [div_eq_mul_inv]
  · convert (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) _ (Ici b.rPlus) from contDiffOn_const.mul
      (contDiffOn_const.sub (contDiffOn_const.mul (hm.fun_inv (fun r hr => rhoStar_closed_ne_zero b hr θ))))) using 1 <;> (try rfl) <;> simp_all [div_eq_mul_inv]
  · convert (show ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) _ (Ici b.rPlus) from contDiffOn_const.mul (hp.fun_inv (fun r hr => rho_closed_ne_zero b hr θ))) using 1 <;> (try rfl) <;> simp_all [div_eq_mul_inv]

end KN.Physics

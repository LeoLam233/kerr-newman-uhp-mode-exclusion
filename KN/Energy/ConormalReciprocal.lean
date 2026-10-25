import KN.Energy.ConormalAlgebra
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

open Set
namespace KN.Energy
open KN.Boundary ConormalExpr

noncomputable def reciprocal (c r : ℝ) : ℂ := ((r-c : ℝ):ℂ)⁻¹

theorem reciprocal_smooth (c : ℝ) : ExteriorSmooth c (reciprocal c) := by
  have hn : ∀ r ∈ Ioi c, ((r-c:ℝ):ℂ) ≠ 0 := by
    intro r hr
    exact_mod_cast ne_of_gt (sub_pos.mpr hr)
  change ContDiffOn ℝ _ (fun r : ℝ => ((r-c:ℝ):ℂ)⁻¹) (Ioi c)
  apply ContDiffOn.inv ?_ hn
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const)

theorem reciprocal_polyBound (c : ℝ) : PolyBound (reciprocal c) := by
  refine ⟨0,1,|c|+1,by norm_num,by positivity,?_⟩
  intro r hr
  have ht : 1 ≤ r-c := by linarith [le_abs_self c]
  have ht0 : 0 < r-c := by linarith
  simp only [reciprocal, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht0, pow_zero, mul_one]
  exact inv_le_one_of_one_le₀ ht

theorem reciprocal_euler (c r : ℝ) (hr : c < r) :
    eulerDeriv (reciprocal c) r = -reciprocal c r-(c:ℂ)*(reciprocal c r)^2 := by
  have hn : ((r-c:ℝ):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr hr)
  have hd := (((hasDerivAt_id r).sub_const c).ofReal_comp).inv hn
  change (r:ℂ)*deriv (fun x : ℝ => ((x-c:ℝ):ℂ)⁻¹) r = _
  have hd' : deriv (fun x : ℝ => ((x-c:ℝ):ℂ)⁻¹) r = -1/((r-c:ℝ):ℂ)^2 := by
    simpa only [Pi.inv_def, id_eq, Complex.ofReal_one] using hd.deriv
  rw [hd']
  dsimp [reciprocal]
  push_cast
  field_simp
  ring

/-- Every shifted reciprocal has conormal bounds, proved by an explicit
Euler derivative polynomial -z-cz² and closure of finite expressions. -/
theorem polynomialConormal_reciprocal (c : ℝ) : PolynomialConormal (reciprocal c) := by
  let F : Fin 2 → ℕ → ℝ → ℂ := fun _ _ => reciprocal c
  let δ : Fin 2 → ℕ → ConormalExpr := fun _ _ =>
    .add (.mul (.const (-1)) (.var 0 0))
      (.mul (.const (-(c:ℂ))) (.mul (.var 0 0) (.var 0 0)))
  have hF : ∀ i n, ExteriorSmooth c (F i n) := fun _ _ => reciprocal_smooth c
  have hD : ∀ i n r, c < r → eulerDeriv (F i n) r=eval F (δ i n) r := by
    intro i n r hr
    simpa [F,δ,eval,pow_two,sub_eq_add_neg] using reciprocal_euler c r hr
  have hE : ∀ p r, c < r → eulerDeriv (eval F p) r=eval F (diffUsing δ p) r :=
    fun p => eval_diffUsing F c hF δ hD p
  have hB : ∀ p, PolyBound (eval F p) := eval_polyBound F (fun _ _ => reciprocal_polyBound c)
  exact conormal_of_euler_family (eval F) (diffUsing δ) c hE hB (.var 0 0)
end KN.Energy

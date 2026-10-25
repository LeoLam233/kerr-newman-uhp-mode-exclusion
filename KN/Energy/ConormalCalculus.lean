import KN.Energy.ConormalReciprocal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

open Set
namespace KN.Energy
open KN.Boundary ConormalExpr

theorem polynomialConormal_congr_exterior {f g : ℝ → ℂ} (rp : ℝ)
    (hf : PolynomialConormal f) (hfg : ∀ r > rp, f r=g r) : PolynomialConormal g := by
  have he : ∀ j : ℕ, ∀ r > rp, (eulerDeriv^[j]) f r=(eulerDeriv^[j]) g r := by
    intro j
    induction j with
    | zero => exact hfg
    | succ j ih =>
      simpa only [Function.iterate_succ_apply'] using euler_congr_exterior ih
  intro j
  exact polyBound_congr_exterior rp (hf j) (he j)

/-- Closure under ordinary differentiation follows from D=r⁻¹ E, not from
an unjustified inference that derivatives of polynomially bounded functions
are polynomially bounded. -/
theorem polynomialConormal_deriv (rp : ℝ) (f : ℝ → ℂ)
    (hfs : ExteriorSmooth rp f) (hf : PolynomialConormal f) : PolynomialConormal (deriv f) := by
  let R := max rp 0
  have hrec : ExteriorSmooth R (reciprocal 0) :=
    (reciprocal_smooth 0).mono (Ioi_subset_Ioi (le_max_right _ _))
  have hef : ExteriorSmooth R (eulerDeriv f) :=
    (euler_smooth hfs).mono (Ioi_subset_Ioi (le_max_left _ _))
  have hm := (polynomialConormal_add_mul R (reciprocal 0) (eulerDeriv f)
    hrec hef (polynomialConormal_reciprocal 0) (polynomialConormal_euler hf)).2
  apply polynomialConormal_congr_exterior R hm
  intro r hr
  have hr0 : r ≠ 0 := ne_of_gt ((le_max_right rp 0).trans_lt hr)
  dsimp [reciprocal,eulerDeriv]
  rw [sub_zero]
  simp [hr0]

theorem polynomialConormal_const (c : ℂ) : PolynomialConormal (fun _ : ℝ => c) := by
  let F : Fin 2 → ℕ → ℝ → ℂ := fun _ _ _ => 0
  have hF : ∀ i n, ExteriorSmooth 0 (F i n) := fun _ _ => contDiffOn_const
  have hD : ∀ i n r, 0 < r → eulerDeriv (F i n) r=F i (n+1) r := by
    intros
    simp [F,eulerDeriv]
  exact eval_conormal F 0 hF hD (fun _ _ => polyBound_const 0) (.const c)

theorem polynomialConormal_coordinate : PolynomialConormal (fun r : ℝ => (r:ℂ)) := by
  let F : Fin 2 → ℕ → ℝ → ℂ := fun _ _ r => r
  have hF : ∀ i n, ExteriorSmooth 0 (F i n) := fun _ _ => Complex.ofRealCLM.contDiff.contDiffOn
  have hD : ∀ i n r, 0 < r → eulerDeriv (F i n) r=F i (n+1) r := by
    intro i n r _
    change r • deriv (fun x : ℝ => (x:ℂ)) r = (r:ℂ)
    have hd : deriv (fun x : ℝ => (x:ℂ)) r = 1 := by
      simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id r).ofReal_comp.deriv
    rw [hd]
    simp
  have hB : ∀ i n, PolyBound (F i n) := by
    intro i n
    refine ⟨1,1,0,by norm_num,le_rfl,?_⟩
    intro r _
    simp only [F,Complex.norm_real,Real.norm_eq_abs,pow_one,one_mul]
    linarith
  exact eval_conormal F 0 hF hD hB (.var 0 0)

theorem polynomialConormal_pow (rp : ℝ) (f : ℝ → ℂ)
    (hfs : ExteriorSmooth rp f) (hf : PolynomialConormal f) (n : ℕ) :
    PolynomialConormal (fun r => f r^n) := by
  induction n with
  | zero => simpa only [pow_zero] using polynomialConormal_const 1
  | succ n ih =>
    simpa only [pow_succ] using (polynomialConormal_add_mul rp (fun r => f r^n) f
      (hfs.pow n) hfs ih hf).2

/-- Every polynomial coefficient in the physical radial operators is conormal. -/
theorem polynomialConormal_polynomial (p : Polynomial ℂ) :
    PolynomialConormal (fun r : ℝ => p.eval (r:ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hps : ExteriorSmooth 0 (fun r : ℝ => p.eval (r:ℂ)) := by
      exact ((p.contDiff_aeval _).restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff).contDiffOn
    have hqs : ExteriorSmooth 0 (fun r : ℝ => q.eval (r:ℂ)) := by
      exact ((q.contDiff_aeval _).restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff).contDiffOn
    simpa only [Polynomial.eval_add] using (polynomialConormal_add_mul 0 _ _ hps hqs hp hq).1
  | monomial n a =>
    have hpow := polynomialConormal_pow 0 (fun r : ℝ => (r:ℂ))
      Complex.ofRealCLM.contDiff.contDiffOn polynomialConormal_coordinate n
    have hm := (polynomialConormal_add_mul 0 (fun _ : ℝ => a) (fun r : ℝ => (r:ℂ)^n)
      contDiffOn_const (Complex.ofRealCLM.contDiff.contDiffOn.pow n) (polynomialConormal_const a) hpow).2
    simpa only [Polynomial.eval_monomial] using hm
end KN.Energy

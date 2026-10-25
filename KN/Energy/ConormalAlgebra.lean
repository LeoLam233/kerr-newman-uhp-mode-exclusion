import KN.Boundary.Radial
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

open Set
namespace KN.Energy
open KN.Boundary

/-- Zeroth-order polynomial growth, with the same explicit quantifiers as
PolynomialConormal. -/
def PolyBound (f : ℝ → ℂ) : Prop :=
  ∃ (N : ℕ) (C R : ℝ), 0 ≤ C ∧ 0 ≤ R ∧
    ∀ r, R ≤ r → ‖f r‖ ≤ C*(1+|r|)^N

theorem polyBound_const (c : ℂ) : PolyBound (fun _ => c) :=
  ⟨0, ‖c‖, 0, norm_nonneg _, le_rfl, by simp⟩

theorem polyBound_add {f g : ℝ → ℂ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun r => f r+g r) := by
  obtain ⟨N,C,R,hC,hR,hf⟩ := hf
  obtain ⟨K,D,S,hD,hS,hg⟩ := hg
  refine ⟨N+K,C+D,max R S,add_nonneg hC hD,le_max_of_le_left hR,?_⟩
  intro r hr
  have hb : 1 ≤ 1+|r| := by linarith [abs_nonneg r]
  have hN : (1+|r|)^N ≤ (1+|r|)^(N+K) := pow_le_pow_right₀ hb (Nat.le_add_right _ _)
  have hK : (1+|r|)^K ≤ (1+|r|)^(N+K) := pow_le_pow_right₀ hb (Nat.le_add_left _ _)
  calc
    ‖f r+g r‖ ≤ ‖f r‖+‖g r‖ := norm_add_le _ _
    _ ≤ C*(1+|r|)^N+D*(1+|r|)^K := add_le_add (hf r ((le_max_left _ _).trans hr)) (hg r ((le_max_right _ _).trans hr))
    _ ≤ (C+D)*(1+|r|)^(N+K) := by nlinarith [mul_le_mul_of_nonneg_left hN hC,mul_le_mul_of_nonneg_left hK hD]

theorem polyBound_mul {f g : ℝ → ℂ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun r => f r*g r) := by
  obtain ⟨N,C,R,hC,hR,hf⟩ := hf
  obtain ⟨K,D,S,hD,hS,hg⟩ := hg
  refine ⟨N+K,C*D,max R S,mul_nonneg hC hD,le_max_of_le_left hR,?_⟩
  intro r hr
  rw [norm_mul]
  calc
    ‖f r‖*‖g r‖ ≤ (C*(1+|r|)^N)*(D*(1+|r|)^K) :=
      mul_le_mul (hf r ((le_max_left _ _).trans hr)) (hg r ((le_max_right _ _).trans hr)) (norm_nonneg _) (by positivity)
    _ = C*D*(1+|r|)^(N+K) := by rw [pow_add]; ring

theorem polyBound_congr_exterior {f g : ℝ → ℂ} (rp : ℝ) (hf : PolyBound f)
    (hfg : ∀ r > rp, f r=g r) : PolyBound g := by
  obtain ⟨N,C,R,hC,hR,hf⟩ := hf
  refine ⟨N,C,max R (rp+1),hC,le_max_of_le_left hR,?_⟩
  intro r hr
  have hrp : rp < r := by have := (le_max_right R (rp+1)).trans hr; linarith
  rw [← hfg r hrp]
  exact hf r ((le_max_left _ _).trans hr)

abbrev ExteriorSmooth (rp : ℝ) (f : ℝ → ℂ) :=
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi rp)

theorem euler_smooth {rp : ℝ} {f : ℝ → ℂ} (hf : ExteriorSmooth rp f) :
    ExteriorSmooth rp (eulerDeriv f) := by
  exact contDiffOn_id.smul (hf.deriv_of_isOpen isOpen_Ioi (by simp))

theorem euler_iterate_smooth {rp : ℝ} {f : ℝ → ℂ} (hf : ExteriorSmooth rp f) (j : ℕ) :
    ExteriorSmooth rp ((eulerDeriv^[j]) f) := by
  induction j with
  | zero => exact hf
  | succ j ih => simpa only [Function.iterate_succ_apply'] using euler_smooth ih

theorem euler_congr_exterior {f g : ℝ → ℂ} {rp : ℝ} (h : ∀ r > rp, f r=g r) :
    ∀ r > rp, eulerDeriv f r=eulerDeriv g r := by
  intro r hr
  dsimp [eulerDeriv]
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact h x hx

/-- Finite expression syntax is used solely to prove closure under all Euler
iterations without assuming or invoking an unproved Leibniz formula. -/
inductive ConormalExpr where
  | const : ℂ → ConormalExpr
  | var : Fin 2 → ℕ → ConormalExpr
  | add : ConormalExpr → ConormalExpr → ConormalExpr
  | mul : ConormalExpr → ConormalExpr → ConormalExpr

namespace ConormalExpr
noncomputable def eval (F : Fin 2 → ℕ → ℝ → ℂ) : ConormalExpr → ℝ → ℂ
  | .const c => fun _ => c
  | .var i n => F i n
  | .add p q => fun r => eval F p r+eval F q r
  | .mul p q => fun r => eval F p r*eval F q r

def diff : ConormalExpr → ConormalExpr
  | .const _ => .const 0
  | .var i n => .var i (n+1)
  | .add p q => .add (diff p) (diff q)
  | .mul p q => .add (.mul (diff p) q) (.mul p (diff q))

theorem eval_polyBound (F : Fin 2 → ℕ → ℝ → ℂ) (hF : ∀ i n, PolyBound (F i n))
    (p : ConormalExpr) : PolyBound (eval F p) := by
  induction p with
  | const c => exact polyBound_const c
  | var i n => exact hF i n
  | add p q hp hq => exact polyBound_add hp hq
  | mul p q hp hq => exact polyBound_mul hp hq

theorem eval_smooth (F : Fin 2 → ℕ → ℝ → ℂ) (rp : ℝ)
    (hF : ∀ i n, ExteriorSmooth rp (F i n)) (p : ConormalExpr) : ExteriorSmooth rp (eval F p) := by
  induction p with
  | const c => exact contDiffOn_const
  | var i n => exact hF i n
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

theorem eval_diff (F : Fin 2 → ℕ → ℝ → ℂ) (rp : ℝ)
    (hF : ∀ i n, ExteriorSmooth rp (F i n))
    (hD : ∀ i n r, rp < r → eulerDeriv (F i n) r=F i (n+1) r)
    (p : ConormalExpr) : ∀ r > rp, eulerDeriv (eval F p) r=eval F (diff p) r := by
  induction p with
  | const c => intro r _; simp [eval, diff, eulerDeriv]
  | var i n => exact hD i n
  | add p q hp hq =>
    intro r hr
    have hpd := ((eval_smooth F rp hF p).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    have hqd := ((eval_smooth F rp hF q).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    change r • deriv (eval F p+eval F q) r = _
    rw [deriv_add hpd hqd, smul_add]
    exact congrArg₂ (·+·) (hp r hr) (hq r hr)
  | mul p q hp hq =>
    intro r hr
    have hpd := ((eval_smooth F rp hF p).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    have hqd := ((eval_smooth F rp hF q).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    change r • deriv (eval F p*eval F q) r = _
    rw [deriv_mul hpd hqd]
    change (r:ℂ)*(deriv (eval F p) r*eval F q r+eval F p r*deriv (eval F q) r)=_
    have hp' := hp r hr
    have hq' := hq r hr
    change (r:ℂ)*deriv (eval F p) r = eval F (diff p) r at hp'
    change (r:ℂ)*deriv (eval F q) r = eval F (diff q) r at hq'
    change _ = eval F (diff p) r*eval F q r+eval F p r*eval F (diff q) r
    rw [← hp', ← hq']
    ring
def diffUsing (δ : Fin 2 → ℕ → ConormalExpr) : ConormalExpr → ConormalExpr
  | .const _ => .const 0
  | .var i n => δ i n
  | .add p q => .add (diffUsing δ p) (diffUsing δ q)
  | .mul p q => .add (.mul (diffUsing δ p) q) (.mul p (diffUsing δ q))

theorem eval_diffUsing (F : Fin 2 → ℕ → ℝ → ℂ) (rp : ℝ)
    (hF : ∀ i n, ExteriorSmooth rp (F i n))
    (δ : Fin 2 → ℕ → ConormalExpr)
    (hD : ∀ i n r, rp < r → eulerDeriv (F i n) r=eval F (δ i n) r)
    (p : ConormalExpr) : ∀ r > rp, eulerDeriv (eval F p) r=eval F (diffUsing δ p) r := by
  induction p with
  | const c => intro r _; simp [eval, diffUsing, eulerDeriv]
  | var i n => exact hD i n
  | add p q hp hq =>
    intro r hr
    have hpd := ((eval_smooth F rp hF p).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    have hqd := ((eval_smooth F rp hF q).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    change r • deriv (eval F p+eval F q) r = _
    rw [deriv_add hpd hqd, smul_add]
    exact congrArg₂ (·+·) (hp r hr) (hq r hr)
  | mul p q hp hq =>
    intro r hr
    have hpd := ((eval_smooth F rp hF p).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    have hqd := ((eval_smooth F rp hF q).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    change r • deriv (eval F p*eval F q) r = _
    rw [deriv_mul hpd hqd]
    change (r:ℂ)*(deriv (eval F p) r*eval F q r+eval F p r*deriv (eval F q) r)=_
    have hp' := hp r hr
    have hq' := hq r hr
    change (r:ℂ)*deriv (eval F p) r = eval F (diffUsing δ p) r at hp'
    change (r:ℂ)*deriv (eval F q) r = eval F (diffUsing δ q) r at hq'
    change _ = eval F (diffUsing δ p) r*eval F q r+eval F p r*eval F (diffUsing δ q) r
    rw [← hp', ← hq']
    ring
theorem eval_iterate_diff (F : Fin 2 → ℕ → ℝ → ℂ) (rp : ℝ)
    (hF : ∀ i n, ExteriorSmooth rp (F i n))
    (hD : ∀ i n r, rp < r → eulerDeriv (F i n) r=F i (n+1) r)
    (p : ConormalExpr) (j : ℕ) :
    ∀ r > rp, (eulerDeriv^[j]) (eval F p) r=eval F ((diff^[j]) p) r := by
  induction j with
  | zero => intro r _; rfl
  | succ j ih =>
    intro r hr
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (euler_congr_exterior ih r hr).trans (eval_diff F rp hF hD ((diff^[j]) p) r hr)

theorem eval_conormal (F : Fin 2 → ℕ → ℝ → ℂ) (rp : ℝ)
    (hF : ∀ i n, ExteriorSmooth rp (F i n))
    (hD : ∀ i n r, rp < r → eulerDeriv (F i n) r=F i (n+1) r)
    (hB : ∀ i n, PolyBound (F i n)) (p : ConormalExpr) : PolynomialConormal (eval F p) := by
  intro j
  exact polyBound_congr_exterior rp (eval_polyBound F hB ((diff^[j]) p))
    (fun r hr => (eval_iterate_diff F rp hF hD p j r hr).symm)
end ConormalExpr

/-- Conormal fields form an algebra on every exterior smooth domain. -/
theorem polynomialConormal_add_mul (rp : ℝ) (f g : ℝ → ℂ)
    (hfs : ExteriorSmooth rp f) (hgs : ExteriorSmooth rp g)
    (hf : PolynomialConormal f) (hg : PolynomialConormal g) :
    PolynomialConormal (fun r => f r+g r) ∧ PolynomialConormal (fun r => f r*g r) := by
  let F : Fin 2 → ℕ → ℝ → ℂ := fun i n => if i=0 then (eulerDeriv^[n]) f else (eulerDeriv^[n]) g
  have hF : ∀ i n, ExteriorSmooth rp (F i n) := by
    intro i n
    dsimp [F]
    split
    · exact euler_iterate_smooth hfs n
    · exact euler_iterate_smooth hgs n
  have hD : ∀ i n r, rp < r → eulerDeriv (F i n) r=F i (n+1) r := by
    intro i n r _
    dsimp [F]
    split
    · exact congrFun ((Function.iterate_succ_apply' eulerDeriv n f).symm.trans
        (Function.iterate_succ_apply eulerDeriv n f)) r
    · exact congrFun ((Function.iterate_succ_apply' eulerDeriv n g).symm.trans
        (Function.iterate_succ_apply eulerDeriv n g)) r
  have hB : ∀ i n, PolyBound (F i n) := by
    intro i n
    dsimp [F]
    split
    · exact hf n
    · exact hg n
  constructor
  · simpa [ConormalExpr.eval, F] using ConormalExpr.eval_conormal F rp hF hD hB
      (.add (.var 0 0) (.var 1 0))
  · simpa [ConormalExpr.eval, F] using ConormalExpr.eval_conormal F rp hF hD hB
      (.mul (.var 0 0) (.var 1 0))

theorem polynomialConormal_euler {f : ℝ → ℂ} (hf : PolynomialConormal f) :
    PolynomialConormal (eulerDeriv f) := by
  intro j
  simpa only [Function.iterate_succ_apply] using hf (j+1)

/-- A family closed under the actual Euler derivative and polynomially bounded
is conormal. The identity is required pointwise on an open exterior, not as an
abstract assumed derivation action. -/
theorem conormal_of_euler_family {ι : Type*} (G : ι → ℝ → ℂ) (next : ι → ι) (rp : ℝ)
    (hE : ∀ i r, rp < r → eulerDeriv (G i) r=G (next i) r)
    (hB : ∀ i, PolyBound (G i)) (i : ι) : PolynomialConormal (G i) := by
  have heq : ∀ j : ℕ, ∀ r > rp, (eulerDeriv^[j]) (G i) r=G ((next^[j]) i) r := by
    intro j
    induction j with
    | zero => intro r _; rfl
    | succ j ih =>
      intro r hr
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (euler_congr_exterior ih r hr).trans (hE _ r hr)
  intro j
  exact polyBound_congr_exterior rp (hB ((next^[j]) i)) (fun r hr => (heq j r hr).symm)

end KN.Energy

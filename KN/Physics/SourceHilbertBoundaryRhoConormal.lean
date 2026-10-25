import KN.Physics.SourceHilbertBoundaryRho
import KN.Analysis.ResolventBoundaryMap
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open Set Filter Topology
open scoped BoundedContinuousFunction ContDiff
namespace KN.Physics
open KN.Boundary
abbrev AngularCoefficient := ℝ →ᵇ ℂ

def coefficientEval (t : ℝ) : AngularCoefficient →L[ℂ] ℂ :=
  ({toFun := fun f => f t, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl} :
    AngularCoefficient →ₗ[ℂ] ℂ).mkContinuous 1 (fun f => by
      change ‖f t‖ ≤ 1*‖f‖
      simpa only [one_mul] using f.norm_coe_le_norm t)

lemma rhoReciprocal_euler (a r : ℝ) (hr : 0<r) :
    eulerDeriv (rhoReciprocal a) r = -rhoReciprocal a r+
      ((Complex.I*a) • angularCosine)*(rhoReciprocal a r)^2 := by
  have hs := (rhoReciprocal_smooth a).differentiableOn (by simp)
  have hd := (hs r hr).differentiableAt (Ioi_mem_nhds hr)
  ext t
  have he : (fun x => rhoReciprocal a x t) =ᶠ[𝓝 r]
      fun x => ((x:ℂ)+Complex.I*a*Real.cos t)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact rhoReciprocal_apply a x t hx
  have hn : (r:ℂ)+Complex.I*a*Real.cos t ≠ 0 := by
    simpa only [rhoCoefficient_apply] using rhoCoefficient_ne_zero a r t hr
  have hpt := (((hasDerivAt_id r).ofReal_comp).add_const (Complex.I*a*Real.cos t)).inv hn
  have hev := ((coefficientEval t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hd.hasDerivAt
  have heq : (deriv (rhoReciprocal a) r) t = -1/((r:ℂ)+Complex.I*a*Real.cos t)^2 := by
    calc
      _ = deriv (fun x => rhoReciprocal a x t) r := hev.deriv.symm
      _ = _ := by rw [he.deriv_eq]; simpa only [Pi.inv_def,Complex.ofReal_one,id_eq] using hpt.deriv
  change (r:ℂ)*(deriv (rhoReciprocal a) r t) = _
  rw [heq]
  simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.neg_apply,
    BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.pow_apply,
    BoundedContinuousFunction.smul_apply,rhoReciprocal_apply a r t hr]
  change _ = -((r:ℂ)+Complex.I*a*Real.cos t)⁻¹+
    (Complex.I*a*(Real.cos t:ℂ))*(((r:ℂ)+Complex.I*a*Real.cos t)⁻¹)^2
  field_simp
  ring

inductive RhoExpr where
  | const (c : AngularCoefficient)
  | atom
  | add (p q : RhoExpr)
  | mul (p q : RhoExpr)

namespace RhoExpr

def eval (a : ℝ) : RhoExpr → ℝ → AngularCoefficient
  | .const c => fun _ => c
  | .atom => rhoReciprocal a
  | .add p q => fun r => eval a p r+eval a q r
  | .mul p q => fun r => eval a p r*eval a q r

def diff (a : ℝ) : RhoExpr → RhoExpr
  | .const _ => .const 0
  | .atom => .add (.mul (.const (-1)) .atom)
    (.mul (.const ((Complex.I*a) • angularCosine)) (.mul .atom .atom))
  | .add p q => .add (diff a p) (diff a q)
  | .mul p q => .add (.mul (diff a p) q) (.mul p (diff a q))

lemma smooth (a : ℝ) (p : RhoExpr) : ContDiffOn ℝ ∞ (eval a p) (Ioi 0) := by
  induction p with
  | const c => exact contDiffOn_const
  | atom => exact rhoReciprocal_smooth a
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

lemma derivative (a : ℝ) (p : RhoExpr) : ∀r>0, eulerDeriv (eval a p) r=eval a (diff a p) r := by
  induction p with
  | const c => intro r _; simp [eval,diff,eulerDeriv]
  | atom => intro r hr; simpa [eval,diff,pow_two] using rhoReciprocal_euler a r hr
  | add p q hp hq =>
    intro r hr
    have hpd := ((smooth a p).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    have hqd := ((smooth a q).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    change r • deriv (eval a p+eval a q) r=_
    rw [deriv_add hpd hqd,smul_add]
    exact congrArg₂ (·+·) (hp r hr) (hq r hr)
  | mul p q hp hq =>
    intro r hr
    have hpd := ((smooth a p).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    have hqd := ((smooth a q).differentiableOn (by simp) r hr).differentiableAt (Ioi_mem_nhds hr)
    change r • deriv (eval a p*eval a q) r=_
    rw [deriv_mul hpd hqd,smul_add]
    rw [← smul_mul_assoc r (deriv (eval a p) r) (eval a q r),
      ← mul_smul_comm r (eval a p r) (deriv (eval a q) r)]
    exact congrArg₂ (·+·) (congrArg (fun z => z*eval a q r) (hp r hr))
      (congrArg (fun z => eval a p r*z) (hq r hr))

lemma bounded (a : ℝ) (p : RhoExpr) : ∃ C : ℝ, 0≤C ∧ ∀r≥1, ‖eval a p r‖≤C := by
  induction p with
  | const c => exact ⟨‖c‖,norm_nonneg _,fun _ _ => le_rfl⟩
  | atom =>
    refine ⟨1,by norm_num,fun r hr => ?_⟩
    exact (rhoReciprocal_norm_le a r (by linarith)).trans (inv_le_one_of_one_le₀ hr)
  | add p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C+D,add_nonneg hC hD,fun r hr => (norm_add_le _ _).trans (add_le_add (hp r hr) (hq r hr))⟩
  | mul p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C*D,mul_nonneg hC hD,fun r hr => (norm_mul_le _ _).trans
      (mul_le_mul (hp r hr) (hq r hr) (norm_nonneg _) hC)⟩

lemma iterate_derivative (a : ℝ) (p : RhoExpr) (n : ℕ) :
    ∀r>0, (eulerDeriv^[n]) (eval a p) r=eval a ((diff a)^[n] p) r := by
  induction n with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r hr
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have he : (eulerDeriv^[n]) (eval a p) =ᶠ[𝓝 r] eval a ((diff a)^[n] p) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact ih x hx
    change r • deriv ((eulerDeriv^[n]) (eval a p)) r=_
    rw [he.deriv_eq]
    exact derivative a _ r hr
end RhoExpr

/-- Uniform angular control of every radial Euler derivative of rho inverse. -/
theorem rhoReciprocal_conormal (a : ℝ) : PolynomialConormal (rhoReciprocal a) := by
  intro n
  obtain ⟨C,hC,hb⟩ := RhoExpr.bounded a ((RhoExpr.diff a)^[n] RhoExpr.atom)
  refine ⟨0,C,1,hC,by norm_num,fun r hr => ?_⟩
  change ‖(eulerDeriv^[n]) (RhoExpr.eval a .atom) r‖≤_
  rw [RhoExpr.iterate_derivative a .atom n r (by linarith)]
  simpa only [pow_zero,mul_one] using hb r hr

end KN.Physics

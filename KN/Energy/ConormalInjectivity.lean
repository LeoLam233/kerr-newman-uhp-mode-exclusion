import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

open Set Filter Polynomial
open scoped Topology
namespace KN.Energy

/-- Polynomial antiderivatives over ℂ, proved explicitly coefficientwise. -/
theorem polynomial_has_primitive (P : Polynomial ℂ) :
    ∃ Q : Polynomial ℂ, Q.derivative = P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨P', hP'⟩ := hP
    obtain ⟨Q', hQ'⟩ := hQ
    exact ⟨P'+Q', by simp [hP', hQ']⟩
  | monomial n a =>
    refine ⟨Polynomial.monomial (n+1) (a/(n+1:ℂ)), ?_⟩
    have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [hn]

/-- The kernel of an iterated derivative on an exterior interval consists
of genuine polynomials, proved by successive polynomial antiderivatives and
the mean-value theorem. No external ODE or polynomial-kernel interface. -/
theorem iteratedDeriv_zero_polynomial (n : ℕ) (rp : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi rp))
    (hz : ∀ r > rp, iteratedDeriv n f r = 0) :
    ∃ P : Polynomial ℂ, ∀ r > rp, f r = P.eval (r:ℂ) := by
  induction n generalizing f with
  | zero => exact ⟨0, by simpa only [iteratedDeriv_zero, Polynomial.eval_zero] using hz⟩
  | succ n ih =>
    have hdf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) (Ioi rp) :=
      hf.deriv_of_isOpen isOpen_Ioi (by simp)
    have hdz : ∀ r > rp, iteratedDeriv n (deriv f) r = 0 := by
      simpa only [iteratedDeriv_succ'] using hz
    obtain ⟨P, hP⟩ := ih (deriv f) hdf hdz
    obtain ⟨Q, hQ⟩ := polynomial_has_primitive P
    have hQd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Q.eval (y:ℂ)) (P.eval (x:ℂ)) x := by
      intro x
      simpa [hQ] using (Q.hasDerivAt (x:ℂ)).comp_ofReal
    have hfd : DifferentiableOn ℝ f (Ioi rp) := hf.differentiableOn (by simp)
    have hdiff : DifferentiableOn ℝ (fun x : ℝ => f x-Q.eval (x:ℂ)) (Ioi rp) :=
      hfd.sub (fun x _ => (hQd x).differentiableAt.differentiableWithinAt)
    have hzero : EqOn (deriv (fun x : ℝ => f x-Q.eval (x:ℂ))) 0 (Ioi rp) := by
      intro x hx
      have hx' := (hfd x hx).differentiableAt (Ioi_mem_nhds hx)
      simpa [hP x hx, Pi.sub_def] using (hx'.hasDerivAt.sub (hQd x)).deriv
    obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
      (convex_Ioi rp).isPreconnected hdiff hzero
    refine ⟨Q+Polynomial.C c, ?_⟩
    intro r hr
    simpa only [Polynomial.eval_add, Polynomial.eval_C, add_comm] using (sub_eq_iff_eq_add.mp (hc r hr))

/-- A complex polynomial on the real axis cannot decay at +∞ unless zero. -/
theorem polynomial_zero_of_real_axis_decay (P : Polynomial ℂ)
    (hP : Tendsto (fun r : ℝ => P.eval (r:ℂ)) atTop (𝓝 0)) : P = 0 := by
  have hd : P.degree ≤ 0 := by
    by_contra hn
    have hp : 0 < P.degree := lt_of_not_ge hn
    have hr : Tendsto (fun r : ℝ => ‖(r:ℂ)‖) atTop atTop := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop
    have hnorm := P.tendsto_norm_atTop hp hr
    have hzero : Tendsto (fun r : ℝ => ‖P.eval (r:ℂ)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hP.norm
    exact not_tendsto_atTop_of_tendsto_nhds hzero hnorm
  rw [P.eq_C_of_degree_le_zero hd] at hP ⊢
  have hc : P.coeff 0 = 0 := tendsto_nhds_unique
    tendsto_const_nhds (by simpa only [Polynomial.eval_C] using hP)
  simp [hc]

/-- Elementary injectivity sufficient for the Kerr spin reversal. Unlike the
asymptotic expansion route, this requires only f→0, not differentiated
expansions or a nonzero leading coefficient. -/
theorem iteratedDeriv_injective_on_decaying (n : ℕ) (rp : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi rp))
    (hz : ∀ r > rp, iteratedDeriv n f r = 0)
    (hdecay : Tendsto f atTop (𝓝 0)) : ∀ r > rp, f r = 0 := by
  obtain ⟨P, hP⟩ := iteratedDeriv_zero_polynomial n rp f hf hz
  have hPe : f =ᶠ[atTop] (fun r : ℝ => P.eval (r:ℂ)) := by
    filter_upwards [eventually_gt_atTop rp] with r hr
    exact hP r hr
  have hzero := polynomial_zero_of_real_axis_decay P (hdecay.congr' hPe)
  intro r hr
  simpa [hzero] using hP r hr
end KN.Energy

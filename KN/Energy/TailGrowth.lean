import KN.Energy.ConormalPhysical
import KN.Energy.ExponentialDomination
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
open Filter Set Asymptotics
namespace KN.Energy
open KN.Boundary

def ExpPolyGrowth (k : ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ N : ℕ, f =O[atTop] (fun r : ℝ => (1+|r|)^N*Real.exp (k*r))

theorem polyBound_isBigO {f : ℝ → ℂ} (hf : PolyBound f) :
    ∃ N : ℕ, f =O[atTop] (fun r : ℝ => (1+|r|)^N) := by
  obtain ⟨N,C,R,_,_,h⟩ := hf
  refine ⟨N,isBigO_iff.mpr ⟨C,?_⟩⟩
  filter_upwards [eventually_ge_atTop R] with r hr
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (by positivity : 0 ≤ 1+|r|)] using h r hr

theorem polyBound_of_norm_le {f g : ℝ → ℂ} (hg : PolyBound g)
    (h : ∀ᶠ r in atTop, ‖f r‖ ≤ ‖g r‖) : PolyBound f := by
  obtain ⟨N,C,R,hC,hR,hg⟩ := hg
  obtain ⟨S,hS⟩ := eventually_atTop.mp h
  refine ⟨N,C,max R S,hC,le_max_of_le_left hR,?_⟩
  intro r hr
  exact (hS r ((le_max_right _ _).trans hr)).trans (hg r ((le_max_left _ _).trans hr))

theorem polynomial_exponential_domination_atTop (N : ℕ) (k : ℝ) (hk : 0 < k) :
    (fun r : ℝ => (1+|r|)^N * Real.exp (-2*k*r)) =O[atTop]
      (fun r : ℝ => Real.exp (-k*r)) := by
  have h := (polynomial_exponential_domination N k hk).comp_tendsto tendsto_neg_atTop_atBot
  change (fun r : ℝ => (1+|-r|)^N * Real.exp (2*k*(-r))) =O[atTop]
    (fun r : ℝ => Real.exp (k*(-r))) at h
  simpa only [abs_neg, mul_neg, neg_mul] using h

theorem expPolyGrowth_damping {k : ℝ} {f : ℝ → ℂ} (hf : ExpPolyGrowth k f)
    (β : ℝ) (hb : β+k < 0) :
    (fun r => (Real.exp (β*r):ℂ)*f r) =O[atTop]
      (fun r : ℝ => Real.exp (((β+k)/2)*r)) := by
  obtain ⟨N,hN⟩ := hf
  have he : (fun r : ℝ => (Real.exp (β*r):ℂ)) =O[atTop] (fun r : ℝ => Real.exp (β*r)) := by
    apply IsBigO.of_norm_left
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (isBigO_refl (fun r : ℝ => Real.exp (β*r)) atTop)
  have hh := he.mul hN
  have heq : (fun r : ℝ => Real.exp (β*r)*((1+|r|)^N*Real.exp (k*r))) =
      (fun r : ℝ => (1+|r|)^N*Real.exp ((β+k)*r)) := by
    funext r
    rw [add_mul,Real.exp_add]
    ring
  rw [heq] at hh
  have hd := polynomial_exponential_domination_atTop N (-(β+k)/2) (by linarith)
  rw [show -2*(-(β+k)/2)=β+k by ring, show -(-(β+k)/2)=(β+k)/2 by ring] at hd
  exact hh.trans hd

theorem expPolyGrowth_of_norm_exp_mul (k : ℝ) (f G : ℝ → ℂ)
    (hG : PolyBound G)
    (h : ∀ᶠ r in atTop, ‖f r‖ = Real.exp (k*r)*‖G r‖) : ExpPolyGrowth k f := by
  obtain ⟨N,C,R,_,_,hG⟩ := hG
  refine ⟨N,isBigO_iff.mpr ⟨C,?_⟩⟩
  filter_upwards [h,eventually_ge_atTop R] with r hr hR
  rw [hr]
  have hn : 0 ≤ (1+|r|)^N*Real.exp (k*r) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  nlinarith [mul_le_mul_of_nonneg_left (hG r hR) (Real.exp_pos (k*r)).le]

theorem ExpPolyGrowth.mul_poly {k : ℝ} {f g : ℝ → ℂ}
    (hf : ExpPolyGrowth k f) (hg : PolyBound g) :
    ExpPolyGrowth k (fun r => f r*g r) := by
  obtain ⟨N,hN⟩ := hf
  obtain ⟨M,hM⟩ := polyBound_isBigO hg
  refine ⟨N+M,?_⟩
  convert hN.mul hM using 1
  ext r
  rw [pow_add]
  ring

theorem delta_eventually_one_le (b : KN.Background) :
    ∀ᶠ r in atTop, 1 ≤ b.Delta r := by
  filter_upwards [eventually_ge_atTop (max (b.rPlus+1) (b.rMinus+1))] with r hr
  have hp : 1 ≤ r-b.rPlus := by have := (le_max_left _ _).trans hr; linarith
  have hm : 1 ≤ r-b.rMinus := by have := (le_max_right _ _).trans hr; linarith
  rw [b.delta_factor]
  nlinarith

theorem delta_rpow_polyBound (b : KN.Background) (q : ℝ) (hq : q ≤ 1) :
    PolyBound (fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ)) := by
  apply polyBound_of_norm_le (f := fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ))
    (g := fun r : ℝ => (b.Delta r:ℂ)) ((delta_conormal b) 0)
  filter_upwards [delta_eventually_one_le b] with r hr
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |(b.Delta r)^q| ≤ |b.Delta r|
  rw [abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hr) q),
    abs_of_nonneg (le_trans zero_le_one hr)]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr hq

theorem exp_poly_degree_mono (k : ℝ) (N M : ℕ) (hNM : N ≤ M) :
    (fun r : ℝ => (1+|r|)^N*Real.exp (k*r)) =O[atTop]
      (fun r : ℝ => (1+|r|)^M*Real.exp (k*r)) := by
  refine isBigO_iff.mpr ⟨1,Filter.Eventually.of_forall (fun r => ?_)⟩
  simp only [one_mul,Real.norm_eq_abs,abs_mul,abs_pow,
    abs_of_pos (Real.exp_pos _),abs_of_nonneg (by positivity : 0 ≤ 1+|r|)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [abs_nonneg r] : 1 ≤ 1+|r|) hNM) (Real.exp_pos _).le

theorem ExpPolyGrowth.add {k : ℝ} {f g : ℝ → ℂ}
    (hf : ExpPolyGrowth k f) (hg : ExpPolyGrowth k g) :
    ExpPolyGrowth k (fun r => f r+g r) := by
  obtain ⟨N,hN⟩ := hf
  obtain ⟨M,hM⟩ := hg
  exact ⟨N+M, (hN.trans (exp_poly_degree_mono k N (N+M) (by omega))).add
    (hM.trans (exp_poly_degree_mono k M (N+M) (by omega)))⟩

theorem ExpPolyGrowth.congr {k : ℝ} {f g : ℝ → ℂ}
    (hf : ExpPolyGrowth k f) (he : f =ᶠ[atTop] g) : ExpPolyGrowth k g := by
  obtain ⟨N,hN⟩ := hf
  exact ⟨N,hN.congr' he Filter.EventuallyEq.rfl⟩

theorem ExpPolyGrowth.mul {k l : ℝ} {f g : ℝ → ℂ}
    (hf : ExpPolyGrowth k f) (hg : ExpPolyGrowth l g) :
    ExpPolyGrowth (k+l) (fun r => f r*g r) := by
  obtain ⟨N,hN⟩ := hf
  obtain ⟨M,hM⟩ := hg
  refine ⟨N+M,?_⟩
  convert hN.mul hM using 1
  ext r
  rw [pow_add,add_mul,Real.exp_add]
  ring

theorem shifted_rpow_polyBound (c p : ℝ) :
    PolyBound (fun r : ℝ => (((r-c)^p:ℝ):ℂ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge p
  have hp : PolyBound (fun r : ℝ => ((r-c:ℝ):ℂ)^N) := by
    have ht := polynomialConormal_polynomial ((Polynomial.X-Polynomial.C (c:ℂ))^N)
    simpa [PolyBound] using ht 0
  apply polyBound_of_norm_le hp
  filter_upwards [eventually_ge_atTop (c+1)] with r hr
  have hc : 1 ≤ r-c := by linarith
  simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hc) p),
    abs_of_nonneg (le_trans zero_le_one hc)]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hc hN

end KN.Energy

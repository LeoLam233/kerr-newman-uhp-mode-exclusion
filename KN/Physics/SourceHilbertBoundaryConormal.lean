import KN.Analysis.ResolventBoundaryMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace KN.Boundary

/-- Polynomial norm growth, for arbitrary normed targets. -/
def PolynomialBound {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) : Prop :=
  ∃ (N : ℕ) (C R : ℝ), 0 ≤ C ∧ 0 ≤ R ∧ ∀ r, R ≤ r → ‖f r‖ ≤ C*(1+|r|)^N

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

abbrev RadialSmooth (rp : ℝ) (f : ℝ → E) :=
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi rp)

omit [NormedSpace ℂ E] in
theorem PolynomialBound.add {f g : ℝ → E} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun r => f r+g r) := by
  obtain ⟨N,C,R,hC,hR,hf⟩ := hf
  obtain ⟨K,D,S,hD,hS,hg⟩ := hg
  refine ⟨N+K,C+D,max R S,add_nonneg hC hD,le_max_of_le_left hR,?_⟩
  intro r hr
  have hb : 1 ≤ 1+|r| := by linarith [abs_nonneg r]
  have hN := pow_le_pow_right₀ hb (Nat.le_add_right N K)
  have hK := pow_le_pow_right₀ hb (Nat.le_add_left K N)
  calc
    ‖f r+g r‖ ≤ ‖f r‖+‖g r‖ := norm_add_le _ _
    _ ≤ C*(1+|r|)^N+D*(1+|r|)^K := add_le_add
      (hf r ((le_max_left _ _).trans hr)) (hg r ((le_max_right _ _).trans hr))
    _ ≤ (C+D)*(1+|r|)^(N+K) := by
      nlinarith [mul_le_mul_of_nonneg_left hN hC,mul_le_mul_of_nonneg_left hK hD]

theorem PolynomialBound.bilinear (B : E →L[ℝ] F →L[ℝ] G) {f : ℝ → E} {g : ℝ → F}
    (hf : PolynomialBound f) (hg : PolynomialBound g) : PolynomialBound (fun r => B (f r) (g r)) := by
  obtain ⟨N,C,R,hC,hR,hf⟩ := hf
  obtain ⟨K,D,S,hD,hS,hg⟩ := hg
  refine ⟨N+K,‖B‖*C*D,max R S,mul_nonneg (mul_nonneg (norm_nonneg B) hC) hD,
    le_max_of_le_left hR,?_⟩
  intro r hr
  calc
    ‖B (f r) (g r)‖ ≤ ‖B‖*‖f r‖*‖g r‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖*(C*(1+|r|)^N)*(D*(1+|r|)^K) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hf r ((le_max_left _ _).trans hr)) (norm_nonneg B))
        (hg r ((le_max_right _ _).trans hr)) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

omit [NormedSpace ℂ E] in
theorem PolynomialBound.congr_exterior {f g : ℝ → E} (rp : ℝ) (hf : PolynomialBound f)
    (he : ∀ r>rp, f r=g r) : PolynomialBound g := by
  obtain ⟨N,C,R,hC,hR,hf⟩ := hf
  refine ⟨N,C,max R (rp+1),hC,le_max_of_le_left hR,?_⟩
  intro r hr
  have hre : rp<r := by have := (le_max_right R (rp+1)).trans hr; linarith
  rw [← he r hre]
  exact hf r ((le_max_left _ _).trans hr)

theorem euler_congr_on_exterior {f g : ℝ → E} {rp : ℝ} (he : ∀ r>rp, f r=g r) :
    ∀ r>rp, eulerDeriv f r=eulerDeriv g r := by
  intro r hr
  unfold eulerDeriv
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact he t ht

theorem euler_iterate_congr_exterior {f g : ℝ → E} {rp : ℝ}
    (he : ∀ r>rp, f r=g r) (n : ℕ) :
    ∀ r>rp, (eulerDeriv^[n]) f r=(eulerDeriv^[n]) g r := by
  induction n with
  | zero => exact he
  | succ n ih => simpa only [Function.iterate_succ_apply'] using euler_congr_on_exterior ih

theorem PolynomialConormal.congr_exterior {f g : ℝ → E} (rp : ℝ)
    (hf : PolynomialConormal f) (he : ∀ r>rp, f r=g r) : PolynomialConormal g := by
  intro n
  exact PolynomialBound.congr_exterior rp (hf n) (euler_iterate_congr_exterior he n)

theorem euler_add_exterior {rp : ℝ} {f g : ℝ → E} (hf : RadialSmooth rp f) (hg : RadialSmooth rp g) :
    ∀ r>rp, eulerDeriv (fun t => f t+g t) r=eulerDeriv f r+eulerDeriv g r := by
  intro r hr
  have hd := ((hf r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)
  have he := ((hg r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)
  change r • deriv (f+g) r=_
  rw [deriv_add hd he,smul_add]
  rfl

theorem euler_iterate_add_exterior {rp : ℝ} {f g : ℝ → E}
    (hf : RadialSmooth rp f) (hg : RadialSmooth rp g) (n : ℕ) :
    ∀ r>rp, (eulerDeriv^[n]) (fun t => f t+g t) r=
      (eulerDeriv^[n]) f r+(eulerDeriv^[n]) g r := by
  induction n with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r hr
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact (euler_congr_on_exterior ih r hr).trans
      (euler_add_exterior (eulerDeriv_iterate_contDiffOn hf n) (eulerDeriv_iterate_contDiffOn hg n) r hr)

theorem PolynomialConormal.add_on {rp : ℝ} {f g : ℝ → E}
    (hf : PolynomialConormal f) (hg : PolynomialConormal g)
    (hfs : RadialSmooth rp f) (hgs : RadialSmooth rp g) : PolynomialConormal (fun r => f r+g r) := by
  intro n
  exact PolynomialBound.congr_exterior rp (PolynomialBound.add (hf n) (hg n))
    (fun r hr => (euler_iterate_add_exterior hfs hgs n r hr).symm)

theorem euler_bilinear_exterior (B : E →L[ℝ] F →L[ℝ] G) {rp : ℝ}
    {f : ℝ → E} {g : ℝ → F} (hf : RadialSmooth rp f) (hg : RadialSmooth rp g) :
    ∀ r>rp, eulerDeriv (fun t => B (f t) (g t)) r=
      B (eulerDeriv f r) (g r)+B (f r) (eulerDeriv g r) := by
  intro r hr
  have hd := ((hf r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)
  have he := ((hg r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)
  have hh := (B.hasFDerivAt.comp_hasDerivAt r hd.hasDerivAt).clm_apply he.hasDerivAt
  dsimp only [Function.comp_def] at hh
  unfold eulerDeriv
  rw [hh.deriv,smul_add]
  simp only [map_smul,smul_apply]

theorem bilinear_radialSmooth (B : E →L[ℝ] F →L[ℝ] G) {rp : ℝ}
    {f : ℝ → E} {g : ℝ → F} (hf : RadialSmooth rp f) (hg : RadialSmooth rp g) :
    RadialSmooth rp (fun t => B (f t) (g t)) :=
  (B.contDiff.comp_contDiffOn hf).clm_apply hg

theorem PolynomialConormal.euler {f : ℝ → E} (hf : PolynomialConormal f) :
    PolynomialConormal (eulerDeriv f) := by
  intro n
  simpa only [Function.iterate_succ_apply] using hf (n+1)

/-- Every Euler iterate of a continuous bilinear product has polynomial growth.
The induction uses the actual derivative product rule, not an assumed Leibniz
formula or an inference from zeroth-order bounds. -/
theorem PolynomialConormal.bilinear_on (B : E →L[ℝ] F →L[ℝ] G) {rp : ℝ}
    {f : ℝ → E} {g : ℝ → F} (hf : PolynomialConormal f) (hg : PolynomialConormal g)
    (hfs : RadialSmooth rp f) (hgs : RadialSmooth rp g) :
    PolynomialConormal (fun r => B (f r) (g r)) := by
  intro n
  induction n generalizing f g with
  | zero => exact PolynomialBound.bilinear B (hf 0) (hg 0)
  | succ n ih =>
    have h1 := ih hf.euler hg (eulerDeriv_contDiffOn hfs) hgs
    have h2 := ih hf hg.euler hfs (eulerDeriv_contDiffOn hgs)
    have hb := PolynomialBound.add h1 h2
    apply PolynomialBound.congr_exterior rp hb
    intro r hr
    rw [Function.iterate_succ_apply]
    have he := euler_iterate_congr_exterior (euler_bilinear_exterior B hfs hgs) n r hr
    have ha := euler_iterate_add_exterior
      (bilinear_radialSmooth B (eulerDeriv_contDiffOn hfs) hgs)
      (bilinear_radialSmooth B hfs (eulerDeriv_contDiffOn hgs)) n r hr
    exact (he.trans ha).symm

theorem PolynomialConormal.smul_on {rp : ℝ} {f : ℝ → ℂ} {g : ℝ → E}
    (hf : PolynomialConormal f) (hg : PolynomialConormal g)
    (hfs : RadialSmooth rp f) (hgs : RadialSmooth rp g) :
    PolynomialConormal (fun r => f r • g r) :=
  PolynomialConormal.bilinear_on (ContinuousLinearMap.lsmul ℝ ℂ) hf hg hfs hgs

theorem PolynomialConormal.const (c : E) : PolynomialConormal (fun _ : ℝ => c) := by
  have he : ∀ n : ℕ, (eulerDeriv^[n+1]) (fun _ : ℝ => c)=0 := by
    intro n
    induction n with
    | zero => funext r; simp [eulerDeriv]
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      funext r
      simp [eulerDeriv]
  intro n
  cases n with
  | zero => exact ⟨0,‖c‖,0,norm_nonneg _,le_rfl,by simp⟩
  | succ n => rw [he n]; exact ⟨0,0,0,le_rfl,le_rfl,by simp⟩

theorem PolynomialConormal.neg_on {rp : ℝ} {f : ℝ → E}
    (hf : PolynomialConormal f) (hfs : RadialSmooth rp f) :
    PolynomialConormal (fun r => -f r) := by
  simpa using hf.map_on hfs (-ContinuousLinearMap.id ℂ E)

theorem PolynomialConormal.sub_on {rp : ℝ} {f g : ℝ → E}
    (hf : PolynomialConormal f) (hg : PolynomialConormal g)
    (hfs : RadialSmooth rp f) (hgs : RadialSmooth rp g) :
    PolynomialConormal (fun r => f r-g r) := by
  simpa only [sub_eq_add_neg] using hf.add_on (hg.neg_on hgs) hfs hgs.neg

theorem PolynomialConormal.congr_atTop {f g : ℝ → E} (hf : PolynomialConormal f)
    (he : f =ᶠ[atTop] g) : PolynomialConormal g := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  exact hf.congr_exterior R (fun r hr => hR r hr.le)

end KN.Boundary

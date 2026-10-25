import KN.Analysis.SmoothPrimitive
import KN.Boundary.Multiplier
import KN.Boundary.HorizonExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
open Set
namespace KN.Boundary

def positivePower (rp : ℝ) (α : ℂ) (r : ℝ) : ℂ :=
  Complex.exp ((Real.log (r-rp):ℂ)*α)

theorem positivePower_eq_cpow (rp r : ℝ) (α : ℂ) (hr : rp < r) :
    positivePower rp α r = ((r-rp:ℝ):ℂ)^α := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr)))]
  simp only [positivePower, Complex.ofReal_log (sub_nonneg.mpr hr.le)]

theorem positivePower_hasDerivAt (rp r : ℝ) (α : ℂ) (hr : rp < r) :
    HasDerivAt (positivePower rp α)
      (positivePower rp α r * (α / ((r-rp:ℝ):ℂ))) r := by
  have hl := (((hasDerivAt_id r).sub_const rp).log (ne_of_gt (sub_pos.mpr hr))).ofReal_comp
  convert (hl.mul_const α).cexp using 1
  · rfl
  · simp only [positivePower, id_eq, Complex.ofReal_div, Complex.ofReal_one]
    ring

/-- A regular singular logarithmic derivative gives an actual smooth nonzero factor,
on a neighborhood extending across the singular endpoint. -/
theorem factor_of_logarithmic_derivative (lo rp : ℝ) (hlo : lo < rp)
    (α : ℂ) (p h : ℝ → ℂ)
    (hh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) h (Ioi lo))
    (hp : ∀ r ∈ Ioi rp, p r ≠ 0)
    (hd : ∀ r ∈ Ioi rp, HasDerivAt p (p r*(α/((r-rp:ℝ):ℂ)+h r)) r) :
    ∃ f : ℝ → ℂ,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi lo) ∧
      (∀ r, f r ≠ 0) ∧
      ∀ r ∈ Ioi rp, p r = ((r-rp:ℝ):ℂ)^α * f r := by
  let g := fun r => positivePower rp α r * KN.Analysis.expPrimitive h rp r
  have hgd : ∀ r ∈ Ioi rp,
      HasDerivAt g (g r*(α/((r-rp:ℝ):ℂ)+h r)) r := by
    intro r hr
    convert (positivePower_hasDerivAt rp r α hr).mul
      (KN.Analysis.expPrimitive_hasDerivAt h lo rp r hh.continuousOn hlo (hlo.trans hr)) using 1
    dsimp [g]
    ring
  have hgn : ∀ r ∈ Ioi rp, g r ≠ 0 := by
    intro r _
    exact mul_ne_zero (Complex.exp_ne_zero _) (KN.Analysis.expPrimitive_ne_zero h rp r)
  have heq : EqOn (logDeriv p) (logDeriv g) (Ioi rp) := by
    intro r hr
    simp only [logDeriv_apply, (hd r hr).deriv, (hgd r hr).deriv]
    rw [mul_div_cancel_left₀ _ (hp r hr), mul_div_cancel_left₀ _ (hgn r hr)]
  obtain ⟨z,hz,hzg⟩ := (logDeriv_eqOn_iff
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hgd r hr).differentiableAt.differentiableWithinAt)
    isOpen_Ioi (convex_Ioi rp).isPreconnected hgn hp).mp heq
  refine ⟨fun r => z*KN.Analysis.expPrimitive h rp r,
    contDiffOn_const.mul (KN.Analysis.expPrimitive_contDiffOn h lo rp hh hlo),
    fun r => mul_ne_zero hz (KN.Analysis.expPrimitive_ne_zero h rp r), ?_⟩
  intro r hr
  have he := hzg hr
  simp only [Pi.smul_apply, smul_eq_mul, g] at he
  rw [← positivePower_eq_cpow rp r α hr]
  rw [he]
  ring

end KN.Boundary

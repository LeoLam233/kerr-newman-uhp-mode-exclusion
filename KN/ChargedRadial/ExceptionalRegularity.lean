import KN.ChargedRadial.CanonicalInterface
import KN.ChargedRadial.RegularDistribution

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace KN.ChargedRadial

/-- At resonance, the second first-order equation removes the apparent pole
whenever its coupling is nonzero at the horizon. Only division in a small
neighbourhood of that nonzero value is used, never division at a turning point. -/
theorem smooth_extension_from_second_equation
    (r : ℝ) (v z B : ℝ → ℂ)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi r))
    (hz : Smooth z) (hB : Smooth B) (hBr : B r ≠ 0)
    (heq : ∀ t > r, deriv z t = B t*v t) :
    ∃ f : ℝ → ℂ, Smooth f ∧ EqOn f v (Ioi r) := by
  let vfill : ℝ → ℂ := fun t => if t = r then deriv z r/B r else v t
  have hfill : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) vfill (Ici r) := by
    intro x hx
    rcases eq_or_lt_of_le (show r ≤ x from hx) with (hxr | hxr)
    · subst x
      have hquot : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t => deriv z t/B t) r := by
        have hzd : Smooth (deriv z) := hz.deriv'
        simp only [div_eq_mul_inv]
        convert! hzd.contDiffAt.mul (hB.contDiffAt.inv hBr) using 1
      apply hquot.contDiffWithinAt.congr_of_eventuallyEq
      · have hne : ∀ᶠ t in 𝓝 r, B t ≠ 0 := hB.continuous.continuousAt.eventually_ne hBr
        filter_upwards [hne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t htne ht
        by_cases htr : t = r
        · subst t; simp [vfill]
        · have htpos : r < t := lt_of_le_of_ne ht (Ne.symm htr)
          simp only [vfill, ite_eq_right_iff.mpr (fun hh => (htr hh).elim)]
          rw [heq t htpos, mul_div_cancel_left₀ _ htne]
      · simp [vfill]
    · have hvx := (hv x hxr).contDiffAt (isOpen_Ioi.mem_nhds hxr)
      apply (hvx.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [isOpen_Ioi.mem_nhds hxr] with t ht
      simp [vfill, ne_of_gt (show r < t from ht)]
  obtain ⟨f,hf,he⟩ := External.smooth_halfline_extension r vfill hfill
  refine ⟨f,hf,?_⟩
  intro t ht
  rw [he (show t ∈ Ici r from le_of_lt (show r < t from ht))]
  simp [vfill, ne_of_gt (show r < t from ht)]

end KN.ChargedRadial

import KN.ChargedRadial.ExceptionalRegularity
import KN.ChargedRadial.SupportedPair

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped Distributions
namespace KN.ChargedRadial

lemma corrected_zeroExtension_support (r : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (c : ℂ) :
    Distribution.dsupport (zeroExtension r f+deltaValue r c) ⊆ Ici r := by
  intro x hx
  apply (Distribution.mem_dsupport_iff x).1 hx (Ici r) ?_ isClosed_Ici
  rw [compl_Ici]
  intro phi hphi
  change zeroExtension r f phi+deltaValue r c phi = 0
  rw [zeroExtension_apply r f hf, deltaValue_apply]
  have hz (t : ℝ) (ht : r ≤ t) : phi t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (not_lt_of_ge ht) (hphi h))
  rw [hz r le_rfl, zero_smul, add_zero]
  exact setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by
    rw [hz t (le_of_lt (show r < t from ht)), zero_smul])

lemma zeroExtension_support (r : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    Distribution.dsupport (zeroExtension r f) ⊆ Ici r := by
  have hh := corrected_zeroExtension_support r f hf 0
  have hz : deltaValue r 0 = 0 := by ext phi; simp [deltaValue_apply]
  simpa only [hz, add_zero] using hh

/-- The resonant branch produces an actual supported pair with the required
z(r₊)/B(r₊) delta correction; smoothness is derived from the second equation. -/
theorem supported_exceptional_pair
    (r : ℝ) (v z Delta L A B : ℝ → ℂ)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi r))
    (hz : Smooth z) (hDelta : Smooth Delta) (hL : Smooth L) (hA : Smooth A) (hB : Smooth B)
    (hzero : Delta r = 0) (hres : L r = deriv Delta r) (hBr : B r ≠ 0)
    (hfirst : ∀ t > r, Delta t*deriv v t+L t*v t = A t*z t)
    (hsecond : ∀ t > r, deriv z t = B t*v t) :
    ∃ f : ℝ → ℂ, Smooth f ∧ EqOn f v (Ioi r) ∧
      ∃ pair : SupportedPair r Delta L A B hDelta hL hA hB,
        pair.v = zeroExtension r f+deltaValue r (z r/B r) ∧ pair.z = zeroExtension r z := by
  obtain ⟨f,hf,he⟩ := smooth_extension_from_second_equation r v z B hv hz hB hBr hsecond
  have hd (t : ℝ) (ht : r < t) : deriv f t = deriv v t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact he hx
  have hh := corrected_zeroExtension_pair r f z Delta L A B
    (hf.of_le (by simp)) (hz.of_le (by simp)) hDelta hL hA hB hzero hres hBr
    (fun t ht => by rw [hd t ht, he ht]; exact hfirst t ht)
    (fun t ht => by rw [he ht]; exact hsecond t ht)
  exact ⟨f, hf, he, ⟨zeroExtension r f+deltaValue r (z r/B r), zeroExtension r z,
    corrected_zeroExtension_support r f hf.continuous _,
    zeroExtension_support r z hz.continuous, hh.1, hh.2⟩, rfl, rfl⟩

end KN.ChargedRadial

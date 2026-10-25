import KN.ChargedRadial.FactorRegularity
import KN.Boundary.RescaleFactor
import KN.Boundary.GaugeSmooth

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial
open KN.Boundary

/-- Rescaling a genuine weighted horizon field gives a smooth representative,
without imposing the value of a singular raw product at the horizon itself. -/
theorem horizon_rescale_representative (b : KN.Background) (m : ℤ) (omega : ℂ)
    (e : ℝ) (original : ℝ → ℂ) (hh : HorizonRegular b m omega (-e) original) :
    ∃ w : ℝ → ℂ, ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus) ∧
      ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega e r*original r := by
  obtain ⟨u,hu,he⟩ := hh
  refine ⟨fun r => Complex.exp (Complex.I*b.eta*omega*r)*u r, ?_, ?_⟩
  · have hx : Smooth (fun r : ℝ => Complex.exp (Complex.I*b.eta*omega*r)) :=
      ((contDiff_const (c := Complex.I*b.eta*omega)).mul Complex.ofRealCLM.contDiff).cexp
    exact hx.contDiffOn.mul hu
  · intro r hr
    rw [he r hr]
    change _ = rescaleFactor b m omega e r*(gauge b m omega r*(Real.rpow (b.Delta r) (-e):ℂ)*u r)
    have hp : (Real.rpow (b.Delta r) e:ℂ)*(Real.rpow (b.Delta r) (-e):ℂ)=1 := by
      change ((b.Delta r ^ e : ℝ):ℂ)*((b.Delta r ^ (-e) : ℝ):ℂ)=1
      rw [← Complex.ofReal_mul,← Real.rpow_add (b.Delta_pos hr),add_neg_cancel,Real.rpow_zero]
      rfl
    dsimp [rescaleFactor]
    field_simp [gauge_ne_zero b m omega r]
    linear_combination -u r*hp

/-- Original horizon regularity also supplies all exterior smoothness needed
for the outgoing transform estimates. -/
theorem horizon_original_exterior_smooth (b : KN.Background) (m : ℤ) (omega : ℂ)
    (q : ℝ) (original : ℝ → ℂ) (hh : HorizonRegular b m omega q original) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) original (Ioi b.rPlus) := by
  obtain ⟨u,hu,he⟩ := hh
  have hd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) b.Delta (Ioi b.rPlus) := by
    unfold KN.Background.Delta
    fun_prop
  have hp := hd.rpow_const_of_ne (p := q) (fun r hr => ne_of_gt (b.Delta_pos hr))
  have hc := (gauge_contDiffOn b m omega).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hp)
  apply (hc.mul (hu.mono Ioi_subset_Ici_self)).congr
  intro r hr
  exact he r hr

end KN.ChargedRadial

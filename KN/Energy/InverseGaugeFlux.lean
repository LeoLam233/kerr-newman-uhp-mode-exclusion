import KN.Energy.Gauge

noncomputable section
namespace KN.Energy

/-- Direct inverse-gauge calculation using actual first and second derivatives
of Y; no differentiability or endpoint condition is hidden in a formal jet. -/
theorem inverse_gauge_flux (ω : ℂ) (g Y Yp : ℝ → ℂ) (P s : ℝ → ℝ)
    (x Pp sp q qp : ℝ) (Ypp d : ℂ)
    (hg : HasDerivAt g (Complex.I*ω*(s x:ℂ)*g x) x)
    (hY : HasDerivAt Y (Yp x) x) (hYp : HasDerivAt Yp Ypp x)
    (hP : HasDerivAt P Pp x) (hs : HasDerivAt s sp x)
    (hq : q=P x*s x) (hqp : qp=Pp*s x+P x*sp)
    (heq : (P x:ℂ)*Ypp+((Pp:ℂ)+2*Complex.I*ω*q)*Yp x+
      (d+Complex.I*ω*qp)*Y x=0) :
    HasDerivAt (fun y => (P y:ℂ)*(g y*(Yp y+Complex.I*ω*(s y:ℂ)*Y y)))
      (-(d+ω^2*q*s x)*(g x*Y x)) x := by
  have hh := hP.ofReal_comp.mul
    (hg.mul (hYp.add ((hs.ofReal_comp.const_mul (Complex.I*ω)).mul hY)))
  convert hh using 1
  rw [hq,hqp] at heq
  rw [hq]
  simp only [Pi.mul_apply,Pi.add_apply]
  push_cast at *
  linear_combination (norm := ring_nf) -(g x)*heq
  simp [Complex.I_sq]

end KN.Energy

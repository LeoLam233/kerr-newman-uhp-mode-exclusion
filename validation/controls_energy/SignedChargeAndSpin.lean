import KN.Energy.PhysicalSigns
import KN.ChargedRadial.OrderedSubstitution
noncomputable section
namespace EnergyControls

def negativeCharge : KN.Background where
  M := 2
  a := 0
  Q := -1
  mass_pos := by norm_num
  subextremal := by norm_num

example : negativeCharge.Q<0 := by norm_num [negativeCharge]
example : 0<KN.Energy.Pplus negativeCharge.eta (-4) ∧
    0<KN.Energy.Wplus negativeCharge.eta (-4) ∧
    0<KN.Energy.Pminus negativeCharge.eta (-4) ∧
    0<KN.Energy.Wminus negativeCharge.eta (-4) := by
  apply KN.Energy.physical_weights_positive
  norm_num [KN.Background.h,KN.Background.eta,KN.Background.d,negativeCharge]

example : 0<KN.Energy.radialR negativeCharge (-4)-negativeCharge.a^2*(negativeCharge.c^2+1) := by
  apply KN.Energy.physical_B_positive
  · norm_num [KN.Background.h,KN.Background.eta,KN.Background.d,negativeCharge]
  · norm_num

example (m : ℤ) (omega lam x : ℂ) :
    let p := KN.ChargedRadial.backgroundPolynomialData negativeCharge m (-1) omega lam
    KN.ChargedRadial.fourierSecond p (omega*x)=
      Complex.I*omega^3*KN.ChargedRadial.transformA p x := by
  exact (KN.ChargedRadial.physical_fourier_coefficients negativeCharge (by norm_num [negativeCharge])
    m (-1) omega lam x (Or.inr rfl)).1
example (m : ℤ) (omega lam x : ℂ) :
    let p := KN.ChargedRadial.backgroundPolynomialData negativeCharge m 1 omega lam
    KN.ChargedRadial.fourierSecond p (omega*x)=
      Complex.I*omega^3*KN.ChargedRadial.transformA p x := by
  exact (KN.ChargedRadial.physical_fourier_coefficients negativeCharge (by norm_num [negativeCharge])
    m 1 omega lam x (Or.inl rfl)).1
end EnergyControls

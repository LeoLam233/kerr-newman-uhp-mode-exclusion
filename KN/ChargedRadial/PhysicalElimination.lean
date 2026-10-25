import KN.ChargedRadial.DistributionElimination
import KN.ChargedRadial.OrderedSubstitution
import KN.ChargedRadial.SupportedPair

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Distributions ContDiff
namespace KN.ChargedRadial

def physicalL (b : KN.Background) (m : ℤ) (sigma omega : ℂ) (r : ℝ) : ℂ :=
  ((1+3*sigma)/2)*(2*(r:ℂ)-2*b.M) -
    2*Complex.I*(b.frequencyK m omega r - b.eta*omega*(b.Delta r:ℂ))

def physicalR1 (b : KN.Background) (sigma omega : ℂ) (r : ℝ) : ℂ :=
  -sigma*b.c*omega*r + sigma*b.Q*b.eta*omega + Complex.I*b.beta

theorem physicalL_smooth (b : KN.Background) (m : ℤ) (sigma omega : ℂ) :
    ContDiff ℝ ∞ (physicalL b m sigma omega) := by
  unfold physicalL KN.Background.frequencyK KN.Background.Delta
  push_cast
  have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

theorem physicalDelta_smooth (b : KN.Background) : ContDiff ℝ ∞ (fun r => (b.Delta r : ℂ)) := by
  have hd : ContDiff ℝ ∞ b.Delta := by unfold KN.Background.Delta; fun_prop
  exact Complex.ofRealCLM.contDiff.comp hd

theorem physicalR1_smooth (b : KN.Background) (sigma omega : ℂ) :
    ContDiff ℝ ∞ (physicalR1 b sigma omega) := by
  unfold physicalR1
  have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

theorem physicalL_polynomial (b : KN.Background) (m : ℤ) (sigma omega lam : ℂ) (r : ℝ) :
    let p := backgroundPolynomialData b m sigma omega lam
    physicalL b m sigma omega r = p.L2*(r:ℂ)^2+p.L1*r+p.L0 := by
  dsimp [physicalL, backgroundPolynomialData, RadialPolynomialData.L2, RadialPolynomialData.L1,
    RadialPolynomialData.L0, KN.Background.frequencyK, KN.Background.Delta]
  push_cast
  ring

theorem physicalR1_affine (b : KN.Background) (m : ℤ) (sigma omega lam : ℂ) :
    physicalR1 b sigma omega = radialAffine
      (backgroundPolynomialData b m sigma omega lam).u (backgroundPolynomialData b m sigma omega lam).b := by
  funext r
  dsimp [physicalR1, radialAffine, backgroundPolynomialData, RadialPolynomialData.u, RadialPolynomialData.b]
  ring

/-- Exact physical (28) to (29) bridge for a horizon-supported distribution pair.
No hypotheses concerning zeros of either coupling occur. -/
theorem physical_supported_pair_elimination
    (b : KN.Background) (m : ℤ) (sigma omega lam : ℂ) (hs : sigma=1 ∨ sigma = -1)
    (pair : SupportedPair b.rPlus (fun r => (b.Delta r:ℂ)) (physicalL b m sigma omega)
      (fun r => physicalR1 b sigma omega r+Complex.I*sigma*lam)
      (fun r => physicalR1 b sigma omega r-Complex.I*sigma*lam)
      (physicalDelta_smooth b) (physicalL_smooth b m sigma omega)
      ((physicalR1_smooth b sigma omega).add contDiff_const)
      ((physicalR1_smooth b sigma omega).sub contDiff_const)) :
    (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist)
      ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist)
        (mulComplexDist (fun r => (b.Delta r:ℂ)) (physicalDelta_smooth b)
          (Distribution.lineDerivCLM (1:ℝ) pair.v) +
          mulComplexDist (physicalL b m sigma omega) (physicalL_smooth b m sigma omega) pair.v)) -
      mulComplexDist (fun r => physicalR1 b sigma omega r^2+lam^2)
        ((physicalR1_smooth b sigma omega).pow 2 |>.add contDiff_const)
        (Distribution.lineDerivCLM (1:ℝ) pair.v) -
      mulComplexDist (fun r => (3*physicalR1 b sigma omega r-Complex.I*sigma*lam)*(-sigma*b.c*omega))
        ((contDiff_const.mul (physicalR1_smooth b sigma omega)).sub contDiff_const |>.mul contDiff_const)
        pair.v = 0 := by
  have hA : ContDiff ℝ ∞ (fun r => physicalR1 b sigma omega r+Complex.I*sigma*lam) :=
    (physicalR1_smooth b sigma omega).add contDiff_const
  have hB : ContDiff ℝ ∞ (fun r => physicalR1 b sigma omega r-Complex.I*sigma*lam) :=
    (physicalR1_smooth b sigma omega).sub contDiff_const
  have hder : ∀ r, HasDerivAt (physicalR1 b sigma omega) (-sigma*b.c*omega) r := by
    intro r
    rw [physicalR1_affine b m sigma omega lam]
    exact radialAffine_hasDerivAt _ _ r
  have hDA : deriv (fun r => physicalR1 b sigma omega r+Complex.I*sigma*lam) = fun _ => -sigma*b.c*omega :=
    funext (fun r => ((hder r).add_const _).deriv)
  have hDB : deriv (fun r => physicalR1 b sigma omega r-Complex.I*sigma*lam) = fun _ => -sigma*b.c*omega :=
    funext (fun r => ((hder r).sub_const _).deriv)
  have h := distribution_affine_elimination _ _ hA hB (-sigma*b.c*omega) hDA hDB _ pair.v pair.z
    pair.first pair.second
  have hp : (fun r => (physicalR1 b sigma omega r+Complex.I*sigma*lam)*
      (physicalR1 b sigma omega r-Complex.I*sigma*lam)) = fun r => physicalR1 b sigma omega r^2+lam^2 := by
    funext r
    rcases hs with rfl | rfl <;> ring_nf <;> simp [Complex.I_sq]
  have hc : (fun r => (2*(physicalR1 b sigma omega r-Complex.I*sigma*lam)+
      (physicalR1 b sigma omega r+Complex.I*sigma*lam))*(-sigma*b.c*omega)) =
      fun r => (3*physicalR1 b sigma omega r-Complex.I*sigma*lam)*(-sigma*b.c*omega) := by funext r; ring
  rwa [mulComplexDist_congr _ _ _ ((physicalR1_smooth b sigma omega).pow 2 |>.add contDiff_const) hp,
    mulComplexDist_congr _ _ _ ((contDiff_const.mul (physicalR1_smooth b sigma omega)).sub contDiff_const |>.mul contDiff_const) hc] at h

end KN.ChargedRadial

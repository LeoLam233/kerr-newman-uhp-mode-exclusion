import KN.ChargedRadial.PhysicalSupportedPair
import KN.Physics.FirstRescaling
import KN.Physics.Rescaling

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace KN.ChargedRadial
open KN.Boundary

/-- The two selected components of the original scalar radial equation (24),
with positive or negative chirality encoded in sigma. -/
def OriginalSelectedPair (b : KN.Background) (m : ℤ) (sigma : ℝ) (omega lam : ℂ)
    (y z : ℝ → ℂ) : Prop :=
  ∀ r > b.rPlus,
    HasDerivAt y
      ((-(3*(sigma:ℂ)/4)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ)+
        Complex.I*(b.frequencyK m omega r-(b.eta:ℂ)*omega*(b.Delta r:ℂ))/(b.Delta r:ℂ))*y r+
        (physicalR1 b sigma omega r+Complex.I*sigma*lam)/(Real.sqrt (b.Delta r):ℂ)*z r) r ∧
    HasDerivAt z
      (((3*(sigma:ℂ)/4)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ)-
        Complex.I*(b.frequencyK m omega r-(b.eta:ℂ)*omega*(b.Delta r:ℂ))/(b.Delta r:ℂ))*z r+
        (physicalR1 b sigma omega r-Complex.I*sigma*lam)/(Real.sqrt (b.Delta r):ℂ)*y r) r

/-- Actual first and second rescalings, including derivative locality for the
smooth representatives at the horizon. No rescaled equation is assumed. -/
theorem original_pair_transport (b : KN.Background) (m : ℤ) (sigma : ℝ) (omega lam : ℂ)
    (y z w ws : ℝ → ℂ) (hpair : OriginalSelectedPair b m sigma omega lam y z)
    (hew : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega (3*sigma/4) r*y r)
    (hes : ∀ r ∈ Ioi b.rPlus, ws r=rescaleFactor b m omega (3*sigma/4-1/2) r*z r)
    {r : ℝ} (hr : b.rPlus < r) :
    let p := radialMultiplier b m omega (-(1+3*sigma)/2)
    (b.Delta r:ℂ)*deriv (fun t => p t*w t) r+physicalL b m sigma omega r*(p r*w r)=
      (physicalR1 b sigma omega r+Complex.I*sigma*lam)*((b.Delta r:ℂ)*p r*ws r) ∧
    deriv (fun t => (b.Delta t:ℂ)*p t*ws t) r=
      (physicalR1 b sigma omega r-Complex.I*sigma*lam)*(p r*w r) := by
  have hew' : w =ᶠ[𝓝 r] (fun t => rescaleFactor b m omega (3*sigma/4) t*y t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact hew t ht
  have hes' : ws =ᶠ[𝓝 r] (fun t => rescaleFactor b m omega (3*sigma/4-1/2) t*z t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact hes t ht
  have hp := hpair r hr
  have hw := ((rescaleFactor_hasDerivAt b m omega (3*sigma/4) hr).mul hp.1).differentiableAt
  have hs := ((rescaleFactor_hasDerivAt b m omega (3*sigma/4-1/2) hr).mul hp.2).differentiableAt
  have hraw := KN.Physics.actual_first_rescaling b m omega sigma y z hr
    (physicalR1 b sigma omega r+Complex.I*sigma*lam)
    (physicalR1 b sigma omega r-Complex.I*sigma*lam) hp.1 hp.2
  dsimp only at hraw
  have heq1 : deriv w r=(physicalR1 b sigma omega r+Complex.I*sigma*lam)*ws r := by
    rw [hew'.deriv_eq,hes r hr]
    exact hraw.1
  have heq2 : (b.Delta r:ℂ)*deriv ws r+
      (((1-3*(sigma:ℂ))/2)*(2*(r:ℂ)-2*b.M)+
        2*Complex.I*(b.frequencyK m omega r-(b.eta:ℂ)*omega*(b.Delta r:ℂ)))*ws r=
      (physicalR1 b sigma omega r-Complex.I*sigma*lam)*w r := by
    rw [hes'.deriv_eq,hes r hr,hew r hr]
    exact hraw.2
  exact KN.Physics.charged_pair_transport b m omega sigma w ws hr
    (hw.congr_of_eventuallyEq hew') (hs.congr_of_eventuallyEq hes')
    _ _ heq1 heq2

end KN.ChargedRadial

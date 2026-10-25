import KN.Kerr.PhysicalCovariance
import KN.Energy.ConormalPhysical

namespace KN.Kerr
open Set
open scoped ContDiff

/-- The actual spin-reversed field preserves the physical outgoing conormal
class. This is derived from rational gauge covariance, not postulated. -/
theorem reversedRadial_outgoing
    (b : KN.Background) (m : ℤ) (omega : ℂ) (k n : ℕ) (R f : ℝ → ℂ)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega (k : ℝ) r * f r)
    (hout : KN.Boundary.Outgoing b m omega R) :
    KN.Boundary.Outgoing b m omega (reversedRadial b m omega k n f) := by
  have hd := KN.Energy.delta_smooth b
  have hdCon := KN.Energy.polynomialConormal_pow b.rPlus _ hd (KN.Energy.delta_conormal b) k
  have hu := (KN.Boundary.gauge_contDiffOn b m omega).mul hR
  have huCon : KN.Boundary.PolynomialConormal (fun r => KN.Boundary.gauge b m omega r * R r) := hout
  have hv := (hd.pow k).mul hu
  have hvCon := (KN.Energy.polynomialConormal_add_mul b.rPlus _ _ (hd.pow k) hu hdCon huCon).2
  have hp := KN.Energy.logarithmicCoefficient_smooth_conormal b m omega
  have hi := KN.Energy.covariantDerivative_iterate_preserves b.rPlus _ _ hp.1 hv hp.2 hvCon n
  have hresult := (KN.Energy.polynomialConormal_add_mul b.rPlus _ _ (hd.pow k) hi.1 hdCon hi.2).2
  apply KN.Energy.polynomialConormal_congr_exterior b.rPlus hresult
  intro r hr
  exact (outgoing_reversal_identity b m omega k n R f hf hrep hp.1 hv r hr).symm

end KN.Kerr

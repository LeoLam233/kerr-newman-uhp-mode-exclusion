import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

/-! Precisely general external classical mathematics. This interface does not
assert a Kerr/KN conclusion, a spin reversal, or exceptional-horizon cancellation.
Source: F. W. J. Olver, Asymptotics and Special Functions (1997 reprint),
pp. 148–152; DLMF §2.7(i), equations (2.7.3)–(2.7.6), including integral
root differences, https://dlmf.nist.gov/2.7.i .
The stated half-line form combines Fuchs–Frobenius local classification with
ordinary-point uniqueness away from the regular singular endpoint.
The other root is 1-B(rp)/A(rp), with strictly negative real part. -/
namespace KN.Kerr.External
open Set Filter
open scoped Topology ContDiff

/-- Explicit classical interface, to appear in every transitive axiom ledger.
It is intentionally parameter-free with respect to black-hole physics. -/
axiom fuchs_smooth_halfline_classification
    (rp : ℝ) (A B C f : ℝ → ℂ)
    (hA : AnalyticOnNhd ℝ A (Ici rp))
    (hB : AnalyticOnNhd ℝ B (Ici rp))
    (hC : AnalyticOnNhd ℝ C (Ici rp))
    (hAnz : ∀ r ∈ Ici rp, A r ≠ 0)
    (hindicial : 1 < (B rp / A rp).re)
    (hf : ContDiffOn ℝ ∞ f (Ici rp))
    (hode : ∀ r ∈ Ioi rp, (r - rp : ℝ) * A r * deriv (deriv f) r +
      B r * deriv f r + C r * f r = 0) :
    (∃ g : ℝ → ℂ, AnalyticAt ℝ g rp ∧
      f =ᶠ[𝓝[≥] rp] g) ∧
    (f rp = 0 → ∀ r ∈ Ici rp, f r = 0)

end KN.Kerr.External

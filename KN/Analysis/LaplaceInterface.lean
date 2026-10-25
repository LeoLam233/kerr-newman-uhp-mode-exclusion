import KN.ChargedRadial.DistributionMultiplication
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
General published Fourier–Laplace interface, independent of Kerr–Newman.
Source: F. Beffa, Weakly Nonlinear Systems (2023), Chapter 5 §§5.1–5.3,
Definitions5.1–5.2, equation(5.2), Table5.1, equation(5.4).
https://doi.org/10.1007/978-3-031-40681-2_5
Convention here is exp(-i*z*t), so s=i*z. Mathlib Fourier uses exp(-2*pi*i*x*t);
the exact horizontal-line representation therefore evaluates F(2*pi*x+i*beta).
No horizon correction, transformed KN equation, coercivity, or mode exclusion is an interface.
-/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions SchwartzMap FourierTransform
namespace KN.Analysis
open KN.ChargedRadial

def testSchwartz (phi : 𝓓((⊤ : Opens ℝ), ℝ)) : SchwartzMap ℝ ℂ :=
  (phi.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp phi.contDiff)

def damping (beta : ℝ) : ℝ → ℝ := fun t => Real.exp (beta*t)
lemma damping_smooth (beta : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (damping beta) := by
  unfold damping; fun_prop

/-- Equality with a genuine exponentially damped distribution on compact real tests. -/
def DampedMatches (T : CDist) (beta : ℝ) (U : TemperedDistribution ℝ ℂ) : Prop :=
  ∀ phi : 𝓓((⊤ : Opens ℝ), ℝ),
    U (testSchwartz phi) = mulDist (damping beta) (damping_smooth beta) T phi

/-- Actual support and exponential temperedness, with no KN-specific conclusion. -/
def LaplaceAdmissible (a c : ℝ) (T : CDist) : Prop :=
  Distribution.dsupport T ⊆ Ici a ∧
    ∀ beta < c, ∃ U : TemperedDistribution ℝ ℂ, DampedMatches T beta U

/-- The transform is anchored to actual Schwartz pairings, not an unconstrained function. -/
def IsFourierLaplaceTransform (T : CDist) (c : ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ beta < c, ∃ U : TemperedDistribution ℝ ℂ, DampedMatches T beta U ∧
    ∀ phi : SchwartzMap ℝ ℂ,
      Integrable (fun x : ℝ => F ((2*Real.pi*x:ℝ)+Complex.I*beta)*phi x) ∧
      (𝓕 U) phi = ∫ x : ℝ, F ((2*Real.pi*x:ℝ)+Complex.I*beta)*phi x

def coordinateMultiply (T : CDist) : CDist := mulDist (fun t : ℝ => t) contDiff_id T

namespace External
/-- General existence/holomorphy theorem for exponentially damped right-sided distributions. -/
axiom fourier_laplace_exists (a c : ℝ) (T : CDist) (hT : LaplaceAdmissible a c T) :
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | z.im < c} ∧ IsFourierLaplaceTransform T c F

/-- The ordinary half-line integral represents the transform of its actual regular distribution.
This is Definition5.2 specialized to locally integrable functions, not a KN formula. -/
axiom fourier_laplace_regular_integral (a c : ℝ) (f : ℝ → ℂ)
    (hf : LocallyIntegrable f (volume.restrict (Ioi a)))
    (hdamp : ∀ beta < c, Integrable (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t)
      (volume.restrict (Ioi a))) :
  let F : ℂ → ℂ := fun z => ∫ t in Ioi a, Complex.exp (-Complex.I*z*t)*f t
  AnalyticOnNhd ℂ F {z : ℂ | z.im < c} ∧
    IsFourierLaplaceTransform (Distribution.ofFun (⊤ : Opens ℝ) f
      (volume.restrict (Ioi a)) ⊤) c F

/-- Distributional differentiation, with no spurious finite endpoint source. -/
axiom fourier_laplace_derivative (T : CDist) (c : ℝ) (F : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F) :
  IsFourierLaplaceTransform (Distribution.lineDerivCLM (1:ℝ) T) c (fun z => Complex.I*z*F z)

/-- Coordinate multiplication is i times complex differentiation. -/
axiom fourier_laplace_coordinate (T : CDist) (c : ℝ) (F : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F)
    (hhol : AnalyticOnNhd ℂ F {z : ℂ | z.im < c}) :
  IsFourierLaplaceTransform (coordinateMultiply T) c (fun z => Complex.I*deriv F z)

/-- General single-valuedness of the holomorphic Fourier–Laplace transform, with
both functions anchored to the same distribution by horizontal Schwartz pairings.
This is the well-definedness statement in Beffa Definition5.2 and §5.3 (5.4). -/
axiom fourier_laplace_single_valued (T : CDist) (c : ℝ) (F G : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F) (hG : IsFourierLaplaceTransform T c G)
    (haF : AnalyticOnNhd ℂ F {z : ℂ | z.im < c})
    (haG : AnalyticOnNhd ℂ G {z : ℂ | z.im < c}) :
    ∀ z : ℂ, z.im < c → F z = G z

/-- Uniqueness is general Fourier uniqueness after exponential damping, not a KN conclusion. -/
theorem fourier_laplace_unique (T S : CDist) (c : ℝ) (F G : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F) (hG : IsFourierLaplaceTransform S c G)
    (heq : ∀ z : ℂ, z.im < c → F z = G z) : T = S := by
  let beta := c-1
  have hb : beta < c := by dsimp [beta]; linarith
  obtain ⟨U, hU, hUF⟩ := hF beta hb
  obtain ⟨V, hV, hVG⟩ := hG beta hb
  have hUV : U = V := by
    have hFourier : 𝓕 U = 𝓕 V := by
      ext phi
      rw [(hUF phi).2, (hVG phi).2]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heq _ (by simpa using hb)]
    have hi := congrArg (fun W : TemperedDistribution ℝ ℂ => 𝓕⁻ W) hFourier
    simpa using hi
  ext phi
  let psi := mulTest (damping (-beta)) (damping_smooth (-beta)) phi
  have htest : mulTest (damping beta) (damping_smooth beta) psi = phi := by
    ext t
    change (phi t*Real.exp ((-beta)*t))*Real.exp (beta*t) = phi t
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hu := hU psi
  have hv := hV psi
  rw [hUV] at hu
  have hm : mulDist (damping beta) (damping_smooth beta) T psi =
      mulDist (damping beta) (damping_smooth beta) S psi := hu.symm.trans hv
  simpa only [mulDist_apply, htest] using hm
end External
end KN.Analysis

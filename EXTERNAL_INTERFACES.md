# Explicit external interface ledger — initial complete candidate

The new C002-specific source conversion, spectral bookkeeping, coercivity, distributional correction, transform equation, endpoint estimates, Kerr spin reversal, whole-field exclusion and charge-split composition are implemented in Lean. This initial candidate still requires full frozen clean-build/checker verification and three independent adversarial audits.

## Physical entry: explicit theorem argument, not an invisible axiom

`KN.Physics.physical_mode_exclusion` takes a `PublishedEinsteinMaxwellEntry` argument. It is a precisely typed one-way classical physical-necessity contract, not a construction of an entire Einstein–Maxwell differential-geometric theory. Its arbitrary carrier and admissibility predicate are supplied by that external theory; the necessary output is explicitly constrained by the original systems and physical boundary conditions below. The theorem `radiative_mode_exclusion` directly ranges over the explicit necessary data. Neither contract contains a no-mode conclusion, transformed PDE/boundary, assumed separation, or new C002 positivity statement. This assumption remains visible in the printed theorem types even though it is a parameter rather than a declared axiom.

Sources: Hintz arXiv:2609.33661v1, original equations (1), (3), (4) and tetrad/boundary conventions; Teukolsky 1973 canonical Kerr necessary equations; Motohashi arXiv:2610.10529v1 (2.10), (5.1)–(5.3), for the background Weyl coefficient and gauge-invariant mixtures. The source transform and its boundary fidelity are proved after this entry.

Exact physical contract:

```lean
import KN.Angular.OriginalSourceField
import KN.Physics.KerrRadiativeExclusion

noncomputable section
namespace KN.Physics
open KN.Angular MeasureTheory Set

/-- Background Weyl coefficient in the fixed principal tetrad. -/
def backgroundPsiTwo (b : KN.Background) (r θ : ℝ) : ℂ :=
  ((b.Q:ℂ)^2/rho b r θ-(b.M:ℂ))/(rhoStar b r θ)^3

/-- Literal gauge-invariant radiative data (8a), before any phantom-frame choice. -/
def radiativeValue (b : KN.Background) (r θ : ℝ) (v : RadiativeCurvatureMaxwell) :
    RadiativeComponent → ℂ
  | .gravitationalPlus => gravitationalPlus v
  | .gravitationalMinus => gravitationalMinus (rhoStar b r θ) v
  | .electromagneticPlus => electromagneticPlus b.M b.Q (rhoStar b r θ) (backgroundPsiTwo b r θ) v
  | .electromagneticMinus => electromagneticMinus b.M b.Q (rhoStar b r θ) (backgroundPsiTwo b r θ) v

/-- The classical phantom-frame identification, stated on the original NP
variables. It contains no transformed field, spectral assertion, or vanishing. -/
def PhantomIdentification (b : KN.Background)
    (raw phantom : ℝ → ℝ → RadiativeCurvatureMaxwell)
    (plus minus : ℝ → ℝ → Fin 4 → ℂ) : Prop :=
  ∀ r θ, b.rPlus<r → θ ∈ Ioo 0 Real.pi →
    (phantom r θ).dPhi0=0 ∧ (phantom r θ).dPhi2=0 ∧
    plus r θ 0=(phantom r θ).dPsi0 ∧
    plus r θ 1=(Real.sqrt 2:ℂ)*rhoStar b r θ*(phantom r θ).dPsi1 ∧
    minus r θ 0=(rhoStar b r θ)^4*(phantom r θ).dPsi4 ∧
    minus r θ 1=(rhoStar b r θ)^3*(phantom r θ).dPsi3/(Real.sqrt 2:ℂ) ∧
    ∀ i, radiativeValue b r θ (raw r θ) i=radiativeValue b r θ (phantom r θ) i

/-- Precisely scoped one-way classical physical input. For nonzero charge the
output is the ORIGINAL published chiral source system and original boundary
classes. For zero charge it is the four canonical Teukolsky necessary equations.
This interface does not assert exclusion, separation, transformed boundary
conditions, energy positivity, or any C002 conclusion.

Sources: Hintz arXiv:2609.33661v1, original NP equations (1), chiral variables (3),
necessary system (4), physical tetrad/axis/horizon conventions; Teukolsky 1973
for the decoupled Kerr necessary equations; Motohashi arXiv:2610.10529v1,
(5.1)–(5.2), for the four invariant mixtures. Only the physical implication is
external. All subsequent source transformation and exclusion are proved here.
-/
structure PublishedPhysicalNecessaryData (b : KN.Background) (m : ℤ) (omega : ℂ)
    (raw : ℝ → ℝ → RadiativeCurvatureMaxwell) : Prop where
  axis_continuity : ∀ i r, b.rPlus<r →
    ContinuousOn (fun θ => radiativeValue b r θ (raw r θ) i) (Icc 0 Real.pi)
  charged : b.Q≠0 → ∃ (plus : OriginalSourceField true b m omega)
      (minus : OriginalSourceField false b m omega)
      (phantom : ℝ → ℝ → RadiativeCurvatureMaxwell),
    PublishedChiralSystem true b m omega plus.components ∧
    PublishedChiralSystem false b m omega minus.components ∧
    PhantomIdentification b raw phantom plus.components minus.components
  kerr : b.Q=0 → ∃ F : RadiativeComponent → ℝ → KN.Kerr.AngularH,
    KerrRadiativeNecessarySystem b m omega F ∧
    ∀ i r, b.rPlus<r →
      ContinuousOn (fun θ => radiativeValue b r θ (raw r θ) i) (Ioo 0 Real.pi) ∧
      F i r =ᵐ[KN.Kerr.sphericalMeasure] fun θ => radiativeValue b r θ (raw r θ) i

/-- An explicit interface for a physical perturbation theory. Its carrier and
admissibility predicate belong to the imported Einstein–Maxwell theory; the
only theorem required of it is the published necessary-system implication.
Keeping this argument explicit avoids pretending the full GR field equations
were independently reimplemented in this development. -/
structure PublishedEinsteinMaxwellEntry (b : KN.Background) (m : ℤ) (omega : ℂ)
    (P : Type*) where
  curvatureMaxwell : P → ℝ → ℝ → RadiativeCurvatureMaxwell
  smoothOutgoingMode : P → Prop
  necessary : ∀ p, smoothOutgoingMode p →
    PublishedPhysicalNecessaryData b m omega (curvatureMaxwell p)

end KN.Physics

```

## Named published mathematical interfaces

The following source extracts give exact parameters, hypotheses and function spaces. Names are qualified by the namespace context in their listed source. The final transitive list is printed by `AuditKN.lean`; declarations below may include a general interface unused by the main theorem. No interface is treated as a kernel proof of the imported published theorem.

### KN/Analysis/LaplaceInterface.lean

The source header and declaration comments record the primary theorem/version.

```lean
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

axiom fourier_laplace_exists (a c : ℝ) (T : CDist) (hT : LaplaceAdmissible a c T) :
  ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | z.im < c} ∧ IsFourierLaplaceTransform T c F

axiom fourier_laplace_regular_integral (a c : ℝ) (f : ℝ → ℂ)
    (hf : LocallyIntegrable f (volume.restrict (Ioi a)))
    (hdamp : ∀ beta < c, Integrable (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t)
      (volume.restrict (Ioi a))) :
  let F : ℂ → ℂ := fun z => ∫ t in Ioi a, Complex.exp (-Complex.I*z*t)*f t
  AnalyticOnNhd ℂ F {z : ℂ | z.im < c} ∧
    IsFourierLaplaceTransform (Distribution.ofFun (⊤ : Opens ℝ) f
      (volume.restrict (Ioi a)) ⊤) c F

axiom fourier_laplace_derivative (T : CDist) (c : ℝ) (F : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F) :
  IsFourierLaplaceTransform (Distribution.lineDerivCLM (1:ℝ) T) c (fun z => Complex.I*z*F z)

axiom fourier_laplace_coordinate (T : CDist) (c : ℝ) (F : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F)
    (hhol : AnalyticOnNhd ℂ F {z : ℂ | z.im < c}) :
  IsFourierLaplaceTransform (coordinateMultiply T) c (fun z => Complex.I*deriv F z)

axiom fourier_laplace_single_valued (T : CDist) (c : ℝ) (F G : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F) (hG : IsFourierLaplaceTransform T c G)
    (haF : AnalyticOnNhd ℂ F {z : ℂ | z.im < c})
    (haG : AnalyticOnNhd ℂ G {z : ℂ | z.im < c}) :
    ∀ z : ℂ, z.im < c → F z = G z

```

### KN/Analysis/ResolventSelfAdjoint.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.Analysis.ResolventSelfAdjointBound

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace External
/-- Precisely general classical input: surjectivity of nonreal shifts of a
self-adjoint operator. Source: Reed--Simon, Methods of Modern Mathematical
Physics I (1980), Theorem VIII.3, pp. 256--257, followed by a real affine
rescaling of T. The source proof establishes range surjectivity at ±i.
Verified text: https://djvu.online/file/UBTVnOK64NlqI (VIII.2).
This assumes no compactness, eigenbasis, angular realization or completeness.
Boundedness and the sharp resolvent norm are proved separately in Lean. -/
axiom selfAdjoint_nonreal_surjective (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) :
    Function.Surjective (fun u : T.domain => T u-z • (u:E))

```

### KN/Angular/ExternalHintz.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.Angular.WeakGraphTransform
import KN.Angular.ExternalMityaginSiegl
import KN.Background.Parameters
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Explicit published real-frequency angular input

P. Hintz, *Perturbations of Kerr–Newman black holes: separation and mode
stability*, arXiv:2609.33661v1, 27 September 2026, Lemma 1 and its proof.
https://arxiv.org/html/2609.33661v1 . The input is used ONLY at frequency zero.
The full four-component expression and maximal weak L² graph below are
explicit; the source establishes essential self-adjointness, identifies the
adjoint with that maximal graph, and proves compactness of the resolvent.
No spectral values, branch bookkeeping, coercivity, complex-frequency
completeness or upper-half-plane exclusion are included in this interface.
-/
namespace KN.Angular.External
noncomputable section

/-- Exact zero-frequency content of the published Hintz angular lemma. -/
axiom hintz_2026_v1_lemma1_zero_frequency
    (b : KN.Background) (hQ : b.Q ≠ 0) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) :
    ∃ T : FullAngularHilbert →ₗ.[ℂ] FullAngularHilbert,
      (∀ u v, (∃ hu : u ∈ T.domain, T ⟨u,hu⟩ = v) ↔ FullStaticGraph σ b.beta m u v) ∧
      IsSelfAdjoint T ∧ ∃ (z : ℂ) (R : ResolventAt T z), IsCompactOperator R.inverse

```

### KN/Angular/ExternalJacobi.lean

The source header and declaration comments record the primary theorem/version.

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# General classical trigonometric Jacobi spectral interface

Source: G. Szegő, Orthogonal Polynomials, fourth edition, AMS Colloquium
Publications 23 (1975), Jacobi chapter; NIST DLMF Table 18.5.1 (Rodrigues),
Table 18.8.1 row 2 (trigonometric differential equation), and §18.2(viii)
(completeness on a bounded interval). URLs https://dlmf.nist.gov/18.5,
https://dlmf.nist.gov/18.8, https://dlmf.nist.gov/18.2.viii .

This is the general α,β≥0 scalar Jacobi theorem, not an angular Dirac or
Kerr–Newman spectrum assertion. The canonical regular solution has exponent
α+1/2 at zero and β+1/2 at pi; the logarithmic branch at α=0 or β=0 is not
included. Identification with a first-order square still has to be proved.
-/
namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace

axiom regular_memLp (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
  MemLp (fun θ => (regularFunction α β n θ : ℂ)) 2 intervalMeasure

axiom orthonormal_complete (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
  Orthonormal ℂ (normalizedVector α β hα hβ) ∧
  Dense (Submodule.span ℂ (Set.range (normalizedVector α β hα hβ)) : Set H)

axiom regular_differential_equation (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
  -deriv (deriv (regularFunction α β n)) θ + potential α β θ*regularFunction α β n θ =
    ((n : ℝ)+(α+β+1)/2)^2*regularFunction α β n θ

axiom regular_smooth (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (regularFunction α β n) (Set.Ioo 0 Real.pi)

```

### KN/Angular/ExternalMityaginSiegl.lean

The source header and declaration comments record the primary theorem/version.

```lean
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Explicit published external interface, not a proved theorem

Source: B. Mityagin and P. Siegl, *Local form subordination without a power
decay and a criterion of Riesz basesness*, Bol. Soc. Mat. Mex. 31, 111 (2025),
published 21 August 2025, Theorem 2.2 (itself citing Dunford–Schwartz,
Corollary XI.9.31), DOI 10.1007/s40590-025-00751-7.
Verified against the published full text on 2026-10-21.

The interface below is only its general p=2 Hilbert-space specialization,
with the eight nonreal rays of C002. It does NOT assume any angular spectrum,
positivity, domain identification, PDE extraction or KN result. All those
hypotheses must be proved separately for a concrete operator.
-/
namespace KN.Angular.External
noncomputable section
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A genuine bounded two-sided inverse to T-z on its actual domain. -/
axiom mityagin_siegl_2025_theorem_2_2_p2
    (T : E →ₗ.[ℂ] E) (hclosed : T.IsClosed)
    (hdense : Dense (T.domain : Set E))
    (basis : HilbertBasis ℕ ℂ E) (z₀ : ℂ) (R₀ : ResolventAt T z₀)
    (hHS : Summable (fun n : ℕ => ‖R₀.inverse (basis n)‖^2))
    (hrays : ∀ j : Fin 8, ∃ (C R : ℝ) (N : ℕ), 0 < C ∧ 0 < R ∧
      ∀ r : ℝ, R ≤ r → ∃ Q : ResolventAt T (completenessRay j r),
        ‖Q.inverse‖ ≤ C*(1+r)^N) :
    Dense (Submodule.span ℂ {u : E | IsGeneralizedRoot T u} : Set E)

```

### KN/Angular/JacobiRecurrences.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.Angular.ExternalJacobi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! General published Jacobi identities, DLMF 18.9.3, 18.9.4,
18.9.5 and 18.9.15 (https://dlmf.nist.gov/18.9).
The parameter-shifting ladder relation below is PROVED from these general
identities; none of the interfaces asserts a Dirac spectrum or domain. -/
namespace KN.Angular.Jacobi
noncomputable section

axiom dlmf_18_9_3 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  polynomial α (β-1) (n+1) x - polynomial (α-1) β (n+1) x = polynomial α β n x

axiom dlmf_18_9_4 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  (1-x)*polynomial (α+1) β n x + (1+x)*polynomial α (β+1) n x =
    2*polynomial α β n x

axiom dlmf_18_9_5 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  (2*((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α β (n+1) x =
    (((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α (β+1) (n+1) x +
    (((n+1 : ℕ) : ℝ)+α)*polynomial α (β+1) n x

axiom dlmf_18_9_5_symmetric (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  (2*((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α β (n+1) x =
    (((n+1 : ℕ) : ℝ)+α+β+1)*polynomial (α+1) β (n+1) x -
    (((n+1 : ℕ) : ℝ)+β)*polynomial (α+1) β n x

axiom dlmf_18_9_15 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  HasDerivAt (polynomial α β (n+1))
    ((1/2)*(((n+1 : ℕ) : ℝ)+α+β+1)*polynomial (α+1) (β+1) n x) x

```

### KN/ChargedRadial/CanonicalInterface.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.ChargedRadial.TranslatedCalculus

/-!
Two general published interfaces absent from the pinned library.
1. I. M. Gel'fand and G. E. Shilov, Generalized Functions, Volume I,
   Chapter I §3: analytic continuation of one-sided powers and its
   multiplication and differential identities. The interface specifies the
   actual integral finite part, restricted to Re α > -2, α ≠ -1.
2. R. T. Seeley, Extension of C∞ functions defined in a half space,
   Proceedings of the American Mathematical Society 15 (1964), 625–626,
   DOI 10.1090/S0002-9939-1964-0165392-8.
   Only the scalar real-half-line consequence is used, not analytic extension.
No radial equation, exceptional cancellation, coefficient identity, endpoint
bound, or Kerr–Newman mode-exclusion assertion is assumed here.
-/
noncomputable section
open Set
namespace KN.ChargedRadial.External

axiom canonical_power_calculus : TranslatedCanonicalPowerCalculus


axiom smooth_halfline_extension (r : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ici r)) :
    ∃ g : ℝ → ℂ, Smooth g ∧ EqOn g f (Ici r)

```

### KN/Kerr/EllipticRegularity.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.Kerr.HilbertAngular
import KN.Analysis.ResolventPerturbation
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

/-!
Published external regularity interface, independent of frequency and radial
parameters. S. Dyatlov, Lecture notes for 18.155, Theorem 14.23, §14.2.3,
pp.194–195, https://math.mit.edu/~dyatlov/18.155/155-notes.pdf (2026-10-20).
Ellipticity is unchanged by a smooth zeroth-order potential and subtracting an
eigenvalue. The fixed-azimuthal realization is the closure of the actual smooth
spin-section graph. Thus the global spin-bundle theorem imposes the two regular
pole powers, including the logarithm-free zero-exponent cases. The formal
adjoint has conjugate potential because the static graph is real symmetric.
The output is an actual representative of the input L² class, not an assumed
angular eigenvalue or completeness assertion.
-/
namespace KN.Kerr
noncomputable section
open Set MeasureTheory
open scoped ContDiff

axiom regular_adjoint_eigenfunction (m s : ℤ)
    (T : AngularH →ₗ.[ℂ] AngularH)
    (hgraph : (T.graph : Set (AngularH × AngularH))=sphericalClosedGraph m s)
    (q : ℝ → ℂ) (hq : MemLp q ⊤ sphericalMeasure)
    (hsmooth : SmoothAxisymmetricPotential q)
    (z : ℂ) (v : AngularH) (hvne : v ≠ 0)
    (hv : v ∈ (KN.Analysis.boundedPerturbation T (angularMultiplier q hq)).adjoint.domain)
    (heig : (KN.Analysis.boundedPerturbation T (angularMultiplier q hq)).adjoint ⟨v,hv⟩ = z • v) :
    ∃ (u : ℝ → ℂ) (hu : MemLp u 2 sphericalMeasure),
      hu.toLp u=v ∧ CanonicalSmoothAngular m s u ∧
      (∃ θ ∈ Ioo (0:ℝ) Real.pi, u θ≠0) ∧
      ∀ θ ∈ Ioo (0:ℝ) Real.pi,
        angularOperator 0 s m 0 u θ + star (q θ)*u θ=z*u θ

```

### KN/Kerr/FuchsInterface.lean

The source header and declaration comments record the primary theorem/version.

```lean
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

```

### KN/Kerr/SphericalSpectrum.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.Kerr.HilbertAngular
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Classical spherical spectral interface. Goldberg, Macfarlane, Newman,
Rohrlich and Sudarshan, J. Math. Phys. 8 (1967), 2155–2161, §2, equations
(2.3), (2.5), (2.8), and the completeness statement on p.2156.
Primary author-hosted text: https://web2.ph.utexas.edu/~gsudama/pub/1967_008.pdf
The usual self-adjoint closure formulation is included. The graph is fixed
below as the closure of the smooth spin-section core; no maximal scalar
endpoint extension is allowed. This interface contains no complex-frequency
root completeness, radial statement, or exclusion theorem.
-/
namespace KN.Kerr
noncomputable section
open scoped ComplexInnerProductSpace

axiom spherical_spectral_data (m s : ℤ) : SphericalSpectralData m s

```

### KN/Kerr/WhitingInterface.lean

The source header and declaration comments record the primary theorem/version.

```lean
import KN.Kerr.AngularDomain
import KN.Boundary.Radial
import Mathlib.Analysis.Analytic.Basic

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

/-- Expanded form of the physical Teukolsky radial equation (52), with the
manuscript's canonical angular separation constant (not AMPW's shifted constant). -/
axiom whiting_negative_spin_non_special
    (b : KN.Background) (hQ : b.Q = 0) (m s : ℤ)
    (hs : s = -1 ∨ s = -2) (omega Λ : ℂ) (homega : 0 < omega.im)
    (u R : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m s omega Λ u)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (heq : PhysicalRadialEquation b m omega Λ s R)
    (hhor : NonSpecialIngoing b m s omega R)
    (hout : KN.Boundary.Outgoing b m omega R) :
    ∀ r ∈ Ioi b.rPlus, R r = 0

```

## Frozen verification records

The accepted final identity and actual full-build, fresh-checker, negative-control and independent-audit results will be recorded separately. Module compiles and author controls are not the three required independent audits.

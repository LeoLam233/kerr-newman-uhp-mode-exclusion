import KN.Kerr.AngularDomain
import KN.Boundary.Radial
import Mathlib.Analysis.Analytic.Basic

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

/-- Expanded form of the physical Teukolsky radial equation (52), with the
manuscript's canonical angular separation constant (not AMPW's shifted constant). -/
def PhysicalRadialEquation (b : KN.Background) (m : ℤ) (omega Λ : ℂ) (s : ℤ)
    (R : ℝ → ℂ) : Prop :=
  ∀ r ∈ Ioi b.rPlus,
    (b.Delta r : ℂ) * deriv (deriv R) r +
    ((s : ℂ) + 1) * (2 * ((r : ℂ) - b.M)) * deriv R r +
    ((b.frequencyK m omega r ^ 2 +
       2 * Complex.I * s * ((r : ℂ) - b.M) * b.frequencyK m omega r) /
       (b.Delta r : ℂ) + 4 * Complex.I * s * omega * r + s - Λ -
       (b.a : ℂ)^2 * omega^2 + 2 * b.a * m * omega) * R r = 0

/-- A canonical regular angular eigenfunction, nonzero on the physical interval. -/
def RegularAngularEigenfunction (b : KN.Background) (m s : ℤ) (omega Λ : ℂ)
    (u : ℝ → ℂ) : Prop :=
  CanonicalSmoothAngular m s u ∧
  (∃ θ ∈ Ioo (0 : ℝ) Real.pi, u θ ≠ 0) ∧
  ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
    angularOperator b.a s m omega u θ = Λ * u θ

/-- The non-special ingoing Frobenius branch. Analyticity is required only of
an actual local coefficient, and its leading coefficient is nonzero.
This is deliberately stronger than mere physical horizon smoothness; the
negative-spin horizon theorem must establish the bridge. -/
def NonSpecialIngoing (b : KN.Background) (m s : ℤ) (omega : ℂ)
    (R : ℝ → ℂ) : Prop :=
  ∃ g : ℝ → ℂ, AnalyticAt ℝ g b.rPlus ∧ g b.rPlus ≠ 0 ∧
    ∀ᶠ r in 𝓝[>] b.rPlus,
      R r = KN.Boundary.gauge b m omega r *
        (Real.rpow (b.Delta r) (-(s : ℝ)) : ℂ) * g r

namespace External
/-- Published external interface restricted to negative spins and the non-special
Frobenius horizon branch. Source: Whiting, J. Math. Phys. 30 (1989), 1301–1305,
https://doi.org/10.1063/1.528308; conventions and Definition 3 in Andersson–Ma–
Paganini–Whiting, arXiv:1607.02759v2, Section II.A.3.
No positive-spin mode theorem, new spin reversal, or smooth-to-Frobenius bridge
is assumed by this interface. Q=0 and all subextremality hypotheses are explicit. -/
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
end External
end KN.Kerr

namespace KN.Kerr
open Set

/-- Exact angular eigenfunction reflection, including the regular pole domain
and nonvanishing on the physical angular interval. -/
theorem RegularAngularEigenfunction.reflect {b : KN.Background} {m s : ℤ}
    {omega Λ : ℂ} {u : ℝ → ℂ}
    (hu : RegularAngularEigenfunction b m s omega Λ u) :
    RegularAngularEigenfunction b m (-s) omega Λ (angularReflect u) := by
  obtain ⟨hreg, ⟨θ, hθ, hnonzero⟩, heig⟩ := hu
  refine ⟨hreg.reflect, ?_, ?_⟩
  · refine ⟨Real.pi - θ, ?_, ?_⟩
    · constructor <;> linarith [hθ.1, hθ.2]
    · simpa [angularReflect] using hnonzero
  · intro x hx
    have hx' : Real.pi - x ∈ Ioo (0 : ℝ) Real.pi := by
      constructor <;> linarith [hx.1, hx.2]
    simpa only [Int.cast_neg, angularOperator_reflection, angularReflect] using heig (Real.pi - x) hx'

end KN.Kerr

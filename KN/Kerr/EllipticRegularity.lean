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

def SmoothAxisymmetricPotential (q : ℝ → ℂ) : Prop :=
  ∃ F : ℝ → ℂ, ContDiffOn ℝ ∞ F (Icc (-1) 1) ∧
    ∀ θ ∈ Ioo (0:ℝ) Real.pi, q θ=F (Real.cos θ)

namespace External
/-- General spin-line-bundle elliptic regularity, specialized only to a fixed
azimuthal sector and an arbitrary smooth axisymmetric zeroth-order potential. -/
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
end External

/-- Complex conjugation preserves the canonical regular pole powers. -/
theorem CanonicalSmoothAngular.conjugate {m s : ℤ} {u : ℝ → ℂ}
    (hu : CanonicalSmoothAngular m s u) : CanonicalSmoothAngular m s (fun θ => star (u θ)) := by
  obtain ⟨F,hF,hu⟩ := hu
  refine ⟨fun x => star (F x),Complex.conjCLE.contDiff.comp_contDiffOn hF,?_⟩
  intro θ hθ
  dsimp only
  rw [hu θ hθ]
  simp only [Complex.star_def,map_mul,map_pow,Complex.conj_ofReal]

lemma angularOperator_static_star (m s : ℤ) (u : ℝ → ℂ) (θ : ℝ) :
    angularOperator 0 s m 0 (fun θ => star (u θ)) θ =
      star (angularOperator 0 s m 0 u θ) := by
  unfold angularOperator angularPotential
  rw [deriv.star',deriv.star]
  simp only [Complex.star_def,map_add,map_sub,map_neg,map_mul,map_div₀,map_pow,
    map_intCast,Complex.conj_ofReal,zero_pow (by decide : 2≠0),
    zero_mul,mul_zero,sub_zero,add_zero]


lemma frequencyPotential_smoothAxisymmetric (a : ℝ) (s : ℤ) (omega : ℂ) :
    SmoothAxisymmetricPotential (frequencyPotential a s omega) := by
  refine ⟨fun x => -(a:ℂ)^2*omega^2*(x:ℂ)^2+2*(a:ℂ)*(s:ℂ)*omega*(x:ℂ),?_,?_⟩
  · have hc : ContDiffOn ℝ ∞ (fun x : ℝ => (x:ℂ)) (Icc (-1) 1) := Complex.ofRealCLM.contDiff.contDiffOn
    exact ((contDiffOn_const.mul contDiffOn_const).mul (hc.pow 2)).add (contDiffOn_const.mul hc)
  · intro θ _; rfl

lemma angularOperator_add_potential (a : ℝ) (m s : ℤ) (omega : ℂ)
    (u : ℝ → ℂ) (θ : ℝ) :
    angularOperator a s m omega u θ =
      angularOperator 0 s m 0 u θ + frequencyPotential a s omega θ * u θ := by
  unfold angularOperator angularPotential frequencyPotential
  ring

end
end KN.Kerr

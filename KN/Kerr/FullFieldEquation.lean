import KN.Kerr.SphericalCompleteness
import KN.Kerr.WhitingInterface
import KN.Analysis.ResolventBoundaryMap

namespace KN.Kerr
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexInnerProductSpace

/-- The radial zeroth-order coefficient before angular separation. -/
def radialPotential (b : KN.Background) (m s : ℤ) (omega : ℂ) (r : ℝ) : ℂ :=
  (b.frequencyK m omega r ^ 2 +
    2 * Complex.I * s * ((r : ℂ) - b.M) * b.frequencyK m omega r) /
    (b.Delta r : ℂ) + 4 * Complex.I * s * omega * r + s -
    (b.a : ℂ)^2 * omega^2 + 2 * b.a * m * omega

/-- Actual Hilbert-valued Teukolsky equation on the canonical angular domain. -/
def FullFieldEquation (b : KN.Background) (m s : ℤ) (omega : ℂ)
    (F : ℝ → AngularH) : Prop :=
  ∀ r ∈ Ioi b.rPlus, ∃ hmem : F r ∈ (spheroidalOperator m s b.a omega).domain,
    (b.Delta r : ℂ) • deriv (deriv F) r +
      (((s : ℂ)+1)*(2*((r:ℂ)-b.M))) • deriv F r +
      radialPotential b m s omega r • F r =
      spheroidalOperator m s b.a omega ⟨F r,hmem⟩

/-- Differentiating twice commutes with each fixed bounded angular coefficient. -/
theorem second_deriv_clm_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {rp : ℝ} {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Ioi rp))
    (L : E →L[ℂ] ℂ) {r : ℝ} (hr : rp<r) :
    deriv (deriv (fun x => L (F x))) r = L (deriv (deriv F) r) := by
  have he : deriv (fun x => L (F x)) =ᶠ[𝓝 r] (fun x => L (deriv F x)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact KN.Boundary.deriv_clm_on hF L hx
  rw [he.deriv_eq]
  exact KN.Boundary.deriv_clm_on (hF.deriv_of_isOpen isOpen_Ioi (by simp)) L hr

/-- Pairing with an actual adjoint-chain member whose predecessor coefficient
vanishes gives the homogeneous separated radial equation. No pointwise angular
representative of the chain is needed. -/
theorem fullField_coefficient_equation
    (b : KN.Background) (m s : ℤ) (omega z : ℂ) (F : ℝ → AngularH)
    (hF : ContDiffOn ℝ ∞ F (Ioi b.rPlus)) (heq : FullFieldEquation b m s omega F)
    (v w : AngularH) (hv : v ∈ (spheroidalOperator m s b.a omega).adjoint.domain)
    (hchain : (spheroidalOperator m s b.a omega).adjoint ⟨v,hv⟩ = z • v+w)
    (hzero : ∀ r ∈ Ioi b.rPlus, ⟪w,F r⟫=0) :
    PhysicalRadialEquation b m omega (star z) s (fun r => ⟪v,F r⟫) := by
  let A := spheroidalOperator m s b.a omega
  have hd : Dense (A.domain : Set AngularH) :=
    (External.spherical_spectral_data m s).selfAdjoint.dense_domain
  intro r hr
  obtain ⟨hmem,he⟩ := heq r hr
  have hi := A.adjoint_isFormalAdjoint hd ⟨v,hv⟩ ⟨F r,hmem⟩
  change ⟪A.adjoint ⟨v,hv⟩,F r⟫=⟪v,A ⟨F r,hmem⟩⟫ at hi
  rw [hchain,inner_add_left,inner_smul_left,hzero r hr,add_zero] at hi
  have hh := congrArg (innerSL ℂ v) he
  change ⟪v, _⟫=⟪v,A ⟨F r,hmem⟩⟫ at hh
  rw [←hi] at hh
  simp only [inner_add_right,inner_smul_right] at hh
  erw [second_deriv_clm_on hF (innerSL ℂ v) hr,
    KN.Boundary.deriv_clm_on hF (innerSL ℂ v) hr]
  change _ = 0
  simp only [radialPotential] at hh
  change _ = _ at hh
  simp only [innerSL_apply_apply, starRingEnd_apply] at *
  linear_combination hh

end
end KN.Kerr

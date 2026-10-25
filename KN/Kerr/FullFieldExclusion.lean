import KN.Kerr.FullFieldEquation
import KN.Kerr.AngularEigenfunctionBridge
import KN.Kerr.SeparatedExclusion
import KN.Angular.DualChainExtraction

namespace KN.Kerr
noncomputable section
open Set
open scoped ContDiff ComplexInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Full fixed-m Kerr mode exclusion for all four nonzero integer spins.
The field takes values in the actual weighted spherical spin-section Hilbert
space and satisfies the canonical angular graph equation. The proof uses dense
adjoint generalized roots, chooses a globally first nonzero radial coefficient,
and applies the proved separated exclusion. No separated expansion, Riesz basis,
or semisimplicity assumption is made. -/
theorem kerr_full_field_exclusion
    (b : KN.Background) (hQ : b.Q=0) (m s : ℤ) (omega : ℂ)
    (hs : s=1 ∨ s=2 ∨ s= -1 ∨ s= -2) (homega : 0<omega.im)
    (F : ℝ → AngularH) (hF : ContDiffOn ℝ ∞ F (Ioi b.rPlus))
    (heq : FullFieldEquation b m s omega F)
    (hhor : KN.Boundary.HorizonRegular b m omega (-(s:ℝ)) F)
    (hout : KN.Boundary.Outgoing b m omega F) :
    ∀ r ∈ Ioi b.rPlus, F r=0 := by
  intro r hr
  by_contra hn
  obtain ⟨z,v,w,hv,hstep,hdetect,hzero,e,he,hene,heeig⟩ :=
    KN.Angular.exists_first_detecting_chain_member
      (spheroidalOperator m s b.a omega).adjoint
      (spheroidal_dense_adjoint_roots m s b.a omega)
      (fun r : Ioi b.rPlus => F r) ⟨⟨r,hr⟩,hn⟩
  obtain ⟨u,hu⟩ := regularAngularEigenfunction_of_adjoint_eigenvector
    b m s omega z e hene he heeig
  have hphysical := fullField_coefficient_equation b m s omega z F hF heq v w hv hstep
    (fun x hx => hzero ⟨x,hx⟩)
  have hc : ContDiffOn ℝ ∞ (fun r => ⟪v,F r⟫) (Ioi b.rPlus) :=
    ((innerSL ℂ v).restrictScalars ℝ).contDiff.comp_contDiffOn hF
  have hhc := hhor.map (innerSL ℂ v)
  have hoc := hout.map hF (innerSL ℂ v)
  have hvanish := kerr_separated_exclusion b hQ m s omega (star z) hs homega
    u (fun r => ⟪v,F r⟫) hu hc hphysical hhc hoc
  obtain ⟨x,hx⟩ := hdetect
  exact hx (hvanish x x.property)

end
end KN.Kerr

import KN.Angular.OriginalSourceExclusion
import KN.Physics.KerrRadiativePointwise
import KN.Physics.PhysicalRadiativeRecovery

noncomputable section
namespace KN.Physics
open Set KN.Angular

/-- Charged physical radiative exclusion uses both complete ORIGINAL source
systems, followed by the exact phantom-invariant identification. -/
theorem charged_radiative_pointwise_zero (b : KN.Background) (hQ : b.Q≠0)
    (m : ℤ) (omega : ℂ) (homega : 0<omega.im)
    (raw : ℝ → ℝ → RadiativeCurvatureMaxwell)
    (h : PublishedPhysicalNecessaryData b m omega raw) :
    ∀ r θ, b.rPlus<r → θ ∈ Ioo 0 Real.pi →
      ∀ i, radiativeValue b r θ (raw r θ) i=0 := by
  obtain ⟨plus,minus,phantom,hplus,hminus,hid⟩ := h.charged hQ
  have hp := original_source_exclusion true b hQ m omega homega plus hplus
  have hm := original_source_exclusion false b hQ m omega homega minus hminus
  intro r θ hr hθ i
  obtain ⟨hg0,hg2,hp2,hp1,hm2,hm1,hinv⟩ := hid r θ hr hθ
  have hp0 := hp r hr hθ
  have hm0 := hm r hr hθ
  have hv := phantom_radiative_zero (b.M:ℂ) (b.Q:ℂ) (rhoStar b r θ)
    (backgroundPsiTwo b r θ) (phantom r θ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt b.mass_pos)) (rhoStar_ne_zero b hr θ) hg0 hg2
    (hp2.symm.trans (congrFun hp0 0)) (hm2.symm.trans (congrFun hm0 0))
    (hp1.symm.trans (congrFun hp0 1)) (hm1.symm.trans (congrFun hm0 1))
  rw [hinv i]
  cases i
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2

/-- The C002 theorem for the four literal physical invariant quantities,
conditional only on the explicitly stated classical necessary-system interface.
Every strictly subextremal background, signed charge, m and upper-half-plane
frequency is included. Axis values follow from original section regularity. -/
theorem radiative_mode_exclusion (b : KN.Background) (m : ℤ) (omega : ℂ)
    (homega : 0<omega.im) (raw : ℝ → ℝ → RadiativeCurvatureMaxwell)
    (h : PublishedPhysicalNecessaryData b m omega raw) :
    ∀ r θ, b.rPlus<r → θ ∈ Icc 0 Real.pi →
      ∀ i, radiativeValue b r θ (raw r θ) i=0 := by
  have hinterior : ∀ r θ, b.rPlus<r → θ ∈ Ioo 0 Real.pi →
      ∀ i, radiativeValue b r θ (raw r θ) i=0 := by
    by_cases hQ : b.Q=0
    · exact kerr_radiative_pointwise_zero b hQ m omega homega raw h
    · exact charged_radiative_pointwise_zero b hQ m omega homega raw h
  intro r θ hr hθ i
  have hi : EqOn (fun θ => radiativeValue b r θ (raw r θ) i) 0 (Ioo 0 Real.pi) :=
    fun θ hθ => hinterior r θ hr hθ i
  apply hi.of_subset_closure (h.axis_continuity i r hr) continuousOn_const Ioo_subset_Icc_self ?_ hθ
  rw [closure_Ioo (ne_of_lt Real.pi_pos)]

/-- Explicit one-way physical-theory bridge. No reconstruction of arbitrary NP
solutions is assumed. `entry` is the precisely typed published physical input,
while all C002-specific implications are proved by `radiative_mode_exclusion`. -/
theorem physical_mode_exclusion (b : KN.Background) (m : ℤ) (omega : ℂ)
    (homega : 0<omega.im) {P : Type*}
    (entry : PublishedEinsteinMaxwellEntry b m omega P) (p : P)
    (hp : entry.smoothOutgoingMode p) :
    ∀ r θ, b.rPlus<r → θ ∈ Icc 0 Real.pi → ∀ i,
      radiativeValue b r θ (entry.curvatureMaxwell p r θ) i=0 :=
  radiative_mode_exclusion b m omega homega (entry.curvatureMaxwell p) (entry.necessary p hp)

end KN.Physics

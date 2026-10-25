import KN.Physics.PhysicalEntry
import KN.Physics.SourceHilbertRecovery

noncomputable section
namespace KN.Physics
open Set MeasureTheory

/-- The spherical L² zero conclusion gives pointwise zero on the regular
angular chart for the original continuous radiative representative. -/
theorem kerr_radiative_pointwise_zero (b : KN.Background) (hQ : b.Q=0)
    (m : ℤ) (omega : ℂ) (homega : 0<omega.im)
    (raw : ℝ → ℝ → RadiativeCurvatureMaxwell)
    (h : PublishedPhysicalNecessaryData b m omega raw) :
    ∀ r θ, b.rPlus<r → θ ∈ Ioo 0 Real.pi →
      ∀ i, radiativeValue b r θ (raw r θ) i=0 := by
  obtain ⟨F,hF,hrep⟩ := h.kerr hQ
  have hz := kerr_all_radiative_fields_zero b hQ m omega homega F hF
  intro r θ hr hθ i
  obtain ⟨hc,he⟩ := hrep i r hr
  have hzero : (fun θ => (0:KN.Kerr.AngularH) θ) =ᵐ[KN.Kerr.sphericalMeasure]
      (fun _ => (0:ℂ)) := Lp.coeFn_zero ℂ 2 KN.Kerr.sphericalMeasure
  rw [hz i r hr] at he
  have ha := he.symm.trans hzero
  exact Measure.eqOn_open_of_ae_eq (source_ae_to_angular ha) isOpen_Ioo hc continuousOn_const hθ

end KN.Physics

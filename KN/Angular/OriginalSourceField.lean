import KN.Angular.SourceAngularSmooth
import KN.Physics.SourceHilbertBoundaryOriginal
import KN.Physics.SourceHilbertRepresentation
import KN.Physics.SourceFullPacking

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set KN.Physics
open scoped ContDiff

/-- Original source sections with their actual spherical-measure representatives.
Only original smoothness and original boost-weight boundary classes occur here;
no transformed PDE, angular domain, or separated coefficient is part of this data. -/
structure OriginalSourceField (positive : Bool) (b : KN.Background) (m : ℤ) (omega : ℂ) where
  components : ℝ → ℝ → Fin 4 → ℂ
  high : ℝ → SourceAngularHilbert
  low : ℝ → SourceAngularHilbert
  interior_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => components p.1 p.2)
    ((Ioi b.rPlus) ×ˢ (Ioo 0 Real.pi))
  high_rep : ∀ r, b.rPlus<r → high r =ᵐ[KN.Kerr.sphericalMeasure]
    fun θ => WithLp.toLp 2 ![components r θ 0,components r θ 2]
  low_rep : ∀ r, b.rPlus<r → low r =ᵐ[KN.Kerr.sphericalMeasure]
    fun θ => WithLp.toLp 2 ![components r θ 1,components r θ 3]
  boundary : OriginalSourceBoundary b m omega (if positive then 1 else -1) high low

namespace OriginalSourceField
variable {positive : Bool} {b : KN.Background} {m : ℤ} {omega : ℂ}

theorem angular_smooth (U : OriginalSourceField positive b m omega) {r : ℝ} (hr : b.rPlus<r)
    (i : Fin 4) : ContDiffOn ℝ ∞ (fun θ => U.components r θ i) (Ioo 0 Real.pi) := by
  have h := U.interior_smooth.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun θ hθ => show (r,θ) ∈ (Ioi b.rPlus) ×ˢ (Ioo 0 Real.pi) from ⟨hr,hθ⟩)
  exact contDiffOn_pi.mp h i

theorem radial_smooth (U : OriginalSourceField positive b m omega) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun r => U.components r θ i) (Ioi b.rPlus) := by
  have h := U.interior_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun r hr => show (r,θ) ∈ (Ioi b.rPlus) ×ˢ (Ioo 0 Real.pi) from ⟨hr,hθ⟩)
  exact contDiffOn_pi.mp h i

theorem source_differentiable (U : OriginalSourceField positive b m omega)
    (r θ : ℝ) (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) (i : Fin 4) :
    SourceDifferentiableAt (fun x y => U.components x y i) r θ := by
  constructor
  · exact ((U.radial_smooth ⟨hθ,hπ⟩ i).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hr)
  · exact ((U.angular_smooth hr i).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨hθ,hπ⟩)

def transformed (U : OriginalSourceField positive b m omega) (r : ℝ) : FullAngularHilbert :=
  sourcePack (sourceHilbertTransform positive b r (U.high r) (U.low r)).1
    (sourceHilbertTransform positive b r (U.high r) (U.low r)).2

theorem transformed_ae (U : OriginalSourceField positive b m omega) {r : ℝ} (hr : b.rPlus<r) :
    U.transformed r =ᵐ[angularMeasure] fun θ => WithLp.toLp 2
      (sourceFullVector positive b U.components r θ) := by
  filter_upwards [sourcePack_ae (sourceHilbertTransform positive b r (U.high r) (U.low r)).1
    (sourceHilbertTransform positive b r (U.high r) (U.low r)).2,
    sourceHilbertTransform_ae positive b hr (U.high r) (U.low r),
    source_ae_to_angular (U.high_rep r hr),source_ae_to_angular (U.low_rep r hr)] with θ hp ht hh hl
  have hpack : sourceFiberPack (U.high r) (U.low r) θ=U.components r θ := by
    ext i
    fin_cases i <;> simp [sourceFiberPack,hh,hl]
  rw [hpack] at ht
  change sourcePack _ _ θ=_
  rw [hp]
  apply WithLp.ofLp_injective 2
  change ![_,_,_,_]=_
  rw [show ((sourceHilbertTransform positive b r (U.high r) (U.low r)).1 θ : Fin 2 → ℂ)=_ from ht.1,
    show ((sourceHilbertTransform positive b r (U.high r) (U.low r)).2 θ : Fin 2 → ℂ)=_ from ht.2]
  rfl

end OriginalSourceField
end
end KN.Angular

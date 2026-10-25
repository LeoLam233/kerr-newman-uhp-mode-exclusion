import KN.Physics.SourceHilbertBoundaryEmbedding
import KN.Analysis.ResolventBoundaryMap

noncomputable section
open Set
open scoped ContDiff
namespace KN.Physics

/-- Boundary data of the original radiative source sections, not of the
transformed field. The high/low boost weights are respectively 2 sigma and sigma.
The input Hilbert space carries the physical spherical measure sin(theta)dtheta. -/
structure OriginalSourceBoundary (b : KN.Background) (m : ℤ) (omega : ℂ) (sigma : ℝ)
    (high low : ℝ → SourceAngularHilbert) : Prop where
  high_smooth : ContDiffOn ℝ ∞ high (Ioi b.rPlus)
  low_smooth : ContDiffOn ℝ ∞ low (Ioi b.rPlus)
  high_horizon : KN.Boundary.HorizonRegular b m omega (-2*sigma) high
  low_horizon : KN.Boundary.HorizonRegular b m omega (-sigma) low
  high_outgoing : KN.Boundary.Outgoing b m omega high
  low_outgoing : KN.Boundary.Outgoing b m omega low

/-- The fixed sqrt-sine isometry preserves the original physical boundary
conditions; source-matrix transport has not yet been applied. -/
theorem original_source_embedding_boundary (b : KN.Background) (m : ℤ) (omega : ℂ)
    (sigma : ℝ) (high low : ℝ → SourceAngularHilbert)
    (h : OriginalSourceBoundary b m omega sigma high low) :
    KN.Boundary.HorizonRegular b m omega (-2*sigma) (fun r => sourceAngularEmbedding (high r)) ∧
    KN.Boundary.HorizonRegular b m omega (-sigma) (fun r => sourceAngularEmbedding (low r)) ∧
    KN.Boundary.Outgoing b m omega (fun r => sourceAngularEmbedding (high r)) ∧
    KN.Boundary.Outgoing b m omega (fun r => sourceAngularEmbedding (low r)) :=
  ⟨h.high_horizon.map sourceAngularEmbedding.toContinuousLinearMap,
   h.low_horizon.map sourceAngularEmbedding.toContinuousLinearMap,
   h.high_outgoing.map h.high_smooth sourceAngularEmbedding.toContinuousLinearMap,
   h.low_outgoing.map h.low_smooth sourceAngularEmbedding.toContinuousLinearMap⟩

end KN.Physics

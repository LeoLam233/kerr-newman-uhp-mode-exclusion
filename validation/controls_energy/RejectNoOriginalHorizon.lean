import KN.Physics.SourceHilbertBoundaryHorizonFinal
open Set
open scoped ContDiff
-- Original source outgoing and exterior smoothness do not manufacture original horizon profiles.
example (b : KN.Background) (m : ℤ) (omega : ℂ)
    (high low : ℝ → KN.Physics.SourceAngularHilbert)
    (hsH : ContDiffOn ℝ ∞ high (Ioi b.rPlus))
    (hsL : ContDiffOn ℝ ∞ low (Ioi b.rPlus))
    (hoH : KN.Boundary.Outgoing b m omega high)
    (hoL : KN.Boundary.Outgoing b m omega low) :
    KN.Boundary.HorizonRegular b m omega ((-1:ℝ)/4)
      (fun r => (KN.Physics.sourceHilbertTransform true b r (high r) (low r)).1+
        (KN.Physics.sourceHilbertTransform true b r (high r) (low r)).2) := by
  apply (KN.Physics.source_hilbert_horizon_positive b m omega high low ?_).1
  exact ⟨hsH,hsL,by assumption,by assumption,hoH,hoL⟩

import KN.Angular.OriginalSourceExclusion
-- Expected rejection: arbitrary L²-valued original blocks cannot supply physical boundary data.
example (positive : Bool) (b : KN.Background) (m : ℤ) (omega : ℂ)
    (high low : ℝ → KN.Physics.SourceAngularHilbert) :
    KN.Physics.OriginalSourceBoundary b m omega (if positive then 1 else -1) high low := by
  assumption

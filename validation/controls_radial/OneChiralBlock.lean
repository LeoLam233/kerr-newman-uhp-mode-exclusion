import KN.Physics.PhysicalTransform
open KN.Physics
-- EXPECTED FAILURE: knowing only the first transformed block does not recover the source.
example (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0)
    {r t : ℝ} (hr : b.rPlus < r) (ht : 0 < t) (hp : t < Real.pi)
    (u : Fin 4 → ℂ) (hz : (sourceTransform positive b r t u).1 = 0) : u = 0 := by
  exact sourceTransform_zero positive b hQ hr ht hp u hz

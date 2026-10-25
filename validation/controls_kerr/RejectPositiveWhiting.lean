import KN.Kerr.WhitingInterface
open KN.Kerr
/-- EXPECTED FAILURE: the published interface is not callable at spin +1. -/
example (b : KN.Background) (hQ : b.Q=0) :=
  External.whiting_negative_spin_non_special b hQ 0 1 (by norm_num)

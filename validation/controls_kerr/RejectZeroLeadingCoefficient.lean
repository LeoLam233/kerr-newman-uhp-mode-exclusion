import KN.Kerr.WhitingInterface
open KN.Kerr
/-- EXPECTED FAILURE: analytic zero is not a non-special Frobenius leading coefficient. -/
example (b : KN.Background) (m s : ℤ) (omega : ℂ) :
    NonSpecialIngoing b m s omega (fun _ => 0) := by
  refine ⟨(fun _ => 0), analyticAt_const, ?_, ?_⟩
  · norm_num
  · exact Filter.Eventually.of_forall (fun _ => by simp)

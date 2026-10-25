import KN.Kerr.FuchsInterface
open KN.Kerr
/-- EXPECTED FAILURE: the general smooth Fuchs uniqueness interface requires
1 < Re(B/A); the resonant A=1, B=0 case does not satisfy it. -/
example := External.fuchs_smooth_halfline_classification 0
  (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun r => (r:ℂ))
  (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_const)
  (fun _ _ => analyticAt_const) (fun _ _ => one_ne_zero) (by norm_num)

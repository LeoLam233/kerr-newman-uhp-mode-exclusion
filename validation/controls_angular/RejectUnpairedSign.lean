import KN.Angular.StaticEigenFamily
-- Expected rejection: dropping the unpaired minus sign changes the spectrum.
example : KN.Angular.Jacobi.staticEigenvalue 0 3 (.inr ⟨by norm_num⟩) = 3 := by
  norm_num [KN.Angular.Jacobi.staticEigenvalue]

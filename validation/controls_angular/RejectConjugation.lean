import KN.Angular.PrimalEigenvector
-- Expected rejection: adjoint eigenvalue I becomes -I, not I, under real structure.
example : star (Complex.I : ℂ) = Complex.I := by simp

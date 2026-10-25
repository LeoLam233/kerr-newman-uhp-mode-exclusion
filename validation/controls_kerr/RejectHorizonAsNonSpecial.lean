import KN.Kerr.WhitingInterface
open KN.Kerr
/-- EXPECTED FAILURE: smooth physical horizon data cannot be supplied as a
nonzero analytic Frobenius coefficient without the proved negative-spin bridge. -/
example (b : KN.Background) (m s : ℤ) (omega : ℂ) (R : ℝ → ℂ)
    (h : KN.Boundary.HorizonRegular b m omega (-(s:ℝ)) R) :
    NonSpecialIngoing b m s omega R := h

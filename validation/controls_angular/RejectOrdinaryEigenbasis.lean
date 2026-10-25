import Mathlib.Analysis.Complex.Basic
-- Expected rejection: a nonzero generalized vector need not be an eigenvector.
example : ((fun v : ℂ × ℂ => (v.2,(0:ℂ))) (0,1)) = (0,0) := by norm_num

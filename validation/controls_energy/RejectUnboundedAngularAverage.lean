import KN.Energy.Coercivity
-- q=100 violates the actual normalized angular expectation upper bound.
example : 0<(3:ℝ)^2*(1^2+2*0^2/(3-2))+2*1^2*3-1^2*100 :=
  KN.Energy.B_strict_positive 0 1 1 3 100 (by norm_num) (by norm_num) (by norm_num)

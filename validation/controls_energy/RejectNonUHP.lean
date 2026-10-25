import KN.Energy.Coercivity
-- Must fail specifically at the missing strict upper-half-plane premise.
example : (1:ℝ)=0 :=
  KN.Energy.mass_energy_eq_zero 1 1 0 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

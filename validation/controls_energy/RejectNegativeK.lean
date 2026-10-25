import KN.Energy.Coercivity
-- omega=i is UHP and the exact energy equation holds, but K=-1 is forbidden.
example : (1:ℝ)=0 :=
  KN.Energy.mass_energy_eq_zero Complex.I 0 (-1) 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [Complex.I_sq])

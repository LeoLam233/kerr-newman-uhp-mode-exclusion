import KN.ChargedRadial.OrderedSubstitution
-- The physical coefficient theorem does not accept an arbitrary spin sigma=0.
example (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam x : ℂ) : True := by
  have h := KN.ChargedRadial.physical_fourier_coefficients b hQ m 0 omega lam x (by norm_num)
  exact True.intro

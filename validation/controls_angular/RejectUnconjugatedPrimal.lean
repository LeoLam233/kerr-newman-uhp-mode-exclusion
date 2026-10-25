import KN.Angular.PrimalEigenvector
open KN.Angular
-- Expected rejection: the actual bridge returns star z, not z.
example (b : KN.Background) (hQ : b.Q≠0) (sigma : ℝ) (hsigma : sigma=1 ∨ sigma= -1)
    (m : ℤ) (omega z : ℂ) (e : FullAngularHilbert)
    (he : e ∈ (fullFrequencyOperator b hQ sigma hsigma m omega).adjoint.domain)
    (hee : (fullFrequencyOperator b hQ sigma hsigma m omega).adjoint ⟨e,he⟩=z • e)
    (hne : e≠0) (hc : ChiralVector e) :
    ∃ u : AngularHilbert, u≠0 ∧ StaticGraph sigma b.beta m u
      (z • u-omega • reducedFrequencyMultiplier b sigma u) := by
  exact reduced_eigenvector_of_chiral_adjoint b hQ sigma hsigma m omega z e he hee hne hc

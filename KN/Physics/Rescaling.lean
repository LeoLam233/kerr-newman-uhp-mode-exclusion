import KN.Boundary.Multiplier

noncomputable section
namespace KN.Physics

/-- Actual first-order system transport (26)→(28), without dividing by A or B. -/
theorem weighted_pair_transport {Δ p w z : ℝ → ℂ} {A B L Δ' p' w' z' : ℂ} {r : ℝ}
    (hΔ : HasDerivAt Δ Δ' r) (hp : HasDerivAt p p' r)
    (hw : HasDerivAt w w' r) (hz : HasDerivAt z z' r)
    (hbalance : Δ r*p' + L*p r = 0)
    (heq1 : w' = A*z r)
    (heq2 : Δ r*z' + (Δ'-L)*z r = B*w r) :
    Δ r*deriv (fun x => p x*w x) r + L*(p r*w r) = A*(Δ r*p r*z r) ∧
    deriv (fun x => Δ x*p x*z x) r = B*(p r*w r) := by
  rw [(hp.fun_mul hw).deriv, ((hΔ.fun_mul hp).fun_mul hz).deriv]
  constructor
  · linear_combination w r * hbalance + Δ r*p r*heq1
  · linear_combination z r*hbalance + p r*heq2

/-- The concrete C002 pair v=pw,z=Δpw♯ satisfies (28). -/
theorem charged_pair_transport (b : KN.Background) (m : ℤ) (ω : ℂ) (σ : ℝ)
    (w ws : ℝ → ℂ) {r : ℝ} (hr : b.rPlus < r)
    (hw : DifferentiableAt ℝ w r) (hws : DifferentiableAt ℝ ws r)
    (A B : ℂ)
    (heq1 : deriv w r = A*ws r)
    (heq2 : (b.Delta r:ℂ)*deriv ws r +
      (((1-3*(σ:ℂ))/2)*(2*(r:ℂ)-2*b.M) +
        2*Complex.I*(b.frequencyK m ω r-(b.eta:ℂ)*ω*(b.Delta r:ℂ)))*ws r = B*w r) :
    let p := KN.Boundary.radialMultiplier b m ω (-(1+3*σ)/2)
    let L := ((1+3*(σ:ℂ))/2)*(2*(r:ℂ)-2*b.M) -
      2*Complex.I*(b.frequencyK m ω r-(b.eta:ℂ)*ω*(b.Delta r:ℂ))
    (b.Delta r:ℂ)*deriv (fun x => p x*w x) r + L*(p r*w r) = A*((b.Delta r:ℂ)*p r*ws r) ∧
    deriv (fun x => (b.Delta x:ℂ)*p x*ws x) r = B*(p r*w r) := by
  dsimp only
  have hp := KN.Boundary.radialMultiplier_hasDerivAt b m ω (-(1+3*σ)/2) hr
  apply weighted_pair_transport (KN.Boundary.delta_hasDerivAt b r).ofReal_comp
    hp hw.hasDerivAt hws.hasDerivAt
  · rw [← hp.deriv]
    exact KN.Boundary.radialMultiplier_balance b m ω σ hr
  · exact heq1
  · convert heq2 using 1; push_cast; ring

end KN.Physics

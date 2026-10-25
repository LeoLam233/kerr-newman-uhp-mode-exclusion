import KN.Energy.PhysicalAngularAverage
import KN.Angular.Expectations

noncomputable section
open scoped ComplexInnerProductSpace
namespace KN.ChargedRadial
open KN.Energy KN.Angular

/-- Quantities obtained from an actual normalized static-domain vector, together
with the first-order eigenvalue expectations. No angular coercivity is assumed. -/
structure PhysicalAngularData (b : KN.Background) (m : ℤ) (sigma : ℝ) (omega lam : ℂ) where
  u : AngularHilbert
  staticImage : AngularHilbert
  normalized : ‖u‖=1
  graph : StaticGraph sigma b.beta m u staticImage
  av : ℝ
  cross : ℝ
  sineAvg : ℝ
  sine_le_one : sineAvg ≤ 1
  first_expectation : lam=((⟪u,staticImage⟫).re:ℂ)+omega*av
  squared_expectation : lam^2=(b.beta:ℂ)^2+(‖staticImage‖^2-b.beta^2:ℝ)+
    omega*cross+omega^2*((b.a^2*(b.c^2+sineAvg):ℝ):ℂ)

namespace PhysicalAngularData

theorem T_nonneg (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (sigma : ℝ)
    (hs : sigma=1 ∨ sigma= -1) (omega lam : ℂ)
    (d : PhysicalAngularData b m sigma omega lam) : 0 ≤ ‖d.staticImage‖^2-b.beta^2 := by
  have hh := physical_static_norm_gap b hQ sigma hs m d.u d.staticImage d.graph
  rw [d.normalized,one_pow,mul_one] at hh
  linarith

theorem D_le (b : KN.Background) (m : ℤ) (sigma : ℝ) (omega lam : ℂ)
    (d : PhysicalAngularData b m sigma omega lam) :
    b.a^2*(b.c^2+d.sineAvg) ≤ b.a^2*b.kappa^2 := by
  have hh := b.kappa_sq_sub_c_sq
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith [d.sine_le_one]

theorem K_nonneg (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (sigma : ℝ)
    (hs : sigma=1 ∨ sigma= -1) (omega lam : ℂ)
    (d : PhysicalAngularData b m sigma omega lam) {x : ℝ} (hx : x < -b.h) :
    0 ≤ angularK b (‖d.staticImage‖^2-b.beta^2) (⟪d.u,d.staticImage⟫).re sigma x := by
  exact physical_normalized_angularK_nonneg b hQ sigma hs m d.u d.staticImage
    d.normalized d.graph hx.le

end PhysicalAngularData
end KN.ChargedRadial

import KN.Energy.PhysicalGaugeWeights
import KN.ChargedRadial.OrderedSubstitution

noncomputable section
namespace KN.Energy
open KN.ChargedRadial

def angularBracket (b : KN.Background) (m : ℤ) (ω lam : ℂ) (σ x : ℝ) : ℂ :=
  (b.beta:ℂ)^2-lam^2+
    (3*(σ:ℂ)*b.h/2-b.c*lam)/(x:ℂ)+2*b.a*m*ω*x+ω^2*(radialR b x:ℂ)

theorem physical_weighted_potential (positive : Bool) (b : KN.Background) (m : ℤ)
    (ω lam : ℂ) {x : ℝ} (hx : x < -b.h) :
    (systemMu positive b x:ℂ)*
      (transformD0 (backgroundPolynomialData b m (spinSign positive) ω lam) x+
        ω*transformD1 (backgroundPolynomialData b m (spinSign positive) ω lam) x+
        ω^2*transformD2 (backgroundPolynomialData b m (spinSign positive) ω lam) x)+
      ω^2*(systemQ positive b x:ℂ)*(phaseRate b x:ℂ) =
    (systemW positive b x:ℂ)*angularBracket b m ω lam (spinSign positive) x := by
  have hn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by have := b.h_pos; linarith)
  have he : ((x+b.eta:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    change x < -(b.eta+2) at hx; linarith)
  have hh : ((x+b.h:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have ht : ((-b.h-x:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  cases positive <;>
    dsimp [systemMu,systemQ,systemW,spinSign,muPlus,muMinus,weightQPlus,weightQMinus,
      Wplus,Wminus,phaseRate,angularBracket,transformD0,transformD1,transformD2,
      backgroundPolynomialData,radialR] <;>
    rw [b.delta_sq] <;>
    simp only [KN.Background.h] at * <;>
    push_cast at *
  all_goals field_simp [hn,he,hh,ht]
  all_goals ring

end KN.Energy

import KN.Energy.PhysicalFiniteEndpoint
import KN.ChargedRadial.GaugeWeights

noncomputable section
namespace KN.Energy
open KN.ChargedRadial

def spinSign (positive : Bool) : ℝ := if positive then 1 else -1
def systemMu (positive : Bool) (b : KN.Background) : ℝ → ℝ :=
  if positive then muPlus b.eta else muMinus b.eta
def systemQ (positive : Bool) (b : KN.Background) : ℝ → ℝ :=
  if positive then weightQPlus b.M b.eta else weightQMinus b.M b.eta
def phaseRate (b : KN.Background) (x : ℝ) : ℝ := b.M*(1+2/(-b.h-x))

theorem phaseRate_hasDerivAt (b : KN.Background) {x : ℝ} (hx : x < -b.h) :
    HasDerivAt (phaseRate b) (2*b.M/(-b.h-x)^2) x := by
  have hn : -b.h-x ≠ 0 := by linarith
  convert ((hasDerivAt_const x (1:ℝ)).add
    ((hasDerivAt_const x (2:ℝ)).div ((hasDerivAt_const x (-b.h)).sub (hasDerivAt_id x)) hn)).const_mul b.M using 1
  · rfl
  · dsimp
    ring

theorem systemP_hasDerivAt (positive : Bool) (b : KN.Background) {x : ℝ} (hx : x < -b.h) :
    HasDerivAt (systemP positive b)
      (systemMu positive b x*(x^2-b.eta*b.h-3*spinSign positive*x*(x+b.h))) x := by
  have hn : x ≠ 0 := by have := b.h_pos; linarith
  have he : x+b.eta ≠ 0 := by change x < -(b.eta+2) at hx; linarith
  cases positive
  · convert weightPMinus_hasDerivAt b.eta b.h x hn using 1
    · funext y
      dsimp [systemP,Pminus,weightPMinus,KN.Background.h]
      ring
    · dsimp [systemMu,spinSign]
      ring
  · convert weightPPlus_hasDerivAt b.eta b.h x hn he using 1
    · funext y
      dsimp [systemP,Pplus,weightPPlus,KN.Background.h]
      ring
    · dsimp [systemMu,spinSign]
      ring

theorem systemQ_hasDerivAt (positive : Bool) (b : KN.Background) {x : ℝ} (hx : x < -b.h) :
    HasDerivAt (systemQ positive b)
      (systemMu positive b x*(b.M*(x+b.eta)*(x-b.eta-3*spinSign positive*x))) x := by
  have hn : x ≠ 0 := by have := b.h_pos; linarith
  have he : x+b.eta ≠ 0 := by change x < -(b.eta+2) at hx; linarith
  cases positive
  · simpa [systemQ,systemMu,spinSign] using weightQMinus_hasDerivAt b.M b.eta x hn
  · simpa [systemQ,systemMu,spinSign] using weightQPlus_hasDerivAt b.M b.eta x hn he

theorem system_weight_identities (positive : Bool) (b : KN.Background) {x : ℝ} (hx : x < -b.h) :
    systemMu positive b x*(x*(x+b.eta)*(x+b.h))=systemP positive b x ∧
    systemMu positive b x*x=systemW positive b x ∧
    systemMu positive b x*(2*b.M*x*(x+b.eta)^2)=2*systemQ positive b x ∧
    systemQ positive b x=systemP positive b x*phaseRate b x := by
  have hn : x ≠ 0 := by have := b.h_pos; linarith
  have he : x+b.eta ≠ 0 := by change x < -(b.eta+2) at hx; linarith
  have hh : x+b.h ≠ 0 := by linarith
  have ht : -b.h-x ≠ 0 := by linarith
  cases positive <;>
    dsimp [systemMu,systemP,systemW,systemQ,spinSign,phaseRate,
      muPlus,muMinus,Pplus,Pminus,Wplus,Wminus,weightQPlus,weightQMinus] <;>
    simp only [KN.Background.h] at *
  all_goals repeat' constructor
  all_goals field_simp [hn,he,hh,ht]
  all_goals ring

end KN.Energy

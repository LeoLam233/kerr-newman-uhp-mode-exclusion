import KN.Angular.OriginalSourceExclusion
import KN.Angular.Jordan

noncomputable section
open KN KN.Angular Set
open scoped ComplexInnerProductSpace

def negativeCharge : Background := ⟨2,0,-1,by norm_num,by norm_num⟩
def positiveCharge : Background := ⟨2,0,1,by norm_num,by norm_num⟩

example : negativeCharge.beta = -3 ∧ negativeCharge.c = -4/3 := by
  norm_num [negativeCharge,Background.beta,Background.c,Background.d]
example : positiveCharge.beta = 3 ∧ positiveCharge.c = 4/3 := by
  norm_num [positiveCharge,Background.beta,Background.c,Background.d]
example : 0 < (-negativeCharge.beta)^2-negativeCharge.beta^2+
    (negativeCharge.c/(-negativeCharge.h))*(-negativeCharge.beta-negativeCharge.beta) :=
  physical_unpaired_plus negativeCharge (by norm_num [negativeCharge]) _ le_rfl
example : 0 < (-positiveCharge.beta)^2-positiveCharge.beta^2+
    (positiveCharge.c/(-positiveCharge.h))*(-positiveCharge.beta-positiveCharge.beta) :=
  physical_unpaired_plus positiveCharge (by norm_num [positiveCharge]) _ le_rfl
example : Jacobi.staticEigenvalue 0 (-3) (.inr ⟨by norm_num⟩) = 3 := by norm_num [Jacobi.staticEigenvalue]
example : Jacobi.staticEigenvalue 0 3 (.inr ⟨by norm_num⟩) = -3 := rfl
example : ¬ (|(2:ℤ)| ≤ 1) := by norm_num
example : star (Complex.I : ℂ) = -Complex.I := by simp
example : star (Complex.I : ℂ) ≠ Complex.I := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

-- A genuine length-two nilpotent block: eigenvectors alone miss the second coordinate.
def nilpotent (v : ℂ × ℂ) : ℂ × ℂ := (v.2,0)
example : nilpotent (0,1) = (1,0) ∧ nilpotent (1,0) = 0 := by constructor <;> rfl
example (v : ℂ × ℂ) (hv : nilpotent v=0) : v.2=0 := by
  exact congrArg Prod.fst hv
example : ((0,1) : ℂ × ℂ) ≠ 0 := by simp

-- Exact whole-field contract, with no separated ansatz or complex-frequency basis input.
example (positive : Bool) (b : Background) (hQ : b.Q≠0) (m : ℤ) (omega : ℂ)
    (homega : 0<omega.im)
    (Z : FullField b hQ (KN.Energy.spinSign positive)
      (KN.ChargedRadial.spinSign_cases positive) m omega) :
    EqOn Z.field 0 (Ioi b.rPlus) :=
  charged_full_field_exclusion positive b hQ m omega homega Z

-- Original boost-weight boundary record is required, not merely pointwise L² membership.
example (positive : Bool) (b : Background) (hQ : b.Q≠0) (m : ℤ) (omega : ℂ)
    (homega : 0<omega.im) (U : OriginalSourceField positive b m omega)
    (hs : KN.Physics.PublishedChiralSystem positive b m omega U.components) :
    ∀ r, b.rPlus<r → EqOn (U.components r) 0 (Ioo 0 Real.pi) :=
  original_source_exclusion positive b hQ m omega homega U hs

example (b : Background) (hQ : b.Q≠0) (sigma : ℝ)
    (hsigma : sigma=1 ∨ sigma= -1) (m : ℤ) (omega : ℂ) :
    (fullFrequencyOperator b hQ sigma hsigma m omega).adjoint =
      fullFrequencyOperator b hQ sigma hsigma m (star omega) :=
  fullFrequencyOperator_adjoint b hQ sigma hsigma m omega

-- The opposite unpaired branch is exactly zero, not strictly positive.
example (beta c x : ℝ) : (-beta)^2-beta^2+(c/x)*(-beta-(-1)*beta)=0 := by ring
-- At zero eigenvalue the Jordan pairing still applies; no division by lambda.
example {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A I : E →ₗ[ℂ] E) (u prev : E)
    (hanti : ∀ v, A (I v)= -(I (A v))) (hchain : A u=prev) :
    A (I u)= -I prev := by
  simpa using paired_jordan_step A I 0 u prev hanti (by simpa using hchain)

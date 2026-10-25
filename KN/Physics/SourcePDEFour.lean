import KN.Physics.SourcePDERegularity
import KN.Angular.FullField

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

/-- The four-vector ordering used in Hintz (8) and C002 (2). -/
def joinSource (p q : Fin 2 → ℂ) : Fin 4 → ℂ := ![p 0,p 1,q 0,q 1]

def sourceFullVector (positive : Bool) (b : Background) (u : ℝ → ℝ → Fin 4 → ℂ)
    (r θ : ℝ) : Fin 4 → ℂ :=
  joinSource (sourceTransform positive b r θ (u r θ)).1
    (sourceTransform positive b r θ (u r θ)).2

def splitCoupling (R0 R1 W T : ℂ) : SourceMatrix :=
  !![R0+Complex.I*W,R1+Complex.I*T;-R1+Complex.I*T,R0-Complex.I*W]

lemma join_source_equations (t R0 R1 W T : ℂ)
    (p q pr qr pθ qθ : Fin 2 → ℂ)
    (hp : (fun i => t*pr i-Complex.I*pθ i)=splitCoupling R0 R1 W T *ᵥ q)
    (hq : (fun i => t*qr i+Complex.I*qθ i)=(splitCoupling R0 R1 W T).adjugate *ᵥ p) :
    (fun i => t*joinSource pr qr i)=
      derivativeMatrix *ᵥ joinSource pθ qθ + angularMatrix W T *ᵥ joinSource p q +
        R0 • (I4 *ᵥ joinSource p q)+R1 • (J4 *ᵥ joinSource p q) := by
  have hp0 := congrFun hp 0
  have hp1 := congrFun hp 1
  have hq0 := congrFun hq 0
  have hq1 := congrFun hq 1
  simp [splitCoupling,Matrix.adjugate_fin_two,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hp0 hp1 hq0 hq1
  ext i
  fin_cases i <;>
    simp [joinSource,derivativeMatrix,angularMatrix,I4,J4]
  · linear_combination hp0
  · linear_combination hp1
  · linear_combination hq0
  · linear_combination hq1

def sourceAngularW (b : Background) (m : ℤ) (omega σ : ℂ) (θ : ℝ) : ℂ :=
  (3:ℂ)/2*(Real.cos θ:ℂ)/(Real.sin θ:ℂ)+σ*(m:ℂ)/(Real.sin θ:ℂ)-
    σ*(b.a:ℂ)*(b.kappa:ℂ)*omega*(Real.sin θ:ℂ)
def sourceAngularT (b : Background) (omega σ : ℂ) (θ : ℝ) : ℂ :=
  -(b.beta:ℂ)-σ*(b.a:ℂ)*(b.c:ℂ)*omega*(Real.cos θ:ℂ)

lemma physicalChiralCoupling_split (b : Background) (m : ℤ) (omega : ℂ) (σ : ℝ)
    {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    physicalChiralCoupling b m omega σ r θ = splitCoupling
      (KN.Angular.radialR0 b σ m omega r) (KN.Angular.radialR1 b σ omega r)
      (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ) := by
  have ht : (Real.sqrt (b.Delta r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  have hdelta : (b.Delta r:ℂ)=(Real.sqrt (b.Delta r):ℂ)^2 := by
    exact_mod_cast (Real.sq_sqrt (le_of_lt (b.Delta_pos hr))).symm
  have hδ : deriv b.Delta r=2*r-2*b.M := (KN.Boundary.delta_hasDerivAt b r).deriv
  unfold physicalChiralCoupling chiralCoupling splitCoupling sourceAngularW sourceAngularT
    KN.Angular.radialR0 KN.Angular.radialR1
  rw [hδ]
  simp only [Background.eta,Background.kappa,Background.c,Background.beta,Background.d,Background.frequencyK]
  push_cast
  rw [hdelta]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- Literal four-component C002 equation (2), derived from the published
pre-integrating-factor system with no transformed-equation assumption. -/
theorem source_four_transport (positive : Bool) (b : Background) (hQ : b.Q≠0)
    (m : ℤ) (omega : ℂ) (σ : ℝ) (hσ : (σ:ℂ)=sourceSign positive)
    (u : ℝ → ℝ → Fin 4 → ℂ)
    (hs : PublishedChiralSystem positive b m omega u)
    (hu : ∀ r θ, b.rPlus<r → 0<θ → θ<Real.pi →
      ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) :
    (fun i => (Real.sqrt (b.Delta r):ℂ)*deriv (fun x => sourceFullVector positive b u x θ i) r)=
      derivativeMatrix *ᵥ (fun i => deriv (fun y => sourceFullVector positive b u r y i) θ) +
      angularMatrix (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ) *ᵥ sourceFullVector positive b u r θ +
      KN.Angular.radialR0 b σ m omega r • (I4 *ᵥ sourceFullVector positive b u r θ) +
      KN.Angular.radialR1 b σ omega r • (J4 *ᵥ sourceFullVector positive b u r θ) := by
  obtain ⟨hp,hm⟩ := source_chiral_transport positive b hQ m omega u hs
    (sourceChiralDifferentiable_of_original positive b u hu) hr hθ hπ
  rw [←hσ,physicalChiralCoupling_split b m omega σ hr θ] at hp hm
  let p := fun x y => (sourceTransform positive b x y (u x y)).1
  let q := fun x y => (sourceTransform positive b x y (u x y)).2
  unfold sourceVectorD sourceD at hp hm
  have hp' : (fun i => (Real.sqrt (b.Delta r):ℂ)*deriv (fun x => p x θ i) r-
      Complex.I*deriv (fun y => p r y i) θ)=
      splitCoupling (KN.Angular.radialR0 b σ m omega r) (KN.Angular.radialR1 b σ omega r)
        (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ) *ᵥ q r θ := by
    simpa only [neg_one_mul,neg_mul,sub_eq_add_neg,one_mul] using hp
  have hm' : (fun i => (Real.sqrt (b.Delta r):ℂ)*deriv (fun x => q x θ i) r+
      Complex.I*deriv (fun y => q r y i) θ)=
      (splitCoupling (KN.Angular.radialR0 b σ m omega r) (KN.Angular.radialR1 b σ omega r)
        (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ)).adjugate *ᵥ p r θ := by
    simpa only [one_mul] using hm
  have h := join_source_equations _ _ _ _ _ (p r θ) (q r θ) _ _ _ _ hp' hm'
  have hdr : (fun i => deriv (fun x => sourceFullVector positive b u x θ i) r)=
      joinSource (fun i => deriv (fun x => p x θ i) r) (fun i => deriv (fun x => q x θ i) r) := by
    ext i; fin_cases i <;> rfl
  have hdθ : (fun i => deriv (fun y => sourceFullVector positive b u r y i) θ)=
      joinSource (fun i => deriv (fun y => p r y i) θ) (fun i => deriv (fun y => q r y i) θ) := by
    ext i; fin_cases i <;> rfl
  rw [hdθ]
  have hdr' := congrArg (fun v : Fin 4 → ℂ => fun i => (Real.sqrt (b.Delta r):ℂ)*v i) hdr
  rw [hdr']
  exact h

end
end KN.Physics

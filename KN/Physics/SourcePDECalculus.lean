import KN.Physics.IntegratingFactor
import KN.Physics.CouplingAlgebra
import KN.Physics.PhysicalTransform
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

namespace KN.Physics
noncomputable section
open Matrix

/-- Actual complex chiral directional differential operator at an exterior point. -/
def sourceD (t ε : ℂ) (f : ℝ → ℝ → ℂ) (r θ : ℝ) : ℂ :=
  t * deriv (fun x => f x θ) r + ε * Complex.I * deriv (f r) θ

def SourceDifferentiableAt (f : ℝ → ℝ → ℂ) (r θ : ℝ) : Prop :=
  DifferentiableAt ℝ (fun x => f x θ) r ∧ DifferentiableAt ℝ (f r) θ

lemma sourceD_const (t ε c : ℂ) (r θ : ℝ) : sourceD t ε (fun _ _ => c) r θ=0 := by
  simp [sourceD]
lemma sourceD_add (t ε : ℂ) (f g : ℝ → ℝ → ℂ) (r θ : ℝ)
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) :
    sourceD t ε (fun x y => f x y+g x y) r θ=sourceD t ε f r θ+sourceD t ε g r θ := by
  unfold sourceD
  rw [deriv_fun_add hf.1 hg.1,deriv_fun_add hf.2 hg.2]
  ring
lemma sourceD_mul (t ε : ℂ) (f g : ℝ → ℝ → ℂ) (r θ : ℝ)
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) :
    sourceD t ε (fun x y => f x y*g x y) r θ=
      sourceD t ε f r θ*g r θ+f r θ*sourceD t ε g r θ := by
  unfold sourceD
  rw [deriv_fun_mul hf.1 hg.1,deriv_fun_mul hf.2 hg.2]
  ring
lemma sourceD_div (t ε : ℂ) (f g : ℝ → ℝ → ℂ) (r θ : ℝ)
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) (hne : g r θ≠0) :
    sourceD t ε (fun x y => f x y/g x y) r θ=
      (sourceD t ε f r θ*g r θ-f r θ*sourceD t ε g r θ)/(g r θ)^2 := by
  unfold sourceD
  rw [deriv_fun_div hf.1 hg.1 hne,deriv_fun_div hf.2 hg.2 hne]
  ring
lemma sourceD_const_mul (t ε c : ℂ) (f : ℝ → ℝ → ℂ) (r θ : ℝ)
    (hf : SourceDifferentiableAt f r θ) :
    sourceD t ε (fun x y => c*f x y) r θ=c*sourceD t ε f r θ := by
  unfold sourceD
  rw [deriv_const_mul c hf.1,deriv_const_mul c hf.2]
  ring
lemma sourceD_sub (t ε : ℂ) (f g : ℝ → ℝ → ℂ) (r θ : ℝ)
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) :
    sourceD t ε (fun x y => f x y-g x y) r θ=sourceD t ε f r θ-sourceD t ε g r θ := by
  unfold sourceD
  rw [deriv_fun_sub hf.1 hg.1,deriv_fun_sub hf.2 hg.2]
  ring

lemma SourceDifferentiableAt.const (c : ℂ) (r θ : ℝ) :
    SourceDifferentiableAt (fun _ _ => c) r θ := ⟨differentiableAt_const _,differentiableAt_const _⟩
lemma SourceDifferentiableAt.add {f g : ℝ → ℝ → ℂ} {r θ : ℝ}
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) :
    SourceDifferentiableAt (fun x y => f x y+g x y) r θ := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
lemma SourceDifferentiableAt.sub {f g : ℝ → ℝ → ℂ} {r θ : ℝ}
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) :
    SourceDifferentiableAt (fun x y => f x y-g x y) r θ := ⟨hf.1.sub hg.1,hf.2.sub hg.2⟩
lemma SourceDifferentiableAt.mul {f g : ℝ → ℝ → ℂ} {r θ : ℝ}
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) :
    SourceDifferentiableAt (fun x y => f x y*g x y) r θ := ⟨hf.1.mul hg.1,hf.2.mul hg.2⟩
lemma SourceDifferentiableAt.div {f g : ℝ → ℝ → ℂ} {r θ : ℝ}
    (hf : SourceDifferentiableAt f r θ) (hg : SourceDifferentiableAt g r θ) (hne : g r θ≠0) :
    SourceDifferentiableAt (fun x y => f x y/g x y) r θ := ⟨hf.1.div hg.1 hne,hf.2.div hg.2 hne⟩

lemma SourceDifferentiableAt.neg {f : ℝ → ℝ → ℂ} {r θ : ℝ}
    (hf : SourceDifferentiableAt f r θ) :
    SourceDifferentiableAt (fun x y => -f x y) r θ := ⟨hf.1.neg,hf.2.neg⟩
lemma SourceDifferentiableAt.conjugate {f : ℝ → ℝ → ℂ} {r θ : ℝ}
    (hf : SourceDifferentiableAt f r θ) :
    SourceDifferentiableAt (fun x y => star (f x y)) r θ :=
  ⟨hf.1.hasDerivAt.star.differentiableAt,hf.2.hasDerivAt.star.differentiableAt⟩

end
end KN.Physics

import KN.Energy.HorizonGauge
import KN.Energy.Vanishing

open Filter Set Asymptotics
open scoped Topology
namespace KN.Energy

/-- Multiplication adds finite-endpoint orders, on the positive side of t=b-x. -/
theorem horizon_mul_orders {R : Type*} [NormedRing R] (f g : ℝ → R) (b p q : ℝ)
    (hf : f =O[𝓝[<] b] (fun x : ℝ => (b-x)^p))
    (hg : g =O[𝓝[<] b] (fun x : ℝ => (b-x)^q)) :
    (fun x => f x*g x) =O[𝓝[<] b] (fun x : ℝ => (b-x)^(p+q)) := by
  refine (hf.mul hg).congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (Real.rpow_add (sub_pos.mpr hx) p q).symm

theorem horizon_normSq_order (U : ℝ → ℂ) (b p : ℝ)
    (hU : U =O[𝓝[<] b] (fun x : ℝ => (b-x)^p)) :
    (fun x => Complex.normSq (U x)) =O[𝓝[<] b] (fun x : ℝ => (b-x)^(2*p)) := by
  have h := horizon_mul_orders (fun x => ‖U x‖) (fun x => ‖U x‖) b p p hU.norm_left hU.norm_left
  simpa only [← pow_two, Complex.sq_norm, ← two_mul] using h

/-- The derivative, angular and mass energy terms have the common worst
order t^(2p-1). Setting p=2Mγ gives exactly the exponent in (47). -/
theorem density_horizon_order (ω : ℂ) (P W k B : ℝ → ℝ) (U V : ℝ → ℂ) (b p : ℝ)
    (hP : P =O[𝓝[<] b] (fun x : ℝ => b-x))
    (hk : (fun x => W x*k x) =O[𝓝[<] b] (fun x : ℝ => 1/(b-x)))
    (hB : (fun x => W x*B x) =O[𝓝[<] b] (fun x : ℝ => 1/(b-x)))
    (hU : U =O[𝓝[<] b] (fun x : ℝ => (b-x)^p))
    (hV : V =O[𝓝[<] b] (fun x : ℝ => (b-x)^(p-1))) :
    density ω P W k B U V =O[𝓝[<] b] (fun x : ℝ => (b-x)^(2*p-1)) := by
  have hp : P =O[𝓝[<] b] (fun x : ℝ => (b-x)^(1:ℝ)) := by simpa using hP
  have hk' : (fun x => W x*k x) =O[𝓝[<] b] (fun x : ℝ => (b-x)^(-1:ℝ)) := by simpa only [Real.rpow_neg_one, one_div] using hk
  have hB' : (fun x => W x*B x) =O[𝓝[<] b] (fun x : ℝ => (b-x)^(-1:ℝ)) := by simpa only [Real.rpow_neg_one, one_div] using hB
  have hA := horizon_mul_orders P (fun x => Complex.normSq (V x)) b 1 (2*(p-1)) hp (horizon_normSq_order V b (p-1) hV)
  have hK := horizon_mul_orders (fun x => W x*k x) (fun x => Complex.normSq (U x)) b (-1) (2*p) hk' (horizon_normSq_order U b p hU)
  have hC := (horizon_mul_orders (fun x => W x*B x) (fun x => Complex.normSq (U x)) b (-1) (2*p) hB' (horizon_normSq_order U b p hU)).const_mul_left (Complex.normSq ω)
  rw [show 1+2*(p-1) = 2*p-1 by ring] at hA
  rw [show -1+2*p = 2*p-1 by ring] at hK hC
  convert (hA.add hK).add hC using 1
  ext x
  dsimp [density]
  ring

/-- The boundary current has one additional power, hence tends to zero. -/
theorem current_horizon_order (ω : ℂ) (P : ℝ → ℝ) (U V : ℝ → ℂ) (b p : ℝ)
    (hP : P =O[𝓝[<] b] (fun x : ℝ => b-x))
    (hU : U =O[𝓝[<] b] (fun x : ℝ => (b-x)^p))
    (hV : V =O[𝓝[<] b] (fun x : ℝ => (b-x)^(p-1))) :
    current ω P U V =O[𝓝[<] b] (fun x : ℝ => (b-x)^(2*p)) := by
  have hp : (fun x => (P x:ℂ)) =O[𝓝[<] b] (fun x : ℝ => (b-x)^(1:ℝ)) := by
    apply IsBigO.of_norm_left
    simpa only [Complex.norm_real, Real.rpow_one] using hP.norm_left
  have hu : (fun x => star (U x)) =O[𝓝[<] b] (fun x : ℝ => (b-x)^p) := by
    apply IsBigO.of_norm_left
    simpa only [norm_star] using hU.norm_left
  have h := (horizon_mul_orders _ _ b (1+(p-1)) p
    (horizon_mul_orders _ _ b 1 (p-1) hp hV) hu).const_mul_left (star ω)
  rw [show 1+(p-1)+p = 2*p by ring] at h
  have hi : current ω P U V =O[𝓝[<] b]
      (fun x => star ω * ((P x:ℂ)*V x*star (U x))) := by
    refine isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall (fun x => ?_)⟩
    simpa only [current, Real.norm_eq_abs, one_mul, starRingEnd_apply] using Complex.abs_im_le_norm (star ω * ((P x:ℂ)*V x*star (U x)))
  exact hi.trans h
end KN.Energy

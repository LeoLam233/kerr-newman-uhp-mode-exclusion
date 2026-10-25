import KN.ChargedRadial.TranslatedCalculus

/-!
Two general published interfaces absent from the pinned library.
1. I. M. Gel'fand and G. E. Shilov, Generalized Functions, Volume I,
   Chapter I §3: analytic continuation of one-sided powers and its
   multiplication and differential identities. The interface specifies the
   actual integral finite part, restricted to Re α > -2, α ≠ -1.
2. R. T. Seeley, Extension of C∞ functions defined in a half space,
   Proceedings of the American Mathematical Society 15 (1964), 625–626,
   DOI 10.1090/S0002-9939-1964-0165392-8.
   Only the scalar real-half-line consequence is used, not analytic extension.
No radial equation, exceptional cancellation, coefficient identity, endpoint
bound, or Kerr–Newman mode-exclusion assertion is assumed here.
-/
noncomputable section
open Set
namespace KN.ChargedRadial.External

axiom canonical_power_calculus : TranslatedCanonicalPowerCalculus

axiom smooth_halfline_extension (r : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ici r)) :
    ∃ g : ℝ → ℂ, Smooth g ∧ EqOn g f (Ici r)

end KN.ChargedRadial.External

# X — Proposed minimal repair of the C001 §8 Kerr bridge (insertion text for a new C002)

**Status:** proposal. The frozen C001 v0.1 files are not modified. This file only states what a new C002 must contain.

- **Scope:** only §8 of C001, "The zero-charge case: an explicit Kerr coverage bridge". §§1–7 (Q ≠ 0) are unchanged.
- **Verification:** every identity used below was checked exactly. The scripts and outputs are in `X_STAGE2/` (ledger in `X_FINAL_ADJUDICATION.md` §7).

Notation is as in C001 §8:
- Q = 0, Δ = r² − 2Mr + a², |a| < M, m ∈ ℤ, and Im ω = γ > 0.
- K_std = (r² + a²)ω − am, and H = exp(i∫_{2r₊}^{r} K/Δ) with K = −K_std. Thus H′/H = −iK_std/Δ.
- k = ω − mΩ_H, Ω_H = a/(r₊² + a²), and κ_H = (r₊ − r₋)/(2(r₊² + a²)).
- T_s(ω) is C001 (50); the radial equation is C001 (52).

---

## Change 1 — attribution of the imported theorem (C001 lines 806–813)

Replace

> "The theorem in this physical product-mode form is recalled by Whiting and coauthors in [AMPW, Introduction]."

by

> "[AMPW, Introduction, p. 5, and §II A 3, Definition 3, eqs. (24)–(25)] recall it for separated solutions which, at r = r₊, equal the **non-special ingoing Frobenius solution** (exponent ξ − s/2 for the field Δ^{s/2}R) and, at infinity, the outgoing normal solution. We use the theorem only in this form, and only for s ∈ {−1, −2}. Positive spins are reduced to negative spins by Lemma 8.2."

## Change 2 — two lemmas, inserted before "Any nonzero full PDE field has a nonzero finite Riesz projection …"

**Conjugated radial operator.** Put R = HΔ^{−s}f. A direct computation shows that (52) holds if and only if E_s f = 0, where

  E_s f := Δ f″ + P_s f′ + C_s f, P_s := (1 − s)Δ′ − 2iK_std, C_s := 2i(2s − 1)ωr − s − Λ − a²ω² + 2amω. (8.a)

*Proof.* Write ψ := (HΔ^{−s})′/(HΔ^{−s}) = −(iK_std + sΔ′)/Δ.
- Then Δ^{−s}(Δ^{s+1}R′)′ = ΔR″ + (s+1)Δ′R′ equals HΔ^{−s}[Δf″ + (2Δψ + (s+1)Δ′)f′ + (Δ(ψ′ + ψ²) + (s+1)Δ′ψ)f].
- The f′-coefficient is (1 − s)Δ′ − 2iK_std.
- The f-coefficient is −iK_std′ − 2s + (−K_std² + isK_stdΔ′)/Δ. Adding the potential of (52) cancels the 1/Δ terms, because Δ′ = 2(r − M).
- With K_std′ = 2rω, what remains is C_s. □

**Lemma 8.1 (negative spins: weighted smoothness equals the non-special ingoing branch).** Let s ∈ {−1, −2} and Λ ∈ ℂ. Let R ≢ 0 solve (52) with R ∈ HΔ^{−s}C^∞([r₊, r₊ + ε)). Then

  R = c (r − r₊)^{ρ_in}(1 + O(r − r₊)), with c ≠ 0 and ρ_in = −s − ik/(2κ_H).

So R is a nonzero multiple of the non-special ingoing Frobenius solution of [AMPW, Def. 3].

*Proof.*
1. Write t = r − r₊ and d = r₊ − r₋, so that Δ = t(d + t). The operator E_s has a regular singular point at t = 0 with indicial equation d ρ(ρ − 1) + P_s(r₊)ρ = 0.
2. Its roots are ρ = 0 and ρ = k_s := s + 2iK_std(r₊)/d = s + ik/κ_H. Since Im k = γ, we get Re k_s = s − γ/κ_H < 0 for s < 0.
3. The Frobenius solution with exponent 0 is therefore analytic and can be normalized by f(r₊) = 1. Any solution not proportional to it contains a nonzero multiple of t^{k_s}·(analytic) (plus a logarithmic term if k_s ∈ −ℕ). Because Re k_s < 0, that is not smooth at t = 0.
4. Hence f = c × (that analytic solution) with c ≠ 0. Finally, H = t^{−ik/(2κ_H)} × (smooth, nonvanishing), which gives the stated form of R. □

**Lemma 8.2 (spin reversal).** Let s ∈ {1, 2}. Let u ≢ 0 be an eigenfunction of T_s(ω) in its canonical domain, with eigenvalue Λ. Let R ≢ 0 solve (52) with R ∈ HΔ^{−s}C^∞([r₊, ∞)), and suppose HR has polynomial conormal bounds at infinity. With R = HΔ^{−s}f, define

  ũ(θ) := u(π − θ),  R̃ := HΔ^{s} ∂_r^{2s} f.

Then:
- (i) ũ is an eigenfunction of T_{−s}(ω) in its canonical domain, with the same Λ.
- (ii) R̃ solves (52) with s replaced by −s and the same Λ.
- (iii) R̃ ∈ HΔ^{s}C^∞([r₊, ∞)), at every frequency with Im ω > 0.
- (iv) HR̃ has polynomial conormal bounds at infinity, and R̃ ≢ 0.

Consequently e^{−iωt+imφ} ũ(θ) R̃(r) is a nonzero separated solution of the spin-(−s) Teukolsky equation. It satisfies the hypotheses of Lemma 8.1 and the outgoing condition.

*Proof.*

**(i)** θ ↦ π − θ sends cos θ ↦ −cos θ and fixes sin θ. It therefore carries (50) for spin s into (50) for spin −s, with the same m and the same eigenvalue. The canonical (Friedrichs) domains correspond, because the regular axis exponents |m + s| at θ = 0 and |m − s| at θ = π are interchanged; these are exactly the spin −s exponents at the two poles. The reflection is unitary on L²(sin θ dθ), so Jordan chains are carried to Jordan chains.

**(ii) Intertwining.** Set n = 2s. Δ and P_s are quadratic in r, and C_s is linear. Leibniz's rule then gives

  ∂ⁿ(E_s g) = Δ g^{(n+2)} + [nΔ′ + P_s] g^{(n+1)} + [½n(n−1)Δ″ + nP_s′ + C_s] g^{(n)} + [½n(n−1)P_s″ + nC_s′] g^{(n−1)}.

Check the three lower coefficients against E_{−s}:
- nΔ′ + P_s = (1 + s)Δ′ − 2iK_std = P_{−s}.
- With Δ″ = 2 and P_s′ = 2(1 − s) − 4iωr: ½n(n−1)·2 + n(2 − 2s − 4iωr) + C_s = s − Λ − a²ω² + 2amω − 2i(2s + 1)ωr = C_{−s}.
- ½n(n−1)(−4iω) + n·2i(2s − 1)ω = 2iωn(2s − n) = 0.

Hence ∂_r^{2s} E_s = E_{−s} ∂_r^{2s}, with the same Λ. Since E_s f = 0, g := f^{(2s)} satisfies E_{−s} g = 0, which by (8.a) for −s is (52) for spin −s.

**(iii)** If f ∈ C^∞([r₊, ∞)), then so is g, so R̃ ∈ HΔ^{s}C^∞. This step has no exceptional frequency.

**(iv)**
1. At infinity, K_std/Δ = ω(1 + 2M/r) + O(r^{−2}). So H = e^{−iωr} r^{−2iMω}·(const + O(1/r)).
2. A nonzero solution with HR polynomially conormal lies in the outgoing branch, which is one-dimensional. Hence f = H^{−1}Δ^{s}R = e^{2iωr} r^{4iMω−1}(c₀ + O(1/r)) with c₀ ≠ 0, and derivatives obey the same expansion.
3. Each derivative multiplies the leading term by 2iω. So g = (2iω)^{2s} c₀ e^{2iωr} r^{4iMω−1}(1 + O(1/r)), which is nonzero because ω ≠ 0.
4. Therefore HR̃ = H²Δ^{s}g = (2iω)^{2s} c₀ r^{2s−1}(const + O(1/r)): polynomially bounded and conormal, and R̃ ≢ 0.
5. Possible kernel elements of f ↦ f^{(2s)} on solutions of E_s f = 0 are polynomials of degree < 2s. Such elements exist exactly when the radial Teukolsky–Starobinsky determinant vanishes. They give R = HΔ^{−s}f, which is incoming at infinity, so they never occur here. □

## Change 3 — the concluding inference of the bridge (C001 lines 878–880)

Replace

> "This produces a nonzero separated physical Teukolsky mode, contradicting Whiting's theorem."

by

> "This produces a nonzero separated physical outgoing mode (u₁, f_J) of spin s.
> - If s ∈ {−1, −2}, Lemma 8.1 identifies f_J as the non-special ingoing Frobenius solution. The mode then satisfies the hypotheses of Whiting's theorem as recalled in [AMPW, Def. 3], which excludes it.
> - If s ∈ {1, 2}, Lemma 8.2 produces a nonzero separated physical outgoing mode of spin −s with the same (ω, m, Λ), which is excluded in the same way.
>
> Hence f_J ≡ 0, contradicting the choice of J. Descending the chain, every coefficient of every finite Riesz projection vanishes, and adjoint-root completeness gives F = 0."

## Change 4 — normalization audit (C001 lines 896–899) and §9 import list

- In the normalization audit, replace "The imported theorem is Whiting's physical separated-mode theorem, with the regular boundary conditions" by: "The imported theorem is Whiting's separated-mode theorem in the form recalled in [AMPW, Def. 3], used only for s ∈ {−1, −2}, where Lemma 8.1 identifies the regular horizon class with that form."
- In §9 ("Imported mathematics consists of …"), read "[W] (as recalled in [AMPW, Def. 3]; negative spins only)".

## Why this is the smallest repair

- **Where the gap is.** The only failure point of C001 §8 is s = +2 at ω* = mΩ_H + iκ_H. There k_2 = 1, the generic smooth branch is "special" (f(r₊) = 0), and AMPW's Definition 3 does not apply (`X_FINAL_ADJUDICATION.md` §2).
- **Why one lemma suffices.** Lemma 8.2 removes all positive spins uniformly and has no exceptional frequency. Lemma 8.1 shows the cited form applies verbatim to every negative-spin frequency.
- **What it needs.**
  - No new imports: in particular no use of TdC's displayed equations or of TdC's s > 0 proof.
  - The negative-spin statement used here is also proved independently in [TdC, §3 and §4.2, s ≤ 0]. Physical negative-spin modes satisfy its admissibility condition Im(λω̄) < 0 under either reading of TdC (2.10): λ = Λ + \|s\| (printed) or λ = Λ (corrected). For s < 0 the normalized horizon solution R_{H+} exists at every UHP frequency.
  - No change to the bridge (completeness, Jordan extraction) or to §§1–7.
  - The s = +1 reduction is not strictly required. At k = iκ_H the exponents of s = +1 coincide and the smooth solution is the non-special Frobenius one. Including s = +1 keeps the statement uniform.

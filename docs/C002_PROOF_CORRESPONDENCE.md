# C002 proof correspondence

Editorial completeness status: **PASS**. This comparison checks preservation and presentation of the frozen proof. It does not repeat a mathematical, literature, or Lean adversarial audit.

The complete frozen manuscript body is retained, with forty purpose/structure headings and explanatory paragraphs, a reading roadmap, six prose-tone replacements, and layout-only reflows of equations (22), (23), and (50). All 398 inline/display mathematical spans remain in order; 395 agree after whitespace normalization and three agree after removing only the declared alignment/spacing changes. All 85 displayed formulas, including 62 numbered tags and 23 unnumbered displays, remain present.

The reader Markdown and TeX contain the same 398 mathematical spans and the same prose after normalizing document markup, typography, headings, and layout commands. The whole frozen-body prose comparison succeeds after only the six declared replacements and removal of the added editorial material. This provides a completeness backstop for all 76 checkpoints, 22 assumption/boundary items, 18 external-input items, and 88 original body paragraphs below.

The original 325 Lean files and four manuscript files match the frozen source manifest byte for byte. The frozen PDF SHA-256 is `3918225f220943dcdf67a2db7646ab7c375238d0a7ec204a1368a938a6173797`. The unchanged frozen TeX SHA-256 is `2913b8cbea9da31cfe520dd4dd0452d3b11b59abb3f020d43daa7a852f52587b`; frozen Markdown SHA-256 is `a67a87f20f7ac522debd8c2999f64ace1f1aa7dcf54a078e35b5c6dc71c476b4`.

All line ranges below are inclusive and one-based. Readable TeX ranges point into [C002_READABLE.tex](../manuscript/C002_READABLE.tex); Markdown ranges point into [C002_READABLE.md](../C002_READABLE.md). PDF pages come from the compiled heading labels in the LaTeX auxiliary file: they identify the linked heading, and a checkpoint may continue onto a later page. No page number is invented for an unlabelled opening or bibliography.

## Complete proof checkpoints

### S001 — Abstract and precise scope

- Frozen source: TeX 77–91; Markdown 19–32.
- Reader location: [opening abstract](../C002_READABLE.md). TeX 39–53; Markdown 5–19; PDF heading page unavailable.
- Preserved content: Exclude radiative UHP modes for every strictly subextremal asymptotically flat KN background; charged proof is for the full coupled system; Kerr proof includes exceptional horizon frequencies; no decay or nonradiative classification claim.
- Editorial comparison: **PASS**.

### S002 — Context and distinct earlier results

- Frozen source: TeX 95–110; Markdown 36–51.
- Reader location: [introduction-and-theorem](../C002_READABLE.md#introduction-and-theorem). TeX 69–84; Markdown 51–66; PDF heading p. 3.
- Preserved content: Real-frequency exclusion does not imply UHP exclusion; retain the separate negative-spin Kerr input and context references without presenting numerical evidence as proof.
- Editorial comparison: **PASS**.

### S003 — Global assumptions and theorem

- Frozen source: TeX 112–121; Markdown 53–63.
- Reader location: [readable-parameters](../C002_READABLE.md#readable-parameters), [readable-theorem](../C002_READABLE.md#readable-theorem). TeX 91–105; Markdown 74–91; PDF heading p. 3.
- Preserved content: Real M,a,Q; M>0; a²+Q²<M²; integer m; complex omega with gamma=Im omega>0; fixed e^{-i omega t+i m phi} convention; outgoing smooth perturbations have vanishing gravitational and electromagnetic radiative data.
- Editorial comparison: **PASS**.

### S004 — Two scientific branches

- Frozen source: TeX 123–131; Markdown 65–72.
- Reader location: [readable-theorem](../C002_READABLE.md#readable-theorem). TeX 107–115; Markdown 93–101; PDF heading p. 3.
- Preserved content: For Q≠0 prove both entire four-component necessary PDE systems vanish, with algebraic transformations valid at complex frequency; Q=0 has its own Kerr full-field argument rather than a singular charge limit.
- Editorial comparison: **PASS**.

### S005 — Geometry and phase conventions

- Frozen source: TeX 133–138; Markdown 74–81.
- Reader location: [readable-theorem](../C002_READABLE.md#readable-theorem). TeX 117–122; Markdown 103–109; PDF heading p. 3.
- Preserved content: Retain Delta,r±,delta,K and H with its integration base 2r+; K has the minus sign relative to K_std.
- Editorial comparison: **PASS**.

### S006 — Physical boundary conditions

- Frozen source: TeX 139–148; Markdown 83–92.
- Reader location: [readable-theorem](../C002_READABLE.md#readable-theorem). TeX 123–132; Markdown 113–122; PDF heading p. 3.
- Preserved content: Retain all five horizon-weight descriptions for original variables, regular ingoing-tetrad smoothness, H-times-original-variable polynomial conormal infinity bounds for fixed radial/angular derivatives, exponential outgoing decay at gamma>0, and smooth spin-weighted sections at the axis.
- Editorial comparison: **PASS**.

### S007 — Exclusions from the claim

- Frozen source: TeX 150–153; Markdown 94–97.
- Reader location: [readable-theorem](../C002_READABLE.md#readable-theorem). TeX 134–137; Markdown 124–127; PDF heading p. 3.
- Preserved content: Do not add gauge/parameter classification, decay, nonlinear stability, extremality or estimates uniform to extremality.
- Editorial comparison: **PASS**.

### S008 — Charged constants and algebraic identities

- Frozen source: TeX 161–170; Markdown 104–118.
- Reader location: [readable-source-algebra](../C002_READABLE.md#readable-source-algebra). TeX 152–161; Markdown 143–157; PDF heading p. 4.
- Preserved content: Q≠0; d,eta,h,kappa,c,beta,xi0,Ktilde; c and beta retain signed Q; kappa²-c²=1 and beta*c=3h/2.
- Editorial comparison: **PASS**.

### S009 — Full transformed first-order PDE

- Frozen source: TeX 171–181; Markdown 119–132.
- Reader location: [readable-source-algebra](../C002_READABLE.md#readable-source-algebra). TeX 162–172; Markdown 161–174; PDF heading p. 4.
- Preserved content: Both sigma signs; complete four-component Z; sqrtDelta*d_r Z=(A+R0 I+R1 J)Z; retain exact R0/R1 and source attribution H equations7–8.
- Editorial comparison: **PASS**.

### S010 — Matrix and chirality structure

- Frozen source: TeX 182–204; Markdown 133–159.
- Reader location: [readable-source-algebra](../C002_READABLE.md#readable-source-algebra). TeX 173–195; Markdown 180–212; PDF heading p. 4.
- Preserved content: I,J Hermitian involutions anticommute; A anticommutes with each; S=IJ commutes with A and has ±i sectors; exact block A,Theta,W,T and explicit I,J,J2; complex algebra with no conjugation of omega.
- Editorial comparison: **PASS**.

### S011 — Invertible original-to-transformed maps

- Frozen source: TeX 209–227; Markdown 163–187.
- Reader location: [readable-invertibility](../C002_READABLE.md#readable-invertibility). TeX 206–224; Markdown 224–250; PDF heading p. 5.
- Preserved content: rho/rho*, exact X and det X=-d≠0; retain both y± positive/negative-spin maps and z+=adj(X)y+,z-=X*y-; X is independent of frequency; every factor invertible in open exterior; substitution does not divide by eliminated scalar coefficients.
- Editorial comparison: **PASS**.

### S012 — Boundary fidelity of transformation

- Frozen source: TeX 229–240; Markdown 189–202.
- Reader location: [readable-boundary-weights](../C002_READABLE.md#readable-boundary-weights). TeX 231–242; Markdown 258–273; PDF heading p. 5.
- Preserved content: Pi±=(1±I)/2; positive exponents(-1/4,-3/4), negative(3/4,5/4) times H; Hilbert-valued smoothness; axis conditions imply maximal angular domain; infinity Z=H^-1 times polynomially bounded functions.
- Editorial comparison: **PASS**.

### S013 — Legitimate charged phantom gauge

- Frozen source: TeX 242–250; Markdown 204–214.
- Reader location: [readable-invariants](../C002_READABLE.md#readable-invariants). TeX 249–257; Markdown 281–287; PDF heading p. 5.
- Preserved content: Phi1=Q/(2rho*²) is nowhere zero for Q≠0; retain all four rescaled Weyl-variable definitions including sqrt2 factors.
- Editorial comparison: **PASS**.

### S014 — Literal four radiative invariants

- Frozen source: TeX 251–267; Markdown 215–235.
- Reader location: [readable-invariants](../C002_READABLE.md#readable-invariants). TeX 258–274; Markdown 294–313; PDF heading p. 5.
- Preserved content: Exact G± and E± curvature–Maxwell mixtures from M equations5.1–5.2; infinitesimal-null-rotation invariance; exact phantom-gauge factors relating them to psi±2,psi±1.
- Editorial comparison: **PASS**.

### S015 — Return to physical data and one-way entry

- Frozen source: TeX 268–276; Markdown 236–244.
- Reader location: [readable-invariants](../C002_READABLE.md#readable-invariants). TeX 275–282; Markdown 319–326; PDF heading p. 5.
- Preserved content: Vanishing four psi variables implies invariant vanishing; finite-charge E± mix curvature and Maxwell; zero-charge limits are deltaPhi0 and rho*²deltaPhi2; no real-frequency flux formula required; only physical perturbation→necessary-system implication, no reconstruction assumption.
- Editorial comparison: **PASS**.

### S016 — Chiral angular realization

- Frozen source: TeX 283–291; Markdown 250–261.
- Reader location: [readable-angular-domain](../C002_READABLE.md#readable-angular-domain). TeX 296–304; Markdown 342–356; PDF heading p. 6.
- Preserved content: Constant unitary identification of S=i sector with Bsigma(omega)=B0+omega V; exact B0,g,V; distinguish scalar sigma from Hermitian Pauli matrices sigma_j.
- Editorial comparison: **PASS**.

### S017 — First-order fixed angular domain

- Frozen source: TeX 293–300; Markdown 263–271.
- Reader location: [readable-angular-domain](../C002_READABLE.md#readable-angular-domain). TeX 306–313; Markdown 358–365; PDF heading p. 6.
- Preserved content: Compactly supported smooth B0 essentially self-adjoint with maximal distributional L²(dtheta) domain; half-integer endpoint indicial roots; <=-1/2 branch not L²; zero-flux deficiency proof; bounded Hermitian V leaves domain fixed for complex omega; H Lemma1 at zero frequency.
- Editorial comparison: **PASS**.

### S018 — Static square and Hadamard rotation

- Frozen source: TeX 302–310; Markdown 273–285.
- Reader location: [readable-jacobi](../C002_READABLE.md#readable-jacobi). TeX 320–328; Markdown 373–384; PDF heading p. 6.
- Preserved content: Exact rotated 2x2 B0 and diagonal second-order L_s of B0²-beta² for s=1,2.
- Editorial comparison: **PASS**.

### S019 — Jacobi basis and domain compatibility

- Frozen source: TeX 311–322; Markdown 286–300.
- Reader location: [readable-jacobi](../C002_READABLE.md#readable-jacobi). TeX 329–338; Markdown 390–403; PDF heading p. 6.
- Preserved content: A_s=|sigma m+s|,B_s=|sigma m-s|; exact Jacobi functions; ell=n+max(|m|,s) and eigenvalue ell(ell+1)-2; x=cos theta and weighted polynomial density; critical exponent1/2 first-image cancellation; functions and first-order images lie in maximal domain; no extra logarithmic second-order extension.
- Editorial comparison: **PASS**.

### S020 — Paired and unpaired static spectrum

- Frozen source: TeX 324–332; Markdown 302–313.
- Reader location: [readable-static-branches](../C002_READABLE.md#readable-static-branches). TeX 346–354; Markdown 412–424; PDF heading p. 7.
- Preserved content: ell≥max(|m|,2) paired ±sqrt(beta²+(ell-1)(ell+2)); if |m|≤1 one unpaired -beta with displayed upper component and zero lower; no unpaired +beta in this sector.
- Editorial comparison: **PASS**.

### S021 — Static gap as a quadratic form

- Frozen source: TeX 333–337; Markdown 313–318.
- Reader location: [readable-static-branches](../C002_READABLE.md#readable-static-branches). TeX 355–359; Markdown 425–429; PDF heading p. 7.
- Preserved content: P0 is possible rank-one ground projection; T0=B0²-beta²≥4(1-P0)≥0 on Dom B0 in form sense.
- Editorial comparison: **PASS**.

### S022 — Signed-charge coercive form

- Frozen source: TeX 342–350; Markdown 322–334.
- Reader location: [readable-angular-sign](../C002_READABLE.md#readable-angular-sign). TeX 370–378; Markdown 444–459; PDF heading p. 7.
- Preserved content: For real x≤-h define Ksigma(x); q=|Q|/M∈(0,1), b=|beta|=3/(2q), |c/x|≤q with sign opposite beta; negative-spin adverse paired lower bound v²-b²-q(v+b), v≥sqrt(b²+4), increasing in v.
- Editorial comparison: **PASS**.

### S023 — Negative-system nonnegative ground

- Frozen source: TeX 350–355; Markdown 334–343.
- Reader location: [readable-angular-sign](../C002_READABLE.md#readable-angular-sign). TeX 378–383; Markdown 458–466; PDF heading p. 7.
- Preserved content: Exact epsilon_q and its positive rationalized form; K_-≥epsilon_q(1-P0); unpaired branch has value ZERO, so do not strengthen to strictly positive on P0.
- Editorial comparison: **PASS**.

### S024 — Positive-system form bound

- Frozen source: TeX 356–362; Markdown 344–352.
- Reader location: [readable-angular-sign](../C002_READABLE.md#readable-angular-sign). TeX 384–390; Markdown 470–480; PDF heading p. 7.
- Preserved content: Paired lower bound (11-sqrt(9+16q²))/2>3; unpaired -2beta*c/x=-3h/x>0; exact K_+ lower bound; no extremal-uniform estimate used.
- Editorial comparison: **PASS**.

### S025 — Actual complex-eigenpair expectations

- Frozen source: TeX 364–374; Markdown 354–368.
- Reader location: [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations). TeX 397–407; Markdown 488–500; PDF heading p. 8.
- Preserved content: Normalized genuine Bsigma(omega)u=lambda u; L,v,T,C,D real with exact definitions; inner product conjugate-linear first; lambda=L+omega v and lambda²=beta²+T+omega C+omega²D.
- Editorial comparison: **PASS**.

### S026 — First-domain square identity and multiplier

- Frozen source: TeX 375–385; Markdown 369–383.
- Reader location: [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations). TeX 408–417; Markdown 505–520; PDF heading p. 8.
- Preserved content: Retain displayed adjoint-pairing proof of lambda² using only first-order domain; no complex-frequency self-adjointness or Dom(B²) premise; Pauli V²=a²(c²+sin²theta) and norm|a|kappa; eigenvector fixed independently of transform x.
- Editorial comparison: **PASS**.

### S027 — Actual Schatten resolvent and ray bound

- Frozen source: TeX 390–401; Markdown 387–400.
- Reader location: [readable-root-completeness](../C002_READABLE.md#readable-root-completeness). TeX 428–439; Markdown 532–547; PDF heading p. 8.
- Preserved content: Static linear eigenvalue growth gives S_p for p>1, notably Hilbert–Schmidt; bounded perturbation preserves at distant point; exact resolvent estimate for |Im z|>Comega; actual point z=i(1+2Comega).
- Editorial comparison: **PASS**.

### S028 — Mityagin–Siegl hypotheses checked

- Frozen source: TeX 403–410; Markdown 402–410.
- Reader location: [readable-root-completeness](../C002_READABLE.md#readable-root-completeness). TeX 441–447; Markdown 549–555; PDF heading p. 8.
- Preserved content: Closed densely defined operator; one S_p resolvent; polynomial ray bounds; successive gaps strictly<pi/p; p=2, eight rays pi/8+j*pi/4 with gaps pi/4<pi/2; conclude generalized-root completeness without Riesz-basis assumption.
- Editorial comparison: **PASS**.

### S029 — Adjoint completeness gives detection

- Frozen source: TeX 412–417; Markdown 412–417.
- Reader location: [readable-adjoint-detection](../C002_READABLE.md#readable-adjoint-detection). TeX 455–460; Markdown 564–569; PDF heading p. 9.
- Preserved content: A(omega)*=A(conj omega); same argument applies; if all finite Riesz projections kill a vector then it is orthogonal to complete adjoint generalized roots and is zero; no convergent ordinary-eigenvector expansion premise.
- Editorial comparison: **PASS**.

### S030 — Refined paired Riesz projection

- Frozen source: TeX 422–431; Markdown 421–433.
- Reader location: [readable-chiral-projection](../C002_READABLE.md#readable-chiral-projection). TeX 471–480; Markdown 581–594; PDF heading p. 9.
- Preserved content: diag(P_lambda^+, I P_lambda^+ I) commutes with A,I,J; avoids double-counting λ and -λ within same sector; works at λ=0; detects nonzero full PDE at an interior radius.
- Editorial comparison: **PASS**.

### S031 — Both chiral Jordan chains and triangular PDE

- Frozen source: TeX 433–443; Markdown 435–450.
- Reader location: [readable-jordan-pair](../C002_READABLE.md#readable-jordan-pair). TeX 487–497; Markdown 602–616; PDF heading p. 9.
- Preserved content: (A-lambda)u_j=u_(j-1),u0=0,v_j=Iu_j; retain all A/I/J actions and ±i factors; chains remain independent at λ=0; exact triangular radial p_j,q_j system including p_(j+1),-q_(j+1).
- Editorial comparison: **PASS**.

### S032 — A globally nonzero coefficient pair

- Frozen source: TeX 444–450; Markdown 451–457.
- Reader location: [readable-jordan-pair](../C002_READABLE.md#readable-jordan-pair). TeX 498–504; Markdown 621–627; PDF heading p. 9.
- Preserved content: Choose highest chain index whose radial pair is not identically zero; higher coefficients vanish identically in radius, yielding homogeneous pair; bounded radius-independent coefficient maps intertwine I,J and preserve unequal horizon weights and outgoing bounds.
- Editorial comparison: **PASS**.

### S033 — Invariant-filtration alternative

- Frozen source: TeX 452–456; Markdown 459–463.
- Reader location: [readable-jordan-pair](../C002_READABLE.md#readable-jordan-pair). TeX 506–510; Markdown 629–633; PDF heading p. 9.
- Preserved content: Retain ker(B-lambda)^j ⊕ I ker(B-lambda)^j and first nonzero semisimple quotient formulation; no application of an anticommuting operator to the whole PDE.
- Editorial comparison: **PASS**.

### S034 — Homogeneous radial system with genuine angular data

- Frozen source: TeX 458–466; Markdown 465–475.
- Reader location: [readable-radial-pair](../C002_READABLE.md#readable-radial-pair). TeX 517–525; Markdown 641–653; PDF heading p. 10.
- Preserved content: Exact radial basis Z=z1(u+Iu)-i z2(u-Iu); exact pair24 and both horizon weights; enough to exclude each genuine eigenpair, no uniform m/omega/lambda bound.
- Editorial comparison: **PASS**.

### S035 — Smooth w,w_sharp normalization

- Frozen source: TeX 471–487; Markdown 479–499.
- Reader location: [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling). TeX 536–552; Markdown 665–692; PDF heading p. 10.
- Preserved content: Both sign-specific substitutions25, horizon smoothness; exact first-order system26; A=R1+i sigma lambda, B=R1-i sigma lambda.
- Editorial comparison: **PASS**.

### S036 — Weighted radial pair

- Frozen source: TeX 487–495; Markdown 500–512.
- Reader location: [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling). TeX 552–560; Markdown 689–701; PDF heading p. 10.
- Preserved content: Exact p, v_r=pw,z_r=Delta p wsharp; distinguish radial variables from angular expectations; exact L_r and pair28.
- Editorial comparison: **PASS**.

### S037 — Division-free scalar equation

- Frozen source: TeX 496–505; Markdown 513–524.
- Reader location: [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling). TeX 561–570; Markdown 706–719; PDF heading p. 10.
- Preserved content: A′=B′=R1′ constant; differentiate first equation twice using z′=Bv; exact ordered operator29; degree≤2 polynomial coefficients; never use A^-1 or B^-1, retaining solutions at coupling zeros.
- Editorial comparison: **PASS**.

### S038 — Horizon distribution exponent and ranges

- Frozen source: TeX 510–517; Markdown 528–537.
- Reader location: [readable-horizon-exponents](../C002_READABLE.md#readable-horizon-exponents). TeX 581–588; Markdown 731–742; PDF heading p. 11.
- Preserved content: t=r-r+,dH=Delta′(r+)=2delta; v=t^alpha f,z=t^(alpha+1)g; exact alpha; Re alpha>1 for negative,>-2 positive, with explicit gamma dependence.
- Editorial comparison: **PASS**.

### S039 — Generic supported extension

- Frozen source: TeX 521–525; Markdown 541–546.
- Reader location: [readable-generic-extension](../C002_READABLE.md#readable-generic-extension). TeX 598–602; Markdown 754–761; PDF heading p. 11.
- Preserved content: Negative spin uses ordinary zero extension; positive alpha≠-1 uses canonical meromorphic t_+^alpha and t_+^(alpha+1) times smooth coefficients, joined to solution away from horizon; only pole in region alpha=-1.
- Editorial comparison: **PASS**.

### S040 — Homogeneity of generic extension

- Frozen source: TeX 525–536; Markdown 546–560.
- Reader location: [readable-generic-extension](../C002_READABLE.md#readable-generic-extension). TeX 602–613; Markdown 758–773; PDF heading p. 11.
- Preserved content: Exact two canonical-power identities31 via meromorphic continuation, including nonnegative integers; Delta=t(dH+t) reduces residuals to canonical extensions of identically vanishing smooth coefficients; fixed omega suffices, no holomorphic family of physical solutions.
- Editorial comparison: **PASS**.

### S041 — Exceptional positive-spin frequency

- Frozen source: TeX 541–545; Markdown 564–570.
- Reader location: [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator). TeX 624–628; Markdown 785–793; PDF heading p. 11.
- Preserved content: alpha=-1 at exact omega_H=(am+i dH/2)/B+,B+=r+²+a²,gamma=delta/B+; L_r(r+)=dH.
- Editorial comparison: **PASS**.

### S042 — Nonvanishing correction denominator: contrary identity

- Frozen source: TeX 545–551; Markdown 570–580.
- Reader location: [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator). TeX 628–634; Markdown 793–799; PDF heading p. 11.
- Preserved content: G_H=2Q(Mr+-Q²)/d; B(r+)=0 implies lambda=beta+i G_H omega; compare its square with18, divide by nonzero omega and take imaginary parts to get33.
- Editorial comparison: **PASS**.

### S043 — Nonvanishing correction denominator: strict contradiction

- Frozen source: TeX 552–561; Markdown 581–594.
- Reader location: [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator). TeX 635–644; Markdown 804–819; PDF heading p. 11.
- Preserved content: T≥0,D≤a²kappa²; retain exact G_H²+a²kappa² identity and positive34; quotient(6M²-4Q²)/d=4+2M²/d>6, a²/B+<1; both charge signs; B(r+)≠0; excluding A(r+)=0 is unnecessary.
- Editorial comparison: **PASS**.

### S044 — Finite exceptional boundary source and its correction

- Frozen source: TeX 563–570; Markdown 596–605.
- Reader location: [readable-delta-correction](../C002_READABLE.md#readable-delta-correction). TeX 651–658; Markdown 827–833; PDF heading p. 12.
- Preserved content: z_r smooth,v=t^-1 f; z′=Bv with B(r+)≠0 forces f(0)=0 and v smooth; plain zero extension still creates delta in z′; exact z_e and v_e plus z_r(r+)/B(r+) delta35.
- Editorial comparison: **PASS**.

### S045 — Why delta correction restores both equations

- Frozen source: TeX 571–582; Markdown 606–619.
- Reader location: [readable-delta-correction](../C002_READABLE.md#readable-delta-correction). TeX 659–670; Markdown 839–852; PDF heading p. 12.
- Preserved content: (Delta d_r+L_r)delta=(-dH+L_r(r+))delta=0; added Bv_e delta exactly matches z_e′;28 and29 homogeneous; Laurent residue vanishing alone insufficient; finite-order supported distribution agrees with physical exterior.
- Editorial comparison: **PASS**.

### S046 — Fourier–Laplace object and interior ray

- Frozen source: TeX 589–600; Markdown 625–640.
- Reader location: [readable-laplace-ray](../C002_READABLE.md#readable-laplace-ray). TeX 684–695; Markdown 868–887; PDF heading p. 12.
- Preserved content: Infinity v_e=e^(-i eta omega r) O_con(r^C); transform via exponential damping/cutoffs; compact finite-part/delta terms pose no convergence issue; holomorphic Im xi<-eta gamma; xi=omega x for x<-h with gamma(x+eta)<-2gamma.
- Editorial comparison: **PASS**.

### S047 — Ordered Fourier substitution and full coefficient table

- Frozen source: TeX 602–621; Markdown 642–665.
- Reader location: [readable-ordered-transform](../C002_READABLE.md#readable-ordered-transform). TeX 702–721; Markdown 895–922; PDF heading p. 13.
- Preserved content: d_r→i xi and r→i d_xi preserving noncommutative operator order, then xi=omega x; retain exact ODE38 and all seven coefficient functions39 including d0,d1,d2.
- Editorial comparison: **PASS**.

### S048 — Positive divergence weights

- Frozen source: TeX 623–632; Markdown 667–680.
- Reader location: [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge). TeX 728–737; Markdown 930–943; PDF heading p. 13.
- Preserved content: mu,P,W_x exact; P,W_x>0 for x<-h; q_x=mu c_x/2 exact; derivative identities41 and ratio q_x/P=M(x+eta)/(x+h).
- Editorial comparison: **PASS**.

### S049 — Gauge removes imaginary transport

- Frozen source: TeX 633–644; Markdown 681–697.
- Reader location: [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge). TeX 738–749; Markdown 948–967; PDF heading p. 13.
- Preserved content: S=M[x-2log(-x-h)],Y=e^(-i omega S)U,S′=q_x/P; exact divergence equation43 and full real R(x)44.
- Editorial comparison: **PASS**.

### S050 — Use genuine angular expectations in transformed bracket

- Frozen source: TeX 649–657; Markdown 701–713.
- Reader location: [readable-coercive-potential](../C002_READABLE.md#readable-coercive-potential). TeX 760–768; Markdown 983–992; PDF heading p. 14.
- Preserved content: Bracket=-k+omega l+omega²B; k=T+c/x(L-sigma beta)=<Ksigma>≥0,l=2amx-C-cv/x real,B=R-D; eigenpair is actual complex angular eigenpair, not arbitrary real separation constant.
- Editorial comparison: **PASS**.

### S051 — Strict transformed quadratic coefficient

- Frozen source: TeX 658–666; Markdown 714–725.
- Reader location: [readable-coercive-potential](../C002_READABLE.md#readable-coercive-potential). TeX 769–777; Markdown 998–1010; PDF heading p. 14.
- Preserved content: y=-x-eta>2; exact B=y²[delta²+2M²/(y-2)]+2a²y-a²<sin²theta>>0; l may be indefinite but will cancel in imaginary identity.
- Editorial comparison: **PASS**.

### S052 — Finite transform endpoint estimates before integration

- Frozen source: TeX 670–679; Markdown 729–742.
- Reader location: [readable-finite-endpoint](../C002_READABLE.md#readable-finite-endpoint). TeX 787–796; Markdown 1022–1035; PDF heading p. 14.
- Preserved content: x→-h lies strictly inside holomorphy half-plane; tx=-x-h; |U|=O(tx^(2M gamma)),|U′|=O(tx^(2M gamma-1)); P~tx,W~1,B~tx^-1,k,l bounded; worst density tx^(4M gamma-1) integrable for every gamma>0; flux O(tx^(4M gamma))→0.
- Editorial comparison: **PASS**.

### S053 — Explicit finite-part bound at remote endpoint

- Frozen source: TeX 681–695; Markdown 744–763.
- Reader location: [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint). TeX 803–817; Markdown 1043–1058; PDF heading p. 14.
- Preserved content: Near-horizon cutoff; generic positive-spin identity48a expressing t_+^alpha f using derivative of integrable t_+^(alpha+1)f and t_+^(alpha+1)f′; alpha≠-1 and Re alpha>-2; explicit Laplace integral bound e^(gamma r+ x) O(|x|^(-Re alpha-2)).
- Editorial comparison: **PASS**.

### S054 — All remote-endpoint branches and derivatives

- Frozen source: TeX 696–703; Markdown 764–773.
- Reader location: [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint). TeX 818–822; Markdown 1064–1068; PDF heading p. 14.
- Preserved content: Derivative costs at most|x|; negative spin directly integrable; exceptional smooth zero extension plus delta; r^j insertion controls each fixed x derivative; outgoing tail starts a positive distance from horizon and decays more strongly; no presumed general support-edge bound or Watson coefficient.
- Editorial comparison: **PASS**.

### S055 — Strict-subextremal decay completes endpoint justification

- Frozen source: TeX 705–712; Markdown 775–785.
- Reader location: [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint). TeX 825–832; Markdown 1071–1082; PDF heading p. 14.
- Preserved content: Gauge modulus e^(-gamma Mx) times power(-x-h); exact bound48 e^(gamma(r+-M)x)=e^(gamma delta x); delta>0; polynomially growing weights; all energy integrals converge and flux zero including delta35.
- Editorial comparison: **PASS**.

### S056 — Energy identity and U=0

- Frozen source: TeX 717–729; Markdown 789–805.
- Reader location: [readable-energy-identity](../C002_READABLE.md#readable-energy-identity). TeX 843–855; Markdown 1094–1112; PDF heading p. 15.
- Preserved content: Integrate43 against conjugate U only after endpoint estimates; keep unnumbered four-term energy identity; multiply by conjugate omega and take imaginary part to cancel real l; exact49; gamma>0,omega≠0,P,W>0,k≥0,B>0 force U=0.
- Editorial comparison: **PASS**.

### S057 — Analytic and Fourier injectivity with partner recovery

- Frozen source: TeX 731–739; Markdown 807–817.
- Reader location: [readable-injectivity](../C002_READABLE.md#readable-injectivity). TeX 862–870; Markdown 1120–1128; PDF heading p. 15.
- Preserved content: Zero on interior complex ray→whole connected half-plane by identity theorem; sufficiently low horizontal line is Fourier transform of exponentially damped tempered distribution; Fourier injectivity v_e=0; open-exterior v_r=0,p≠0→w=0; Awsharp=0; affine A not identically zero since Q omega M/d≠0; isolated zero plus continuity yields wsharp=0; invert back to pair zero.
- Editorial comparison: **PASS**.

### S058 — Full charged conclusion

- Frozen source: TeX 741–743; Markdown 819–822.
- Reader location: [readable-injectivity](../C002_READABLE.md#readable-injectivity). TeX 872–874; Markdown 1130–1132; PDF heading p. 15.
- Preserved content: Contradict nonzero pair extracted from any nonzero full PDE; both sigma systems vanish; invertible source transformations return four radiative invariant conclusion8a–8b.
- Editorial comparison: **PASS**.

### S059 — Separate zero-charge equations and precise Kerr import

- Frozen source: TeX 747–758; Markdown 826–837.
- Reader location: [readable-kerr-input](../C002_READABLE.md#readable-kerr-input). TeX 884–895; Markdown 1144–1155; PDF heading p. 16.
- Preserved content: Q=0 background Maxwell vanishes; linearization gives Teukolsky spins±1,±2; imported W/AMPW input restricted to negative spins, regular-axis, non-special ingoing Frobenius and outgoing infinity; positive spins reduced by proved reversal; no initial product ansatz.
- Editorial comparison: **PASS**.

### S060 — Canonical Kerr angular operator and domain

- Frozen source: TeX 760–779; Markdown 839–863.
- Reader location: [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain). TeX 902–921; Markdown 1163–1190; PDF heading p. 16.
- Preserved content: Weighted L²(sin theta dtheta) fixed-m space; exact Ts50; canonical self-adjoint spin-bundle Ts0; eigenvalues51 ell(ell+1)-s² with ell≥max(|m|,|s|); regular/Friedrichs domain excludes scalar log when m±s=0; elliptic regularity gives smooth generalized eigenvectors after smooth potential.
- Editorial comparison: **PASS**.

### S061 — Kerr trace-class completeness

- Frozen source: TeX 781–786; Markdown 865–871.
- Reader location: [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain). TeX 923–928; Markdown 1192–1197; PDF heading p. 16.
- Preserved content: Complex potential bounded at fixed omega; quadratic ell growth gives trace-class resolvent p=1; same bounded perturbation/ray argument for Ts and adjoint; eight gaps pi/4<pi.
- Editorial comparison: **PASS**.

### S062 — Physical separated radial equation and scalar shifts

- Frozen source: TeX 788–801; Markdown 873–888.
- Reader location: [readable-kerr-normalization](../C002_READABLE.md#readable-kerr-normalization). TeX 936–948; Markdown 1206–1222; PDF heading p. 16.
- Preserved content: K_std=(r²+a²)omega-am; exact Teukolsky52; canonical Lambda differs from standard radial constant Lambda-s+a²omega²-2amomega; full PDE=radial operator-Ts with exactly this shift.
- Editorial comparison: **PASS**.

### S063 — Conjugated Kerr equation with no leftover singular potential

- Frozen source: TeX 806–824; Markdown 892–917.
- Reader location: [readable-kerr-conjugation](../C002_READABLE.md#readable-kerr-conjugation). TeX 959–977; Markdown 1234–1260; PDF heading p. 17.
- Preserved content: OmegaH,kappaH,k exact; H′/H=-iKstd/Delta; R=H Delta^-s f; exact E_s,P_s,C_s53; logarithmic derivative psi and 2Delta psi+(s+1)Delta′=P_s; remaining1/Delta terms cancel via Delta′=2(r-M),Kstd′=2omega r.
- Editorial comparison: **PASS**.

### S064 — Negative-spin horizon lemma including integral root differences

- Frozen source: TeX 826–845; Markdown 919–946.
- Reader location: [readable-kerr-negative](../C002_READABLE.md#readable-kerr-negative). TeX 984–1003; Markdown 1268–1293; PDF heading p. 17.
- Preserved content: s=-1,-2,Lambda complex, nonzero radial solution with weighted smooth horizon; f roots0 and k_s=s+i k/kappaH with Re<0; root0 unique analytic solution/nonzero constant; second has nonzero negative-power contribution possibly logs so is not smooth; recover exact54 with c≠0, proving non-special ingoing branch.
- Editorial comparison: **PASS**.

### S065 — Positive-spin reversal lemma assumptions and conclusion

- Frozen source: TeX 847–862; Markdown 948–967.
- Reader location: [readable-kerr-positive](../C002_READABLE.md#readable-kerr-positive). TeX 1010–1025; Markdown 1301–1320; PDF heading p. 18.
- Preserved content: s=1,2,m integer,gamma>0; actual nonzero canonical angular eigenfunction and nonzero radial solution; R∈H Delta^-s C∞ horizon-to-infinity and HR conormal polynomial infinity; define f,H Delta^s d_r^(2s)f and reflected u55; same Lambda,omega,m; nonzero negative-spin image, both boundary conditions, no positive-spin nonzero horizon-leading premise.
- Editorial comparison: **PASS**.

### S066 — Angular reflection preserves correct domain

- Frozen source: TeX 864–868; Markdown 969–974.
- Reader location: [readable-kerr-positive](../C002_READABLE.md#readable-kerr-positive). TeX 1027–1031; Markdown 1322–1326; PDF heading p. 18.
- Preserved content: theta→pi-theta interchanges Ts,T-s at same omega,m,Lambda; exchanges pole exponents|m+s| and|m-s|; maps canonical spin-bundle domains.
- Editorial comparison: **PASS**.

### S067 — Every coefficient of the spin-reversal identity

- Frozen source: TeX 870–881; Markdown 976–995.
- Reader location: [readable-kerr-reversal-identity](../C002_READABLE.md#readable-kerr-reversal-identity). TeX 1037–1048; Markdown 1334–1350; PDF heading p. 18.
- Preserved content: n=2s,Delta/P quadratic and C affine; exact d_r^(2s)E_s=E_-s d_r^(2s)56; nDelta′+P_s=P_-s; n(n-1)/2 Delta″+nP_s′+C_s=C_-s; n(n-1)/2 P_s″+nC_s′=2i omega n(2s-n)=0; no lower terms.
- Editorial comparison: **PASS**.

### S068 — Radial image and exceptional horizon regularity

- Frozen source: TeX 882–887; Markdown 996–1003.
- Reader location: [readable-kerr-reversal-identity](../C002_READABLE.md#readable-kerr-reversal-identity). TeX 1049–1054; Markdown 1354–1359; PDF heading p. 18.
- Preserved content: g=d_r^(2s)f solves E_-s; conjugate back to H Delta^s g solving spin-s reversed physical52; smooth f→smooth g at horizon, including resonant Frobenius cases.
- Editorial comparison: **PASS**.

### S069 — Nonzero image from differentiated outgoing asymptotics

- Frozen source: TeX 889–901; Markdown 1005–1022.
- Reader location: [readable-kerr-reversal-infinity](../C002_READABLE.md#readable-kerr-reversal-infinity). TeX 1060–1072; Markdown 1367–1382; PDF heading p. 18.
- Preserved content: Two radial exponential types distinct for gamma>0; HR conormal polynomial selects outgoing; retain f=e^(2iomega r)r^(4iMomega-1)(c0+O(r^-1)),c0≠0 and H expansion; retain differentiated58 with nonzero(2iomega)^(2s) factor.
- Editorial comparison: **PASS**.

### S070 — Outgoing reversed image

- Frozen source: TeX 902–906; Markdown 1023–1027.
- Reader location: [readable-kerr-reversal-infinity](../C002_READABLE.md#readable-kerr-reversal-infinity). TeX 1073–1077; Markdown 1388–1392; PDF heading p. 18.
- Preserved content: omega≠0 proves derivative not identically zero; H Rtilde=H²Delta^s d_r^(2s)f has polynomial conormal bounds and is outgoing spin-s branch; completes both nonzero and boundary claims.
- Editorial comparison: **PASS**.

### S071 — Automatic angular admissibility inequality

- Frozen source: TeX 908–915; Markdown 1029–1039.
- Reader location: [readable-kerr-admissibility](../C002_READABLE.md#readable-kerr-admissibility). TeX 1084–1091; Markdown 1400–1411; PDF heading p. 19.
- Preserved content: Exact59 Im(conj omega Lambda)||u||²=-gamma(<u,Ts0u>+a²|omega|²||cos theta u||²)<0; eigenvalues≥|s|>0 for all four spins.
- Editorial comparison: **PASS**.

### S072 — Nonseparated Kerr field to actual separated mode

- Frozen source: TeX 920–930; Markdown 1043–1054.
- Reader location: [readable-kerr-full](../C002_READABLE.md#readable-kerr-full). TeX 1102–1112; Markdown 1423–1433; PDF heading p. 19.
- Preserved content: Any nonzero full field detected by finite Riesz projection; highest nonzero Jordan coefficient solves52 homogeneously; bottom angular vector genuine regular eigenfunction; bounded radius-independent maps preserve scalar HDelta^-s horizon factor/smooth coefficient and infinity bounds; distinct exponentials select outgoing.
- Editorial comparison: **PASS**.

### S073 — Negative and positive Kerr branches both contradict import

- Frozen source: TeX 930–939; Markdown 1055–1064.
- Reader location: [readable-kerr-full](../C002_READABLE.md#readable-kerr-full). TeX 1112–1121; Markdown 1433–1442; PDF heading p. 19.
- Preserved content: Negative spins use Lemma8.1 then W; positive use Lemma8.2 producing nonzero negative-spin mode; descend finite chain and use adjoint completeness; full fixed-frequency field vanishes also a=0.
- Editorial comparison: **PASS**.

### S074 — External separation-constant dictionary and protected exceptional scope

- Frozen source: TeX 941–953; Markdown 1066–1079.
- Reader location: [readable-kerr-conventions](../C002_READABLE.md#readable-kerr-conventions). TeX 1128–1140; Markdown 1450–1462; PDF heading p. 19.
- Preserved content: Physical Teukolsky equation T; PV symmetrization context; AMPW Rtilde=Delta^(s/2)R; Lambda_AMPW+2amomega-a²omega²=A_Whiting+s with A_Whiting=Lambda-s; only negative-spin non-special import; no division by positive-spin horizon TS coefficient and no nonzero positive-spin horizon-leading assumption.
- Editorial comparison: **PASS**.

### S075 — Completion of all parameter sectors

- Frozen source: TeX 955–956; Markdown 1081–1082.
- Reader location: [readable-kerr-conventions](../C002_READABLE.md#readable-kerr-conventions). TeX 1142–1143; Markdown 1464–1465; PDF heading p. 19.
- Preserved content: Kerr Q=0 plus charged Q≠0 cover entire strictly subextremal theorem; preserve end-of-proof conclusion.
- Editorial comparison: **PASS**.

### S076 — Full frozen bibliography and its roles

- Frozen source: TeX 958–1012; Markdown 1084–1138.
- Reader location: [references](../C002_READABLE.md#references). TeX 1145–1199; Markdown 1471–1545; PDF heading page unavailable.
- Preserved content: Preserve all12 source entries H,MS,W,AMPW,TdC,PV,T,He,DGS,DCH,M,Z and their exact author/title/year/URLs; distinguish proof inputs from background context and bibliography-only items.
- Editorial comparison: **PASS**.

## Every displayed formula

The displayed-formula sequence is unchanged. Mathematical alignment changes are limited to (22), (23), and (50).

| Display | Frozen TeX | Reader TeX | Reader anchor | Content preserved |
|---|---|---|---|---|
| unnumbered 1 | 112–114 | 91–93 | [readable-parameters](../C002_READABLE.md#readable-parameters) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 2 | 133–136 | 117–120 | [readable-theorem](../C002_READABLE.md#readable-theorem) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 3 | 136–139 | 120–123 | [readable-theorem](../C002_READABLE.md#readable-theorem) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 4 | 161–165 | 152–156 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 5 | 165–168 | 156–159 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (1) | 168–171 | 159–162 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Charged constants fix the signed algebra used in positivity. |
| (2) | 173–177 | 164–168 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Full four-component first-order PDE; no initial angular separation. |
| (3) | 177–182 | 168–173 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Exact radial coefficient functions, including spin and charge signs. |
| (4) | 182–187 | 173–178 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Anticommutation/involution algebra supporting paired chiral reduction. |
| (5) | 189–194 | 180–185 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Actual full angular differential operator and 2x2 Theta block. |
| unnumbered 11 | 194–197 | 185–188 | [readable-source-algebra](../C002_READABLE.md#readable-source-algebra) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (6) | 209–215 | 206–212 | [readable-invertibility](../C002_READABLE.md#readable-invertibility) | Explicit invertible source matrix X, det=-d. |
| unnumbered 13 | 215–219 | 212–216 | [readable-invertibility](../C002_READABLE.md#readable-invertibility) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 14 | 219–223 | 216–220 | [readable-invertibility](../C002_READABLE.md#readable-invertibility) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (7) | 229–236 | 231–238 | [readable-boundary-weights](../C002_READABLE.md#readable-boundary-weights) | Different horizon weights for the I± sectors; must survive coefficient extraction. |
| (8) | 245–251 | 252–258 | [readable-invariants](../C002_READABLE.md#readable-invariants) | Exact phantom-gauge Weyl scalings. |
| (8a) | 252–262 | 259–269 | [readable-invariants](../C002_READABLE.md#readable-invariants) | Literal four gravitational/electromagnetic radiative quantities. |
| (8b) | 263–268 | 270–275 | [readable-invariants](../C002_READABLE.md#readable-invariants) | Exact invariant recovery factors in phantom gauge. |
| (9) | 283–288 | 296–301 | [readable-angular-domain](../C002_READABLE.md#readable-angular-domain) | First-order chiral angular realization B0+omega V. |
| unnumbered 20 | 288–290 | 301–303 | [readable-angular-domain](../C002_READABLE.md#readable-angular-domain) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (10) | 302–306 | 320–324 | [readable-jacobi](../C002_READABLE.md#readable-jacobi) | Constant Hadamard rotation exhibiting static first-order coupling. |
| (11) | 306–311 | 324–329 | [readable-jacobi](../C002_READABLE.md#readable-jacobi) | Second-order diagonal entries of the actual first-order square. |
| (12) | 311–315 | 329–333 | [readable-jacobi](../C002_READABLE.md#readable-jacobi) | Jacobi functions with complete regular-domain realizations. |
| (13) | 326–329 | 348–351 | [readable-static-branches](../C002_READABLE.md#readable-static-branches) | Paired static spectrum with correct ell threshold. |
| (14) | 334–337 | 356–359 | [readable-static-branches](../C002_READABLE.md#readable-static-branches) | Quadratic-form gap apart from the possible unpaired -beta branch. |
| (15) | 342–345 | 370–373 | [readable-angular-sign](../C002_READABLE.md#readable-angular-sign) | Angular form parameterized by real transform coordinate x≤-h. |
| unnumbered 27 | 348–350 | 376–378 | [readable-angular-sign](../C002_READABLE.md#readable-angular-sign) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 28 | 350–353 | 378–381 | [readable-angular-sign](../C002_READABLE.md#readable-angular-sign) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (16) | 353–356 | 381–384 | [readable-angular-sign](../C002_READABLE.md#readable-angular-sign) | Negative-system nonnegativity with a zero unpaired branch. |
| (17) | 358–362 | 386–390 | [readable-angular-sign](../C002_READABLE.md#readable-angular-sign) | Positive-system signed-charge lower bound. |
| unnumbered 31 | 365–371 | 398–404 | [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (18) | 371–375 | 404–408 | [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations) | Actual complex-eigenpair expectation identities, not real-separation approximation. |
| unnumbered 33 | 375–379 | 408–411 | [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (19) | 381–384 | 413–416 | [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations) | Exact multiplier square and norm controlling D. |
| (20) | 395–400 | 433–438 | [readable-root-completeness](../C002_READABLE.md#readable-root-completeness) | Resolvent ray bounds for generalized-root completeness. |
| (21) | 423–427 | 472–476 | [readable-chiral-projection](../C002_READABLE.md#readable-chiral-projection) | Refined two-sector Riesz pairing, including lambda=0. |
| (22) | 434–439 | 488–493 | [readable-jordan-pair](../C002_READABLE.md#readable-jordan-pair) | Exact actions on the two independent chiral Jordan chains. |
| (23) | 440–444 | 494–498 | [readable-jordan-pair](../C002_READABLE.md#readable-jordan-pair) | Triangular radial Jordan-coefficient equations. |
| (24) | 459–463 | 518–522 | [readable-radial-pair](../C002_READABLE.md#readable-radial-pair) | Homogeneous two-component radial system from highest globally nonzero pair. |
| (25) | 471–482 | 536–547 | [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling) | Both sign-dependent smooth horizon normalizations. |
| (26) | 482–487 | 547–552 | [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling) | Regular first-order pair for w,wsharp and affine A,B. |
| (27) | 487–491 | 552–556 | [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling) | Nonzero radial weight p and radial functions v_r,z_r. |
| (28) | 492–496 | 557–561 | [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling) | Weighted first-order pair used distributionally without scalar division. |
| (29) | 497–503 | 562–568 | [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling) | Ordered polynomial-coefficient scalar operator without inverse A/B. |
| (30) | 510–515 | 581–586 | [readable-horizon-exponents](../C002_READABLE.md#readable-horizon-exponents) | Horizon exponent determining integrability and unique positive-spin pole. |
| (31) | 525–531 | 602–608 | [readable-generic-extension](../C002_READABLE.md#readable-generic-extension) | Canonical finite-part differentiation identities establishing homogeneous extension. |
| (32) | 541–545 | 624–628 | [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator) | Exceptional positive-spin UHP frequency alpha=-1. |
| (33) | 548–552 | 631–635 | [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator) | Contrary angular identity if the correction denominator B(r+) vanished. |
| unnumbered 49 | 552–554 | 635–637 | [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (34) | 554–558 | 637–641 | [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator) | Strict denominator positivity contradiction for both signed charges. |
| (35) | 566–571 | 654–659 | [readable-delta-correction](../C002_READABLE.md#readable-delta-correction) | Essential finite delta correction, not merely a vanishing Laurent residue. |
| unnumbered 52 | 571–574 | 659–662 | [readable-delta-correction](../C002_READABLE.md#readable-delta-correction) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (36) | 591–594 | 686–689 | [readable-laplace-ray](../C002_READABLE.md#readable-laplace-ray) | Distributional Fourier–Laplace transform with fixed phase sign. |
| (37) | 597–600 | 692–695 | [readable-laplace-ray](../C002_READABLE.md#readable-laplace-ray) | Interior complex ray x<-h, safely inside holomorphy domain. |
| (38) | 604–608 | 704–708 | [readable-ordered-transform](../C002_READABLE.md#readable-ordered-transform) | Second-order transformed ODE with complex transport term. |
| (39) | 608–619 | 708–719 | [readable-ordered-transform](../C002_READABLE.md#readable-ordered-transform) | Complete transformed polynomial coefficient table. |
| (40) | 623–628 | 728–733 | [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge) | Exact positive divergence weights mu,P,W_x. |
| (41) | 629–633 | 734–738 | [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge) | Derivative identities that allow the transport-removing gauge. |
| (42) | 633–636 | 738–741 | [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge) | Exact gauge phase and substitution Y=e^-iomegaS U. |
| (43) | 636–641 | 741–746 | [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge) | Gauged divergence-form equation. |
| (44) | 641–645 | 746–750 | [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge) | Full real radial potential R, including charge/rotation terms. |
| (45) | 650–653 | 761–764 | [readable-coercive-potential](../C002_READABLE.md#readable-coercive-potential) | Actual angular expectation decomposition into -k+omega l+omega²B. |
| unnumbered 63 | 653–658 | 764–769 | [readable-coercive-potential](../C002_READABLE.md#readable-coercive-potential) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (46) | 658–663 | 769–774 | [readable-coercive-potential](../C002_READABLE.md#readable-coercive-potential) | Strictly positive transformed quadratic coefficient for y>2. |
| (47) | 672–676 | 789–793 | [readable-finite-endpoint](../C002_READABLE.md#readable-finite-endpoint) | Finite-endpoint powers ensuring integrability before energy integration. |
| (48a) | 684–689 | 806–811 | [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint) | Explicit finite-part representation for generic positive spin, alpha≠-1. |
| unnumbered 67 | 691–696 | 813–818 | [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (48) | 706–710 | 826–830 | [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint) | Remote-endpoint exponential decay from strict delta>0. |
| unnumbered 69 | 718–722 | 844–848 | [readable-energy-identity](../C002_READABLE.md#readable-energy-identity) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (49) | 723–728 | 849–854 | [readable-energy-identity](../C002_READABLE.md#readable-energy-identity) | Coercive imaginary-part energy identity forcing U=0. |
| (50) | 761–767 | 903–909 | [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain) | Kerr canonical spin-bundle angular operator in stated convention. |
| (51) | 769–773 | 911–915 | [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain) | Canonical spherical spectrum and regular-domain threshold. |
| (52) | 791–798 | 938–945 | [readable-kerr-normalization](../C002_READABLE.md#readable-kerr-normalization) | Physical Kerr radial Teukolsky equation with exact scalar shifts. |
| unnumbered 74 | 806–810 | 959–963 | [readable-kerr-conjugation](../C002_READABLE.md#readable-kerr-conjugation) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (53) | 811–814 | 964–967 | [readable-kerr-conjugation](../C002_READABLE.md#readable-kerr-conjugation) | Conjugated Kerr radial equation for weighted-smooth horizon coefficient. |
| unnumbered 76 | 814–819 | 967–972 | [readable-kerr-conjugation](../C002_READABLE.md#readable-kerr-conjugation) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (54) | 828–832 | 986–990 | [readable-kerr-negative](../C002_READABLE.md#readable-kerr-negative) | Non-special negative-spin ingoing Frobenius branch with nonzero coefficient. |
| unnumbered 78 | 836–839 | 994–997 | [readable-kerr-negative](../C002_READABLE.md#readable-kerr-negative) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (55) | 853–857 | 1016–1020 | [readable-kerr-positive](../C002_READABLE.md#readable-kerr-positive) | Positive→negative spin angular reflection and radial derivative map. |
| (56) | 872–876 | 1039–1043 | [readable-kerr-reversal-identity](../C002_READABLE.md#readable-kerr-reversal-identity) | Exact all-coefficient spin-reversal intertwining identity. |
| unnumbered 81 | 877–879 | 1044–1046 | [readable-kerr-reversal-identity](../C002_READABLE.md#readable-kerr-reversal-identity) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| unnumbered 82 | 879–882 | 1046–1049 | [readable-kerr-reversal-identity](../C002_READABLE.md#readable-kerr-reversal-identity) | Unnumbered formula: preserve within the linked proof checkpoint(s). |
| (57) | 892–896 | 1063–1067 | [readable-kerr-reversal-infinity](../C002_READABLE.md#readable-kerr-reversal-infinity) | Nonzero outgoing radial asymptotic, with differentiated expansions available. |
| (58) | 897–902 | 1068–1073 | [readable-kerr-reversal-infinity](../C002_READABLE.md#readable-kerr-reversal-infinity) | Nonzero derivative image and outgoing preservation. |
| (59) | 909–914 | 1085–1090 | [readable-kerr-admissibility](../C002_READABLE.md#readable-kerr-admissibility) | Automatic complex angular admissibility with strict positive spherical energy. |

## Assumptions and boundary conditions

- **A01 Global background and mode convention.** M,a,Q real; M>0; a²+Q²<M²; signed Q unrestricted; m∈Z; omega∈C; gamma>0; e^-iomega t+im phi. Frozen TeX 112–116; [readable-parameters](../C002_READABLE.md#readable-parameters); TeX 91–95; Markdown 74–80; PDF heading p. 3.
- **A02 Open exterior and physical boundaries.** r>r+,delta>0; exact weighted horizon smoothness and H-phase; conormal radial/angular polynomial infinity bounds; regular spin sections on axis. Frozen TeX 133–148; [readable-theorem](../C002_READABLE.md#readable-theorem); TeX 117–132; Markdown 103–122; PDF heading p. 3.
- **A03 Theorem scope.** Radiative exclusion only; no nonradiative classification/decay/nonlinear/extremal/uniform-extremal claim. Frozen TeX 150–153; [readable-theorem](../C002_READABLE.md#readable-theorem); TeX 134–137; Markdown 124–127; PDF heading p. 3.
- **A04 Charged branch.** Q≠0 and sigma=±1; fixed real background; exact complex algebra without conjugating omega. Frozen TeX 161–204; [readable-source-algebra](../C002_READABLE.md#readable-source-algebra); TeX 152–195; Markdown 143–212; PDF heading p. 4.
- **A05 Invertibility and Hilbert domain transfer.** d>0,detX=-d,nonvanishing rho/rho*,Delta>0,sin theta>0 inside exterior; physical source axis/horizon/infinity data imply transformed conditions. Frozen TeX 215–240; [readable-invertibility](../C002_READABLE.md#readable-invertibility), [readable-boundary-weights](../C002_READABLE.md#readable-boundary-weights); TeX 212–242; Markdown 234–273; PDF heading p. 5.
- **A06 Physical necessary-system entry.** Legitimate phantom gauge because Q≠0; use physical→necessary equations only; do not assume reconstruction or a real-frequency flux identity. Frozen TeX 242–276; [readable-invariants](../C002_READABLE.md#readable-invariants); TeX 249–282; Markdown 281–326; PDF heading p. 5.
- **A07 First-order charged angular domain.** Maximal distributional L²(dtheta) first-order domain selected by endpoint half-integers; V bounded Hermitian; no logarithmic second-order extension. Frozen TeX 293–322; [readable-angular-domain](../C002_READABLE.md#readable-angular-domain), [readable-jacobi](../C002_READABLE.md#readable-jacobi); TeX 306–338; Markdown 358–403; PDF heading p. 6.
- **A08 Angular form coordinate/sign conditions.** Real x≤-h; q=|Q|/M∈(0,1); c/x opposite beta; unpaired negative-system contribution may vanish. Frozen TeX 342–362; [readable-angular-sign](../C002_READABLE.md#readable-angular-sign); TeX 370–390; Markdown 444–480; PDF heading p. 7.
- **A09 Genuine normalized eigenvector.** B(omega)u=lambda u with u in first-order domain and ||u||=1; complex frequency retained; real expectations; no Dom(B²) or omega-dependent-in-x vector premise. Frozen TeX 364–385; [readable-angular-expectations](../C002_READABLE.md#readable-angular-expectations); TeX 397–417; Markdown 488–520; PDF heading p. 8.
- **A10 Completeness/detection assumptions.** Closed dense fixed-domain operator with one actual Schatten resolvent; polynomial nonreal-ray bounds/gaps; apply to adjoint too; generalized roots suffice. Frozen TeX 390–417; [readable-root-completeness](../C002_READABLE.md#readable-root-completeness), [readable-adjoint-detection](../C002_READABLE.md#readable-adjoint-detection); TeX 428–460; Markdown 532–569; PDF heading p. 8,9.
- **A11 Full-field extraction.** Nonzero entire PDE field at an interior radius; finite paired Riesz projection; globally highest nonidentically-zero radial pair; bounded radius-independent coefficient maps preserve differing horizon powers. Frozen TeX 422–466; [readable-chiral-projection](../C002_READABLE.md#readable-chiral-projection), [readable-jordan-pair](../C002_READABLE.md#readable-jordan-pair), [readable-radial-pair](../C002_READABLE.md#readable-radial-pair); TeX 471–525; Markdown 581–653; PDF heading p. 9,10.
- **A12 Division-free radial branch.** A/B may vanish at isolated exterior points; all arguments must avoid inverse A or B during elimination. Frozen TeX 471–505; [readable-radial-rescaling](../C002_READABLE.md#readable-radial-rescaling); TeX 536–570; Markdown 665–719; PDF heading p. 10.
- **A13 Generic distribution range.** Realpha>1 negative or>-2 positive; positive alpha≠-1 uses canonical finite part; fixed omega, no holomorphic family of physical modes. Frozen TeX 510–536; [readable-horizon-exponents](../C002_READABLE.md#readable-horizon-exponents), [generic-frequencies](../C002_READABLE.md#generic-frequencies), [readable-generic-extension](../C002_READABLE.md#readable-generic-extension); TeX 581–613; Markdown 731–773; PDF heading p. 11.
- **A14 Exceptional branch.** Only alpha=-1; prove B(r+)≠0 before using correction denominator; finite horizon delta must be included even though v_r becomes smooth. Frozen TeX 541–582; [readable-resonance-denominator](../C002_READABLE.md#readable-resonance-denominator), [readable-delta-correction](../C002_READABLE.md#readable-delta-correction); TeX 624–670; Markdown 785–852; PDF heading p. 11,12.
- **A15 Laplace domain and operator order.** Finite-order supported v_e; controlled outgoing exponential tail; Imxi<-eta gamma; interior ray x<-h; derivative/multiplication substitutions retain order. Frozen TeX 589–621; [readable-laplace-ray](../C002_READABLE.md#readable-laplace-ray), [readable-ordered-transform](../C002_READABLE.md#readable-ordered-transform); TeX 684–721; Markdown 868–922; PDF heading p. 12,13.
- **A16 Energy coefficient conditions.** Real x<-h; P,W>0;k≥0 from genuine angular form; B>0 from actual D expectation and delta>0;l real but not required positive. Frozen TeX 623–666; [readable-energy-gauge](../C002_READABLE.md#readable-energy-gauge), [the-coercive-sign](../C002_READABLE.md#the-coercive-sign), [readable-coercive-potential](../C002_READABLE.md#readable-coercive-potential); TeX 728–777; Markdown 930–1010; PDF heading p. 13,14.
- **A17 Boundary prerequisites for integration.** Both x→-h and x→-infinity estimates proved before IBP; gamma>0 ensures finite-endpoint integrability;delta>0 remote exponential; corrected delta branch included. Frozen TeX 670–712; [readable-finite-endpoint](../C002_READABLE.md#readable-finite-endpoint), [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint); TeX 787–832; Markdown 1022–1082; PDF heading p. 14.
- **A18 Injectivity and recovery.** Holomorphic connected half-plane and interior ray; exponentially damped tempered distribution on horizontal line; p nonzero; A affine not identically zero; continuity across possible A zero. Frozen TeX 731–739; [readable-injectivity](../C002_READABLE.md#readable-injectivity); TeX 862–870; Markdown 1120–1128; PDF heading p. 15.
- **A19 Kerr canonical/angular hypotheses.** Q=0; all spins±1±2; fixed-m L²(sin theta dtheta); canonical regular spin-bundle/Friedrichs domain excludes logarithmic scalar branch; trace-class resolvent/adjoint roots. Frozen TeX 747–786; [readable-kerr-input](../C002_READABLE.md#readable-kerr-input), [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain); TeX 884–928; Markdown 1144–1197; PDF heading p. 16.
- **A20 Negative-spin horizon lemma hypotheses.** s∈{-1,-2}; Lambda arbitrary complex; nonzero physical radial52; R=HDelta^-s f with f smooth up to horizon; gamma>0 forces second indicial root negative real part. Frozen TeX 826–845; [readable-kerr-negative](../C002_READABLE.md#readable-kerr-negative); TeX 984–1003; Markdown 1268–1293; PDF heading p. 17.
- **A21 Positive-spin reversal hypotheses.** s∈{1,2}; integer m; gamma>0; nonzero canonical eigenfunction u; nonzero radial52; horizon-to-infinity smooth f; HR polynomial conormal infinity; do not assume nonzero horizon-leading f(0). Frozen TeX 847–906; [readable-kerr-positive](../C002_READABLE.md#readable-kerr-positive), [readable-kerr-reversal-identity](../C002_READABLE.md#readable-kerr-reversal-identity), [readable-kerr-reversal-infinity](../C002_READABLE.md#readable-kerr-reversal-infinity); TeX 1010–1077; Markdown 1301–1392; PDF heading p. 18.
- **A22 Kerr import and dictionary.** Actual angular Lambda obeys59; regular-axis angular eigenfunction, outgoing infinity and proved non-special negative-spin horizon branch; exact radial constant shifts; no positive-spin TS division. Frozen TeX 908–953; [readable-kerr-admissibility](../C002_READABLE.md#readable-kerr-admissibility), [completion-of-the-full-kerr-field-argument](../C002_READABLE.md#completion-of-the-full-kerr-field-argument), [readable-kerr-full](../C002_READABLE.md#readable-kerr-full), [readable-kerr-conventions](../C002_READABLE.md#readable-kerr-conventions); TeX 1084–1140; Markdown 1400–1462; PDF heading p. 19.

## External inputs and their hypotheses as stated in C002

These entries preserve the manuscript’s stated inputs and scope. They are not new source checks or new claims that a cited theorem was re-audited.

- **E01 Context literature H,He,DGS,DCH,M,Z.** Background only. Retain the distinction between prior real-frequency/limited-parameter results, numerical evidence and the present proof. This inventory does not verify or update bibliographic claims. Frozen TeX 95–110; [introduction-and-theorem](../C002_READABLE.md#introduction-and-theorem); TeX 69–84; Markdown 51–66; PDF heading p. 3.
- **E02 Hintz original necessary system, equations7–8.** Input is the exact four-component first-order system with specified matrices and original physical conditions; transformed equivalence complex algebraic, no omega conjugation. Frozen TeX 171–204; [readable-source-algebra](../C002_READABLE.md#readable-source-algebra); TeX 162–195; Markdown 161–212; PDF heading p. 4.
- **E03 Motohashi radiative mixtures equations5.1–5.2 and phantom gauge.** Requires original physical perturbation data and nonzero charged background Maxwell Phi1 for the null-rotation gauge; only necessary physical implication used, no reconstruction. Frozen TeX 242–276; [readable-invariants](../C002_READABLE.md#readable-invariants); TeX 249–282; Markdown 281–326; PDF heading p. 5.
- **E04 Hintz Lemma1 at zero frequency; deficiency argument also supplied.** Static compact-support angular operator, half-integer endpoint roots, singular branch not L², vanishing boundary flux; conclusion essential self-adjointness/maximal first-order realization. Bounded Hermitian V preserves domain. Frozen TeX 293–300; [readable-angular-domain](../C002_READABLE.md#readable-angular-domain); TeX 306–313; Markdown 358–365; PDF heading p. 6.
- **E05 Jacobi differential equation, weighted polynomial density and first-order coupling.** Parameters A_s,B_s nonnegative absolute values; weighted norms after x=cos theta; regular functions and first-order images in actual domain; critical leading-image cancellation; conclusion exact complete paired/unpaired spectrum. No precise separate Jacobi citation is attached in the frozen paragraph. Frozen TeX 311–332; [readable-jacobi](../C002_READABLE.md#readable-jacobi), [readable-static-branches](../C002_READABLE.md#readable-static-branches); TeX 329–354; Markdown 390–424; PDF heading p. 6,7.
- **E06 Mityagin–Siegl Theorem2.2, charged operator.** Closed densely defined operator with one S_p resolvent, polynomial resolvent bounds along rays with successive gaps strictly<pi/p. Verified in source at p=2 using static spectrum, bounded perturbation, actual Hilbert–Schmidt point, eight nonreal rays. Apply to adjoint for detection, not Riesz-basis expansion. Frozen TeX 390–417; [readable-root-completeness](../C002_READABLE.md#readable-root-completeness), [readable-adjoint-detection](../C002_READABLE.md#readable-adjoint-detection); TeX 428–460; Markdown 532–569; PDF heading p. 8,9.
- **E07 Canonical meromorphic power distributions.** Continue from integrable region; Realpha>-2,alpha≠-1 in positive case; multiply smooth coefficients and use identities31; compact support localization/joining. Conclusion homogeneous supported pair at fixed omega. No separately named distribution reference is attached in frozen text. Frozen TeX 521–536; [readable-generic-extension](../C002_READABLE.md#readable-generic-extension); TeX 598–613; Markdown 754–773; PDF heading p. 11.
- **E08 Distributional Fourier–Laplace calculus.** Finite-order distribution supported [r+,infty), outgoing exponential tail and cutoffs/exponential damping; Imxi<-eta gamma. Compact finite-part/delta terms harmless; transform analytic in stated half-plane. Frozen TeX 589–600; [readable-laplace-ray](../C002_READABLE.md#readable-laplace-ray); TeX 684–695; Markdown 868–887; PDF heading p. 12.
- **E09 Explicit endpoint Laplace estimate.** Uses identity48a and integrable powers, not a blanket support-edge theorem or Watson asymptotic. Include delta and ordinary negative-spin cases and every fixed derivative. Frozen TeX 681–712; [readable-remote-endpoint](../C002_READABLE.md#readable-remote-endpoint); TeX 803–832; Markdown 1043–1082; PDF heading p. 14.
- **E10 Holomorphic identity theorem and Fourier injectivity.** Zero along interior complex ray with accumulation point inside holomorphic connected half-plane; sufficiently low horizontal line corresponds to exponentially damped tempered distribution; Fourier injectivity gives distribution zero. Frozen TeX 731–739; [readable-injectivity](../C002_READABLE.md#readable-injectivity); TeX 862–870; Markdown 1120–1128; PDF heading p. 15.
- **E11 Whiting UHP Kerr theorem recalled in AMPW introduction/II.A.3 Definition3.** Restricted to negative spins s=-1,-2, regular-axis separated mode, non-special ingoing Frobenius horizon branch, outgoing infinity, open UHP frequency on subextremal Kerr. Positive spins and nonseparated fields are reduced in manuscript rather than imported wholesale. Frozen TeX 747–758; [readable-kerr-input](../C002_READABLE.md#readable-kerr-input); TeX 884–895; Markdown 1144–1155; PDF heading p. 16.
- **E12 Canonical spin-bundle spherical spectrum and elliptic regularity.** Fixed-m canonical/Friedrichs spin-bundle realization on weighted sphere; regular branch, excludes scalar logarithmic L² solution; smooth potential perturbation; yields smooth eigenvectors/generalized eigenvectors. Exact spherical eigenvalues stated51. Frozen TeX 760–779; [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain); TeX 902–921; Markdown 1163–1190; PDF heading p. 16.
- **E13 Mityagin–Siegl theorem reused for Kerr.** Canonical Ts0 quadratic spectrum gives trace-class resolvent p=1; bounded complex potential, closed fixed domain; nonreal-ray bounds and eight gaps pi/4<pi; apply to Ts and adjoint. Frozen TeX 781–786; [readable-kerr-domain](../C002_READABLE.md#readable-kerr-domain); TeX 923–928; Markdown 1192–1197; PDF heading p. 16.
- **E14 Physical Teukolsky separation and direct conjugation.** Use stated time/azimuthal mode, canonical Lambda convention, Kstd=-K; exact radial52 and its scalar shift; direct conjugation yields53 without singular remainder. Frozen TeX 788–824; [readable-kerr-normalization](../C002_READABLE.md#readable-kerr-normalization), [horizon-branches-and-the-spin-reversal-identity](../C002_READABLE.md#horizon-branches-and-the-spin-reversal-identity), [readable-kerr-conjugation](../C002_READABLE.md#readable-kerr-conjugation); TeX 936–977; Markdown 1206–1260; PDF heading p. 16,17.
- **E15 Regular-singular/Frobenius classification in Lemma8.1.** Smooth weighted horizon f, negative s and gamma>0; analytic coefficient equation with roots0 and k_s of strictly negative real part; root0 unique analytic branch, other independent solution nonsmooth even with integral-difference logarithms. No separate theorem citation is attached in frozen proof. Frozen TeX 826–845; [readable-kerr-negative](../C002_READABLE.md#readable-kerr-negative); TeX 984–1003; Markdown 1268–1293; PDF heading p. 17.
- **E16 Differentiated outgoing radial asymptotic expansions.** For gamma>0 distinct radial exponentials; conormal bound on HR selects outgoing nonzero solution. Exact57 with c0≠0 and differentiated58; conclusion nonzero reversed image and polynomial conormal outgoing bounds. The frozen paragraph does not state a separate asymptotic theorem or an explicit sector theorem citation; reconstruction must retain its claim without silently replacing it by a different proof. Frozen TeX 889–905; [readable-kerr-reversal-infinity](../C002_READABLE.md#readable-kerr-reversal-infinity); TeX 1060–1076; Markdown 1367–1391; PDF heading p. 18.
- **E17 AMPW separation normalization and Teukolsky/PV conventions.** Rtilde=Delta^(s/2)R; Lambda_AMPW+2amomega-a²omega²=A_Whiting+s and A_Whiting=Lambda-s. Invoke only negative-spin non-special Kerr theorem; no positive-spin horizon coefficient assumption/division. Frozen TeX 941–953; [readable-kerr-conventions](../C002_READABLE.md#readable-kerr-conventions); TeX 1128–1140; Markdown 1450–1462; PDF heading p. 19.
- **E18 Teixeira da Costa bibliography entry.** Included in frozen bibliography but not explicitly invoked in the frozen proof body. Do not pretend an additional theorem/hypothesis was stated in frozen C002; any explanatory supplement using it must be separately identified. Frozen TeX 976–979; [readable-kerr-conventions](../C002_READABLE.md#readable-kerr-conventions); TeX 1163–1166; Markdown 1496–1499; PDF heading p. 19.

## Prose-tone changes

These six replacements adjust presentation while retaining the surrounding calculation and hypotheses.

| Frozen wording | Reader wording |
|---|---|
| with no unauthorized logarithmic second-order boundary extension. | with the logarithmic second-order boundary branch excluded by the first-order domain. |
| For clarity, the canonical eigenvalue | The canonical eigenvalue |
| This does not presume self-adjointness at complex frequency or a square-operator domain. | This calculation stays on the first-order domain; it requires neither self-adjointness at complex frequency nor a square-operator domain. |
| No Riesz-basis property is needed. | Completeness is used as a finite-projection detection principle, without a Riesz-basis assumption. |
| These local algebraic identifications do not require a real-frequency flux formula. | These identifications follow from the local algebraic relations at the fixed complex frequency. |
| Thus no general support-edge distribution bound or Watson asymptotic coefficient is being presumed. | These explicit estimates give the required bound for each part of the distribution. |

## Added explanations and scope

All forty added explanations were checked for placement and consistency with the preserved calculation. They introduce purposes and structure without changing theorem assumptions or adding a different proof. One draft sign ambiguity was corrected before this receipt: the potential is written as `-k + omega l + omega^2 B`, and the explanation now explicitly says the nonnegative form enters with a minus sign.

| Reader heading | Frozen insertion point | Reader TeX | PDF heading page |
|---|---|---|---|
| [Parameters and the exterior geometry](../C002_READABLE.md#readable-parameters) | 112 | 87 | 3 |
| [Radiative conclusion and physical boundary conditions](../C002_READABLE.md#readable-theorem) | 118 | 98 | 3 |
| [The coupled operator and its chiral symmetries](../C002_READABLE.md#readable-source-algebra) | 161 | 148 | 4 |
| [An invertible change of physical variables](../C002_READABLE.md#readable-invertibility) | 209 | 202 | 5 |
| [Transporting the horizon and infinity conditions](../C002_READABLE.md#readable-boundary-weights) | 229 | 227 | 5 |
| [Returning to the radiative invariants](../C002_READABLE.md#readable-invariants) | 242 | 245 | 5 |
| [The first-order angular realization](../C002_READABLE.md#readable-angular-domain) | 283 | 292 | 6 |
| [Jacobi functions and the complete static spectrum](../C002_READABLE.md#readable-jacobi) | 302 | 316 | 6 |
| [Paired modes and the unpaired ground branch](../C002_READABLE.md#readable-static-branches) | 324 | 342 | 7 |
| [A form estimate retaining the signed charge](../C002_READABLE.md#readable-angular-sign) | 342 | 366 | 7 |
| [Complex eigenvalues through real expectations](../C002_READABLE.md#readable-angular-expectations) | 364 | 393 | 8 |
| [Resolvent bounds and the completeness theorem](../C002_READABLE.md#readable-root-completeness) | 390 | 424 | 8 |
| [Detection through the adjoint root spaces](../C002_READABLE.md#readable-adjoint-detection) | 412 | 451 | 9 |
| [Finite projections preserving the coupled system](../C002_READABLE.md#readable-chiral-projection) | 422 | 467 | 9 |
| [Jordan chains and the last nonzero coefficient](../C002_READABLE.md#readable-jordan-pair) | 433 | 483 | 9 |
| [The radial pair and its inherited boundary class](../C002_READABLE.md#readable-radial-pair) | 458 | 513 | 10 |
| [Smooth horizon variables](../C002_READABLE.md#readable-radial-rescaling) | 471 | 532 | 10 |
| [The two horizon exponents](../C002_READABLE.md#readable-horizon-exponents) | 510 | 577 | 11 |
| [Homogeneous extension away from the pole](../C002_READABLE.md#readable-generic-extension) | 521 | 594 | 11 |
| [The exceptional frequency and a nonzero denominator](../C002_READABLE.md#readable-resonance-denominator) | 541 | 620 | 11 |
| [Cancelling the horizon delta source](../C002_READABLE.md#readable-delta-correction) | 563 | 647 | 12 |
| [The transform domain and the interior ray](../C002_READABLE.md#readable-laplace-ray) | 589 | 680 | 12 |
| [Transforming the ordered polynomial operator](../C002_READABLE.md#readable-ordered-transform) | 602 | 698 | 13 |
| [Divergence form and removal of imaginary transport](../C002_READABLE.md#readable-energy-gauge) | 623 | 724 | 13 |
| [The three real coefficients of the potential](../C002_READABLE.md#readable-coercive-potential) | 649 | 756 | 14 |
| [The finite endpoint](../C002_READABLE.md#readable-finite-endpoint) | 670 | 783 | 14 |
| [The remote endpoint, including finite parts and deltas](../C002_READABLE.md#readable-remote-endpoint) | 681 | 799 | 14 |
| [The positive transformed energy](../C002_READABLE.md#readable-energy-identity) | 717 | 839 | 15 |
| [Recovering the radial pair and the full charged field](../C002_READABLE.md#readable-injectivity) | 731 | 858 | 15 |
| [The negative-spin input and the full-field problem](../C002_READABLE.md#readable-kerr-input) | 747 | 880 | 16 |
| [The canonical angular operator and its root spaces](../C002_READABLE.md#readable-kerr-domain) | 760 | 898 | 16 |
| [Angular and radial separation conventions](../C002_READABLE.md#readable-kerr-normalization) | 788 | 931 | 16 |
| [The horizon-regular conjugated equation](../C002_READABLE.md#readable-kerr-conjugation) | 806 | 955 | 17 |
| [The negative-spin horizon branch](../C002_READABLE.md#readable-kerr-negative) | 826 | 980 | 17 |
| [Spin reversal for both positive spins](../C002_READABLE.md#readable-kerr-positive) | 847 | 1006 | 18 |
| [The radial differential identity.](../C002_READABLE.md#readable-kerr-reversal-identity) | 870 | 1033 | 18 |
| [Nonzero image and the outgoing condition.](../C002_READABLE.md#readable-kerr-reversal-infinity) | 889 | 1056 | 18 |
| [The angular admissibility inequality](../C002_READABLE.md#readable-kerr-admissibility) | 908 | 1080 | 19 |
| [From the full field to a forbidden separated mode](../C002_READABLE.md#readable-kerr-full) | 920 | 1098 | 19 |
| [Matching the classical theorem and concluding](../C002_READABLE.md#readable-kerr-conventions) | 941 | 1124 | 19 |

## Verification boundary

This receipt covers editorial source correspondence. Compilation and visual page review are recorded separately by the publication workflow. Native Lean verification belongs to the unchanged theorem tree; this editorial comparison does not rerun or replace those completed checks. The original mathematical manuscript, all Lean declarations, and the disclosed external physical-entry boundary remain intact.

Machine-readable details: [READABLE_EDITION_VERIFICATION.json](../release_checks/READABLE_EDITION_VERIFICATION.json).

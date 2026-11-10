# Paper-to-Lean release notes

This document compares the published paper *The irrationality exponent of small-height lacunary series* by Ruiyi Zhang with the Lean formalization, using the frozen 2026-11-09 source comparison and the final packaged modules. It records mathematical representation, proof-route, quantitative, and scope differences. It does not certify a build, the kernel axioms, or the Palomar comparator; those require their own saved receipts.

The main Lean statement has the same hypotheses and conclusions as the published main theorem, including arbitrary coefficient signs, the boundary lower ratio 2, and an infinite upper limit. None of the three auxiliary contracts considered here is a statement printed in the paper. Several intermediate quantitative bounds or parameter choices differ, and several stronger intermediate or ancillary assertions are outside the exported Lean scope, as listed below.

## Frozen comparison inputs

- Published version: Zenodo record [24056145](https://zenodo.org/records/24056145), concept DOI [10.5281/zenodo.24056144](https://doi.org/10.5281/zenodo.24056144).
- Published source archive: SHA-256 `5079d452273e5f6295d33d287d0f63ce529df89a4621bced5479fa2865f48329`.
- The archive's `source/main.tex`: SHA-256 `21ab905f25860832a6d5755b6f4d6ff1519a06f4b039e68a3c240ee3d9ef0953`.
- Published PDF: SHA-256 `9ead9fd52ddb275de352e706991ff7240ed034b3beef763e1c4f8aed6dcb27cc`; its extracted text independently confirms the theorem and equation numbering used here.
- Lean: source paths below refer to modules in this package, whose exact hashes are recorded in the package manifests. The package includes the comparison and verification records supporting the statements below.
- Toolchain: `leanprover/lean4:v4.35.0-rc4`; Mathlib commit `1f414401f69059aa7eead47b53ee40bd38455eeb`.

Paper line references refer to the exact published `source/main.tex` identified above. Lean references use stable module and declaration names; source line numbers from earlier audit snapshots are omitted because proof simplifications and comment normalization change them.

The main declaration is named `Paper4.theorem_1` to match the published Theorem 1.

## Main-statement identity

The full Lean declarations in `Challenge.lean` and `Solution.lean` have identical types, including their normalized declaration headers. The following table compares that type with published Theorem 1 (`main.tex:57–76`) and its definitions (`43–55`).

| Published statement | Lean representation | Identity finding |
|---|---|---|
| Integer base `N >= 2` | `N : ℕ`, `hN : 2 ≤ N` | Equivalent: every integer at least 2 is a natural number. |
| Positive integers `u_1 < u_2 < ...` | `u : ℕ → ℕ`, `∀ j, 0 < u j`, `StrictMono u` | Equivalent after paper index `j+1` is represented by Lean index `j`. |
| Nonzero rational coefficients | `coeff : ℕ → ℚ`, `∀ j, coeff j ≠ 0` | Exact hypothesis; no sign restriction. |
| Reduced height `H(a/b)=max(|a|,b)` | `max q.num.natAbs q.den` | Exact canonical rational height. |
| `log H(coeff_j) = o(u_j)` | The quotient by positive `u j` tends to zero at `atTop` | Equivalent little-o condition; no uniform exponential constant is substituted. |
| `liminf u_(j+1)/u_j >= 2` | For every positive epsilon, eventually `2-epsilon <= exponentRatio u j` | Equivalent epsilon-tail form; neither convergence nor eventual ratio at least 2 is assumed. |
| Absolutely convergent series | `Summable (fun j => |term N u coeff j|)` and its real `tsum` | Same series and absolute convergence. |
| The sum is irrational | `Irrational (∑' j, term N u coeff j)` | Exact conclusion. |
| `mu(x)=limsup ratio`, both sides in `[2,+infinity]` | Explicit `2 ≤ irrationalityExponent x` and equality of `EReal` values | Exact conclusion, retaining `⊤`; no finite-limsup hypothesis. |
| Infinitely many integer numerator/positive denominator pairs, strict error inequality | Unbounded natural supplied denominators, integer numerators, the same strict inequality | Equivalent: for fixed positive denominator the allowed numerator interval is finite. Supplied fractions need not be reduced in either definition. |

The paper defines the exponent for irrational inputs only. Lean gives a total definition on real inputs; its restriction to the irrational sum is the paper's exponent. No inference from `mu > 1` to irrationality is used. On rational inputs this total definition gives `⊤`, an auxiliary convention that does not change the main theorem.

## Classification

- **A:** equivalent reformulation or a different intermediate construction/proof organization.
- **B:** changed intermediate constant or parameter; the quantitative effect is stated explicitly.
- **C:** a paper statement false or imprecise as printed, with its effect on the main theorem.
- **D:** an extra hypothesis or a weaker/omitted result in Lean. The main theorem has no class-D restriction. Class-D items below are explicitly limited to intermediate exports or ancillary scope.

## A — equivalent reformulations and different constructions

| ID | Paper location and wording | Lean location and difference | Effect/reason |
|---|---|---|---|
| A01 | Theorem 1 and definitions, Section 1, lines 43–76 | `Paper4/Statement.lean`; `Challenge.lean`; `Solution.lean` | Natural types, zero-based sequences, quotient limits, `tsum`, epsilon tails, and an extended-real supremum/limsup encode the same statement. |
| A02 | Section 2, lines 192–227: actual canonical finite/infinite regular continued fractions; zero-based convergents; initial `1,1` allowed | `CF/Bridge.lean`; `CF/Canonical.lean`; `CF/Gap.lean` | Uses Mathlib `GenContFract.of` and certificates tied to that actual expansion. `CFGap` stores nonterminalness, the actual convergent value, and its actual next denominator. `LogGap` stores `(left,width)` rather than `(left,right)`; `right=left+width`. |
| A03 | Section 2, equations (2.1)–(2.2), lines 200–222 | `CF/Bridge.lean`; `CF/Gap.lean` | CF error estimates and strict Legendre recognition are isolated as reusable lemmas valid for rational and irrational targets. Nonzero error is explicit where needed for rational nonterminalness. These are the paper's existing conditions, not new main hypotheses. |
| A04 | Section 3, Lemma 3.1, equations (3.1)–(3.2), lines 231–275 | `CF/Continuants.lean`; `HmuSkeleton/ReversalBridge.lean` | Matrix/list continuants, recognition of the canonical reversed word, and the final-one merge are proved separately before obtaining the same actual old-gap endpoint estimates with error `log 2`. Only `m=1,a_1=1` is excluded by `V>=2`; no extra length restriction is introduced. Universal reversal remains valid for every actual reverse-point gap. The perturbation-scale endpoint/location estimates belong to the selected local construction in Section 4, not to every such gap. |
| A05 | Section 4, equations (4.1)–(4.2), lines 280–294 | `HmuSkeleton/InverseCoordinateDeterminant.lean`; `HmuSkeleton/InverseCoordinatePair.lean`; `HmuSkeleton/PerturbationCases.lean` | Lean uses the denominator of `1/(V^2*delta)` for `coordinateDen`; multiplication by `-sigma=±1` preserves the reduced denominator, so it equals the paper's `den(zeta)`. Signed exact arithmetic is separated from real logarithmic estimates. |
| A06 | Section 4, equations (4.10)–(4.17), lines 358–429 | `HmuSkeleton/PerturbationCases.lean`; `HmuSkeleton/ReflectedLegendreGap.lean` | The reflected witness is constructed from the selected new gap via the unimodular inverse pair and `r=zeta-h/k`. Its nonzero reverse-point error and strict `1/8` cutoff produce the same actual local gap used in the denominator and endpoint estimates. No global reflected-gap callback is assumed. |
| A07 | Section 4, equation (4.12), lines 369–380: `K>=1` implies `q >= (2/3)VW` | `HmuSkeleton/SelectedGapTail.lean` | The same location bound is proved directly from rational separation and the selected branch's error `< |delta|/2`, without routing it through `K`. The conclusion remains `a >= L-M-log(3/2)`. |
| A08 | Section 5, lines 456–515, especially equations (5.4)–(5.6): irrationality and lower bound use reduced denominator `V_n` | `Arithmetic/Definitions.lean`; `Arithmetic/RawScale.lean`; `Arithmetic/RawTailAdapter.lean`; `Arithmetic/RawRationalSeparation.lean`; `Arithmetic/TruncationLower.lean`; `Solution.lean` | Irrationality and the full lower exponent use unreduced integer denominator `Q_n=N^u_n D_n`, `Q_n→∞`, eventually nonzero error, and `Q_n*|x-x_n|→0`. This avoids valuation cancellation in that branch. It includes infinite limsup. Reduced-denominator asymptotics are still proved and used for the finite upper bound. |
| A09 | Section 5, equations (5.3)–(5.4), lines 466–486 | `Arithmetic/ValuationCore.lean`; `HmuSkeleton/ReducedScale.lean` | Signed integer/rational valuations, a unique least-valuation summand, finite prime support, and gcd logarithmic cost are explicit separate lemmas. The resulting reduced scale `M_n/t_n→1` is the same. The valuation proof uses the sufficient divisibility threshold `p^(u_n-u_(n-1))`, although the full `v_p(N)` factor is available. No exact gcd value or coefficient positivity is required. |
| A10 | Section 5, equations (5.7), (5.9)–(5.10), lines 516–550 | `HmuSkeleton/CoordinateSmall.lean`; `HmuSkeleton/StepScales.lean`; `HmuSkeleton/SeriesProfileClosure.lean`; `HmuSkeleton/ReducedScaleClosure.lean` | Finite-limsup shifted-height normalization, positive-part ratio deficit, coordinate smallness, and one-sided scale tails are packaged separately on the same truncations. Finite `F` is required only in the finite upper branch. |
| A11 | Section 6, equations (6.1)–(6.5), lines 556–620 | `HmuSkeleton/UniformProfile.lean`; `HmuSkeleton/SelectedProfileClosure.lean` | Generic scalar induction is instantiated with actual truncation gaps. `profileTolerance` explicitly takes maxima of normalized one-sided costs rather than choosing an unnamed sequence. The same constants 16 and 32, old-gap membership, terminal bound, and `A+C(n-n0)` uniformity are retained. `n0,A` are fixed after `kappa`, before an individual gap is considered. |
| A12 | Section 7, equations (7.1)–(7.6), lines 624–683 | `HmuSkeleton/ScalarTransfer.lean`; `HmuSkeleton/SelectedProfileClosure.lean`; `HmuSkeleton/SeriesProfileClosure.lean` | The least selected offset is `Nat.find`; the actual index is `n0+offset`. Lean proves the bound by an explicit multiple of `log(a+b+2)` and an additive constant, and composes eventual denominator/tail estimates through the cofinal selected index. The resulting bootstrap is the paper's logarithmic error argument. In denominator variables this is `log(log q+log qPlus+2)`, not `log(q+qPlus+2)`. |
| A13 | Section 7, lines 643–647: reduced scale and logarithmic tail give `V_n>=exp(t_n/2)` and tail `<=exp(-t_n)` | `HmuSkeleton/SeriesProfileClosure.lean` | The denominator estimate still comes from reduced scale. The exponential tail bound is obtained from the already proved raw-Q separation limit and `Q_n>=exp(t_n)`. Same actual truncation and same inequalities, different dependency. |
| A14 | Section 8, equation (8.1), lines 687–708 | `CF/Irrational.lean`; `Exponent/Bridge.lean`; `Exponent/CF.lean`; `Exponent/Formula.lean` | Lean discards the first two CF indices, ensuring denominators at least 2 and positive logarithms. Finite-prefix omission leaves the limsup unchanged. Exact supplied-denominator/reduced-approximant bridges and finite EReal translation implement the same CF exponent identity, also at infinity. |
| A15 | Sections 5–8, lines 513–520,554–555,709–713 | `HmuSkeleton/TopBranch.lean`; `HmuSkeleton/FinalAssembly.lean`; `Solution.lean` | The infinity branch is split before extracting a real `F`; the finite branch obtains epsilon upper tails rather than assuming ratio convergence. Lean closes with epsilon inequalities, rather than writing “let kappa decrease to F-2.” Same finite/infinite conclusion. |

## B — changed intermediate constants or parameters

| ID | Paper location and bound | Lean bound | Quantitative effect and reason |
|---|---|---|---|
| B01 | Section 5, equation (5.8), lines 533–537: `B_n <= |alpha_(n+1)| D_n^2 N^((2u_n-u_(n+1))_+)` | `HmuSkeleton/CoordinateBound.lean` proves the bound with `|alpha_(n+1)|^2`, then with `H(coeff_(n+1))^2` | Lean multiplies numerator and denominator by the signed next coefficient numerator, producing its square in the natural denominator before applying `den_scaled_powers_le` (`CoordinateBound.lean`). This is a weaker pointwise bound. It adds at most one further `log H(coeff_(n+1))` to the paper's logarithmic majorant. Finite `F` gives `log H(coeff_(n+1))=o(u_n)`, so `E_n=o(M_n)` and the final exponent are unchanged. It is not a correction of a false printed bound. |
| B02 | Section 4, equation (4.5), lines 316–320: `g <= log 12 + 2log B <= 2E` | `HmuSkeleton/PerturbationCases.lean` exports only `g <= 2E=log 16+2log B` | The short-branch cutoff remains exactly `qPlus/q<=12B^2`. Its proof relaxes that bound to `qPlus <= (4B)^2*q` before taking logarithms. The exported bound drops the sharper first link, an additive relaxation of `log(4/3)`. The profile induction already uses only `2E`; none of its constants or the main result changes. |
| B03 | Section 5, lines 493–503: choose arbitrary `0<tau<log N*(rho-1)/(rho+1)` for an exponentially small relative tail | `Arithmetic/ConcreteTail.lean` fixes eventual ratio `rho=3/2`, coefficient allowance `log N/20`, and eventually adjacent-term contraction `1/4`; `Arithmetic/GeometricTail.lean` uses the constants `1/2,3/2` | These convenient fixed constants suffice for eventual nonzero signed tails. A quarter-contraction bounds the relative remainder by `1/3`; the exported bounds are relaxed to `1/2` and `3/2`. See D02 for the stronger asymptotic statement not exported. No new assumption. |
| B04 | Section 6, lines 611–620: the available tolerance gives `(2+2*kappa)*eta <= kappa^2/16` | `HmuSkeleton/UniformProfile.lean`, `profile_step`, records the weaker sufficient bound `<= kappa^2/4` in the large reflected branch | The unchanged hypothesis `32*(1+kappa)*eta <= kappa^2` already implies the sharper printed bound. The weaker intermediate record suffices to prevent an increase of the profile defect; no public tolerance constant or final result changes. |
| B05 | Section 7, lines 673–677: a contradiction argument rules out `b >= 2*(1+kappa)*a` eventually | `HmuSkeleton/ScalarTransfer.lean` obtains the convenient eventual bound `b <= (2*kappa+3)*a` | Both bounds yield `b=O(a)`, which makes the accumulated `log(a+b+2)` loss negligible relative to `a`. The limiting gap bound and main exponent remain identical. |

The important paper constants **6**, **12B²**, **log(4B)**, **log(3/2)**, **log 2**, the transfer threshold **4(a+b+1)**, and the finite-profile tolerance constants **16**, **32** otherwise agree with the Lean construction. The unchanged denominator comparisons have factors `2B`; the shifted-endpoint error remains `E=log(4B)`.

## C — printed-paper defects

**None identified in this comparison.** In particular, the following three false auxiliary contracts were artifacts of the formalization plan, not statements printed in the published paper. Their rejection does not by itself identify a defect in the paper or a failure of its main theorem. Their replacement is the valid paper-specific construction described in A08–A13.

### False selector-only transfer contract: not printed

The rejected interface permitted `selector <= K*log(q+qPlus+2)+D` and tried to deduce a normalized gap limsup from that selector/profile package. A counterexample takes `q_n=exp(n)`, `qPlus_n=exp(2n)`, `selector_n=n`, `Gap(m,a,g): g<=m`, `kappa=A=D=n0=0`, and `C=K=1`. With transferred denominator `s=qPlus/6`, its premises hold, but the normalized gap is 1, not at most 0.

The paper instead proves (7.2), `n=O(log(a+b+2))`, at lines 634–639, with `a=log q,b=log qPlus`. It then proves (7.5) and performs the necessary bootstrap `b=O(a)` at lines 665–679 before concluding (7.6). It also explicitly proves the actual rational Legendre witness, using both denominator and tail estimates at lines 643–664. The false generic theorem has a different logarithmic scale and omits essential structure used in the paper.

Current Lean: `HmuSkeleton/CFProfileTransfer.lean` exposes only the corrected eventual-profile implication; `ScalarTransfer.lean` and `SelectedProfileClosure.lean` supply the genuine paper-scale transfer. Thus no false selector-only contract is being credited as a paper theorem.

### Original raw-scale log generalization without ratio/cumulative height: not printed

The false generalization tried to infer `log Q_n/(u_n log N)→1` from positive strictly increasing `u_n` and pointwise `log H(c_n)/u_n→0`, without geometric ratio growth or accumulated denominator/height control.

A corrected explicit counterexample is

`N=2`, `u_n=n+1`, `c_n=1/2^floor(sqrt(n+1))`.

Then `log H(c_n)/u_n = log(2)*floor(sqrt(n+1))/(n+1)→0`, but

`log Q_n/(u_n log 2) = 1 + [sum_(j=0)^n floor(sqrt(j+1))]/(n+1)`,

which diverges to infinity, with the additional term asymptotic to `(2/3)*sqrt(n+1)`. For `n=m^2-1`, the sum is exactly `m(m-1)(4m+1)/6+m`. This sequence has ratio tending to 1 and violates the main theorem's lower-ratio assumption.

The paper explicitly invokes a fixed eventual ratio `rho>1` at lines 449–451, then proves cumulative height (5.2) at lines 452–460 before claiming `log D_n=o(u_n)` at lines 462–466. The reduced-scale assertion (5.4) retains the valuation/gcd argument as well. The missing implication is never printed under the weakened premises.

Current Lean makes the cumulative input explicit in `Arithmetic/RawScale.lean` and derives it from the full paper assumptions before use (`Arithmetic/TruncationLower.lean`; `HmuSkeleton/ReducedScale.lean`). The standalone historical helper `Paper4/RawScaleCorrected.lean` is outside the main proof dependency closure and supplies no additional main hypothesis; it is not part of this package.

### Global reflected `ReflectedBranchBoundary.actual_gap`: not printed

The rejected boundary demanded perturbation-scale endpoints/location for **every** gap of `reversePoint(alpha)`. For `alpha=1/2` and `delta=1/(4T)` with integer `T>=1`, one has `reversePoint(alpha)=1/2`, `M=log 2`, `L=log(4T)`, `B=1`, `E=log 4`, and `c0=log(3/2)`. Its reverse-point gap `1→2` has left endpoint `a=0`, whereas the demanded location inequality would be `0>=log(4T/3)>0`. Thus the global boundary is false even though `W=T>=1`.

The paper's universal reversal lemma is instead centered at **M**, with error `log 2`, and has no perturbation-scale location condition: Lemma 3.1, lines 242–250, equation (3.1). Its reflected perturbation branch has a different scope: after selecting a gap of `alpha+delta`, it assumes the near-error branch `epsilon<Delta/2` (lines 348–349) and the large-ratio branch `qPlus/q>12B^2` (lines 394–402). Only then does it construct `r=zeta-h/k`, prove the cutoff (4.15), recognize its actual gap, and combine the scaled endpoints with reversal (lines 382–429). The location bound (4.7) comes from this selected branch's (4.11)–(4.12). No universal statement assigning that location to arbitrary reverse-point gaps is printed.

Current Lean follows this branch-local construction (`PerturbationCases.lean`). `SelectedGapTail.lean` explicitly retains the necessary near-error premise. The false global boundary is not a theorem used by the main proof. The historical diagnostic modules are outside the shipped proof dependency closure and are not part of this package.

## D — intermediate export reductions and ancillary scope

| ID | Paper statement/location | Current Lean scope | Main theorem effect |
|---|---|---|---|
| D01 | Lemma 4.1 inherited/central alternatives, lines 306–315: inherited convergent is the same `p/q`, with actual next denominator `U>=qPlus/6`; central alternative says `p/q=alpha` | `PerturbationGapCases` at `HmuSkeleton/PerturbationCases.lean` exports only actual old-gap membership at the same **denominator logarithm** and its width inequality, or `a=M` and the central width inequality. The branch dispatcher proves/uses the stronger rational-value facts internally, but the public relational five-way conclusion forgets numerator provenance. | Intermediate conclusion is deliberately projected to the gap data needed by induction. No additional hypothesis or weaker final theorem. This exported proposition is not the complete printed Lemma 4.1. |
| D02 | Equation (5.5), lines 489–503: signed relative tail `tail=first omitted term*(1+o(1))` and a logarithmic tail limit | `Arithmetic/TailTwoSided.lean` exports eventual absolute-value bounds between one half and three halves of the first omitted term; `EventualTailNonzeroConcrete.lean`/`HneGlue.lean` export nonzero tails. `RawTailAdapter.lean` and `TruncationLower.lean` prove the needed raw-Q and approximation thresholds directly. A standalone signed relative-limit statement, and a standalone exact normalized log-tail limit matching (5.5), are not exported in this snapshot. | Sufficient estimates for irrationality, the entire lower bound, and Section 7 are proved. Stronger printed auxiliary asymptotics are outside the exported scope. |
| D03 | Equation (5.10), lines 545–549 includes `limsup L_n/M_n=F` | `HmuSkeleton/StepScales.lean` and `SeriesProfileArithmetic` (`SeriesProfileClosure.lean`) export step asymptotics and the one-sided epsilon bounds consumed by the upper proof. A separate EReal equality for `limsup L_n/M_n` is not exported. | The finite upper proof needs only those bounds; the lower bound is proved independently by truncation thresholds. This is a narrower intermediate export, not a narrowed main theorem. |
| D04 | Section 9, lines 717–802: linear-height sharpness, positive-weight rational and Liouville constructions, a sufficient-but-not-necessary example, and scope discussion | The formalization proves the main theorem and its proof infrastructure; it does not formalize these ancillary constructions or the optimality assertion. | No restriction of Theorem 1. The formalization does not claim that all results in the paper have been formalized. |
| D05 | Introduction, lines 78–178, and literature/scope comparison at 793–802: examples and deductions from Bugeaud, BKS, DKS, Amou–Bugeaud, earlier binary work | These comparison theorems, citation claims, illustrative specializations, rational-prefix invariance used only in that discussion, and historical assertions are not separate Lean targets. | They are not premises of the Lean proof of the main theorem. Bibliographic verification is a separate task. |

**Main-theorem class D: none.** No coefficient positivity, extra divisibility, eventual ratio at least 2, finite limsup, bounded height, or auxiliary profile/transfer assumption is added to `Paper4.theorem_1`.

## Retained mathematical coverage and audit limits

Every proof section on the path to the main theorem has been compared with the actual source: canonical CF facts (Section 2), reversal (3), selected five-way perturbation and local reflection (4), signed arithmetic and denominator scales (5), uniform finite profiles (6), selected actual-gap transfer (7), and finite/infinite exponent closure (8). The proof retains the paper's original truncations and actual canonical continued fractions; it does not substitute arbitrary abstract profiles at the final application. Sections 1 and 9 contain the additional unformalized material listed above.

This is a mathematical/source comparison, supported by frozen input hashes, statement-identity checks, and exact rational counterexample calculations. It introduces no paper edits. The proof simplifications retain the public statement interfaces. Build success, absence of transitive admissions, the three standard kernel axioms, comparator/nanoda acceptance, and resource measurements are recorded in the saved outputs under `verification/`. Comments or `#print axioms` commands in source are not those receipts. The saved outputs are bound to the tested snapshot recorded in `verification/source-sha256.txt`; current package hashes are recorded in the manifests.

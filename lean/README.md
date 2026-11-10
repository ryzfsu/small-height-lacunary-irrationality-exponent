# Lean formalization

Ruiyi Zhang · Independent Researcher · ORCID
[0009-0003-3110-8524](https://orcid.org/0009-0003-3110-8524)

This package formalizes Theorem 1 of *The irrationality exponent of small-height
lacunary series*. The concept DOI is [10.5281/zenodo.24056144](https://doi.org/10.5281/zenodo.24056144);
the published version used here is Zenodo record [10.5281/zenodo.24056145](https://doi.org/10.5281/zenodo.24056145).
All commands below run from the package root.

Saved verification outputs are kept separately from the proof sources.
The saved checks refer to the exact tested snapshot recorded in
`verification/source-sha256.txt`; `SOURCE-SHA256SUMS` covers the current package
source and metadata. The Lean source entries are unchanged by the wording edits.

## Statement

`Solution.lean` supplies `Paper4.theorem_1`, whose statement inside the
`Paper4` namespace is:

```lean
theorem theorem_1
    (N : ℕ) (hN : 2 ≤ N)
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ j, coeff j ≠ 0)
    (hheight : Tendsto
      (fun j => Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) :
    Summable (fun j => |term N u coeff j|) ∧
      Irrational (∑' j, term N u coeff j) ∧
      (2 : EReal) ≤ irrationalityExponent (∑' j, term N u coeff j) ∧
      irrationalityExponent (∑' j, term N u coeff j) =
        Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop
```

Lean index `j : ℕ` represents paper index `j + 1`.
`rationalHeight q` is `max q.num.natAbs q.den` in the canonical reduced rational
form, and `term N u coeff j` is the real number `coeff j / N^(u j)`.
`irrationalityExponent` is an `EReal` supremum of exponents admitting strict
approximations at unbounded positive denominators; supplied fractions need
not be reduced. The ratio is cast to `EReal` before taking the limsup.

The height limit expresses `log H(coeff j) = o(u j)`. The epsilon-tail
hypothesis expresses `liminf u (j+1) / u j ≥ 2`; it does not require every
ratio to be at least 2. Coefficients may have either sign. The conclusion
includes absolute summability, irrationality, and the exact exponent,
including the value `⊤` for an infinite limsup. It adds no hypothesis to the
published main theorem.

## Paper-to-module map

Paths are relative to the package root. Declarations are in `Paper4` unless
qualified otherwise; most profile declarations are in `Paper4.HmuSkeleton`,
and the list-continuant algebra is in `Lacunary.Reversal`. The historical
namespace `HmuSkeleton` is retained in the proof development.

| Published section or lemma | Main source modules | Principal declarations |
|---|---|---|
| §1, height, series and approximation definitions | `Paper4/Statement.lean` | `rationalHeight`, `term`, `exponentAdmissible`, `irrationalityExponent`, `exponentRatio` |
| §1, Theorem 1 | `Challenge.lean`; `Solution.lean` | `Paper4.theorem_1` |
| §2, actual continued fractions, canonical rationals and error bounds | `Paper4/CF/Bridge.lean`; `Paper4/CF/Canonical.lean`; `Paper4/CF/Gap.lean` | `Lacunary.CFBridge.error_lower`, `Lacunary.CFBridge.error_upper`, `CFGap`, `cfGap_bounds`, `cfGap_legendre`, `rational_gap_finite`, `rational_gap_range` |
| §2, infinite convergents and unbounded denominators | `Paper4/CF/Irrational.lean` | `cfP`, `cfQ`, `cfQ_ge_two`, `cfQ_tendsto`, `cf_legendre_eventually` |
| §3, continuant splitting and the final-one merge | `Paper4/CF/Continuants.lean` | `continuant_append`, `canonicalReverseWord`, `finite_reversal_profile` |
| §3, Lemma 3.1 on the actual rational expansion | `Paper4/HmuSkeleton/ReversalBridge.lean` | `actual_prefix_continuant_den`, `reversePoint_eq_canonical_reverse_value`, `actual_reversal_profile` |
| §4, inverse coordinates and local reflection estimates | `Paper4/HmuSkeleton/InverseCoordinateDeterminant.lean`; `Paper4/HmuSkeleton/InverseCoordinatePair.lean`; `Paper4/HmuSkeleton/ReflectedLegendreGap.lean`; `Paper4/HmuSkeleton/ReflectedEndpointScale.lean` | `inverse_coordinate_determinant`, `inverse_coordinate_pair`, `reflected_legendre_gap_witness`, `reflected_endpoint_scale` |
| §4, Lemma 4.1: bounded, inherited, central, short and reflected gap alternatives | `Paper4/HmuSkeleton/PerturbationCases.lean` | `PerturbationGapCases`, `five_way_perturbation`, `rational_perturbation`, `reflected_r_choice_data`, `perturbation_cases_to_profile_transition` |
| §5, truncations, integerization and accumulated heights | `Paper4/Arithmetic/Definitions.lean`; `Paper4/Arithmetic/RawScale.lean`; `Paper4/Arithmetic/RawTailAdapter.lean` | `trunc`, `D`, `Q`, `truncNumerator`, `trunc_integerized`, `log_Q_div_t_tendsto_one_of_height_sum`, `tendsto_Q_atTop`, `master_raw_tail_mul_Q_tendsto` |
| §5, absolute convergence and signed nonzero tails | `Paper4/Arithmetic/Summability.lean`; `Paper4/Arithmetic/ConcreteTail.lean`; `Paper4/Arithmetic/GeometricTail.lean`; `Paper4/Arithmetic/TailTwoSided.lean`; `Paper4/Arithmetic/EventualTailNonzeroConcrete.lean`; `Paper4/Arithmetic/HneGlue.lean` | `summable_term_abs`, `tail_two_sided_concrete`, `eventual_x_ne_trunc_of_signed_tail` |
| §5, irrationality and the full truncation lower bound | `Paper4/Arithmetic/RawRationalSeparation.lean`; `Paper4/Arithmetic/TruncationLower.lean` | `raw_rational_separation`, `irrational_of_tendsto_mul_error_of_ratSep`, `raw_truncation_lower_of_limsup` |
| §5, reduced denominators and finite-limsup scale costs | `Paper4/Arithmetic/ValuationCore.lean`; `Paper4/HmuSkeleton/ReducedScale.lean`; `Paper4/HmuSkeleton/CoordinateBound.lean`; `Paper4/HmuSkeleton/CoordinateSmall.lean`; `Paper4/HmuSkeleton/StepScales.lean`; `Paper4/HmuSkeleton/ReducedScaleClosure.lean` | `reduced_scale_actual`, `coordinate_den_trunc_delta_le`, `coordinate_small_of_bound_and_reduced_scale`, `step_bounds_of_reduced_scale` |
| §6, uniform finite profile induction | `Paper4/HmuSkeleton/UniformProfile.lean`; `Paper4/HmuSkeleton/SelectedProfileClosure.lean` | `profile_step`, `profile_all_stages`, `uniform_finite_profile`, `finite_profiles_of_rational_perturbation` |
| §7, least selected truncation, actual gap transfer and logarithmic bootstrap | `Paper4/HmuSkeleton/ScalarTransfer.lean`; `Paper4/HmuSkeleton/SelectedProfileClosure.lean`; `Paper4/HmuSkeleton/SeriesProfileClosure.lean`; `Paper4/HmuSkeleton/FinalProfile.lean` | `selectedOffset`, `selectedOffset_paper_bound`, `selected_rational_gap_transfer`, `actual_profile_of_finite_profiles`, `series_cf_profile_of_arithmetic`, `actual_cf_profile_of_paper` |
| §8, continued-fraction formula for the exponent | `Paper4/Exponent/Bridge.lean`; `Paper4/Exponent/CF.lean`; `Paper4/Exponent/Formula.lean`; `Paper4/Exponent/FiniteClosure.lean` | `irrationalityExponent_eq_liouville_sSup`, `irrationalityExponent_cf_formula`, `irrationalityExponent_le_of_cf_gap_profile` |
| §8, finite and infinite branches and final assembly | `Paper4/HmuSkeleton/TopBranch.lean`; `Paper4/HmuSkeleton/FinalAssembly.lean`; `Solution.lean` | `hmu_top_branch`, `hmu_of_R_packages`, `two_le_exponentRatio_limsup`, `Paper4.theorem_1` |
| §9, height sharpness and scope | Not formalized | The illustrative sharpness constructions and literature discussion are outside the formalized main theorem. |

The irrationality and truncation lower-bound route uses a common denominator
`Q`, without requiring the reduced-denominator asymptotics. The finite upper
bound uses the latter together with actual continued-fraction gaps. The
infinite-limsup branch closes from truncation approximations.

`Challenge.lean` is the small comparison statement and imports Mathlib only;
it inlines the five fixed definitions used by the theorem. Its intentional
placeholder proof is not part of the solution proof. `Solution.lean` proves
the same proposition without importing `Challenge.lean`. The comparator
configuration names `Paper4.theorem_1`; its `definition_names` list is empty
because those definitions are already fully specified in the challenge.

## Build and verification

The toolchain is `leanprover/lean4:v4.35.0-rc4`. The committed
`lake-manifest.json` pins Mathlib to
`1f414401f69059aa7eead47b53ee40bd38455eeb`. The package is `lacunaryLeanPalomar` and its default
library is `Lacunary`.

With Elan and Git installed, from the package root:

```bash
lake exe cache get
lake build
lake env lean SolutionAxioms.lean
```

The default library includes the `Paper4` submodules, `Challenge` and
`Solution`. `SolutionAxioms.lean` imports `Solution` and prints the main
statement's kernel dependencies. The expected output is:

```text
'Paper4.theorem_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The saved output is in `verification/axioms.txt`. The deliberate challenge
placeholder is separate from the proof closure.

The independent nanoda kernel accepts the complete proof (30,847 declarations), and the Lean kernel accepts it through the comparator tool; the receipts are in `verification/`.
The saved comparator runs used `--inadvisably-no-sandbox`; acceptance under the default sandbox is not claimed.
The standalone Lean-kernel check uses the upstream development wrapper with
nanoda disabled only in its runtime configuration. The rc4 check runs both
kernels in sequence. The strict standalone nanoda check permits only the three
standard axioms and uses four threads.

Lean 4.35.0-rc4 includes `lake comparator`:

```bash
lake comparator --config comparator.json --inadvisably-no-sandbox
sha256sum -c SHA256SUMS
```

Comparator reads `comparator.json` and compares the challenge with the
solution. Non-hole constants in the challenge are compared by value.
`verification/README.txt` describes the saved outputs and their scope.
`SOURCE-SHA256SUMS` covers the source files; `SHA256SUMS` covers all package
files except itself.

## Differences and scope

`RELEASE_NOTES.md` compares the formalization with the exact published v1
source. The main theorem has the same hypotheses and conclusions, expressed
using zero-based indexing, filters and extended real values. Several
intermediate propositions use different constructions or bounds. These include a squared
coefficient-numerator cost in the coordinate-denominator bound, the `2E`
short-gap bound without the paper's sharper sub-bound, and fixed tail
parameters. These changes do not weaken the main conclusion. The gap
classification is the form needed by the induction; it is not a claim that
every auxiliary assertion in the printed Lemma 4.1 is exported verbatim.
RELEASE_NOTES.md gives the itemized comparison with the paper. Section 9 examples
and introductory literature claims are not certified by the Lean theorem.

The code is licensed under Apache-2.0; see `LICENSE` and
`LICENSES/Apache-2.0.txt`. Pinned dependencies retain their own licenses.

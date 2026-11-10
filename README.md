# The irrationality exponent of small-height lacunary series

Ruiyi Zhang

DOI: [10.5281/zenodo.24056144](https://doi.org/10.5281/zenodo.24056144)

## Main result

Let N >= 2 be an integer, let u_1 < u_2 < ... be positive integers with liminf u_{j+1}/u_j >= 2, and let
(lambda_j) be nonzero rational numbers with log H(lambda_j) = o(u_j), where H(a/b) = max(|a|, b) for a/b in lowest
terms with b > 0. Then

    x = sum_{j >= 1} lambda_j N^(-u_j)

is irrational and its irrationality exponent is mu(x) = limsup u_{j+1}/u_j, finite or infinite. The coefficients may
have arbitrary signs, and the height condition cannot be replaced by log H(lambda_j) <= C u_j for any fixed C > 0.

## Method

The proof compares logarithmic gaps between the continued-fraction denominators of consecutive truncations. A
perturbation lemma places each gap of the next truncation in at least one of five classes (bounded, inherited,
central, short, reflected), each with an explicit error. Reflection moves a large gap far enough to the right to give a
uniform bound at the boundary liminf u_{j+1}/u_j = 2, including ratios that tend to 2 from below.

## Contents

- `main.pdf`: the manuscript (12 pages).
- `source/main.tex`: LaTeX source (amsart; no other files are needed).
- `lean/`: Lean 4 formalization of the main theorem (see below and `lean/README.md`), with its own `SHA256SUMS`.
- `SHA256SUMS`: SHA-256 checksums of `main.pdf`, `README.md` and `source/main.tex`.

## Build

    cd source
    pdflatex main.tex && pdflatex main.tex && pdflatex main.tex

Built with TeX Live 2026.

## Lean formalization

`lean/` contains a Lean 4 formalization of the main theorem (Lean 4.35.0-rc4,
Mathlib `1f414401`). The formal statement is

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

The proof depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. The independent nanoda kernel accepts the complete proof
(30,847 declarations), and the Lean kernel accepts it through the comparator
tool; the receipts are in `lean/verification/`. The saved comparator runs used
`--inadvisably-no-sandbox`; the sandboxed Palomar verification run
([42737481615](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/42737481615))
also accepted the proof.

The same Lean package is the root of the `palomar` branch, commit
[`a1208b6d1c06fd63e1daf90c1342c23a62267742`](https://github.com/ryzfsu/small-height-lacunary-irrationality-exponent/tree/a1208b6d1c06fd63e1daf90c1342c23a62267742),
whose tree is identical to `lean/`. That commit is registered in the Palomar registry as
[PALOMAR-2026-11-10-000002](https://palomar-registry.org/entry?id=PALOMAR-2026-11-10-000002).

The formalization follows the structure of the paper:

| part of the proof | Lean modules |
|---|---|
| statement and main theorem | `Paper4/Statement.lean`, `Challenge.lean`, `Solution.lean` |
| rational and irrational continued fractions | `Paper4/CF/` |
| reversal, perturbation, finite profiles and transfer | `Paper4/HmuSkeleton/` |
| heights, denominators, tails and truncation approximations | `Paper4/Arithmetic/` |
| continued-fraction formula for the exponent | `Paper4/Exponent/` |

Some intermediate constructions and bounds differ from the paper;
`lean/RELEASE_NOTES.md` lists them and explains their effect on the main theorem.
The formalized theorem retains the full signed coefficient hypotheses and
includes the finite and infinite exponent cases. Section 9 examples and the
introductory literature discussion are outside its scope. `lean/README.md`
explains how to build and check the proof.

## Citation

Ruiyi Zhang, *The irrationality exponent of small-height lacunary series*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.24056144

```bibtex
@misc{zhang2026smallheight,
  author    = {Zhang, Ruiyi},
  title     = {The irrationality exponent of small-height lacunary series},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.24056144},
  url       = {https://doi.org/10.5281/zenodo.24056144}
}
```

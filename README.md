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
- `SHA256SUMS`: SHA-256 checksums of the files above.

## Build

    cd source
    pdflatex main.tex && pdflatex main.tex && pdflatex main.tex

Built with TeX Live 2026.

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

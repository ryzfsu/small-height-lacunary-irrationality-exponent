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
`--inadvisably-no-sandbox`; acceptance under the default sandbox is not claimed.

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

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/-- The paper's height on a reduced rational, expressed using `Rat`'s canonical form. -/
def rationalHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

/-- The `j`th summand, with the paper's positive integer exponent. -/
noncomputable def term (N : ℕ) (u : ℕ → ℕ) (coeff : ℕ → ℚ) (j : ℕ) : ℝ :=
  (coeff j : ℝ) / (N : ℝ) ^ (u j)

/-- The paper's approximation condition for a real exponent, indexed by unbounded
positive denominators. This is equivalent to infinitely many numerator-denominator
pairs because a fixed denominator admits only finitely many numerators in the interval. -/
def exponentAdmissible (x : ℝ) (ν : ℝ) : Prop :=
  ∃ᶠ q : ℕ in atTop, ∃ p : ℤ, 0 < q ∧
    |x - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)

/-- Extended-real supremum, so an unbounded set of admissible exponents has value `⊤`. -/
noncomputable def irrationalityExponent (x : ℝ) : EReal :=
  sSup ((fun ν : ℝ => (ν : EReal)) '' {ν | exponentAdmissible x ν})

/-- The ratio of consecutive exponents, with index `j` representing the paper's index `j + 1`. -/
noncomputable def exponentRatio (u : ℕ → ℕ) (j : ℕ) : ℝ :=
  (u (j + 1) : ℝ) / (u j : ℝ)

/-- Theorem 1 of *The irrationality exponent of small-height lacunary series*.
Sequence index `j : ℕ` represents the paper's index `j + 1`. -/
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
        Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop := by
  sorry

end Paper4

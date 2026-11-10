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

end Paper4

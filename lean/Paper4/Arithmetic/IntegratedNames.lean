/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.TailTwoSided
public import Paper4.Arithmetic.EventualTailNonzeroConcrete

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

theorem tail_two_sided
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * |term N u coeff (n + 1)| ≤
          |(∑' j, term N u coeff j) - (trunc N u coeff n : ℝ)| ∧
      |(∑' j, term N u coeff j) - (trunc N u coeff n : ℝ)| ≤
          (3 / 2 : ℝ) * |term N u coeff (n + 1)| :=
  tail_two_sided_concrete N hN u hu_pos hu_strict coeff hcoeff hheight hgap

theorem eventual_tail_nonzero
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      (∑' j, term N u coeff j) ≠ (trunc N u coeff n : ℝ) :=
  eventual_tail_nonzero_concrete N hN u hu_pos hu_strict coeff hcoeff hheight hgap

#print axioms tail_two_sided
#print axioms eventual_tail_nonzero

end Paper4

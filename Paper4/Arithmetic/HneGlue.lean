/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.IntegratedNames
public import Paper4.Arithmetic.Definitions

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/- The Section-5 hne input is exactly the eventual signed-tail nonvanishing
   statement, with the public `x` abbreviation unfolded. -/
theorem eventual_x_ne_trunc_of_signed_tail
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      x N u coeff ≠ (trunc N u coeff n : ℝ) := by
  simpa only [x] using
    (eventual_tail_nonzero N hN u hu_pos hu_strict coeff hcoeff hheight hgap)

/- Import-graph-neutral form of the same adapter.  The sole upstream obligation
   is the concrete signed-tail nonzero interface displayed here. -/
theorem eventual_x_ne_trunc_of_tail_interface
    (tail_nonzero :
      ∀ (N : ℕ) (_hN : 2 ≤ N) (u : ℕ → ℕ),
        (∀ n, 0 < u n) → StrictMono u →
        ∀ (coeff : ℕ → ℚ), (∀ n, coeff n ≠ 0) →
        Tendsto
          (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
          atTop (𝓝 0) →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          2 - ε ≤ exponentRatio u n) →
        ∀ᶠ n : ℕ in atTop,
          (∑' j, term N u coeff j) ≠ (trunc N u coeff n : ℝ))
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      x N u coeff ≠ (trunc N u coeff n : ℝ) := by
  simpa only [x] using
    (tail_nonzero N hN u hu_pos hu_strict coeff hcoeff hheight hgap)

#print axioms eventual_x_ne_trunc_of_signed_tail
#print axioms eventual_x_ne_trunc_of_tail_interface

end Paper4

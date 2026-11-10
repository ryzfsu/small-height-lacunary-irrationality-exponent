/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.TailTwoSided
public import Paper4.Arithmetic.Definitions
public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

theorem eventual_tail_nonzero_concrete
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      (∑' j, term N u coeff j) ≠ (trunc N u coeff n : ℝ) := by
  have htail := tail_two_sided_concrete N hN u hu_pos hu_strict
    coeff hcoeff hheight hgap
  have hterm : ∀ j : ℕ, term N u coeff j ≠ 0 := by
    intro j
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (show N ≠ 0 by omega)
    have hc : (coeff j : ℝ) ≠ 0 := by
      exact_mod_cast (hcoeff j)
    simp [term, hc, hN0]
  filter_upwards [htail] with n hn
  intro heq
  have hpos : 0 < |term N u coeff (n + 1)| :=
    abs_pos.mpr (hterm (n + 1))
  have hlo := hn.1
  simp only [heq, sub_self, abs_zero] at hlo
  nlinarith

end Paper4

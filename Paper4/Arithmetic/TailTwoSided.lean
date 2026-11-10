/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.ConcreteTail
public import Paper4.Arithmetic.GeometricTail
public import Paper4.Arithmetic.Definitions
public import Paper4.Arithmetic.Summability
public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

theorem tail_two_sided_concrete
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
          (3 / 2 : ℝ) * |term N u coeff (n + 1)| := by
  have hsum := summable_term_abs N hN u hu_pos hu_strict coeff hcoeff hheight hgap
  have hratio := term_ratio_quarter_eventually N hN u hu_pos hu_strict
    coeff hcoeff hheight hgap
  have hgeom := geometric_tail_two_sided
    (f := fun j : ℕ => term N u coeff j) hsum hratio
  filter_upwards [hgeom] with n hn
  simpa only [trunc_cast] using hn

end Paper4

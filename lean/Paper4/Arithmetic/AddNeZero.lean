/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Mathlib

@[expose] public section

namespace Paper4

theorem add_ne_zero_of_abs_lt {a b : ℝ} (h : |b| < |a|) : a + b ≠ 0 := by
  intro hz
  have ha : a = -b := by
    linarith only [hz]
  rw [ha, abs_neg] at h
  exact (lt_irrefl _) h

end Paper4

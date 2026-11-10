/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Mathlib

@[expose] public section

namespace Paper4

theorem one_div_mul_le_abs_sub_div
    {A C : ℤ} {B D : ℕ} (hB : 0 < B) (hD : 0 < D)
    (hcross : A * (D : ℤ) - C * (B : ℤ) ≠ 0) :
    1 / ((B : ℝ) * (D : ℝ)) ≤
      |(A : ℝ) / (B : ℝ) - (C : ℝ) / (D : ℝ)| := by
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hden : (0 : ℝ) < (B : ℝ) * (D : ℝ) := mul_pos hBr hDr
  have hnum : (1 : ℝ) ≤
      |(A : ℝ) * (D : ℝ) - (C : ℝ) * (B : ℝ)| := by
    have hpos : (0 : ℤ) < |A * (D : ℤ) - C * (B : ℤ)| :=
      abs_pos.mpr hcross
    have hreal : (1 : ℝ) ≤
        ((|A * (D : ℤ) - C * (B : ℤ)| : ℤ) : ℝ) :=
      Int.cast_one_le_of_pos hpos
    simpa only [Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hreal
  rw [div_sub_div (A : ℝ) (C : ℝ) (ne_of_gt hBr) (ne_of_gt hDr),
      abs_div, abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).2 (by
    simpa only [mul_comm (B : ℝ) (C : ℝ)] using hnum)

end Paper4

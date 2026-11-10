/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

import Mathlib

namespace Paper4.HmuSkeleton

theorem reflected_value_denominator_scale
    {q T B K s : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hB : 0 < B)
    (hKlower : q / (2 * T) ≤ K)
    (hKupper : K ≤ 3 * q / (2 * T))
    (hslower : K / B ≤ s)
    (hsupper : s ≤ B * K) :
    q / (2 * B * T) ≤ s ∧ s ≤ 2 * B * q / T := by
  have h2T : 0 < 2 * T := by positivity
  have h2BT : 0 < 2 * B * T := by positivity
  constructor
  · apply (div_le_iff₀ h2BT).2
    calc
      q ≤ K * (2 * T) :=
        (div_le_iff₀ h2T).1 hKlower
      _ ≤ (s * B) * (2 * T) :=
        mul_le_mul_of_nonneg_right
          ((div_le_iff₀ hB).1 hslower) h2T.le
      _ = s * (2 * B * T) := by ring
  · apply (le_div_iff₀ hT).2
    have h1 : s * T ≤ (B * K) * T :=
      mul_le_mul_of_nonneg_right hsupper hT.le
    have h2 : 2 * (B * K * T) ≤ 3 * (B * q) := by
      calc
        2 * (B * K * T) = B * (K * (2 * T)) := by ring
        _ ≤ B * (3 * q) :=
          mul_le_mul_of_nonneg_left
            ((le_div_iff₀ h2T).1 hKupper) hB.le
        _ = 3 * (B * q) := by ring
    have h3 : 0 ≤ B * q := (mul_pos hB hq).le
    nlinarith only [h1, h2, h3]

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.reflected_value_denominator_scale

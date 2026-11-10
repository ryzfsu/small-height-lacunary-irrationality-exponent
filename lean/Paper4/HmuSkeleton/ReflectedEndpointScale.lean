/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module
public import Mathlib

@[expose] public section


namespace Paper4.HmuSkeleton

theorem reflected_endpoint_scale
    {q s B T L M d : ℝ}
    (hq : 0 < q) (hs : 0 < s) (hB : 1 ≤ B) (hT : 0 < T)
    (hscale : Real.log T = L - M)
    (hlo : q / (2 * B * T) ≤ s)
    (hhi : s ≤ 2 * B * q / T)
    (hrev : |Real.log s - (M - d)| ≤ Real.log 2) :
    |Real.log q - (L - d)| ≤ Real.log (4 * B) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have h2Bpos : 0 < 2 * B := by positivity
  have hstpos : 0 < s * T := mul_pos hs hT

  have hmul_upper : q ≤ (2 * B) * (s * T) := by
    calc
      q ≤ s * (2 * B * T) :=
        (div_le_iff₀ (by positivity : 0 < 2 * B * T)).mp hlo
      _ = (2 * B) * (s * T) := by ring

  have hmul_lower : s * T ≤ (2 * B) * q :=
    (le_div_iff₀ hT).mp hhi

  have hlog_upper :
      Real.log q ≤ Real.log (2 * B) + Real.log s + Real.log T := by
    have h := Real.log_le_log hq hmul_upper
    rw [Real.log_mul (ne_of_gt h2Bpos) (ne_of_gt hstpos),
        Real.log_mul (ne_of_gt hs) (ne_of_gt hT)] at h
    linarith only [h]

  have hlog_lower :
      Real.log s + Real.log T ≤ Real.log (2 * B) + Real.log q := by
    have h := Real.log_le_log hstpos hmul_lower
    rw [Real.log_mul (ne_of_gt hs) (ne_of_gt hT),
        Real.log_mul (ne_of_gt h2Bpos) (ne_of_gt hq)] at h
    exact h

  have hlog4 :
      Real.log (4 * B) = Real.log 2 + Real.log (2 * B) := by
    calc
      Real.log (4 * B) = Real.log (2 * (2 * B)) := by
        congr 1
        ring
      _ = Real.log 2 + Real.log (2 * B) :=
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h2Bpos)

  rcases abs_le.mp hrev with ⟨hrev_lower, hrev_upper⟩
  rw [hlog4]
  apply abs_le.mpr
  constructor
  · linarith only [hlog_lower, hrev_lower, hscale]
  · linarith only [hlog_upper, hrev_upper, hscale]

end Paper4.HmuSkeleton

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.OneDivSeparation
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

theorem selected_gap_tail_lower (α δ r : ℚ) (hδ : δ ≠ 0)
    (hnear : |((α + δ : ℚ) : ℝ) - (r : ℝ)| < |(δ : ℝ)| / 2) :
    -Real.log |(δ : ℝ)| - Real.log (α.den : ℝ) -
      Real.log (3 / 2 : ℝ) ≤ Real.log (r.den : ℝ) := by
  have hβ : ((α + δ : ℚ) : ℝ) = (α : ℝ) + (δ : ℝ) := by
    norm_cast
  have hδne : (δ : ℝ) ≠ 0 := by
    exact_mod_cast hδ
  have hδpos : 0 < |(δ : ℝ)| := abs_pos.mpr hδne
  have hnear' : |(α : ℝ) + (δ : ℝ) - (r : ℝ)| <
      |(δ : ℝ)| / 2 := by
    simpa [hβ] using hnear
  have hneq : (α : ℝ) ≠ (r : ℝ) := by
    intro heq
    have habs : |(α : ℝ) + (δ : ℝ) - (r : ℝ)| = |(δ : ℝ)| := by
      rw [heq]
      congr 1
      ring
    rw [habs] at hnear'
    nlinarith
  have hcross : α.num * (r.den : ℤ) - r.num * (α.den : ℤ) ≠ 0 := by
    intro hz
    have hcross_eq : α.num * (r.den : ℤ) = r.num * (α.den : ℤ) :=
      sub_eq_zero.mp hz
    have hrat : (α : ℝ) = (r : ℝ) := by
      rw [Rat.cast_def, Rat.cast_def]
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      exact_mod_cast hcross_eq
    exact hneq hrat
  have hsep : 1 / ((α.den : ℝ) * (r.den : ℝ)) ≤
      |(α : ℝ) - (r : ℝ)| := by
    have hsep' := Paper4.one_div_mul_le_abs_sub_div
      (A := α.num) (B := α.den) (C := r.num) (D := r.den)
      α.den_pos r.den_pos hcross
    simpa only [Rat.cast_def] using hsep'
  have htri : |(α : ℝ) - (r : ℝ)| ≤
      |(α : ℝ) - ((α : ℝ) + (δ : ℝ))| +
        |((α : ℝ) + (δ : ℝ)) - (r : ℝ)| := by
    calc
      |(α : ℝ) - (r : ℝ)| =
          |((α : ℝ) - ((α : ℝ) + (δ : ℝ))) +
            (((α : ℝ) + (δ : ℝ)) - (r : ℝ))| := by
              congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
  have hαβ : |(α : ℝ) - ((α : ℝ) + (δ : ℝ))| = |(δ : ℝ)| := by
    rw [show (α : ℝ) - ((α : ℝ) + (δ : ℝ)) = -(δ : ℝ) by ring, abs_neg]
  have hupper : |(α : ℝ) - (r : ℝ)| <
      (3 / 2 : ℝ) * |(δ : ℝ)| := by
    calc
      |(α : ℝ) - (r : ℝ)| ≤
          |(α : ℝ) - ((α : ℝ) + (δ : ℝ))| +
            |((α : ℝ) + (δ : ℝ)) - (r : ℝ)| := htri
      _ = |(δ : ℝ)| + |((α : ℝ) + (δ : ℝ)) - (r : ℝ)| := by rw [hαβ]
      _ < |(δ : ℝ)| + |(δ : ℝ)| / 2 := by nlinarith [hnear']
      _ = (3 / 2 : ℝ) * |(δ : ℝ)| := by ring
  have hdenpos : 0 < (α.den : ℝ) * (r.den : ℝ) := by positivity
  have hprod : 1 < (3 / 2 : ℝ) * |(δ : ℝ)| *
      ((α.den : ℝ) * (r.den : ℝ)) :=
    (div_lt_iff₀ hdenpos).1 (lt_of_le_of_lt hsep hupper)
  have hqbound : (2 : ℝ) /
      (3 * (|(δ : ℝ)| * (α.den : ℝ))) < (r.den : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 3 * (|(δ : ℝ)| * (α.den : ℝ)))).2
    nlinarith [hprod]
  have hVpos : 0 < (α.den : ℝ) := by exact_mod_cast α.den_pos
  have hlogid :
      Real.log (2 / (3 * (|(δ : ℝ)| * (α.den : ℝ)))) =
        -Real.log |(δ : ℝ)| - Real.log (α.den : ℝ) -
          Real.log (3 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (mul_ne_zero (by norm_num)
      (mul_ne_zero (ne_of_gt hδpos) (ne_of_gt hVpos)))]
    rw [Real.log_mul (by norm_num) (mul_ne_zero
      (ne_of_gt hδpos) (ne_of_gt hVpos))]
    rw [Real.log_mul (ne_of_gt hδpos) (ne_of_gt hVpos)]
    rw [Real.log_div (by norm_num) (by norm_num)]
    ring
  calc
    -Real.log |(δ : ℝ)| - Real.log (α.den : ℝ) -
        Real.log (3 / 2 : ℝ) =
          Real.log (2 / (3 * (|(δ : ℝ)| * (α.den : ℝ)))) := hlogid.symm
    _ ≤ Real.log (r.den : ℝ) :=
      le_of_lt (Real.log_lt_log (by positivity) hqbound)

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.selected_gap_tail_lower

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.Summability

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

theorem geometric_tail_two_sided
    {f : ℕ → ℝ}
    (hsum : Summable (fun n => |f n|))
    (hratio : ∀ᶠ n : ℕ in atTop,
      |f (n + 1)| ≤ (1 / 4 : ℝ) * |f n|) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * |f (n + 1)| ≤
          |(∑' j, f j) - (∑ j ∈ Finset.range (n + 1), f j)| ∧
      |(∑' j, f j) - (∑ j ∈ Finset.range (n + 1), f j)| ≤
          (3 / 2 : ℝ) * |f (n + 1)| := by
  have hsum_f : Summable f := by
    exact hsum.of_norm
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hratio
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hratio_n : ∀ k : ℕ, |f (k + (n + 1) + 1)| ≤
      (1 / 4 : ℝ) * |f (k + (n + 1))| := by
    intro k
    apply hn₀
    omega
  have hgeom : ∀ k : ℕ,
      |f (k + (n + 1))| ≤ (1 / 4 : ℝ) ^ k * |f (n + 1)| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          |f (k.succ + (n + 1))| =
              |f (k + (n + 1) + 1)| := by congr 2 <;> omega
          _ ≤ (1 / 4 : ℝ) * |f (k + (n + 1))| := hratio_n k
          _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ k * |f (n + 1)|) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 4 : ℝ) ^ k.succ * |f (n + 1)| := by
            rw [pow_succ]
            ring
  have hsum_tail_abs : Summable (fun k : ℕ => |f (k + (n + 2))|) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (n + 2)).2 hsum
  have hsum_geom : Summable (fun k : ℕ =>
      (1 / 4 : ℝ) ^ k * |f (n + 1)|) := by
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hsum_geom_shift : Summable (fun k : ℕ =>
      (1 / 4 : ℝ) ^ (k + 1) * |f (n + 1)|) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      hsum_geom.mul_left (1 / 4 : ℝ)
  have hrem_sum :
      (∑' k : ℕ, |f (k + (n + 2))|) ≤
        ∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) * |f (n + 1)| := by
    apply hsum_tail_abs.tsum_le_tsum _ hsum_geom_shift
    intro k
    have hk := hgeom (k + 1)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  have hgeom_sum :
      (∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) * |f (n + 1)|) =
        (1 / 3 : ℝ) * |f (n + 1)| := by
    have hbase := tsum_geometric_of_lt_one
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 by norm_num)
    calc
      (∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) * |f (n + 1)|) =
          (1 / 4 : ℝ) * (∑' k : ℕ, (1 / 4 : ℝ) ^ k * |f (n + 1)|) := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            rw [pow_succ]
            ring
      _ = (1 / 4 : ℝ) * ((∑' k : ℕ, (1 / 4 : ℝ) ^ k) * |f (n + 1)|) := by
            rw [tsum_mul_right]
      _ = (1 / 3 : ℝ) * |f (n + 1)| := by
            rw [hbase]
            norm_num
            ring
  have hrem_abs :
      |∑' k : ℕ, f (k + (n + 2))| ≤ (1 / 3 : ℝ) * |f (n + 1)| := by
    have hnorm := norm_tsum_le_tsum_norm
      (show Summable (fun k : ℕ => ‖f (k + (n + 2))‖) by
        simpa only [Real.norm_eq_abs] using hsum_tail_abs)
    have hnorm' :
        |∑' k : ℕ, f (k + (n + 2))| ≤
          ∑' k : ℕ, |f (k + (n + 2))| := by
      simpa only [Real.norm_eq_abs] using hnorm
    exact hnorm'.trans (hrem_sum.trans_eq hgeom_sum)
  have hsum_tail : Summable (fun k : ℕ => f (k + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).2 hsum_f
  have hsplit :
      (∑' k : ℕ, f (k + (n + 1))) =
        f (n + 1) + ∑' k : ℕ, f (k + (n + 2)) := by
    have h := hsum_tail.sum_add_tsum_nat_add 1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
  have htail_eq :
      (∑' j : ℕ, f j) - (∑ j ∈ Finset.range (n + 1), f j) =
        ∑' k : ℕ, f (k + (n + 1)) := by
    have h := hsum_f.sum_add_tsum_nat_add (n + 1)
    linarith
  rw [htail_eq, hsplit]
  have hupper := abs_add_le (f (n + 1)) (∑' k : ℕ, f (k + (n + 2)))
  have hlower :
      |f (n + 1)| ≤
        |f (n + 1) + ∑' k : ℕ, f (k + (n + 2))| +
          |∑' k : ℕ, f (k + (n + 2))| := by
    simpa only [add_neg_cancel_right, abs_neg] using
      abs_add_le (f (n + 1) + ∑' k : ℕ, f (k + (n + 2)))
        (-(∑' k : ℕ, f (k + (n + 2))))
  constructor <;> linarith [hrem_abs, abs_nonneg (f (n + 1))]

end Paper4

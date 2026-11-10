/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Statement

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/-- The rational truncation through the term with index `n` (index zero is the
paper's first summand). -/
def trunc (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), c j / (N : ℚ) ^ u j

/-- The product of reduced coefficient denominators in a truncation. -/
def D (c : ℕ → ℚ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (n + 1), (c j).den

/-- An unreduced common denominator for the `n`th truncation. -/
def Q (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) : ℕ :=
  N ^ u n * D c n

/-- The real value of the full signed series. -/
noncomputable def x (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) : ℝ :=
  ∑' j : ℕ, term N u c j

/-- The main logarithmic scale at index `n`. -/
noncomputable def t (N : ℕ) (u : ℕ → ℕ) (n : ℕ) : ℝ :=
  (u n : ℝ) * Real.log (N : ℝ)

/-- The logarithm of the reduced denominator of the rational truncation. -/
noncomputable def M (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) : ℝ :=
  Real.log ((trunc N u c n).den : ℝ)

/-- The next summand omitted by `trunc ... n`. -/
def delta (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) : ℚ :=
  c (n + 1) / (N : ℚ) ^ u (n + 1)

/-- The logarithmic size of the next summand. -/
noncomputable def L (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) : ℝ :=
  -Real.log |(delta N u c n : ℝ)|

/-- Casting the finite rational truncation to the real finite sum of terms. -/
theorem trunc_cast (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) :
    (trunc N u c n : ℝ) =
      ∑ j ∈ Finset.range (n + 1), term N u c j := by
  simp only [trunc, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, term]

/-- The exact successor identity for truncations. -/
theorem trunc_succ (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) :
    trunc N u c (n + 1) = trunc N u c n + delta N u c n := by
  simp only [trunc, delta, Finset.sum_range_succ]

/-- The successor identity after casting to the reals. -/
theorem trunc_succ_cast (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) :
    (trunc N u c (n + 1) : ℝ) =
      (trunc N u c n : ℝ) + (delta N u c n : ℝ) := by
  exact_mod_cast trunc_succ N u c n

/-- Every coefficient denominator occurring in `D` is positive. -/
theorem D_pos (c : ℕ → ℚ) (n : ℕ) : 0 < D c n := by
  unfold D
  exact Finset.prod_pos (fun i hi => (c i).den_pos)

/-- The common denominator is positive when the base is positive. -/
theorem Q_pos (N : ℕ) (hN : 0 < N) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) :
    0 < Q N u c n := by
  unfold Q
  exact Nat.mul_pos (pow_pos hN _) (D_pos c n)

def truncNumerator (N : ℕ) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    (c j).num * (D c n / (c j).den : ℤ) *
      (N ^ (u n - u j) : ℤ)

theorem trunc_integerized (N : ℕ) (hN : 2 ≤ N)
    (u : ℕ → ℕ) (hu_strict : StrictMono u) (c : ℕ → ℚ) (n : ℕ) :
    ((trunc N u c n : ℚ) : ℝ) =
      (truncNumerator N u c n : ℝ) / (Q N u c n : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  have hNq0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  have hQ0nat : Q N u c n ≠ 0 :=
    ne_of_gt (Q_pos N (by omega) u c n)
  have hQ0 : (Q N u c n : ℚ) ≠ 0 := by exact_mod_cast hQ0nat

  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (c j / (N : ℚ) ^ u j) * (Q N u c n : ℚ) =
        (((c j).num * (D c n / (c j).den : ℤ) *
          (N ^ (u n - u j) : ℤ) : ℤ) : ℚ) := by
    have hj_le : j ≤ n := by
      have hj_lt : j < n + 1 := Finset.mem_range.mp hj
      omega
    have hu_le : u j ≤ u n := hu_strict.monotone hj_le
    have hden : (c j).den ∣ D c n := by
      unfold D
      exact Finset.dvd_prod_of_mem (fun k => (c k).den) hj
    have hdenZ : ((c j).den : ℤ) ∣ (D c n : ℤ) := by
      exact_mod_cast hden
    have hquot :
        ((D c n / (c j).den : ℤ) : ℚ) * ((c j).den : ℚ) =
          (D c n : ℚ) := by
      exact_mod_cast (Int.ediv_mul_cancel hdenZ)
    have hpow :
        (N : ℚ) ^ u j * (N : ℚ) ^ (u n - u j) =
          (N : ℚ) ^ u n := by
      rw [← pow_add, Nat.add_sub_of_le hu_le]
    have hpow0 : (N : ℚ) ^ u j ≠ 0 := pow_ne_zero _ hNq0
    calc
      (c j / (N : ℚ) ^ u j) * (Q N u c n : ℚ) =
          (c j / (N : ℚ) ^ u j) *
            ((N : ℚ) ^ u n * (D c n : ℚ)) := by
              simp only [Q, Nat.cast_mul, Nat.cast_pow]
      _ = (c j / (N : ℚ) ^ u j) *
            (((N : ℚ) ^ u j * (N : ℚ) ^ (u n - u j)) *
              (D c n : ℚ)) := by rw [hpow]
      _ = c j * ((N : ℚ) ^ (u n - u j) * (D c n : ℚ)) := by
        calc
          _ = ((c j / (N : ℚ) ^ u j) * (N : ℚ) ^ u j) *
                ((N : ℚ) ^ (u n - u j) * (D c n : ℚ)) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ hpow0]
      _ = (c j * ((c j).den : ℚ)) *
            (((D c n / (c j).den : ℤ) : ℚ) *
              (N : ℚ) ^ (u n - u j)) := by
        rw [← hquot]
        ring
      _ = ((c j).num : ℚ) *
            ((D c n / (c j).den : ℤ) : ℚ) *
              (N : ℚ) ^ (u n - u j) := by
        rw [Rat.mul_den_eq_num]
        ring
      _ = (((c j).num * (D c n / (c j).den : ℤ) *
              (N ^ (u n - u j) : ℤ) : ℤ) : ℚ) := by
        push_cast <;> ring

  have hrat :
      trunc N u c n =
        (truncNumerator N u c n : ℚ) / (Q N u c n : ℚ) := by
    apply (eq_div_iff hQ0).2
    calc
      trunc N u c n * (Q N u c n : ℚ) =
          ∑ j ∈ Finset.range (n + 1),
            (c j / (N : ℚ) ^ u j) * (Q N u c n : ℚ) := by
              simp only [trunc, Finset.sum_mul]
      _ = ∑ j ∈ Finset.range (n + 1),
            (((c j).num * (D c n / (c j).den : ℤ) *
              (N ^ (u n - u j) : ℤ) : ℤ) : ℚ) := by
                apply Finset.sum_congr rfl
                intro j hj
                exact hterm j hj
      _ = (truncNumerator N u c n : ℚ) := by
            simp only [truncNumerator, Int.cast_sum]
  have hreal := congrArg (fun x : ℚ => (x : ℝ)) hrat
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hreal

end Paper4

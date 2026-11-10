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

theorem summable_term_abs
    (N : ℕ) (hN : 2 ≤ N)
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ j, coeff j ≠ 0)
    (hheight : Tendsto
      (fun j => Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) :
    Summable (fun j => |term N u coeff j|) := by
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  let B : ℝ := ((N : ℝ) + 1) / 2
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBone : 1 < B := by dsimp [B]; linarith
  have hBN : B < (N : ℝ) := by dsimp [B]; linarith
  have hlogB : 0 < Real.log B := Real.log_pos hBone
  have hsmall : ∀ᶠ j : ℕ in atTop,
      Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ) < Real.log B :=
    Filter.Tendsto.eventually_lt_const hlogB hheight
  let r : ℝ := B / (N : ℝ)
  have hrpos : 0 < r := div_pos hBpos (by exact_mod_cast (show 0 < N by omega))
  have hrlt : r < 1 := (div_lt_one (by exact_mod_cast (show 0 < N by omega))).2 hBN
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one (le_of_lt hrpos) hrlt
  have hsub : Summable (fun j : ℕ => r ^ u j) := by
    simpa [Function.comp_def] using hgeom.comp_injective hu_strict.injective
  refine hsub.of_norm_bounded_eventually_nat ?_
  filter_upwards [hsmall] with j hj
  have hden : 0 < (u j : ℝ) := by exact_mod_cast hu_pos j
  have hheight_pos : 0 < rationalHeight (coeff j) := by
    unfold rationalHeight
    exact lt_of_lt_of_le (Rat.den_pos _) (Nat.le_max_right _ _)
  have hheightR : 0 < (rationalHeight (coeff j) : ℝ) := by exact_mod_cast hheight_pos
  have hlog_lt : Real.log (rationalHeight (coeff j) : ℝ) <
      Real.log B * (u j : ℝ) := by
    exact (div_lt_iff₀ hden).mp hj
  have hheight_lt : (rationalHeight (coeff j) : ℝ) < B ^ u j := by
    have hexp : Real.exp (Real.log B * (u j : ℝ)) = B ^ u j := by
      rw [Real.exp_mul, Real.exp_log hBpos, Real.rpow_natCast]
    rw [← hexp]
    exact (Real.log_lt_iff_lt_exp hheightR).mp hlog_lt
  have hcoeff_abs : |(coeff j : ℝ)| ≤ (rationalHeight (coeff j) : ℝ) := by
    rw [Rat.cast_def, abs_div]
    have hnum : |((coeff j).num : ℝ)| = ((coeff j).num.natAbs : ℝ) := by
      simpa using (Int.natCast_natAbs (coeff j).num).symm
    rw [hnum]
    have hden1nat : 1 ≤ (coeff j).den := Nat.succ_le_iff.mpr (Rat.den_pos (coeff j))
    have hden1 : (1 : ℝ) ≤ (coeff j).den := by exact_mod_cast hden1nat
    have hdenabs : |((coeff j).den : ℝ)| = (coeff j).den := abs_of_pos (by exact_mod_cast Rat.den_pos (coeff j))
    rw [hdenabs]
    calc
      ((coeff j).num.natAbs : ℝ) / (coeff j).den ≤ ((coeff j).num.natAbs : ℝ) :=
        div_le_self (by positivity) hden1
      _ ≤ (rationalHeight (coeff j) : ℝ) := by
        exact_mod_cast (Nat.le_max_left (coeff j).num.natAbs (coeff j).den)
  have hterm : |term N u coeff j| ≤ r ^ u j := by
    rw [term, abs_div]
    have hNpow : 0 < (N : ℝ) ^ u j := by positivity
    rw [abs_of_pos hNpow]
    calc
      |(coeff j : ℝ)| / (N : ℝ) ^ u j ≤ B ^ u j / (N : ℝ) ^ u j :=
        div_le_div_of_nonneg_right (le_trans hcoeff_abs (le_of_lt hheight_lt)) (le_of_lt hNpow)
      _ = r ^ u j := by
        rw [← div_pow]
  simpa [Real.norm_eq_abs] using hterm

end Paper4

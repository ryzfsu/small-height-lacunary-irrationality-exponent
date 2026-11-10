/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.Definitions
public import Paper4.Arithmetic.Summability
public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

theorem rationalHeight_abs_bounds_local
    (q : ℚ) (hq : q ≠ 0) :
    (rationalHeight q : ℝ)⁻¹ ≤ |(q : ℝ)| ∧
    |(q : ℝ)| ≤ (rationalHeight q : ℝ) := by
  have hnum_ne : q.num ≠ 0 := (Rat.num_ne_zero).2 hq
  have hnum_pos : 0 < q.num.natAbs := (Int.natAbs_pos).2 hnum_ne
  have hden_pos : 0 < q.den := Rat.den_pos q
  have hnumR_pos : 0 < (q.num.natAbs : ℝ) := by exact_mod_cast hnum_pos
  have hdenR_pos : 0 < (q.den : ℝ) := by exact_mod_cast hden_pos
  have hnum_abs : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    simp
  have hheight_pos : 0 < rationalHeight q := by
    unfold rationalHeight
    exact lt_of_lt_of_le hnum_pos (Nat.le_max_left _ _)
  have hheightR_pos : 0 < (rationalHeight q : ℝ) := by
    exact_mod_cast hheight_pos
  have hnum_le_height : (q.num.natAbs : ℝ) ≤ (rationalHeight q : ℝ) := by
    exact_mod_cast (Nat.le_max_left q.num.natAbs q.den)
  have hden_le_height : (q.den : ℝ) ≤ (rationalHeight q : ℝ) := by
    exact_mod_cast (Nat.le_max_right q.num.natAbs q.den)
  have hnum_ge_one : (1 : ℝ) ≤ (q.num.natAbs : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hnum_ne))
  have hden_ge_one : (1 : ℝ) ≤ (q.den : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hden_le_prod : (q.den : ℝ) ≤
      (q.num.natAbs : ℝ) * (rationalHeight q : ℝ) := by
    calc
      (q.den : ℝ) ≤ (rationalHeight q : ℝ) := hden_le_height
      _ ≤ (rationalHeight q : ℝ) * (q.num.natAbs : ℝ) :=
        le_mul_of_one_le_right (le_of_lt hheightR_pos) hnum_ge_one
      _ = (q.num.natAbs : ℝ) * (rationalHeight q : ℝ) := by ring
  have hnum_le_prod : (q.num.natAbs : ℝ) ≤
      (rationalHeight q : ℝ) * (q.den : ℝ) := by
    calc
      (q.num.natAbs : ℝ) ≤ (rationalHeight q : ℝ) := hnum_le_height
      _ ≤ (rationalHeight q : ℝ) * (q.den : ℝ) :=
        le_mul_of_one_le_right (le_of_lt hheightR_pos) hden_ge_one
  have hlow : (rationalHeight q : ℝ)⁻¹ ≤
      (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    apply (le_div_iff₀ hdenR_pos).2
    simpa [div_eq_mul_inv, mul_comm] using
      ((div_le_iff₀ hheightR_pos).2 hden_le_prod)
  have hupp : (q.num.natAbs : ℝ) / (q.den : ℝ) ≤
      (rationalHeight q : ℝ) := by
    exact (div_le_iff₀ hdenR_pos).2 hnum_le_prod
  rw [Rat.cast_def, abs_div, abs_of_pos hdenR_pos, hnum_abs]
  exact ⟨hlow, hupp⟩

theorem term_ratio_quarter_eventually
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      |term N u coeff (n + 1)| ≤ (1 / 4 : ℝ) * |term N u coeff n| := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hterm_ne : ∀ j : ℕ, term N u coeff j ≠ 0 := by
    intro j
    have hc : (coeff j : ℝ) ≠ 0 := by exact_mod_cast (hcoeff j)
    simp [term, hc, ne_of_gt hNpos]
  have hheight_event : ∀ᶠ n : ℕ in atTop,
      Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ) <
        Real.log (N : ℝ) / 20 :=
    hheight.eventually_lt_const (by positivity)
  have hheight_succ : ∀ᶠ n : ℕ in atTop,
      Real.log (rationalHeight (coeff (n + 1)) : ℝ) / (u (n + 1) : ℝ) <
        Real.log (N : ℝ) / 20 := by
    simpa only [Function.comp_apply] using
      (tendsto_add_atTop_nat 1).eventually hheight_event
  have hratio : ∀ᶠ n : ℕ in atTop,
      (3 / 2 : ℝ) * (u n : ℝ) ≤ (u (n + 1) : ℝ) := by
    have hg := hgap (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hg] with n hn
    have hun : 0 < (u n : ℝ) := by exact_mod_cast hu_pos n
    have hn' : (3 / 2 : ℝ) ≤ exponentRatio u n := by
      linarith
    apply (le_div_iff₀ hun).mp
    simpa [exponentRatio] using hn'
  have hutop : Tendsto (fun n : ℕ => (u n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hu_strict.tendsto_atTop
  have hbig : ∀ᶠ n : ℕ in atTop,
      Real.log 4 ≤ (3 / 8 * Real.log (N : ℝ)) * (u n : ℝ) := by
    have hc : 0 < (3 / 8 * Real.log (N : ℝ)) := by positivity
    have hU := (tendsto_atTop.1 hutop
      (Real.log 4 / (3 / 8 * Real.log (N : ℝ))))
    filter_upwards [hU] with n hn
    calc
      Real.log 4 = (Real.log 4 / (3 / 8 * Real.log (N : ℝ))) *
          (3 / 8 * Real.log (N : ℝ)) := by field_simp
      _ ≤ (u n : ℝ) * (3 / 8 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hn hc.le
      _ = (3 / 8 * Real.log (N : ℝ)) * (u n : ℝ) := by ring
  filter_upwards [hheight_event, hheight_succ, hratio, hbig] with n hn hn1 hstep hlarge
  have hun : 0 < (u n : ℝ) := by exact_mod_cast hu_pos n
  have hun1 : 0 < (u (n + 1) : ℝ) := by exact_mod_cast hu_pos (n + 1)
  have hHn_pos : 0 < (rationalHeight (coeff n) : ℝ) := by
    exact_mod_cast (show 0 < rationalHeight (coeff n) by
      unfold rationalHeight
      exact lt_of_lt_of_le (Rat.den_pos _) (Nat.le_max_right _ _))
  have hHn1_pos : 0 < (rationalHeight (coeff (n + 1)) : ℝ) := by
    exact_mod_cast (show 0 < rationalHeight (coeff (n + 1)) by
      unfold rationalHeight
      exact lt_of_lt_of_le (Rat.den_pos _) (Nat.le_max_right _ _))
  have hcn_pos : 0 < |(coeff n : ℝ)| := abs_pos.mpr (by
    exact_mod_cast (hcoeff n))
  have hcn1_pos : 0 < |(coeff (n + 1) : ℝ)| := abs_pos.mpr (by
    exact_mod_cast (hcoeff (n + 1)))
  have hcn_upper : Real.log |(coeff n : ℝ)| ≤
      Real.log (rationalHeight (coeff n) : ℝ) :=
    Real.log_le_log hcn_pos (rationalHeight_abs_bounds_local _ (hcoeff n)).2
  have hcn1_upper : Real.log |(coeff (n + 1) : ℝ)| ≤
      Real.log (rationalHeight (coeff (n + 1)) : ℝ) :=
    Real.log_le_log hcn1_pos (rationalHeight_abs_bounds_local _ (hcoeff (n + 1))).2
  have hcn_lower : -Real.log (rationalHeight (coeff n) : ℝ) ≤
      Real.log |(coeff n : ℝ)| := by
    have h := Real.log_le_log (inv_pos.mpr hHn_pos)
      (rationalHeight_abs_bounds_local _ (hcoeff n)).1
    simpa [Real.log_inv] using h
  have hlogterm (j : ℕ) :
      Real.log |term N u coeff j| =
        Real.log |(coeff j : ℝ)| - (u j : ℝ) * Real.log (N : ℝ) := by
    rw [term, abs_div, abs_of_pos (pow_pos hNpos _),
      Real.log_div (ne_of_gt (abs_pos.mpr (by exact_mod_cast hcoeff j)))
        (pow_ne_zero _ (ne_of_gt hNpos)), Real.log_pow]
  have hlogratio :
      Real.log |term N u coeff (n + 1)| - Real.log |term N u coeff n| ≤
        -(3 / 8 * Real.log (N : ℝ)) * (u n : ℝ) := by
    rw [hlogterm, hlogterm]
    have hn' := (div_lt_iff₀ hun).mp hn
    have hn1' := (div_lt_iff₀ hun1).mp hn1
    nlinarith
  have hApos : 0 < |term N u coeff (n + 1)| :=
    abs_pos.mpr (hterm_ne (n + 1))
  have hBpos : 0 < |term N u coeff n| :=
    abs_pos.mpr (hterm_ne n)
  have hlogdiv :
      Real.log (|term N u coeff (n + 1)| / |term N u coeff n|) ≤
        Real.log (1 / 4 : ℝ) := by
    rw [Real.log_div (ne_of_gt hApos) (ne_of_gt hBpos)]
    have hsmall :
        -(3 / 8 * Real.log (N : ℝ)) * (u n : ℝ) ≤ -Real.log 4 := by
      linarith
    calc
      Real.log |term N u coeff (n + 1)| - Real.log |term N u coeff n| ≤
          -(3 / 8 * Real.log (N : ℝ)) * (u n : ℝ) := hlogratio
      _ ≤ -Real.log 4 := hsmall
      _ = Real.log (1 / 4 : ℝ) := by
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hdiv_le :
      |term N u coeff (n + 1)| / |term N u coeff n| ≤ (1 / 4 : ℝ) := by
    have he := Real.exp_le_exp.mpr hlogdiv
    simpa only [Real.exp_log (div_pos hApos hBpos),
      Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4)] using he
  exact (div_le_iff₀ hBpos).mp hdiv_le

end Paper4

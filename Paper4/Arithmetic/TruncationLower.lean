/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.RawTailAdapter
public import Paper4.Arithmetic.TailTwoSided
public import Paper4.Arithmetic.RawScale
import Mathlib.Tactic

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

private lemma lower_abs_coeff_le_height (q : ℚ) :
    |(q : ℝ)| ≤ (rationalHeight q : ℝ) := by
  rw [Rat.cast_def, abs_div]
  have hnum : |((q).num : ℝ)| = ((q).num.natAbs : ℝ) := by
    simpa using (Int.natCast_natAbs q.num).symm
  rw [hnum]
  have hden1nat : 1 ≤ q.den := Nat.succ_le_iff.mpr (Rat.den_pos q)
  have hden1 : (1 : ℝ) ≤ q.den := by exact_mod_cast hden1nat
  have hdenabs : |(q.den : ℝ)| = q.den := abs_of_pos (by exact_mod_cast Rat.den_pos q)
  rw [hdenabs]
  calc
    (q.num.natAbs : ℝ) / q.den ≤ (q.num.natAbs : ℝ) :=
      div_le_self (by positivity) hden1
    _ ≤ (rationalHeight q : ℝ) := by
      exact_mod_cast (Nat.le_max_left q.num.natAbs q.den)

private lemma lower_term_abs_exp_bound
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (coeff : ℕ → ℚ)
    (hheight : Tendsto
      (fun j => Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ))
      atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop,
      |term N u coeff j| ≤
        Real.exp (-(Real.log (N : ℝ) - η) * (u j : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hsmall : ∀ᶠ j : ℕ in atTop,
      Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ) < η :=
    Filter.Tendsto.eventually_lt_const hη hheight
  filter_upwards [hsmall] with j hj
  have hu : (0 : ℝ) < u j := by exact_mod_cast hu_pos j
  have hH : 0 < rationalHeight (coeff j) :=
    lt_of_lt_of_le (Rat.den_pos _) (Nat.le_max_right _ _)
  have hHR : (0 : ℝ) < (rationalHeight (coeff j) : ℝ) := by exact_mod_cast hH
  have hlog : Real.log (rationalHeight (coeff j) : ℝ) < η * (u j : ℝ) :=
    (div_lt_iff₀ hu).mp hj
  have hheight_lt : (rationalHeight (coeff j) : ℝ) <
      Real.exp (η * (u j : ℝ)) :=
    (Real.log_lt_iff_lt_exp hHR).mp hlog
  have hcoeff : |(coeff j : ℝ)| ≤ Real.exp (η * (u j : ℝ)) :=
    (lower_abs_coeff_le_height (coeff j)).trans hheight_lt.le
  have hpow : (N : ℝ) ^ u j > 0 := by positivity
  calc
    |term N u coeff j| = |(coeff j : ℝ)| / (N : ℝ) ^ u j := by
      simp only [term, abs_div, abs_of_pos hpow]
    _ ≤ Real.exp (η * (u j : ℝ)) / (N : ℝ) ^ u j :=
      div_le_div_of_nonneg_right hcoeff (le_of_lt hpow)
    _ = Real.exp (-(Real.log (N : ℝ) - η) * (u j : ℝ)) := by
      have hpow' : (N : ℝ) ^ u j =
          Real.exp ((u j : ℝ) * Real.log (N : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hNpos]
      rw [hpow', ← Real.exp_sub]
      congr 1
      ring
theorem raw_truncation_lower_of_limsup
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (R : EReal)
    (hR : R = Filter.limsup (fun n => (exponentRatio u n : EReal)) atTop) :
    ∀ ν : ℝ, (ν : EReal) < R → ∃ᶠ n : ℕ in atTop,
      0 < Q N u coeff n ∧
      |x N u coeff - (truncNumerator N u coeff n : ℝ) /
          (Q N u coeff n : ℝ)| < (Q N u coeff n : ℝ) ^ (-ν) := by
  intro ν hνR
  obtain ⟨r, hrν, hrR⟩ := EReal.exists_rat_btwn_of_lt hνR
  let β : ℝ := r
  have hνβ : ν < β := by
    apply EReal.coe_lt_coe_iff.mp
    simpa [β] using hrν
  have hβR : (β : EReal) < R := by simpa [β] using hrR
  have hlim : (β : EReal) <
      Filter.limsup (fun n => (exponentRatio u n : EReal)) atTop := by
    rw [← hR]
    exact hβR
  have hfreqE : ∃ᶠ n : ℕ in atTop,
      (β : EReal) < (exponentRatio u n : EReal) :=
    Filter.frequently_lt_of_lt_limsup (h := hlim)
  have hfreq : ∃ᶠ n : ℕ in atTop, β < exponentRatio u n :=
    hfreqE.mono (fun n hn =>
      EReal.coe_lt_coe_iff.mp (by simpa using hn))
  have hQpos : ∀ n, 0 < Q N u coeff n := by
    intro n
    exact Q_pos N (by omega) u coeff n
  have hheightSum :=
    raw_height_sum_div_tendsto_zero u hu_pos hu_strict coeff hheight hgap
  have hlogD := log_D_div_u_tendsto_zero_of_height_sum
    u hu_pos coeff hheightSum
  have hQscale := log_Q_div_t_tendsto_one_of_log_D
    N hN u hu_pos coeff hlogD
  by_cases hν0 : 0 ≤ ν
  · have hβ0 : 0 ≤ β := hν0.trans hνβ.le
    let δ : ℝ := (β - ν) / (2 * (β + ν + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδlt1 : δ < 1 := by
      dsimp [δ]
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith
    have hδfactor : δ * (β + ν + 1) = (β - ν) / 2 := by
      dsimp [δ]
      field_simp
    have hmargin : ν * (1 + δ) < (1 - δ) * β - δ := by
      nlinarith [hδfactor]
    let L : ℝ := Real.log (N : ℝ)
    have hL : 0 < L := by
      dsimp [L]
      apply Real.log_pos
      exact_mod_cast (show 1 < N by omega)
    have hterm : ∀ᶠ j : ℕ in atTop,
        |term N u coeff j| ≤
          Real.exp (-(L - δ * L) * (u j : ℝ)) := by
      simpa [L] using lower_term_abs_exp_bound
        N hN u hu_pos coeff hheight (δ * L) (mul_pos hδ hL)
    have huTop : Tendsto (fun n : ℕ => (u n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_iff).2 hu_strict.tendsto_atTop
    have hconstant : ∀ᶠ n : ℕ in atTop,
        (3 / 2 : ℝ) ≤ Real.exp (δ * L * (u n : ℝ)) := by
      have hscale : Tendsto (fun n : ℕ => δ * L * (u n : ℝ))
          atTop atTop := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          huTop.atTop_mul_const (mul_pos hδ hL)
      have hev := (tendsto_atTop.1 hscale)
        (Real.log (3 / 2 : ℝ) + 1)
      filter_upwards [hev] with n hn
      have hlog : Real.log (3 / 2 : ℝ) < δ * L * (u n : ℝ) := by linarith
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mp hlog |>.le
    have hQscaleEvent : ∀ᶠ n : ℕ in atTop,
        Real.log (Q N u coeff n : ℝ) / ((u n : ℝ) * L) < 1 + δ := by
      have hev := (tendsto_order.mp hQscale).2 (1 + δ) (by linarith)
      filter_upwards [hev] with n hn
      simpa [t, L, mul_comm] using hn
    have hQlog : ∀ᶠ n : ℕ in atTop,
        Real.log (Q N u coeff n : ℝ) < (1 + δ) * L * (u n : ℝ) := by
      filter_upwards [hQscaleEvent] with n hn
      have hun : (0 : ℝ) < u n := by exact_mod_cast hu_pos n
      have ht : 0 < (u n : ℝ) * L := mul_pos hun hL
      have hn' := (div_lt_iff₀ ht).mp hn
      nlinarith
    have htail : ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) * |term N u coeff (n + 1)| ≤
          |x N u coeff - (trunc N u coeff n : ℝ)| ∧
        |x N u coeff - (trunc N u coeff n : ℝ)| ≤
          (3 / 2 : ℝ) * |term N u coeff (n + 1)| := by
      simpa only [x] using tail_two_sided_concrete
        N hN u hu_pos hu_strict coeff hcoeff hheight hgap
    have htermNext : ∀ᶠ n : ℕ in atTop,
        |term N u coeff (n + 1)| ≤
          Real.exp (-(L - δ * L) * (u (n + 1) : ℝ)) := by
      simpa only [Function.comp_apply] using
        (tendsto_add_atTop_nat 1).eventually hterm
    have hgood : ∀ᶠ n : ℕ in atTop,
        β < exponentRatio u n →
          |x N u coeff - (truncNumerator N u coeff n : ℝ) /
              (Q N u coeff n : ℝ)| < (Q N u coeff n : ℝ) ^ (-ν) := by
      filter_upwards [hconstant, hQlog, htermNext, htail] with n hc hq ht ht2
      intro hn
      have hu : (0 : ℝ) < u n := by exact_mod_cast hu_pos n
      have huNext : (0 : ℝ) < u (n + 1) := by exact_mod_cast hu_pos (n + 1)
      have hQ : (0 : ℝ) < (Q N u coeff n : ℝ) := by exact_mod_cast hQpos n
      have hratio : β <
          (u (n + 1) : ℝ) / (u n : ℝ) := by
        simpa [exponentRatio] using hn
      have hstep : β * (u n : ℝ) < (u (n + 1) : ℝ) :=
        (lt_div_iff₀ hu).mp hratio
      have hscaledMargin :=
        mul_lt_mul_of_pos_right hmargin (mul_pos hL hu)
      have hstep' :=
        mul_lt_mul_of_pos_left hstep
          (mul_pos (sub_pos.mpr hδlt1) hL)
      have hExp :
          -((1 - δ) * L) * (u (n + 1) : ℝ) +
              δ * L * (u n : ℝ) <
            -ν * ((1 + δ) * L * (u n : ℝ)) := by
        nlinarith [hscaledMargin, hstep']
      have hneg : -ν * ((1 + δ) * L * (u n : ℝ)) ≤
          -ν * Real.log (Q N u coeff n : ℝ) := by
        have hq' := (mul_le_mul_of_nonpos_left hq.le (by linarith : -ν ≤ 0))
        nlinarith
      have hExp' :
          -((1 - δ) * L) * (u (n + 1) : ℝ) +
              δ * L * (u n : ℝ) <
            -ν * Real.log (Q N u coeff n : ℝ) :=
        lt_of_lt_of_le hExp hneg
      have htailExp :
          |x N u coeff - (trunc N u coeff n : ℝ)| ≤
            Real.exp (-((1 - δ) * L) * (u (n + 1) : ℝ) +
              δ * L * (u n : ℝ)) := by
        calc
          |x N u coeff - (trunc N u coeff n : ℝ)| ≤
              (3 / 2 : ℝ) * |term N u coeff (n + 1)| := ht2.2
          _ ≤ Real.exp (δ * L * (u n : ℝ)) *
                Real.exp (-((1 - δ) * L) * (u (n + 1) : ℝ)) :=
            mul_le_mul hc (by convert ht using 1 <;> congr 1 <;> ring)
              (abs_nonneg _) (Real.exp_nonneg _)
          _ = Real.exp (-((1 - δ) * L) * (u (n + 1) : ℝ) +
                δ * L * (u n : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hExpStrict := Real.exp_lt_exp.mpr hExp'
      have hrealerr :
          |x N u coeff - (trunc N u coeff n : ℝ)| <
            Real.exp (-ν * Real.log (Q N u coeff n : ℝ)) :=
        lt_of_le_of_lt htailExp hExpStrict
      have hqpow : (Q N u coeff n : ℝ) ^ (-ν) =
          Real.exp (-ν * Real.log (Q N u coeff n : ℝ)) := by
        rw [Real.rpow_def_of_pos hQ]
        congr 1
        ring
      have htailApprox :
          |x N u coeff - (trunc N u coeff n : ℝ)| <
            (Q N u coeff n : ℝ) ^ (-ν) := by
        simpa [hqpow] using hrealerr
      rw [← trunc_integerized N hN u hu_strict coeff n]
      exact htailApprox
    have hfreqGood : ∃ᶠ n : ℕ in atTop,
        |x N u coeff - (truncNumerator N u coeff n : ℝ) /
            (Q N u coeff n : ℝ)| < (Q N u coeff n : ℝ) ^ (-ν) :=
      hfreq.mp hgood
    exact hfreqGood.mono (fun n hn => ⟨hQpos n, hn⟩)
  · have hνneg : ν < 0 := lt_of_not_ge hν0
    have hlim0 := master_raw_tail_mul_Q_tendsto N hN u hu_pos hu_strict
      coeff hcoeff hheight hgap
    have hprodSmall : ∀ᶠ n : ℕ in atTop,
        (Q N u coeff n : ℝ) *
          |x N u coeff - (trunc N u coeff n : ℝ)| < 1 := by
      have h := (tendsto_order.mp hlim0).2 (1 : ℝ) (by norm_num)
      simpa only [x] using h
    have hgood : ∀ᶠ n : ℕ in atTop,
        |x N u coeff - (truncNumerator N u coeff n : ℝ) /
            (Q N u coeff n : ℝ)| < (Q N u coeff n : ℝ) ^ (-ν) := by
      filter_upwards [hprodSmall] with n hp
      have hQ : (0 : ℝ) < (Q N u coeff n : ℝ) := by exact_mod_cast hQpos n
      have hQone : 1 ≤ (Q N u coeff n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hQpos n).ne')
      have herr : 0 ≤ |x N u coeff - (trunc N u coeff n : ℝ)| := abs_nonneg _
      have herrle : |x N u coeff - (trunc N u coeff n : ℝ)| ≤
          (Q N u coeff n : ℝ) *
            |x N u coeff - (trunc N u coeff n : ℝ)| :=
        by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hQone herr)
      have htailSmall : |x N u coeff - (trunc N u coeff n : ℝ)| < 1 :=
        lt_of_le_of_lt herrle hp
      have hlogQ : 0 ≤ Real.log (Q N u coeff n : ℝ) := Real.log_nonneg hQone
      have hpow : 1 ≤ (Q N u coeff n : ℝ) ^ (-ν) := by
        rw [Real.rpow_def_of_pos hQ, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact mul_nonneg hlogQ (le_of_lt (neg_pos.mpr hνneg))
      have htailApprox : |x N u coeff - (trunc N u coeff n : ℝ)| <
          (Q N u coeff n : ℝ) ^ (-ν) := lt_of_lt_of_le htailSmall hpow
      rw [← trunc_integerized N hN u hu_strict coeff n]
      exact htailApprox
    exact hgood.frequently.mono (fun n hn => ⟨hQpos n, hn⟩)

end Paper4


#print axioms Paper4.raw_truncation_lower_of_limsup

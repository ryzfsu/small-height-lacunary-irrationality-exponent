/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Statement
public import Paper4.Arithmetic.Definitions
public import Paper4.Arithmetic.RawScale
public import Paper4.Arithmetic.Summability
public import Paper4.Arithmetic.ValuationCore

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/- Geometric height bounds and absolute summability yield the raw-Q
   approximation-error limit. -/

private lemma master_prefix_exponent_sum_eventually_le
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      (∑ i ∈ Finset.range (k + 1), (u i : ℝ)) ≤ C + 3 * (u k : ℝ) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (by
      have h := hgap (1 / 2 : ℝ) (by norm_num)
      filter_upwards [h] with j hj
      exact (le_div_iff₀ (by exact_mod_cast hu_pos j)).mp hj)
  let C : ℝ := ∑ i ∈ Finset.range J, (u i : ℝ)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop J] with k hk
  induction k, hk using Nat.le_induction with
  | base =>
      rw [Finset.sum_range_succ]
      dsimp [C]
      have hp : (0 : ℝ) ≤ u J := by positivity
      linarith
  | succ k hk ih =>
      rw [Finset.sum_range_succ]
      have hnext := hJ k hk
      linarith

private lemma master_prefix_nonneg_eventually_le
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (u : ℕ → ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpoint : ∀ᶠ j : ℕ in atTop, f j ≤ δ * (u j : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      (∑ i ∈ Finset.range (k + 1), f i) ≤
        B + δ * (∑ i ∈ Finset.range (k + 1), (u i : ℝ)) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hpoint
  let B : ℝ := ∑ i ∈ Finset.range J, f i
  refine ⟨B, Finset.sum_nonneg (fun i hi => hf i), ?_⟩
  filter_upwards [eventually_ge_atTop J] with k hk
  induction k, hk using Nat.le_induction with
  | base =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => (u i : ℝ))]
      have h := hJ J le_rfl
      have hp : (0 : ℝ) ≤ δ * (∑ i ∈ Finset.range J, (u i : ℝ)) := by positivity
      dsimp [B]
      nlinarith
  | succ k hk ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => (u i : ℝ))]
      have hnext := hJ (k + 1) (hk.trans (Nat.le_succ k))
      nlinarith

theorem raw_height_sum_div_tendsto_zero
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ)
    (hheight : Tendsto
      (fun j => Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) :
    Tendsto (fun k => (∑ i ∈ Finset.range (k + 1),
      Real.log (rationalHeight (coeff i) : ℝ)) / (u k : ℝ))
      atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun i => Real.log (rationalHeight (coeff i) : ℝ)
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    apply Real.log_nonneg
    have hi : 1 ≤ rationalHeight (coeff i) :=
      (Nat.succ_le_iff.mpr (Rat.den_pos _)).trans
        (Nat.le_max_right _ _)
    exact_mod_cast hi
  have hnonneg : ∀ k, 0 ≤ (∑ i ∈ Finset.range (k + 1), f i) / (u k : ℝ) := by
    intro k
    exact div_nonneg (Finset.sum_nonneg (fun i hi => hf i)) (by positivity)
  obtain ⟨C, hC, hprefix⟩ :=
    master_prefix_exponent_sum_eventually_le u hu_pos hgap
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun k => ha.trans_le (hnonneg k))
  · intro ε hε
    let δ : ℝ := ε / 6
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hpoint : ∀ᶠ j : ℕ in atTop, f j ≤ δ * (u j : ℝ) := by
      filter_upwards [(tendsto_order.mp hheight).2 δ hδ] with j hj
      exact ((div_lt_iff₀ (by exact_mod_cast hu_pos j)).mp hj).le
    obtain ⟨B, hB, hsum⟩ :=
      master_prefix_nonneg_eventually_le f hf u δ hδ.le hpoint
    have hlim : Tendsto (fun k : ℕ => (B + δ * C) / (u k : ℝ))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def] using
        (tendsto_const_div_atTop_nhds_zero_nat (B + δ * C)).comp
          hu_strict.tendsto_atTop
    filter_upwards [hprefix, hsum,
      (tendsto_order.mp hlim).2 (ε / 2) (by positivity)]
      with k hk hsk hsmall
    have huk : (0 : ℝ) < u k := by exact_mod_cast hu_pos k
    have hmajor : (∑ i ∈ Finset.range (k + 1), f i) ≤
        B + δ * C + 3 * δ * (u k : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hk hδ.le
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hmajor huk.le
    have heq : (B + δ * C + 3 * δ * (u k : ℝ)) / (u k : ℝ) =
        (B + δ * C) / (u k : ℝ) + 3 * δ := by
      field_simp
    rw [heq] at hdiv
    dsimp [δ] at hdiv
    linarith

private lemma master_abs_coeff_le_height (q : ℚ) :
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

private lemma master_term_eventually_bound
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (coeff : ℕ → ℚ)
    (hheight : Tendsto
      (fun j => Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ))
      atTop (𝓝 0)) :
    ∀ᶠ j : ℕ in atTop,
      |term N u coeff j| ≤
        Real.exp (-(Real.log (N : ℝ) * (15 / 16 : ℝ))) ^ u j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  let δ : ℝ := Real.log (N : ℝ) / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ j : ℕ in atTop,
      Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ) < δ := by
    exact Filter.Tendsto.eventually_lt_const hδ hheight
  filter_upwards [hsmall] with j hj
  have hu : (0 : ℝ) < u j := by exact_mod_cast hu_pos j
  have hH : 0 < rationalHeight (coeff j) := by
    exact lt_of_lt_of_le (Rat.den_pos _) (Nat.le_max_right _ _)
  have hHR : (0 : ℝ) < (rationalHeight (coeff j) : ℝ) := by exact_mod_cast hH
  have hlog : Real.log (rationalHeight (coeff j) : ℝ) < δ * (u j : ℝ) :=
    (div_lt_iff₀ hu).mp hj
  have hheight_lt : (rationalHeight (coeff j) : ℝ) <
      Real.exp (δ * (u j : ℝ)) := by
    exact (Real.log_lt_iff_lt_exp hHR).mp hlog
  have hcoeff : |(coeff j : ℝ)| ≤ Real.exp (δ * (u j : ℝ)) := by
    exact (master_abs_coeff_le_height (coeff j)).trans hheight_lt.le
  have hpow : (N : ℝ) ^ u j > 0 := by positivity
  calc
    |term N u coeff j| = |(coeff j : ℝ)| / (N : ℝ) ^ u j := by
      simp only [term, abs_div, abs_of_pos hpow]
    _ ≤ Real.exp (δ * (u j : ℝ)) / (N : ℝ) ^ u j :=
      div_le_div_of_nonneg_right hcoeff (le_of_lt hpow)
    _ = Real.exp (-(Real.log (N : ℝ) * (15 / 16 : ℝ))) ^ u j := by
      have hpow' : (N : ℝ) ^ u j =
          Real.exp ((u j : ℝ) * Real.log (N : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hNpos]
      rw [hpow', ← Real.exp_sub]
      congr 1
      dsimp [δ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private lemma master_abs_tsum_nat_add_le_geometric
    (a : ℕ → ℝ) (ha : Summable a) (u : ℕ → ℕ) (hu : StrictMono u)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ)
    (hbound : ∀ j, K ≤ j → |a j| ≤ r ^ u j) :
    |∑' n : ℕ, a (n + K)| ≤ r ^ u K / (1 - r) := by
  have hg := (summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ u K)
  have hshift : Summable (fun n : ℕ => a (n + K)) :=
    (summable_nat_add_iff K).2 ha
  have hcmp : ∀ n : ℕ, |a (n + K)| ≤ r ^ u K * r ^ n := by
    intro n
    calc
      |a (n + K)| ≤ r ^ u (n + K) := hbound _ (Nat.le_add_left K n)
      _ ≤ r ^ (u K + n) := pow_le_pow_of_le_one hr0 hr1.le
        (by simpa [Nat.add_comm] using hu.add_le_nat n K)
      _ = r ^ u K * r ^ n := pow_add _ _ _
  calc
    |∑' n : ℕ, a (n + K)| ≤ ∑' n : ℕ, |a (n + K)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hshift.norm
    _ ≤ ∑' n : ℕ, r ^ u K * r ^ n := hshift.abs.tsum_le_tsum hcmp hg
    _ = r ^ u K / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

private lemma exponent_eventually_mul_le_master
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) (r : ℝ) (hr : r < 2) :
    ∀ᶠ j : ℕ in atTop, r * (u j : ℝ) ≤ u (j + 1) := by
  filter_upwards [hgap (2 - r) (sub_pos.mpr hr)] with j hj
  have hj' : r ≤ exponentRatio u j := by linarith
  exact (le_div_iff₀ (by exact_mod_cast hu_pos j)).mp hj'

theorem master_raw_tail_mul_Q_hmajor
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      abs ((Q N u coeff n : ℝ) *
        abs ((∑' j, term N u coeff j) - (trunc N u coeff n : ℝ))) ≤
      Real.exp (-(Real.log (N : ℝ) / 8) * (u n : ℝ)) := by
  let L : ℝ := Real.log (N : ℝ)
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsum_abs := summable_term_abs N hN u hu_pos hu_strict coeff hcoeff hheight hgap
  have hsum : Summable (term N u coeff) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hsum_abs
  have hheight_sum := raw_height_sum_div_tendsto_zero u hu_pos hu_strict coeff hheight hgap
  have hlogD := log_D_div_u_tendsto_zero_of_height_sum u hu_pos coeff hheight_sum
  have hq_t := log_Q_div_t_tendsto_one_of_log_D N hN u hu_pos coeff hlogD
  have hq : Tendsto (fun n => Real.log (Q N u coeff n : ℝ) / (u n : ℝ))
      atTop (𝓝 L) := by
    have hm : Tendsto (fun n => Real.log (Q N u coeff n : ℝ) / t N u n * L)
        atTop (𝓝 L) := by simpa [L] using hq_t.mul_const L
    apply hm.congr'
    filter_upwards [] with n
    have hu : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu_pos n).ne'
    have hLN : Real.log (N : ℝ) ≠ 0 := ne_of_gt hL
    dsimp [t, L]
    field_simp [hLN]
  have hq_bound : ∀ᶠ n : ℕ in atTop,
      Real.log (Q N u coeff n : ℝ) / (u n : ℝ) < (9 / 8 : ℝ) * L := by
    apply (tendsto_order.mp hq).2
    linarith
  let r : ℝ := Real.exp (-(L * (15 / 16 : ℝ)))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [hL])
  have hterm := master_term_eventually_bound N hN u hu_pos coeff hheight
  have htail : ∀ᶠ n : ℕ in atTop,
      |∑' k : ℕ, term N u coeff (k + (n + 1))| ≤
        r ^ u (n + 1) / (1 - r) := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp hterm
    filter_upwards [eventually_ge_atTop K] with n hn
    apply master_abs_tsum_nat_add_le_geometric (term N u coeff) hsum u hu_strict r hr0 hr1
      (n + 1)
    intro j hj
    exact hK j (hn.trans (Nat.le_trans (Nat.le_succ n) hj))
  have hgap32 : ∀ᶠ n : ℕ in atTop,
      (3 / 2 : ℝ) * (u n : ℝ) ≤ (u (n + 1) : ℝ) :=
    exponent_eventually_mul_le_master u hu_pos hgap (3 / 2 : ℝ) (by norm_num)
  have hu_top : Tendsto (fun n : ℕ => (u n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_iff).2 hu_strict.tendsto_atTop
  have hscale_top : Tendsto
      (fun n : ℕ => Real.exp ((L / 32) * (u n : ℝ))) atTop atTop := by
    have hlin : Tendsto (fun n : ℕ => (u n : ℝ) * (L / 32)) atTop atTop :=
      hu_top.atTop_mul_const (by positivity)
    simpa only [Function.comp_def, mul_comm] using Real.tendsto_exp_atTop.comp hlin
  have hden_bound : ∀ᶠ n : ℕ in atTop,
      (1 - r)⁻¹ ≤ Real.exp ((L / 32) * (u n : ℝ)) := by
    exact hscale_top.eventually (eventually_ge_atTop ((1 - r)⁻¹))
  filter_upwards [hq_bound, htail, hgap32, hden_bound] with
      n hnQ hnTail hnGap hnDen
  have hQpos : 0 < (Q N u coeff n : ℝ) := by
    exact_mod_cast Q_pos N (by omega) u coeff n
  have huN : (0 : ℝ) < (u n : ℝ) := by exact_mod_cast hu_pos n
  have huNext : (0 : ℝ) < (u (n + 1) : ℝ) := by
    exact_mod_cast hu_pos (n + 1)
  have hlogQ : Real.log (Q N u coeff n : ℝ) ≤
      (9 / 8 : ℝ) * L * (u n : ℝ) := by
    exact (div_lt_iff₀ huN).mp hnQ |>.le
  have hQexp : (Q N u coeff n : ℝ) ≤
      Real.exp ((9 / 8 : ℝ) * L * (u n : ℝ)) := by
    have hexp := Real.exp_le_exp.mpr hlogQ
    simpa [Real.exp_log hQpos] using hexp
  have htail_exp :
      |∑' k : ℕ, term N u coeff (k + (n + 1))| ≤
        Real.exp (-(L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ) +
          (L / 32) * (u n : ℝ)) := by
    calc
      |∑' k : ℕ, term N u coeff (k + (n + 1))| ≤
          r ^ u (n + 1) / (1 - r) := hnTail
      _ = Real.exp (-(L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ)) *
          (1 - r)⁻¹ := by
        rw [div_eq_mul_inv]
        congr 1
        dsimp [r]
        rw [show -(L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ) =
          (u (n + 1) : ℝ) * (-(L * (15 / 16 : ℝ))) by ring,
          ← Real.exp_nat_mul]
      _ ≤ Real.exp (-(L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ)) *
          Real.exp ((L / 32) * (u n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnDen (Real.exp_pos _).le
      _ = Real.exp (-(L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ) +
          (L / 32) * (u n : ℝ)) := by rw [← Real.exp_add]
  have hprod_exp :
      (Q N u coeff n : ℝ) *
          |∑' k : ℕ, term N u coeff (k + (n + 1))| ≤
        Real.exp (-(L / 8) * (u n : ℝ)) := by
    calc
      (Q N u coeff n : ℝ) *
          |∑' k : ℕ, term N u coeff (k + (n + 1))| ≤
          Real.exp ((9 / 8 : ℝ) * L * (u n : ℝ)) *
            Real.exp (-(L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ) +
              (L / 32) * (u n : ℝ)) :=
        mul_le_mul hQexp htail_exp (abs_nonneg _) (by positivity)
      _ = Real.exp ((9 / 8 : ℝ) * L * (u n : ℝ) -
          (L * (15 / 16 : ℝ)) * (u (n + 1) : ℝ) +
          (L / 32) * (u n : ℝ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(L / 8) * (u n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hL, hnGap]
  have htail_eq :
      (∑' k : ℕ, term N u coeff (k + (n + 1))) =
        (∑' j, term N u coeff j) - (trunc N u coeff n : ℝ) := by
    rw [trunc_cast]
    exact eq_sub_iff_add_eq.mpr (by
      simpa [add_comm] using hsum.sum_add_tsum_nat_add (n + 1))
  rw [← htail_eq]
  simpa [abs_of_pos hQpos] using hprod_exp

theorem master_raw_tail_mul_Q_tendsto
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    Tendsto
      (fun n => (Q N u coeff n : ℝ) *
        |(∑' j, term N u coeff j) - (trunc N u coeff n : ℝ)|)
      atTop (𝓝 0) := by
  have hmajor := master_raw_tail_mul_Q_hmajor N hN u hu_pos hu_strict
    coeff hcoeff hheight hgap
  have hN' : 1 < N := by omega
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN'
  have hc : -(Real.log (N : ℝ) / 8) < 0 := by
    have hp := Real.log_pos hNr
    linarith
  have hu_top : Tendsto (fun n : ℕ => (u n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_iff).2 hu_strict.tendsto_atTop
  have hbot : Tendsto
      (fun n : ℕ => (-(Real.log (N : ℝ) / 8)) * (u n : ℝ))
      atTop atBot :=
    Filter.Tendsto.neg_mul_atTop hc tendsto_const_nhds hu_top
  have henv : Tendsto
      (fun n : ℕ => Real.exp (-(Real.log (N : ℝ) / 8) * (u n : ℝ)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hbot
  have habs : Tendsto
      (fun n : ℕ => abs ((Q N u coeff n : ℝ) *
        |(∑' j, term N u coeff j) - (trunc N u coeff n : ℝ)|))
      atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze' tendsto_const_nhds henv
    · exact Filter.Eventually.of_forall (fun n => abs_nonneg _)
    · exact hmajor
  exact (tendsto_zero_iff_abs_tendsto_zero (fun n : ℕ =>
    (Q N u coeff n : ℝ) *
      |(∑' j, term N u coeff j) - (trunc N u coeff n : ℝ)|)).2 habs

end Paper4

#print axioms Paper4.master_raw_tail_mul_Q_hmajor
#print axioms Paper4.master_raw_tail_mul_Q_tendsto

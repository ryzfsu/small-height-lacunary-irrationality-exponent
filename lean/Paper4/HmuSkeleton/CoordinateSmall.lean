/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module
public import Paper4.HmuSkeleton.StepScales
@[expose] public section
namespace Paper4.HmuSkeleton
open Filter Asymptotics
open scoped Topology
theorem profile_prefix_exponent_sum_eventually_le
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

theorem profile_prefix_nonneg_eventually_le
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

theorem profile_height_sum_div_tendsto_zero
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
  exact Paper4.raw_height_sum_div_tendsto_zero u hu_pos hu_strict coeff hheight hgap


theorem shifted_small_of_finite_ratio
    (f : ℕ → ℝ) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (hf : Tendsto (fun n => f n / (u n : ℝ)) atTop (𝓝 0))
    (F : ℝ)
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop) :
    Tendsto (fun n => f (n + 1) / (u n : ℝ)) atTop (𝓝 0) := by
  have hs := ((hf.comp (tendsto_add_atTop_nat 1)).norm).mul_const (F + 1)
  simp only [norm_zero, zero_mul] at hs
  apply squeeze_zero_norm' _ hs
  filter_upwards [exponentRatio_eventually_upper hF (by norm_num : (0 : ℝ) < 1)] with n hn
  have heq : f (n + 1) / (u n : ℝ) =
      (f (n + 1) / (u (n + 1) : ℝ)) * exponentRatio u n := by
    have hu0 : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu n).ne'
    have hu1 : (u (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hu (n + 1)).ne'
    unfold exponentRatio
    field_simp
  rw [heq, norm_mul, Real.norm_eq_abs (exponentRatio u n),
    abs_of_nonneg (by unfold exponentRatio; positivity : 0 ≤ exponentRatio u n)]
  exact mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)

theorem deficit_div_u_tendsto_zero
    (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 2 - ε ≤ exponentRatio u n) :
    Tendsto (fun n => ((2 * u n - u (n + 1) : ℕ) : ℝ) / (u n : ℝ))
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (by positivity))
  · intro ε hε
    filter_upwards [hgap (ε / 2) (by linarith)] with n hn
    have hu0 : (0 : ℝ) < u n := by exact_mod_cast hu n
    by_cases he : 2 * u n ≤ u (n + 1)
    · simp [Nat.sub_eq_zero_of_le he, hε]
    · have he' : u (n + 1) ≤ 2 * u n := by omega
      rw [Nat.cast_sub he', Nat.cast_mul, Nat.cast_ofNat]
      have hstep := (le_div_iff₀ hu0).1 hn
      apply (div_lt_iff₀ hu0).2
      nlinarith

/-- The harmless squared numerator cost permits either sign of coefficients.
The pointwise denominator inequality is kept as a separate exact arithmetic atom. -/
theorem coordinate_small_of_bound_and_reduced_scale
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu : ∀ n, 0 < u n) (hstrict : StrictMono u)
    (coeff : ℕ → ℚ) (hc : ∀ n, coeff n ≠ 0)
    (hh : Tendsto (fun n => Real.log (rationalHeight (coeff n) : ℝ) /
      (u n : ℝ)) atTop (𝓝 0))
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 2 - ε ≤ exponentRatio u n)
    (F : ℝ)
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop)
    (hM : Tendsto (fun n => M N u coeff n / t N u n) atTop (𝓝 1))
    (hbound : ∀ n, coordinateDen (trunc N u coeff n) (delta N u coeff n) ≤
      (rationalHeight (coeff (n + 1))) ^ 2 * (D coeff n) ^ 2 *
        N ^ (2 * u n - u (n + 1))) :
    (fun n => Real.log (4 * (coordinateDen (trunc N u coeff n)
      (delta N u coeff n) : ℝ))) =o[atTop] (M N u coeff) := by
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogD := log_D_div_u_tendsto_zero_of_height_sum u hu coeff
    (profile_height_sum_div_tendsto_zero u hu hstrict coeff hh hgap)
  have hshift := shifted_small_of_finite_ratio
    (fun n => Real.log (rationalHeight (coeff n) : ℝ)) u hu hh F hF
  have hdef := deficit_div_u_tendsto_zero u hu hgap
  have hconst : Tendsto (fun n => Real.log 4 / (u n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4)).comp hstrict.tendsto_atTop
  have hsum := ((hconst.add (hshift.const_mul 2)).add (hlogD.const_mul 2)).add
    (hdef.mul_const (Real.log (N : ℝ)))
  simp only [zero_add, mul_zero, zero_mul] at hsum
  have hE_u : Tendsto
      (fun n => Real.log (4 * (coordinateDen (trunc N u coeff n)
        (delta N u coeff n) : ℝ)) / (u n : ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    · apply Eventually.of_forall
      intro n
      apply div_nonneg _ (by positivity)
      apply Real.log_nonneg
      have hp : (1 : ℝ) ≤ coordinateDen (trunc N u coeff n) (delta N u coeff n) := by
        exact_mod_cast Rat.den_pos _
      linarith
    · apply Eventually.of_forall
      intro n
      have hHp : (0 : ℝ) < rationalHeight (coeff (n + 1)) := by
        exact_mod_cast (coeff (n + 1)).den_pos.trans_le (Nat.le_max_right _ _)
      have hDp : (0 : ℝ) < D coeff n := by exact_mod_cast D_pos coeff n
      have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hBp : (0 : ℝ) < coordinateDen (trunc N u coeff n) (delta N u coeff n) := by
        exact_mod_cast Rat.den_pos _
      have hb : (coordinateDen (trunc N u coeff n) (delta N u coeff n) : ℝ) ≤
          (rationalHeight (coeff (n + 1)) : ℝ)^2 * (D coeff n : ℝ)^2 *
            (N : ℝ) ^ (2 * u n - u (n + 1)) := by exact_mod_cast hbound n
      have hl := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 4) hBp)
        (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4))
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hBp.ne',
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
        Real.log_mul (by positivity) (pow_ne_zero _ hNp.ne'),
        Real.log_mul (pow_ne_zero _ hHp.ne') (pow_ne_zero _ hDp.ne'),
        Real.log_pow, Real.log_pow, Real.log_pow] at hl
      have hdiv := div_le_div_of_nonneg_right hl (show 0 ≤ (u n : ℝ) by positivity)
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hBp.ne']
      convert hdiv using 1 <;> ring
  have hE_t := hE_u.div_const (Real.log (N : ℝ))
  simp only [zero_div] at hE_t
  have hE_M := hE_t.div hM (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_div] at hE_M
  have hMne : ∀ᶠ n : ℕ in atTop, M N u coeff n ≠ 0 := by
    filter_upwards [(tendsto_order.mp hM).1 (1 / 2 : ℝ) (by norm_num)] with n hn
    intro hz
    simp [hz] at hn
    linarith
  apply isLittleO_of_tendsto' (hMne.mono (fun n hn hz => (hn hz).elim))
  apply hE_M.congr'
  filter_upwards [hMne] with n hn
  have hu0 : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu n).ne'
  dsimp [t]
  field_simp


end Paper4.HmuSkeleton
#print axioms Paper4.HmuSkeleton.profile_height_sum_div_tendsto_zero
#print axioms Paper4.HmuSkeleton.shifted_small_of_finite_ratio
#print axioms Paper4.HmuSkeleton.deficit_div_u_tendsto_zero
#print axioms Paper4.HmuSkeleton.coordinate_small_of_bound_and_reduced_scale

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module
public import Paper4.HmuSkeleton.SeriesProfileClosure
@[expose] public section
namespace Paper4.HmuSkeleton
open Filter Asymptotics
open scoped Topology

private theorem abs_log_coeff_le_height (q : ℚ) (hq : q ≠ 0) :
    |Real.log (|(q : ℝ)|)| ≤ Real.log (rationalHeight q : ℝ) := by
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hH : (0 : ℝ) < rationalHeight q := by
    exact_mod_cast q.den_pos.trans_le (Nat.le_max_right _ _)
  have hnum : (1 : ℝ) ≤ q.num.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq)
  have hdH : (q.den : ℝ) ≤ rationalHeight q := by
    exact_mod_cast Nat.le_max_right q.num.natAbs q.den
  have hnH : (q.num.natAbs : ℝ) ≤ rationalHeight q := by
    exact_mod_cast Nat.le_max_left q.num.natAbs q.den
  have habs : |(q : ℝ)| = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    simp only [Rat.cast_def, abs_div, Nat.abs_cast, ← Int.cast_abs,
      ← Int.natCast_natAbs, Int.cast_natCast]
  have hc : 0 < |(q : ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  apply abs_le.mpr
  constructor
  · have hh : (rationalHeight q : ℝ)⁻¹ ≤ |(q : ℝ)| := by
      rw [habs, ← one_div]
      exact div_le_div₀ (by positivity) hnum hden hdH
    simpa only [Real.log_inv] using Real.log_le_log (inv_pos.mpr hH) hh
  · apply Real.log_le_log hc
    rw [habs]
    exact (div_le_self (by positivity)
      (by exact_mod_cast q.den_pos : (1 : ℝ) ≤ q.den)).trans hnH

theorem step_next_scale
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (coeff : ℕ → ℚ) (hc : ∀ n, coeff n ≠ 0)
    (hh : Tendsto (fun n => Real.log (rationalHeight (coeff n) : ℝ) /
      (u n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => L N u coeff n / t N u (n + 1)) atTop (𝓝 1) := by
  have hln : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hcoeff : Tendsto (fun n => Real.log |(coeff n : ℝ)| / (u n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hh
    intro n
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (abs_log_coeff_le_height (coeff n) (hc n))
      (by positivity)
  have hshift := (hcoeff.comp (tendsto_add_atTop_nat 1)).div_const (Real.log (N : ℝ))
  have hout := (tendsto_const_nhds (x := (1 : ℝ))).sub hshift
  simp only [zero_div, sub_zero] at hout
  apply hout.congr'
  filter_upwards [] with n
  have hu0 : (u (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hu (n + 1)).ne'
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcp : |(coeff (n + 1) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (by exact_mod_cast hc (n + 1))
  simp only [L, delta, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    abs_div, abs_of_pos (pow_pos hNp _), Real.log_div hcp
      (pow_ne_zero _ hNp.ne'), Real.log_pow, t, Function.comp_apply]
  field_simp
  <;> ring

/-- The finite real limsup gives the bounded ratio needed to multiply the
relative scale errors. -/
theorem exponentRatio_eventually_upper
    {u : ℕ → ℕ} {F : ℝ}
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, exponentRatio u n < F + ε := by
  have h := (Filter.limsup_le_iff).1 (le_of_eq hF.symm)
    ((F + ε : ℝ) : EReal) (EReal.coe_lt_coe_iff.2 (by linarith))
  exact h.mono fun n hn => EReal.coe_lt_coe_iff.1 hn

theorem step_scale_difference
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (coeff : ℕ → ℚ) (hc : ∀ n, coeff n ≠ 0)
    (hh : Tendsto (fun n => Real.log (rationalHeight (coeff n) : ℝ) /
      (u n : ℝ)) atTop (𝓝 0))
    (F : ℝ) (hF2 : 2 ≤ F)
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop)
    (hM : Tendsto (fun n => M N u coeff n / t N u n) atTop (𝓝 1)) :
    Tendsto (fun n => L N u coeff n / M N u coeff n - exponentRatio u n)
      atTop (𝓝 0) := by
  let f := fun n => (L N u coeff n / t N u (n + 1)) /
    (M N u coeff n / t N u n)
  have hf : Tendsto f atTop (𝓝 1) := by
    have hh := (step_next_scale N hN u hu coeff hc hh).div hM (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto f atTop (𝓝 (1 / 1)) at hh
    simpa using hh
  have hf0 := (hf.sub_const 1).norm.mul_const (F + 1)
  simp only [sub_self, norm_zero, zero_mul] at hf0
  have hln : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hdiff : ∀ n, L N u coeff n / M N u coeff n - exponentRatio u n =
      (f n - 1) * exponentRatio u n := by
    intro n
    have hu0 : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu n).ne'
    have hu1 : (u (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hu (n + 1)).ne'
    dsimp [f, t, exponentRatio]
    field_simp
    <;> ring
  apply squeeze_zero_norm' _ hf0
  filter_upwards [exponentRatio_eventually_upper hF (by norm_num : (0 : ℝ) < 1)] with n hn
  rw [hdiff, norm_mul, Real.norm_eq_abs (exponentRatio u n),
    abs_of_nonneg (by unfold exponentRatio; positivity : 0 ≤ exponentRatio u n)]
  exact mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)

theorem step_bounds_of_reduced_scale
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (coeff : ℕ → ℚ) (hc : ∀ n, coeff n ≠ 0)
    (hh : Tendsto (fun n => Real.log (rationalHeight (coeff n) : ℝ) /
      (u n : ℝ)) atTop (𝓝 0))
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 2 - ε ≤ exponentRatio u n)
    (F : ℝ) (hF2 : 2 ≤ F)
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop)
    (hM : Tendsto (fun n => M N u coeff n / t N u n) atTop (𝓝 1)) :
    (∀ ε > 0, ∀ᶠ n : ℕ in atTop, (2 - ε) * M N u coeff n ≤ L N u coeff n) ∧
    (∀ ε > 0, ∀ᶠ n : ℕ in atTop, L N u coeff n ≤ (F + ε) * M N u coeff n) := by
  have hd := step_scale_difference N hN u hu coeff hc hh F hF2 hF hM
  have hMpos : ∀ᶠ n : ℕ in atTop, 0 < M N u coeff n := by
    filter_upwards [(tendsto_order.mp hM).1 (1 / 2 : ℝ) (by norm_num)] with n hn
    have ht : 0 < t N u n :=
      mul_pos (by exact_mod_cast hu n)
        (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    have hh := (lt_div_iff₀ ht).1 hn
    linarith
  constructor
  · intro ε hε
    filter_upwards [hMpos, hgap (ε / 2) (by linarith),
      (tendsto_order.mp hd).1 (-ε / 2) (by linarith)] with n hm hg he
    have hr : 2 - ε ≤ L N u coeff n / M N u coeff n := by linarith
    exact (le_div_iff₀ hm).1 hr
  · intro ε hε
    filter_upwards [hMpos, exponentRatio_eventually_upper hF (show 0 < ε / 2 by linarith),
      (tendsto_order.mp hd).2 (ε / 2) (by linarith)] with n hm hg he
    have hr : L N u coeff n / M N u coeff n ≤ F + ε := by linarith
    exact (div_le_iff₀ hm).1 hr

end Paper4.HmuSkeleton
#print axioms Paper4.HmuSkeleton.step_next_scale
#print axioms Paper4.HmuSkeleton.exponentRatio_eventually_upper
#print axioms Paper4.HmuSkeleton.step_scale_difference
#print axioms Paper4.HmuSkeleton.step_bounds_of_reduced_scale

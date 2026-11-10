/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Statement

@[expose] public section

open Filter Asymptotics

/- Source module: TransferBootstrap. -/
namespace Lacunary.Transfer

/-- A logarithmic error is negligible on the positive half-line. -/
theorem log_profile_error_littleO (K D : ℝ) :
    (fun s : ℝ => K * Real.log s + D) =o[atTop] id := by
  exact (Real.isLittleO_log_id_atTop.const_mul_left K).add
    (isLittleO_const_id_atTop D)

/-- A logarithmic profile first forces the right endpoint to be linear in the
left endpoint. The constants in the logarithmic error can have either sign. -/
theorem log_profile_bootstrap {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {κ K D : ℝ}
    (_hκ : 0 ≤ κ) (ha : Tendsto a l atTop)
    (hab : ∀ᶠ i in l, a i ≤ b i)
    (hprofile : ∀ᶠ i in l,
      b i - a i ≤ κ * a i + K * Real.log (a i + b i + 2) + D) :
    ∀ᶠ i in l, b i ≤ (2 * κ + 3) * a i := by
  have ha1 : ∀ᶠ i in l, 1 ≤ a i := tendsto_atTop.1 ha 1
  have hs : Tendsto (fun i => a i + b i + 2) l atTop := by
    apply tendsto_atTop_mono' l _ ha
    filter_upwards [ha1, hab] with i hi hiab
    linarith
  have he := ((log_profile_error_littleO K D).comp_tendsto hs).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [ha1, hab, hprofile, he] with i hi hiab hip hie
  have hsi : 0 ≤ a i + b i + 2 := by linarith
  have herror : K * Real.log (a i + b i + 2) + D ≤
      (a i + b i + 2) / 4 := by
    simp only [Function.comp_def, Real.norm_eq_abs, id_eq, abs_of_nonneg hsi] at hie
    exact (le_abs_self _).trans (by simpa [div_eq_mul_inv, mul_comm] using hie)
  nlinarith

/-- Once the endpoints are comparable, the logarithmic loss is negligible
relative to the left endpoint. This yields the limiting gap bound. -/
theorem log_profile_eventually {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {κ K D : ℝ}
    (hκ : 0 ≤ κ) (ha : Tendsto a l atTop)
    (hab : ∀ᶠ i in l, a i ≤ b i)
    (hprofile : ∀ᶠ i in l,
      b i - a i ≤ κ * a i + K * Real.log (a i + b i + 2) + D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, b i - a i ≤ (κ + ε) * a i := by
  have hboot := log_profile_bootstrap hκ ha hab hprofile
  have ha1 : ∀ᶠ i in l, 1 ≤ a i := tendsto_atTop.1 ha 1
  have hs : Tendsto (fun i => a i + b i + 2) l atTop := by
    apply tendsto_atTop_mono' l _ ha
    filter_upwards [ha1, hab] with i hi hiab
    linarith
  have hden : 0 < 2 * κ + 6 := by linarith
  have hδ : 0 < ε / (2 * κ + 6) := div_pos hε hden
  have he := ((log_profile_error_littleO K D).comp_tendsto hs).bound hδ
  filter_upwards [ha1, hab, hprofile, hboot, he] with i hi hiab hip hib hie
  have hsi : 0 ≤ a i + b i + 2 := by linarith
  have hsum : a i + b i + 2 ≤ (2 * κ + 6) * a i := by nlinarith
  have herror : K * Real.log (a i + b i + 2) + D ≤
      ε / (2 * κ + 6) * (a i + b i + 2) := by
    simp only [Function.comp_def, Real.norm_eq_abs, id_eq, abs_of_nonneg hsi] at hie
    exact (le_abs_self _).trans hie
  have hmul := mul_le_mul_of_nonneg_left hsum hδ.le
  have hcancel : ε / (2 * κ + 6) * (2 * κ + 6) = ε :=
    div_mul_cancel₀ _ hden.ne'
  have herror' : K * Real.log (a i + b i + 2) + D ≤ ε * a i := by
    calc
      _ ≤ ε / (2 * κ + 6) * (a i + b i + 2) := herror
      _ ≤ ε / (2 * κ + 6) * ((2 * κ + 6) * a i) := hmul
      _ = ε * a i := by rw [← mul_assoc, hcancel]
  nlinarith

/-- The finite profile and an index bound combine into the form used by the
logarithmic bootstrap. `m` can be the real cast of `n - n₀`. -/
theorem combine_finite_profile_index
    {a b κ A C K D m : ℝ}
    (hC : 0 ≤ C)
    (hprofile : b - a ≤ κ * a + A + C * m)
    (hindex : m ≤ K * Real.log (a + b + 2) + D) :
    b - a ≤ κ * a + (C * K) * Real.log (a + b + 2) + (A + C * D) := by
  have hm := mul_le_mul_of_nonneg_left hindex hC
  nlinarith

/-- A lower bound on the transferred finite next denominator turns into a
logarithmic gap comparison. -/
theorem log_gap_of_next_denominator
    {q qPlus s : ℝ}
    (_hq : 0 < q) (hqPlus : 0 < qPlus) (hs : 0 < s)
    (hnext : qPlus ≤ 6 * s) :
    Real.log qPlus - Real.log q ≤ Real.log s - Real.log q + Real.log 6 := by
  have hnext' : qPlus ≤ (6 : ℝ) * s := by simpa using hnext
  have hlog := Real.log_le_log hqPlus hnext'
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hs.ne'] at hlog
  nlinarith

/-- Gaps with bounded denominator ratio contribute only a bounded logarithmic
width. -/
theorem bounded_log_gap
    {q qPlus : ℝ}
    (hq : 0 < q) (hqPlus : 0 < qPlus)
    (hbound : qPlus ≤ 6 * q) :
    Real.log qPlus - Real.log q ≤ Real.log 6 := by
  have hbound' : qPlus ≤ (6 : ℝ) * q := by simpa using hbound
  have hlog := Real.log_le_log hqPlus hbound'
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hq.ne'] at hlog
  linarith

end Lacunary.Transfer

/- Source module: SelectedIndex. -/
namespace Lacunary.Transfer

/-- The non-strict limiting ratio hypothesis supplies any fixed growth factor
strictly below two, including when individual ratios lie below two. -/
theorem geometric_step_of_paper_gap
    (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ Paper4.exponentRatio u n)
    {ρ : ℝ} (hρ : ρ < 2) :
    ∀ᶠ n : ℕ in atTop, ρ * (u n : ℝ) ≤ (u (n + 1) : ℝ) := by
  have hg := hgap (2 - ρ) (by linarith)
  filter_upwards [hg] with n hn
  have hpos : (0 : ℝ) < u n := by exact_mod_cast hu n
  have hr : ρ ≤ (u (n + 1) : ℝ) / (u n : ℝ) := by
    simpa only [Paper4.exponentRatio, sub_sub_cancel] using hn
  exact (le_div_iff₀ hpos).mp hr

/-- Geometric lower growth from a fixed starting index. -/
theorem geometric_lower_of_step
    {t : ℕ → ℝ} {n₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hstep : ∀ n, n₀ ≤ n → ρ * t n ≤ t (n + 1)) :
    ∀ m : ℕ, t n₀ * ρ ^ m ≤ t (n₀ + m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      t n₀ * ρ ^ (m + 1) = ρ * (t n₀ * ρ ^ m) := by rw [pow_succ]; ring
      _ ≤ ρ * t (n₀ + m) := mul_le_mul_of_nonneg_left ih hρ
      _ ≤ t (n₀ + m + 1) := hstep _ (by omega)
      _ = t (n₀ + (m + 1)) := by congr 1

/-- A positive geometric lower bound makes the shifted scale cofinal. -/
theorem tendsto_scale_of_geometric
    {t : ℕ → ℝ} {n₀ : ℕ} {c ρ : ℝ}
    (hc : 0 < c) (hρ : 1 < ρ)
    (hgrowth : ∀ m : ℕ, c * ρ ^ m ≤ t (n₀ + m)) :
    Tendsto (fun m => t (n₀ + m)) atTop atTop := by
  exact tendsto_atTop_mono hgrowth
    ((tendsto_pow_atTop_atTop_of_one_lt hρ).const_mul_atTop hc)

/-- Offset of the least truncation index n ≥ n₀ at or above a requested
scale. Paper §7 uses s = 4(a + b + 1); the selected index is n₀ plus this
Nat.find offset. The next two lemmas record attainment and minimality. -/
noncomputable def selectedOffset
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop) (s : ℝ) : ℕ := by
  classical
  exact Nat.find ((tendsto_atTop.1 ht s).exists)

theorem selectedOffset_spec
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop) (s : ℝ) :
    s ≤ t (n₀ + selectedOffset t n₀ ht s) := by
  classical
  exact Nat.find_spec ((tendsto_atTop.1 ht s).exists)

theorem selectedOffset_min
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop) (s : ℝ)
    {m : ℕ} (hm : m < selectedOffset t n₀ ht s) :
    t (n₀ + m) < s := by
  classical
  exact lt_of_not_ge (Nat.find_min ((tendsto_atTop.1 ht s).exists) hm)

/-- Minimality, rather than an upper bound on adjacent ratios, gives the
logarithmic index bound. The zero-offset case is included. -/
theorem selectedOffset_log_bound
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop)
    {c ρ s : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (hs : 1 ≤ s)
    (hgrowth : ∀ m : ℕ, c * ρ ^ m ≤ t (n₀ + m)) :
    (selectedOffset t n₀ ht s : ℝ) ≤
      (Real.log s + |Real.log c|) / Real.log ρ + 1 := by
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hρ0 : 0 < ρ := by linarith
  cases hsel : selectedOffset t n₀ ht s with
  | zero =>
    have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs
    have hdiv : 0 ≤ (Real.log s + |Real.log c|) / Real.log ρ :=
      div_nonneg (by positivity) hlogρ.le
    simp only [Nat.cast_zero]
    linarith
  | succ k =>
    have hprev : t (n₀ + k) < s :=
      selectedOffset_min t n₀ ht s (by rw [hsel]; omega)
    have hprod : c * ρ ^ k ≤ s := (hgrowth k).trans hprev.le
    have hlog := Real.log_le_log (mul_pos hc (pow_pos hρ0 k)) hprod
    rw [Real.log_mul hc.ne' (pow_ne_zero _ hρ0.ne'), Real.log_pow] at hlog
    have hk : (k : ℝ) ≤ (Real.log s + |Real.log c|) / Real.log ρ := by
      apply (le_div_iff₀ hlogρ).2
      have hcabs := neg_abs_le (Real.log c)
      nlinarith
    simp only [Nat.cast_succ]
    linarith

/-- The paper's threshold produces the explicit `O(log(a+b+2))` bound. -/
theorem selectedOffset_paper_bound
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop)
    {c ρ a b : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (hab : 0 ≤ a + b)
    (hgrowth : ∀ m : ℕ, c * ρ ^ m ≤ t (n₀ + m)) :
    (selectedOffset t n₀ ht (4 * (a + b + 1)) : ℝ) ≤
      (1 / Real.log ρ) * Real.log (a + b + 2) +
        ((Real.log 4 + |Real.log c|) / Real.log ρ + 1) := by
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hbase := selectedOffset_log_bound t n₀ ht hc hρ
    (show (1 : ℝ) ≤ 4 * (a + b + 1) by linarith) hgrowth
  have hp : 0 < a + b + 2 := by linarith
  have hl := Real.log_le_log
    (show (0 : ℝ) < 4 * (a + b + 1) by linarith)
    (show 4 * (a + b + 1) ≤ 4 * (a + b + 2) by linarith)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hp.ne'] at hl
  have hd := div_le_div_of_nonneg_right
    (add_le_add_right hl |Real.log c|) hlogρ.le
  have heq : (Real.log 4 + Real.log (a + b + 2) + |Real.log c|) / Real.log ρ + 1 =
      (1 / Real.log ρ) * Real.log (a + b + 2) +
        ((Real.log 4 + |Real.log c|) / Real.log ρ + 1) := by ring
  calc
    _ ≤ (Real.log (4 * (a + b + 1)) + |Real.log c|) / Real.log ρ + 1 := hbase
    _ ≤ (Real.log 4 + Real.log (a + b + 2) + |Real.log c|) / Real.log ρ + 1 := by
      convert add_le_add_right hd 1 using 1 <;> ring
    _ = _ := heq

/-- A cofinal requested scale forces the selected indices to infinity. -/
theorem tendsto_selectedIndex
    {ι : Type*} {l : Filter ι}
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop)
    (hmono : Monotone t) {s : ι → ℝ} (hs : Tendsto s l atTop) :
    Tendsto (fun i => n₀ + selectedOffset t n₀ ht (s i)) l atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [tendsto_atTop.1 hs (t k + 1)] with i hi
  have hspec := selectedOffset_spec t n₀ ht (s i)
  by_contra hk
  have hle : n₀ + selectedOffset t n₀ ht (s i) ≤ k := by omega
  have hscale := hmono hle
  linarith

/-- The paper's moving threshold is cofinal with the left log denominator. -/
theorem tendsto_selectedIndex_paper
    {ι : Type*} {l : Filter ι}
    (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop)
    (hmono : Monotone t) {a b : ι → ℝ} (ha : Tendsto a l atTop)
    (hab : ∀ᶠ i in l, a i ≤ b i) :
    Tendsto (fun i => n₀ + selectedOffset t n₀ ht (4 * (a i + b i + 1))) l atTop := by
  apply tendsto_selectedIndex t n₀ ht hmono
  apply tendsto_atTop_mono' l _ ha
  filter_upwards [tendsto_atTop.1 ha 0, hab] with i hi hiab
  linarith

/-- The actual logarithmic scale is increasing because the integer exponents
are strictly increasing and `N ≥ 2`. -/
theorem paper_scale_strictMono
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu : StrictMono u) :
    StrictMono (fun n => Real.log (N : ℝ) * (u n : ℝ)) := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  intro i j hij
  have huij : (u i : ℝ) < u j := by exact_mod_cast hu hij
  exact mul_lt_mul_of_pos_left huij hlogN

/-- The actual hypotheses give a geometric scale after any prescribed cutoff,
so the starting index can also satisfy the finite-profile hypotheses. -/
theorem paper_scale_geometric_after
    (nbase N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ Paper4.exponentRatio u n) :
    ∃ n₀ : ℕ, nbase ≤ n₀ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ m : ℕ, c * (3 / 2 : ℝ) ^ m ≤
        Real.log (N : ℝ) * (u (n₀ + m) : ℝ) := by
  have hg := geometric_step_of_paper_gap u hu hgap (by norm_num : (3 / 2 : ℝ) < 2)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hg
  let n₀ := max nbase j₀
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  let t : ℕ → ℝ := fun n => Real.log (N : ℝ) * (u n : ℝ)
  have ht0 : 0 < t n₀ := mul_pos hlogN (by exact_mod_cast hu n₀)
  refine ⟨n₀, le_max_left _ _, t n₀, ht0, ?_⟩
  apply geometric_lower_of_step (by norm_num : (0 : ℝ) ≤ 3 / 2)
  intro n hn
  have h := mul_le_mul_of_nonneg_left (hj₀ n ((le_max_right _ _).trans hn)) hlogN.le
  dsimp [t]
  nlinarith

/-- The actual natural-exponent hypotheses give a usable geometric scale,
with no permanent ratio bound of two. -/
theorem paper_scale_geometric
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ Paper4.exponentRatio u n) :
    ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ m : ℕ, c * (3 / 2 : ℝ) ^ m ≤
        Real.log (N : ℝ) * (u (n₀ + m) : ℝ) := by
  obtain ⟨n₀, _, c, hc, hg⟩ := paper_scale_geometric_after 0 N hN u hu hgap
  exact ⟨n₀, c, hc, hg⟩

end Lacunary.Transfer

/- Source module: TransferAlgebra. -/
namespace Lacunary.Transfer

/-- The selected threshold is strong enough to halve the convergent error.
The error lower bound is the ordinary two-sided CF bound. -/
theorem tail_lt_half_error
    {a b t tail ε : ℝ} (hab : 0 ≤ a + b)
    (ht : 4 * (a + b + 1) ≤ t)
    (htail : tail ≤ Real.exp (-t))
    (hε : (1 / 2 : ℝ) * Real.exp (-(a + b)) ≤ ε) :
    tail < ε / 2 := by
  have hl4 : Real.log (4 : ℝ) < 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have harg : -t < -(a + b) - Real.log 4 := by linarith
  have he := Real.exp_lt_exp.mpr harg
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at he
  linarith

/-- The reduced denominator of the selected truncation exceeds the old one. -/
theorem large_denominator_of_threshold
    {a b t V : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 4 * (a + b + 1) ≤ t)
    (hV : Real.exp (t / 2) ≤ V) :
    Real.exp a < V := by
  have ha' : a < t / 2 := by linarith
  exact (Real.exp_lt_exp.mpr ha').trans_le hV

/-- Triangle inequality supplies the finite error needed for Legendre. -/
theorem transferred_error_bound
    {x y r ε : ℝ} (hε : |x - r| = ε)
    (hclose : |x - y| < ε / 2) :
    |y - r| ≤ 3 * ε / 2 := by
  have ht := abs_sub_le y x r
  rw [abs_sub_comm y x, hε] at ht
  linarith

/-- A distinct truncation has strictly positive approximation error. -/
theorem transferred_error_pos {y r : ℝ} (hne : y ≠ r) : 0 < |y - r| :=
  abs_pos.mpr (sub_ne_zero.mpr hne)

/-- In the unbounded-gap case, the transferred error is in Legendre's range. -/
theorem transferred_error_lt_legendre
    {q qPlus δ : ℝ} (hq : 0 < q) (hgap : 6 * q < qPlus)
    (hδ : δ ≤ 3 / (2 * q * qPlus)) :
    δ < 1 / (2 * q ^ 2) := by
  have hqPlus : 0 < qPlus := by linarith
  apply hδ.trans_lt
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q * qPlus)
    (by positivity : (0 : ℝ) < 2 * q ^ 2)).2
  have h3 : 3 * q < qPlus := by linarith
  have hm := mul_lt_mul_of_pos_left h3 (show (0 : ℝ) < 2 * q by positivity)
  nlinarith

/-- The finite two-sided CF error bound gives the required lower bound on its
next denominator. The slightly stronger `qPlus/2` is available. -/
theorem next_denominator_of_error_bounds
    {q qPlus s δ : ℝ} (hq : 0 < q) (hs : 0 < s)
    (hgap : 6 * q < qPlus)
    (hlower : 1 / (q * (s + q)) ≤ δ)
    (hupper : δ ≤ 3 / (2 * q * qPlus)) :
    qPlus ≤ 6 * s := by
  have hqPlus : 0 < qPlus := by linarith
  have hc := (div_le_div_iff₀ (mul_pos hq (add_pos hs hq))
    (show (0 : ℝ) < 2 * q * qPlus by positivity)).mp (hlower.trans hupper)
  have hlin : 2 * qPlus ≤ 3 * (s + q) := by
    exact le_of_mul_le_mul_left (by nlinarith [hc] : q * (2 * qPlus) ≤ q * (3 * (s + q))) hq
  linarith

end Lacunary.Transfer

/- Source module: Section7. -/
namespace Lacunary.Transfer

/-- Normalizing the proved logarithmic profile gives every strict upper bound
on the eventual gap ratio. -/
theorem log_profile_ratio_eventually
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {κ K D : ℝ}
    (hκ : 0 ≤ κ) (ha : Tendsto a l atTop)
    (hab : ∀ᶠ i in l, a i ≤ b i)
    (hprofile : ∀ᶠ i in l,
      b i - a i ≤ κ * a i + K * Real.log (a i + b i + 2) + D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, (b i - a i) / a i ≤ κ + ε := by
  have hb := log_profile_eventually hκ ha hab hprofile hε
  have ha1 := tendsto_atTop.1 ha 1
  filter_upwards [hb, ha1] with i hi hi1
  exact (div_le_iff₀ (by linarith : 0 < a i)).2 hi

/-- Section 7's gap conclusion is an extended-real limsup statement; it does
not silently replace an infinite limsup by a finite real value. -/
theorem log_profile_gap_limsup_le
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {κ K D : ℝ}
    (hκ : 0 ≤ κ) (ha : Tendsto a l atTop)
    (hab : ∀ᶠ i in l, a i ≤ b i)
    (hprofile : ∀ᶠ i in l,
      b i - a i ≤ κ * a i + K * Real.log (a i + b i + 2) + D) :
    Filter.limsup (fun i => (((b i - a i) / a i : ℝ) : EReal)) l ≤ (κ : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hz' : κ < z := EReal.coe_lt_coe_iff.mp hz
  have hb := log_profile_ratio_eventually hκ ha hab hprofile (sub_pos.mpr hz')
  have hb' : ∀ᶠ i in l, (((b i - a i) / a i : ℝ) : EReal) ≤ (z : EReal) := by
    filter_upwards [hb] with i hi
    apply EReal.coe_le_coe_iff.mpr
    linarith
  exact Filter.limsup_le_of_le (h := hb')

/-- Paper §7 transfer, equations `eq:chosentruncation` through
`eq:infiniteprofile`, in scalar form.

`Gap n a g` denotes the actual finite CF gaps at truncation `n`. The index is
the least one at or above n₀ with t_n ≥ 4(a + b + 1); its logarithmic cost is
accounted for using selectedOffset_paper_bound. The CF-specific premise
`htransfer` places a large infinite gap at this selected truncation and gives
a finite next denominator at least qPlus/6. The subsequent logarithmic
bootstrap makes the accumulated profile cost negligible relative to a. -/
theorem finite_profile_transfer
    {ι : Type*} {l : Filter ι}
    (Gap : ℕ → ℝ → ℝ → Prop)
    (q qPlus : ι → ℝ) (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop)
    {c ρ κ A C : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hgrowth : ∀ m : ℕ, c * ρ ^ m ≤ t (n₀ + m))
    (hq : ∀ᶠ i in l, 0 < q i)
    (hnext : ∀ᶠ i in l, q i ≤ qPlus i)
    (ha : Tendsto (fun i => Real.log (q i)) l atTop)
    (hfinite : ∀ m a g, Gap (n₀ + m) a g →
      g ≤ κ * a + A + C * (m : ℝ))
    (htransfer : ∀ᶠ i in l, 6 * q i < qPlus i →
      ∃ s : ℝ, 0 < s ∧ qPlus i ≤ 6 * s ∧
        Gap (n₀ + selectedOffset t n₀ ht
          (4 * (Real.log (q i) + Real.log (qPlus i) + 1)))
          (Real.log (q i)) (Real.log s - Real.log (q i))) :
    ∀ᶠ i in l,
      Real.log (qPlus i) - Real.log (q i) ≤
        κ * Real.log (q i) + (C / Real.log ρ) *
          Real.log (Real.log (q i) + Real.log (qPlus i) + 2) +
        (A + C * ((Real.log 4 + |Real.log c|) / Real.log ρ + 1) + Real.log 6) := by
  have ha1 := tendsto_atTop.1 ha 1
  filter_upwards [hq, hnext, ha1, htransfer] with i hiq hinext hia hitransfer
  have hiqPlus : 0 < qPlus i := hiq.trans_le hinext
  have hab := Real.log_le_log hiq hinext
  have hsum : 0 ≤ Real.log (q i) + Real.log (qPlus i) := by linarith
  have hindex := selectedOffset_paper_bound t n₀ ht hc hρ hsum hgrowth
  by_cases hbounded : qPlus i ≤ 6 * q i
  · have hb := bounded_log_gap hiq hiqPlus hbounded
    have hnonneg : 0 ≤ (1 / Real.log ρ) *
        Real.log (Real.log (q i) + Real.log (qPlus i) + 2) +
        ((Real.log 4 + |Real.log c|) / Real.log ρ + 1) :=
      (Nat.cast_nonneg _).trans hindex
    have hCindex := mul_nonneg hC hnonneg
    have hκa := mul_nonneg hκ (show 0 ≤ Real.log (q i) by linarith)
    have hCindex' : 0 ≤ (C / Real.log ρ) *
        Real.log (Real.log (q i) + Real.log (qPlus i) + 2) +
        C * ((Real.log 4 + |Real.log c|) / Real.log ρ + 1) := by
      convert hCindex using 1; ring
    linarith
  · have hlarge : 6 * q i < qPlus i := lt_of_not_ge hbounded
    obtain ⟨s, hs, hden, hgap⟩ := hitransfer hlarge
    have hf := hfinite _ _ _ hgap
    have hg := log_gap_of_next_denominator hiq hiqPlus hs hden
    have hraw : Real.log (qPlus i) - Real.log (q i) ≤
        κ * Real.log (q i) + (A + Real.log 6) +
          C * (selectedOffset t n₀ ht
            (4 * (Real.log (q i) + Real.log (qPlus i) + 1)) : ℝ) := by linarith
    have hh := combine_finite_profile_index hC hraw hindex
    convert hh using 1; ring

/-- The finite profile and genuine CF transfer witness imply the limiting
infinite-CF gap bound. -/
theorem finite_profile_gap_limsup_le
    {ι : Type*} {l : Filter ι}
    (Gap : ℕ → ℝ → ℝ → Prop)
    (q qPlus : ι → ℝ) (t : ℕ → ℝ) (n₀ : ℕ)
    (ht : Tendsto (fun m => t (n₀ + m)) atTop atTop)
    {c ρ κ A C : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hgrowth : ∀ m : ℕ, c * ρ ^ m ≤ t (n₀ + m))
    (hq : ∀ᶠ i in l, 0 < q i)
    (hnext : ∀ᶠ i in l, q i ≤ qPlus i)
    (ha : Tendsto (fun i => Real.log (q i)) l atTop)
    (hfinite : ∀ m a g, Gap (n₀ + m) a g →
      g ≤ κ * a + A + C * (m : ℝ))
    (htransfer : ∀ᶠ i in l, 6 * q i < qPlus i →
      ∃ s : ℝ, 0 < s ∧ qPlus i ≤ 6 * s ∧
        Gap (n₀ + selectedOffset t n₀ ht
          (4 * (Real.log (q i) + Real.log (qPlus i) + 1)))
          (Real.log (q i)) (Real.log s - Real.log (q i))) :
    Filter.limsup (fun i =>
      (((Real.log (qPlus i) - Real.log (q i)) / Real.log (q i) : ℝ) : EReal)) l ≤
        (κ : EReal) := by
  have hp := finite_profile_transfer Gap q qPlus t n₀ ht hc hρ hκ hA hC
    hgrowth hq hnext ha hfinite htransfer
  apply log_profile_gap_limsup_le hκ ha _ hp
  filter_upwards [hq, hnext] with i hi hinext
  exact Real.log_le_log hi hinext

end Lacunary.Transfer

/- Source module: TransferWitness. -/
namespace Lacunary.Transfer

/-- Paper §7, equations `eq:transfererror` and `eq:transferlegendre`:
the threshold 4(a + b + 1), tail bound exp(-t), and reduced-denominator bound
exp(t/2) make the selected truncation distinct and close enough for Legendre.
The supplied recognition and finite-error bounds give next denominator at
least qPlus/6. -/
theorem rational_transfer_witness
    (Gap : ℕ → ℝ → ℝ → Prop) (n : ℕ)
    (x : ℝ) (y r : ℚ) {qPlus t : ℝ}
    (hgap : 6 * (r.den : ℝ) < qPlus)
    (ht : 4 * (Real.log (r.den : ℝ) + Real.log qPlus + 1) ≤ t)
    (htail : |x - (y : ℝ)| ≤ Real.exp (-t))
    (hV : Real.exp (t / 2) ≤ (y.den : ℝ))
    (hlower : 1 / ((r.den : ℝ) * (qPlus + (r.den : ℝ))) ≤ |x - (r : ℝ)|)
    (hupper : |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * qPlus))
    (hrecognize : r.den < y.den →
      0 < |(y : ℝ) - (r : ℝ)| →
      |(y : ℝ) - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2) →
      ∃ s : ℝ, 0 < s ∧
        Gap n (Real.log (r.den : ℝ)) (Real.log s - Real.log (r.den : ℝ)) ∧
        1 / ((r.den : ℝ) * (s + (r.den : ℝ))) ≤ |(y : ℝ) - (r : ℝ)|) :
    ∃ s : ℝ, 0 < s ∧ qPlus ≤ 6 * s ∧
      Gap n (Real.log (r.den : ℝ)) (Real.log s - Real.log (r.den : ℝ)) := by
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hqp : 0 < qPlus := by linarith
  have hqp1 : 1 ≤ qPlus := by linarith
  have ha : 0 ≤ Real.log (r.den : ℝ) := Real.log_nonneg hq1
  have hb : 0 ≤ Real.log qPlus := Real.log_nonneg hqp1
  have hlarge := large_denominator_of_threshold ha hb ht hV
  rw [Real.exp_log hq] at hlarge
  have hden : r.den < y.den := by exact_mod_cast hlarge
  have hne : y ≠ r := by
    intro heq
    have hh := congrArg Rat.den heq
    omega
  have hneR : (y : ℝ) ≠ (r : ℝ) := by exact_mod_cast hne
  have hpos := transferred_error_pos hneR
  have hexp : Real.exp (-(Real.log (r.den : ℝ) + Real.log qPlus)) =
      1 / ((r.den : ℝ) * qPlus) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hq, Real.exp_log hqp]
    simp only [one_div]
  have hεlower : (1 / 2 : ℝ) *
      Real.exp (-(Real.log (r.den : ℝ) + Real.log qPlus)) ≤ |x - (r : ℝ)| := by
    calc
      _ = 1 / (2 * (r.den : ℝ) * qPlus) := by rw [hexp]; ring
      _ ≤ 1 / ((r.den : ℝ) * (qPlus + (r.den : ℝ))) := by
        apply one_div_le_one_div_of_le (by positivity :
          (0 : ℝ) < (r.den : ℝ) * (qPlus + (r.den : ℝ)))
        nlinarith
      _ ≤ |x - (r : ℝ)| := hlower
  have hclose := tail_lt_half_error (show 0 ≤ Real.log (r.den : ℝ) + Real.log qPlus by linarith)
    ht htail hεlower
  have herr := transferred_error_bound (ε := |x - (r : ℝ)|) rfl hclose
  have herr' : |(y : ℝ) - (r : ℝ)| ≤ 3 / (2 * (r.den : ℝ) * qPlus) := by
    calc
      _ ≤ 3 * |x - (r : ℝ)| / 2 := herr
      _ ≤ 3 * (1 / ((r.den : ℝ) * qPlus)) / 2 := by gcongr
      _ = _ := by ring
  have hlegendre := transferred_error_lt_legendre hq hgap herr'
  obtain ⟨s, hs, hmem, hsLower⟩ := hrecognize hden hpos hlegendre
  exact ⟨s, hs, next_denominator_of_error_bounds hq hs hgap hsLower herr', hmem⟩

/-- The exponent upper bound, once the CF exponent identity has been proved
for the paper's definition of irrationality exponent. -/
theorem exponent_upper_of_gap_limsup
    (x : ℝ) (q qPlus : ℕ → ℝ) (κ : ℝ)
    (hidentity : Paper4.irrationalityExponent x = (2 : EReal) +
      Filter.limsup (fun i =>
        (((Real.log (qPlus i) - Real.log (q i)) / Real.log (q i) : ℝ) : EReal)) Filter.atTop)
    (hgap : Filter.limsup (fun i =>
      (((Real.log (qPlus i) - Real.log (q i)) / Real.log (q i) : ℝ) : EReal)) Filter.atTop ≤
        (κ : EReal)) :
    Paper4.irrationalityExponent x ≤ ((2 + κ : ℝ) : EReal) := by
  rw [hidentity]
  calc
    _ ≤ (2 : EReal) + (κ : EReal) := add_le_add (show (2 : EReal) ≤ 2 from le_rfl) hgap
    _ = ((2 + κ : ℝ) : EReal) := by norm_cast

end Lacunary.Transfer

#print axioms Lacunary.Transfer.log_profile_error_littleO
#print axioms Lacunary.Transfer.log_profile_bootstrap
#print axioms Lacunary.Transfer.log_profile_eventually
#print axioms Lacunary.Transfer.combine_finite_profile_index
#print axioms Lacunary.Transfer.log_gap_of_next_denominator
#print axioms Lacunary.Transfer.bounded_log_gap
#print axioms Lacunary.Transfer.geometric_step_of_paper_gap
#print axioms Lacunary.Transfer.geometric_lower_of_step
#print axioms Lacunary.Transfer.tendsto_scale_of_geometric
#print axioms Lacunary.Transfer.selectedOffset_spec
#print axioms Lacunary.Transfer.selectedOffset_min
#print axioms Lacunary.Transfer.selectedOffset_log_bound
#print axioms Lacunary.Transfer.selectedOffset_paper_bound
#print axioms Lacunary.Transfer.tendsto_selectedIndex
#print axioms Lacunary.Transfer.tendsto_selectedIndex_paper
#print axioms Lacunary.Transfer.paper_scale_strictMono
#print axioms Lacunary.Transfer.paper_scale_geometric_after
#print axioms Lacunary.Transfer.paper_scale_geometric
#print axioms Lacunary.Transfer.tail_lt_half_error
#print axioms Lacunary.Transfer.large_denominator_of_threshold
#print axioms Lacunary.Transfer.transferred_error_bound
#print axioms Lacunary.Transfer.transferred_error_pos
#print axioms Lacunary.Transfer.transferred_error_lt_legendre
#print axioms Lacunary.Transfer.next_denominator_of_error_bounds
#print axioms Lacunary.Transfer.log_profile_ratio_eventually
#print axioms Lacunary.Transfer.log_profile_gap_limsup_le
#print axioms Lacunary.Transfer.finite_profile_transfer
#print axioms Lacunary.Transfer.finite_profile_gap_limsup_le
#print axioms Lacunary.Transfer.rational_transfer_witness
#print axioms Lacunary.Transfer.exponent_upper_of_gap_limsup

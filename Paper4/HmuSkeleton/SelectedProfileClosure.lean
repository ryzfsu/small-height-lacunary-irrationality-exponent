/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.ScalarTransfer
public import Paper4.HmuSkeleton.CFProfileTransfer
public import Paper4.Arithmetic.Definitions
public import Paper4.Arithmetic.RawTailAdapter

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter Asymptotics Lacunary.Transfer
open scoped Topology

/-- The finite target is the actual rational truncation, and the returned gap
is an actual `CFGap` supplied by Legendre. -/
theorem selected_rational_gap_transfer
    {x : ℝ} (G : CFGap x) (y : ℚ) {s : ℝ}
    (hlarge : 6 * (G.value.den : ℝ) < (G.nextDen : ℝ))
    (hthreshold : 4 * (G.left + G.right + 1) ≤ s)
    (htail : |x - (y : ℝ)| ≤ Real.exp (-s))
    (hden : Real.exp (s / 2) ≤ (y.den : ℝ)) :
    ∃ S : ℝ, 0 < S ∧ (G.nextDen : ℝ) ≤ 6 * S ∧
      LogGap (y : ℝ) G.left (Real.log S - G.left) := by
  have hb := cfGap_bounds G
  apply rational_transfer_witness
    (fun _ a g => LogGap (y : ℝ) a g) 0 x y G.value
    hlarge hthreshold htail hden hb.2.2.1 hb.2.2.2
  intro _ hpos hleg
  have hne : (y : ℝ) ≠ (G.value : ℝ) := by
    intro heq
    simpa [heq] using hpos
  obtain ⟨H, hv⟩ := cfGap_legendre hne hleg
  refine ⟨(H.nextDen : ℝ), ?_, ?_, ?_⟩
  · exact_mod_cast (cfGap_bounds H).1
  · refine ⟨H, ?_, ?_⟩
    · simp [CFGap.left, hv]
    · simp [CFGap.width, CFGap.right, CFGap.left, hv]
  · simpa [hv] using (cfGap_bounds H).2.2.1

/-- This bridge retains the logarithmic selected-index cost. It does not infer
an actual profile from a selector threshold alone. -/
theorem actual_profile_of_finite_profiles
    {x F : ℝ} (hx : Irrational x) (hF : 2 ≤ F)
    (y : ℕ → ℚ) (t : ℕ → ℝ)
    (hmono : Monotone t)
    (hgrowth : ∀ nbase : ℕ, ∃ n₀ : ℕ, nbase ≤ n₀ ∧
      ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
        c * (3 / 2 : ℝ) ^ m ≤ t (n₀ + m))
    (htransfer : ∀ᶠ n : ℕ in atTop,
      |x - (y n : ℝ)| ≤ Real.exp (-t n) ∧
      Real.exp (t n / 2) ≤ ((y n).den : ℝ))
    (hfinite : ∀ κ : ℝ, F - 2 < κ →
      ∃ nbase : ℕ, ∃ A : ℝ, Real.log 6 ≤ A ∧
        ∀ n ≥ nbase, ∀ a g,
          LogGap (y n : ℝ) a g →
          g ≤ κ * a + A + Real.log 6 * ((n - nbase : ℕ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      Real.log (cfQ x (j + 1) : ℝ) - Real.log (cfQ x j : ℝ) ≤
        (F - 2 + ε) * Real.log (cfQ x j : ℝ) := by
  intro ε hε
  let κ := F - 2 + ε / 2
  have hk : F - 2 < κ := by dsimp [κ]; linarith
  have hk0 : 0 ≤ κ := by dsimp [κ]; linarith
  obtain ⟨nbase, A, hA, hfin⟩ := hfinite κ hk
  obtain ⟨n₀, hn₀, c, hc, hgeom⟩ := hgrowth nbase
  have ht := tendsto_scale_of_geometric hc (by norm_num : (1 : ℝ) < 3 / 2) hgeom
  let a : ℕ → ℝ := fun j => Real.log (cfQ x j : ℝ)
  let b : ℕ → ℝ := fun j => Real.log (cfQ x (j + 1) : ℝ)
  have ha : Tendsto a atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_iff).2 (cfQ_tendsto hx))
  have hab : ∀ᶠ j : ℕ in atTop, a j ≤ b j := by
    apply Eventually.of_forall
    intro j
    exact Real.log_le_log (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (cfQ_ge_two hx j))
      (by exact_mod_cast cfQ_mono hx j)
  let sel : ℕ → ℕ := fun j =>
    n₀ + selectedOffset t n₀ ht (4 * (a j + b j + 1))
  have hsel : Tendsto sel atTop atTop :=
    tendsto_selectedIndex_paper t n₀ ht hmono ha hab
  have hq : ∀ᶠ j : ℕ in atTop, 0 < (cfQ x j : ℝ) := by
    apply Eventually.of_forall
    intro j
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (cfQ_ge_two hx j)
  have hnext : ∀ᶠ j : ℕ in atTop, (cfQ x j : ℝ) ≤ cfQ x (j + 1) := by
    apply Eventually.of_forall
    intro j
    exact_mod_cast cfQ_mono hx j
  have hC : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hA0 : 0 ≤ A := hC.trans hA
  let A' := A + Real.log 6 * ((n₀ - nbase : ℕ) : ℝ)
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  have hfin' : ∀ m a g, LogGap (y (n₀ + m) : ℝ) a g →
      g ≤ κ * a + A' + Real.log 6 * (m : ℝ) := by
    intro m a g hg
    have hh := hfin (n₀ + m) (by omega) a g hg
    have heq : n₀ + m - nbase = (n₀ - nbase) + m := by omega
    rw [heq, Nat.cast_add] at hh
    dsimp [A']
    nlinarith
  have htr : ∀ᶠ j : ℕ in atTop,
      6 * (cfQ x j : ℝ) < (cfQ x (j + 1) : ℝ) →
        ∃ S : ℝ, 0 < S ∧ (cfQ x (j + 1) : ℝ) ≤ 6 * S ∧
          LogGap (y (sel j) : ℝ) (a j) (Real.log S - a j) := by
    filter_upwards [hsel.eventually htransfer] with j hj
    intro hjlarge
    let G : CFGap x :=
      { index := j + 2
        value := cfRat x (j + 2)
        nextDen := cfQ x (j + 1)
        nonterminal := irrational_not_terminated hx (j + 2)
        value_eq := cfRat_spec x (j + 2)
        nextDen_eq := by
          simpa only [show j + 2 + 1 = j + 1 + 2 by omega] using cfQ_dens hx (j + 1) }
    have hleft : G.left = a j := rfl
    have hright : G.right = b j := rfl
    have hh : 4 * (G.left + G.right + 1) ≤ t (sel j) :=
      selectedOffset_spec t n₀ ht _
    simpa only [hleft] using
      selected_rational_gap_transfer G (y (sel j)) hjlarge hh hj.1 hj.2
  have hprof := finite_profile_transfer
    (fun n a g => LogGap (y n : ℝ) a g)
    (fun j => (cfQ x j : ℝ)) (fun j => (cfQ x (j + 1) : ℝ))
    t n₀ ht hc (by norm_num : (1 : ℝ) < 3 / 2) hk0 hA' hC hgeom
    hq hnext ha hfin' htr
  have he := log_profile_eventually hk0 ha hab hprof (show 0 < ε / 2 by linarith)
  filter_upwards [he] with j hj
  dsimp [a, b, κ] at hj
  convert hj using 1 <;> ring

/-- Consume the exact current perturbation contract on the same rational
sequence; no global reflected-gap witness is assumed. -/
theorem finite_profiles_of_rational_perturbation
    (y δ : ℕ → ℚ) (F : ℝ) (hF : 2 ≤ F)
    (hsucc : ∀ n, y (n + 1) = y n + δ n)
    (hδ : ∀ᶠ n : ℕ in atTop, δ n ≠ 0)
    (hM : Tendsto (fun n => Real.log ((y n).den : ℝ)) atTop atTop)
    (hE : (fun n => Real.log (4 * (coordinateDen (y n) (δ n) : ℝ)))
      =o[atTop] (fun n => Real.log ((y n).den : ℝ)))
    (hLlo : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (2 - ε) * Real.log ((y n).den : ℝ) ≤ -Real.log |(δ n : ℝ)|)
    (hLhi : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      -Real.log |(δ n : ℝ)| ≤ (F + ε) * Real.log ((y n).den : ℝ)) :
    ∀ κ : ℝ, F - 2 < κ →
      ∃ nbase : ℕ, ∃ A : ℝ, Real.log 6 ≤ A ∧
        ∀ n ≥ nbase, ∀ a g,
          LogGap (y n : ℝ) a g →
          g ≤ κ * a + A + Real.log 6 * ((n - nbase : ℕ) : ℝ) := by
  intro κ hk
  apply uniform_finite_profile
    (fun n a g => LogGap (y n : ℝ) a g)
    (fun n => Real.log ((y n).den : ℝ))
    (fun n => -Real.log |(δ n : ℝ)|)
    (fun n => Real.log (4 * (coordinateDen (y n) (δ n) : ℝ)))
    F (Real.log 6) (Real.log (3 / 2 : ℝ)) hF
    (Real.log_nonneg (by norm_num)) hM hE hLlo hLhi
    (fun n => rational_gap_finite (y n))
    (fun n a g hg => (rational_gap_range hg).1)
    (fun n a g hg => (rational_gap_range hg).2.2) ?_ hk
  have hden : ∀ᶠ n : ℕ in atTop, 2 ≤ (y n).den := by
    filter_upwards [hM.eventually (eventually_gt_atTop (Real.log 2))] with n hn
    have hh : (2 : ℝ) < ((y n).den : ℝ) :=
      (Real.log_lt_log_iff (by norm_num) (by positivity)).1 hn
    exact_mod_cast hh.le
  filter_upwards [hden, hδ] with n hn hδn
  intro a g hg
  rw [hsucc] at hg
  exact rational_perturbation (y n) (δ n) hn hδn hg

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.selected_rational_gap_transfer
#print axioms Paper4.HmuSkeleton.actual_profile_of_finite_profiles
#print axioms Paper4.HmuSkeleton.finite_profiles_of_rational_perturbation

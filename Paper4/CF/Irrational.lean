/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.CF.Bridge
public import Mathlib

@[expose] public section

namespace Paper4

open Filter GenContFract Lacunary.CFBridge
open scoped Topology

/-- The rational value of the actual `n`th convergent. -/
noncomputable def cfRat (x : ℝ) (n : ℕ) : ℚ :=
  Classical.choose (GenContFract.exists_rat_eq_nth_conv x n)

theorem cfRat_spec (x : ℝ) (n : ℕ) :
    (GenContFract.of x).convs n = (cfRat x n : ℝ) :=
  Classical.choose_spec (GenContFract.exists_rat_eq_nth_conv x n)

theorem irrational_not_terminated {x : ℝ} (hx : Irrational x) (n : ℕ) :
    ¬(GenContFract.of x).TerminatedAt n := by
  intro ht
  exact hx.ne_rat _ ((GenContFract.of_correctness_of_terminatedAt ht).trans (cfRat_spec x n))

/-- Shift by two so that every denominator is at least two. -/
noncomputable def cfP (x : ℝ) (n : ℕ) : ℤ := (cfRat x (n + 2)).num
noncomputable def cfQ (x : ℝ) (n : ℕ) : ℕ := (cfRat x (n + 2)).den

theorem cf_convs (x : ℝ) (n : ℕ) :
    (GenContFract.of x).convs (n + 2) = (cfP x n : ℝ) / (cfQ x n : ℝ) := by
  exact (cfRat_spec x (n + 2)).trans (Rat.cast_def _)

theorem cfQ_dens {x : ℝ} (hx : Irrational x) (n : ℕ) :
    (GenContFract.of x).dens (n + 2) = (cfQ x n : ℝ) :=
  (nonterminal_num_den (cfRat_spec x (n + 2)) (irrational_not_terminated hx (n + 2))).2

theorem cfQ_fib_le {x : ℝ} (hx : Irrational x) (n : ℕ) : Nat.fib (n + 3) ≤ cfQ x n := by
  have hf := GenContFract.succ_nth_fib_le_of_nth_den (v := x) (n := n + 2)
    (Or.inr (irrational_not_terminated hx (n + 2 - 1)))
  rw [cfQ_dens hx n] at hf
  exact_mod_cast hf

theorem cfQ_ge_two {x : ℝ} (hx : Irrational x) (n : ℕ) : 2 ≤ cfQ x n := by
  calc
    2 = Nat.fib 3 := rfl
    _ ≤ Nat.fib (n + 3) := Nat.fib_mono (by omega)
    _ ≤ cfQ x n := cfQ_fib_le hx n

theorem cfQ_mono {x : ℝ} (hx : Irrational x) (n : ℕ) : cfQ x n ≤ cfQ x (n + 1) := by
  have hm : (GenContFract.of x).dens (n + 2) ≤ (GenContFract.of x).dens (n + 2 + 1) := of_den_mono
  have heq : n + 2 + 1 = n + 1 + 2 := by omega
  rw [heq, cfQ_dens hx n, cfQ_dens hx (n + 1)] at hm
  exact_mod_cast hm

theorem cfQ_tendsto {x : ℝ} (hx : Irrational x) : Tendsto (cfQ x) atTop atTop := by
  apply tendsto_atTop_mono (fun n => show n ≤ cfQ x n from ?_) tendsto_id
  by_cases hn : 2 ≤ n
  · exact (Nat.le_add_right n 3).trans ((Nat.le_fib_self (by omega : 5 ≤ n + 3)).trans (cfQ_fib_le hx n))
  · exact (show n ≤ 2 by omega).trans (cfQ_ge_two hx n)

theorem cf_upper {x : ℝ} (hx : Irrational x) (n : ℕ) :
    |x - (cfP x n : ℝ) / (cfQ x n : ℝ)| ≤
      1 / ((cfQ x n : ℝ) * (cfQ x (n + 1) : ℝ)) := by
  have h := error_upper (irrational_not_terminated hx (n + 2))
  have heq : n + 2 + 1 = n + 1 + 2 := by omega
  rw [cf_convs, heq, cfQ_dens hx n, cfQ_dens hx (n + 1)] at h
  exact h

theorem cf_lower {x : ℝ} (hx : Irrational x) (n : ℕ) :
    1 / (2 * (cfQ x n : ℝ) * (cfQ x (n + 1) : ℝ)) ≤
      |x - (cfP x n : ℝ) / (cfQ x n : ℝ)| := by
  have h := error_lower (irrational_not_terminated hx (n + 2))
  have heq : n + 2 + 1 = n + 1 + 2 := by omega
  rw [cf_convs, heq, cfQ_dens hx n, cfQ_dens hx (n + 1)] at h
  have hq : (0 : ℝ) < cfQ x n := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (cfQ_ge_two hx n)
  have hqn : (0 : ℝ) < cfQ x (n + 1) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (cfQ_ge_two hx (n + 1))
  have hm : (cfQ x n : ℝ) ≤ cfQ x (n + 1) := by exact_mod_cast cfQ_mono hx n
  apply le_trans _ h
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  nlinarith

/-- Reduction cannot increase a rational's supplied positive denominator. -/
theorem rat_div_nat_den_le (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((a : ℚ) / (b : ℚ)).den ≤ b := by
  have hi : (((a : ℚ) / (b : ℚ)).den : ℤ) ∣ (b : ℤ) := by
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd a (b : ℤ)
  have hn : ((a : ℚ) / (b : ℚ)).den ∣ b := by exact_mod_cast hi
  exact Nat.le_of_dvd hb hn

/-- Legendre approximations with large supplied denominator occur arbitrarily late in the
shifted sequence, even when the supplied fraction is not reduced. -/
theorem cf_legendre_eventually {x : ℝ} (hx : Irrational x) (N : ℕ) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      |x - (a : ℝ) / (b : ℝ)| < 1 / (2 * (b : ℝ) ^ 2) →
        ∃ n : ℕ, N ≤ n ∧ cfQ x n ≤ b ∧
          (a : ℝ) / (b : ℝ) = (cfP x n : ℝ) / (cfQ x n : ℝ) := by
  have hlim : Tendsto (fun b : ℕ => (b : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall (i : Fin (N + 2)) :
      ∀ᶠ b : ℕ in atTop, (b : ℝ)⁻¹ < |x - (GenContFract.of x).convs i.val| := by
    have hne : x ≠ (GenContFract.of x).convs i.val := by
      rw [cfRat_spec]
      exact hx.ne_rat _
    exact (tendsto_order.1 hlim).2 _ (abs_pos.2 (sub_ne_zero.2 hne))
  have hall : ∀ᶠ b : ℕ in atTop, ∀ i : Fin (N + 2),
      (b : ℝ)⁻¹ < |x - (GenContFract.of x).convs i.val| :=
    Filter.eventually_all.2 hsmall
  filter_upwards [hall, eventually_ge_atTop 1] with b hprefix hb
  intro a ha
  let r : ℚ := (a : ℚ) / (b : ℚ)
  have hr : (r : ℝ) = (a : ℝ) / (b : ℝ) := by simp [r]
  have hbr : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : 0 < b := by omega
  have hden : r.den ≤ b := rat_div_nat_den_le a b hbpos
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hdb : (r.den : ℝ) ≤ b := by exact_mod_cast hden
  have hleg : |x - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2) := by
    rw [hr]
    apply lt_of_lt_of_le ha
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    nlinarith
  obtain ⟨k, hk, hnt⟩ := legendre_nonterminal hleg (hx.ne_rat r)
  have hklarge : N + 2 ≤ k := by
    by_contra hkn
    have hkl : k < N + 2 := by omega
    have hpre := hprefix ⟨k, hkl⟩
    have hinv : 1 / (2 * (b : ℝ) ^ 2) ≤ (b : ℝ)⁻¹ := by
      rw [← one_div]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      nlinarith
    rw [hk, hr] at hpre
    linarith
  let n := k - 2
  have hn : n + 2 = k := by dsimp [n]; omega
  have heqRat : cfRat x k = r := by
    have heq : (cfRat x k : ℝ) = (r : ℝ) := (cfRat_spec x k).symm.trans hk
    exact_mod_cast heq
  refine ⟨n, by dsimp [n]; omega, ?_, ?_⟩
  · simpa only [cfQ, hn, heqRat] using hden
  · have hc := cf_convs x n
    rw [hn, hk, hr] at hc
    exact hc

end Paper4

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.OneDivSeparation
public import Mathlib

open Filter
open scoped Topology

@[expose] public section

namespace Paper4

/--
  An unreduced integer-over-positive-natural rational approximation is separated
  from a fixed rational by the reciprocal of the fixed rational's denominator.

  The only arithmetic input is the preceding integer cross-product lemma.  The
  sequence `s` is retained as an explicit adapter so an eventual nonzero-tail
  theorem can be passed without changing its normalization.
-/
theorem raw_rational_separation
    {x : ℝ} {s : ℕ → ℝ} {S : ℕ → ℤ} {Q : ℕ → ℕ}
    (hQ : ∀ n, 0 < Q n)
    (hrep : ∀ n, s n = (S n : ℝ) / (Q n : ℝ))
    (hne : ∀ᶠ n : ℕ in atTop, x ≠ s n) :
    ∀ r : ℚ, x = (r : ℝ) →
      ∀ᶠ n : ℕ in atTop,
        1 / (r.den : ℝ) ≤
          (Q n : ℝ) * |x - (S n : ℝ) / (Q n : ℝ)| := by
  intro r hxr
  filter_upwards [hne] with n hn
  have hfrac_ne : x ≠ (S n : ℝ) / (Q n : ℝ) := by
    intro heq
    apply hn
    exact heq.trans (hrep n).symm
  have hcross : r.num * (Q n : ℤ) - S n * (r.den : ℤ) ≠ 0 := by
    intro hzero
    have hcross_eq : r.num * (Q n : ℤ) = S n * (r.den : ℤ) :=
      sub_eq_zero.mp hzero
    have hQne : (Q n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hQ n))
    have hrat : (r : ℝ) = (S n : ℝ) / (Q n : ℝ) := by
      rw [Rat.cast_def]
      apply (div_eq_div_iff (by positivity) hQne).2
      exact_mod_cast hcross_eq
    exact hfrac_ne (hxr.trans hrat)
  have hraw :=
    one_div_mul_le_abs_sub_div
      (A := r.num) (B := r.den) (C := S n) (D := Q n)
      r.den_pos (hQ n) hcross
  have hmul := mul_le_mul_of_nonneg_left hraw
      (by positivity : (0 : ℝ) ≤ (Q n : ℝ))
  have hQne : (Q n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hQ n))
  calc
    1 / (r.den : ℝ) =
        (Q n : ℝ) * (1 / ((r.den : ℝ) * (Q n : ℝ))) := by
      field_simp [hQne]
    _ ≤ (Q n : ℝ) *
          |(r.num : ℝ) / (r.den : ℝ) - (S n : ℝ) / (Q n : ℝ)| := hmul
    _ = (Q n : ℝ) *
          |(r : ℝ) - (S n : ℝ) / (Q n : ℝ)| := by
      rw [Rat.cast_def]
    _ = (Q n : ℝ) *
          |x - (S n : ℝ) / (Q n : ℝ)| := by
      rw [← hxr]

/--
  A vanishing raw-denominator error is incompatible with rationality.  This is
  the downstream consumer of `raw_rational_separation`; it does not infer an
  irrationality exponent or use a reduced denominator.
-/
theorem irrational_of_tendsto_mul_error_of_ratSep
    {x : ℝ} {P : ℕ → ℤ} {q : ℕ → ℕ}
    (hlim : Tendsto
      (fun n : ℕ => (q n : ℝ) *
        |x - (P n : ℝ) / (q n : ℝ)|)
      atTop (𝓝 0))
    (hsep : ∀ r : ℚ, x = (r : ℝ) →
      ∀ᶠ n : ℕ in atTop,
        1 / (r.den : ℝ) ≤
          (q n : ℝ) * |x - (P n : ℝ) / (q n : ℝ)|) :
    Irrational x := by
  rw [Irrational]
  rintro ⟨r, hxr⟩
  have hrpos : 0 < (1 / (r.den : ℝ)) := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (q n : ℝ) * |x - (P n : ℝ) / (q n : ℝ)| <
        1 / (r.den : ℝ) :=
    (tendsto_order.1 hlim).2 _ hrpos
  have hlower := hsep r hxr.symm
  rcases (hsmall.and hlower).exists with ⟨n, hn, hln⟩
  exact (not_lt_of_ge hln) hn

end Paper4

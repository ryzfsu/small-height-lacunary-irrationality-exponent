/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Exponent.Formula

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/-- Eventual logarithmic gap bounds give the upper exponent, with the full
`forall ε > 0` order visible at the interface. -/
theorem cfExponentCandidate_le_of_gap_profile {q : ℕ → ℕ} {F : ℝ}
    (hq2 : ∀ n, 2 ≤ q n)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (q (n + 1) : ℝ) - Real.log (q n : ℝ) ≤
        (F - 2 + ε) * Real.log (q n : ℝ)) :
    cfExponentCandidate q ≤ (F : EReal) := by
  have hL : limsup (fun n => (cfLogRatio q n : EReal)) atTop ≤
      ((F - 1 : ℝ) : EReal) := by
    apply (limsup_le_iff).2
    intro y hy
    obtain ⟨r, hr, hry⟩ := EReal.exists_rat_btwn_of_lt hy
    have hε : 0 < (r : ℝ) - (F - 1) := by
      exact sub_pos.2 (EReal.coe_lt_coe_iff.1 hr)
    apply (hgap ((r : ℝ) - (F - 1)) hε).mono
    intro n hn
    have hlog : 0 < Real.log (q n : ℝ) :=
      Real.log_pos (by exact_mod_cast
        (lt_of_lt_of_le (by decide : 1 < 2) (hq2 n)))
    have hratio : cfLogRatio q n ≤ (r : ℝ) := by
      rw [cfLogRatio, div_le_iff₀ hlog]
      nlinarith
    exact (EReal.coe_le_coe hratio).trans_lt hry
  calc cfExponentCandidate q ≤ (1 : EReal) + ((F - 1 : ℝ) : EReal) :=
      add_le_add le_rfl hL
    _ = (F : EReal) := by
      rw [← EReal.coe_one, ← EReal.coe_add]
      congr 1
      ring

/-- Section 7's transferred profile closes the upper bound on the exact real
whose actual convergents satisfy the profile. -/
theorem irrationalityExponent_le_of_cf_gap_profile {x F : ℝ}
    (hx : Irrational x)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
        (F - 2 + ε) * Real.log (cfQ x n : ℝ)) :
    irrationalityExponent x ≤ (F : EReal) := by
  rw [irrationalityExponent_cf_formula hx]
  exact cfExponentCandidate_le_of_gap_profile (cfQ_ge_two hx) hgap

/-- A lower truncation package only needs to turn each strict finite threshold
below the desired value into frequent unit-constant approximations. This also
handles `F = ⊤` without a separate finite-valued argument. -/
theorem lower_exponent_of_truncation_thresholds
    {x : ℝ} {F : EReal} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hlower : ∀ ν : ℝ, (ν : EReal) < F →
      ∃ᶠ n : ℕ in atTop, 0 < q n ∧
        |x - (p n : ℝ) / (q n : ℝ)| < (q n : ℝ) ^ (-ν)) :
    F ≤ irrationalityExponent x := by
  apply le_irrationalityExponent_of_threshold
  intro ν hν
  apply exponentAdmissible_of_sequence hq
  exact (hlower ν hν).mono (fun n hn => ⟨p n, hn⟩)

/-- A finite upper CF profile and a truncation lower package prove equality. -/
theorem irrationalityExponent_eq_of_cf_profile_and_truncations
    {x F : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hx : Irrational x) (hq : Tendsto q atTop atTop)
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
        (F - 2 + ε) * Real.log (cfQ x n : ℝ))
    (hlower : ∀ ν : ℝ, ν < F →
      ∃ᶠ n : ℕ in atTop, 0 < q n ∧
        |x - (p n : ℝ) / (q n : ℝ)| < (q n : ℝ) ^ (-ν)) :
    irrationalityExponent x = (F : EReal) := by
  exact le_antisymm (irrationalityExponent_le_of_cf_gap_profile hx hgap)
    (lower_exponent_of_truncation_thresholds hq (by
      intro ν hν
      exact hlower ν (EReal.coe_lt_coe_iff.1 hν)))

#print axioms irrationalityExponent_le_of_cf_gap_profile
#print axioms irrationalityExponent_eq_of_cf_profile_and_truncations

end Paper4

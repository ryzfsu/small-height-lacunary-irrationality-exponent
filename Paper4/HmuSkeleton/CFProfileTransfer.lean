/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

module

public import Paper4.HmuSkeleton.UniformProfile
public import Paper4.CF.Irrational
public import Paper4.CF.Gap
public import Paper4.Exponent.FiniteClosure
import Mathlib.Tactic

/-!
# Continued-fraction gap profiles

An eventual additive bound on logarithmic denominator gaps gives the normalized
limsup bound. The resulting profile supplies the upper bound for the
irrationality exponent through the actual continued-fraction denominators.
-/

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter
open scoped Topology

theorem actual_cf_gap_from_legendre
    {x : ℝ} {r : ℚ} (hne : x ≠ (r : ℝ))
    (h : |x - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2)) :
    ∃ G : CFGap x, G.value = r := by
  exact cfGap_legendre hne h

/--
An eventual additive log-gap profile implies the normalized limsup bound.
The limit hypothesis supplies eventual positivity of the logarithmic denominator.
-/
theorem actual_cf_gap_profile_limsup_le_of_eventual
    {ι : Type*} {l : Filter ι}
    (q qPlus : ι → ℝ) (κ : ℝ)
    (ha : Tendsto (fun i => Real.log (q i)) l atTop)
    (hprofile : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      Real.log (qPlus i) - Real.log (q i) ≤
        (κ + ε) * Real.log (q i)) :
    Filter.limsup (fun i =>
      (((Real.log (qPlus i) - Real.log (q i)) /
        Real.log (q i) : ℝ) : EReal)) l ≤ (κ : EReal) := by
  apply (Filter.limsup_le_iff).2
  intro y hy
  obtain ⟨r, hr, hry⟩ := EReal.exists_rat_btwn_of_lt hy
  have hε : 0 < (r : ℝ) - κ := sub_pos.2 (EReal.coe_lt_coe_iff.1 hr)
  have hlog : ∀ᶠ i in l, 0 < Real.log (q i) :=
    ha.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hprofile ((r : ℝ) - κ) hε, hlog] with i hgi hli
  have hratio :
      (Real.log (qPlus i) - Real.log (q i)) /
          Real.log (q i) ≤ (r : ℝ) := by
    rw [div_le_iff₀ hli]
    simpa only [add_comm κ, sub_add_cancel] using hgi
  exact (EReal.coe_le_coe hratio).trans_lt hry

/- The arithmetic/CF output is specialized to the actual shifted sequence
   `cfQ`; the conclusion preserves the epsilon-first eventual quantifiers. -/
theorem actual_cf_gap_profile
    {x F : ℝ} (hx : Irrational x)
    (hlimsup : Filter.limsup (fun n =>
      (((Real.log (cfQ x (n + 1) : ℝ) -
        Real.log (cfQ x n : ℝ)) /
        Real.log (cfQ x n : ℝ) : ℝ) : EReal)) atTop ≤
      ((F - 2 : ℝ) : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
        (F - 2 + ε) * Real.log (cfQ x n : ℝ) := by
  intro ε hε
  have hκlt : ((F - 2 : ℝ) : EReal) < ((F - 2 + ε : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.2 (lt_add_of_pos_right (F - 2) hε)
  rw [Filter.limsup_le_iff] at hlimsup
  have hev := hlimsup ((F - 2 + ε : ℝ) : EReal) hκlt
  filter_upwards [hev] with n hn
  have hlog : 0 < Real.log (cfQ x n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (cfQ_ge_two hx n))
  exact le_of_lt ((div_lt_iff₀ hlog).1 (EReal.coe_lt_coe_iff.1 hn))

theorem hmu_upper_of_actual_cf_profile
    {x F : ℝ} (hx : Irrational x)
    (hprofile : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
        (F - 2 + ε) * Real.log (cfQ x n : ℝ)) :
    irrationalityExponent x ≤ (F : EReal) := by
  exact irrationalityExponent_le_of_cf_gap_profile hx hprofile

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.actual_cf_gap_profile_limsup_le_of_eventual
#print axioms Paper4.HmuSkeleton.actual_cf_gap_profile
#print axioms Paper4.HmuSkeleton.hmu_upper_of_actual_cf_profile

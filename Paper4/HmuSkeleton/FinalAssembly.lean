/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.TopBranch
public import Paper4.HmuSkeleton.CFProfileTransfer
public import Paper4.Exponent.FiniteClosure
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter
open scoped Topology

theorem hmu_finite_of_profile_and_truncations
    {x F : ℝ}
    {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hx : Irrational x)
    (hq : Tendsto q atTop atTop)
    (hprofile : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
        (F - 2 + ε) * Real.log (cfQ x n : ℝ))
    (htrunc : ∀ ν : ℝ, ν < F → ∃ᶠ n : ℕ in atTop,
      0 < q n ∧ |x - (p n : ℝ) / (q n : ℝ)| <
        (q n : ℝ) ^ (-ν)) :
    irrationalityExponent x = (F : EReal) := by
  exact irrationalityExponent_eq_of_cf_profile_and_truncations
    hx hq hprofile htrunc

theorem hmu_of_R_packages
    {x : ℝ} {R : EReal}
    {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hx : Irrational x)
    (hR2 : (2 : EReal) ≤ R)
    (hfinite : R ≠ (⊤ : EReal) → ∃ F : ℝ, (F : EReal) = R)
    (hq : Tendsto q atTop atTop)
    (htrunc : ∀ ν : ℝ, (ν : EReal) < R → ∃ᶠ n : ℕ in atTop,
      0 < q n ∧ |x - (p n : ℝ) / (q n : ℝ)| <
        (q n : ℝ) ^ (-ν))
    (hprofile : ∀ F : ℝ, (F : EReal) = R → (2 : ℝ) ≤ F →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
          (F - 2 + ε) * Real.log (cfQ x n : ℝ)) :
    irrationalityExponent x = R := by
  by_cases hTop : R = (⊤ : EReal)
  · exact hmu_top_branch hTop hq htrunc
  · obtain ⟨F, rfl⟩ := hfinite hTop
    exact hmu_finite_of_profile_and_truncations hx hq
      (hprofile F rfl (EReal.coe_le_coe_iff.1 hR2))
      (fun ν hν => htrunc ν (EReal.coe_lt_coe_iff.2 hν))

theorem two_le_exponentRatio_limsup
    {u : ℕ → ℕ}
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) :
    (2 : EReal) ≤ Filter.limsup
      (fun j => (exponentRatio u j : EReal)) atTop := by
  by_contra hnot
  have hRlt : Filter.limsup
      (fun j => (exponentRatio u j : EReal)) atTop < (2 : EReal) :=
    lt_of_not_ge hnot
  obtain ⟨r, hrR, hr2⟩ := EReal.exists_rat_btwn_of_lt hRlt
  have hε : 0 < (2 : ℝ) - (r : ℝ) := by
    exact sub_pos.mpr (EReal.coe_lt_coe_iff.1 hr2)
  have hev := hgap ((2 : ℝ) - (r : ℝ)) hε
  have hfreq : ∃ᶠ j : ℕ in atTop,
      ((r : ℝ) : EReal) ≤ (exponentRatio u j : EReal) :=
    (hev.mono (fun j hj =>
      EReal.coe_le_coe (by linarith))).frequently
  have hle : ((r : ℝ) : EReal) ≤
      Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop :=
    le_limsup_of_frequently_le hfreq
      (Filter.isBoundedUnder_of_eventually_le (a := ⊤)
        (Filter.Eventually.of_forall fun _ => le_top))
  exact (not_lt_of_ge hle) hrR

/- The series-level contract combines the finite and infinite branches
   with the explicit truncation lower-bound hypotheses. -/
theorem final_hmu_assembly_contract
    {x : ℝ} {R : EReal}
    {u : ℕ → ℕ}
    {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hx : Irrational x)
    (hR : R = Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop)
    (hR2 : (2 : EReal) ≤ R)
    (hfinite : R ≠ (⊤ : EReal) → ∃ F : ℝ, (F : EReal) = R)
    (hq : Tendsto q atTop atTop)
    (htrunc : ∀ ν : ℝ, (ν : EReal) < R → ∃ᶠ n : ℕ in atTop,
      0 < q n ∧ |x - (p n : ℝ) / (q n : ℝ)| <
        (q n : ℝ) ^ (-ν))
    (hprofile : ∀ F : ℝ, (F : EReal) = R → (2 : ℝ) ≤ F →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        Real.log (cfQ x (n + 1) : ℝ) - Real.log (cfQ x n : ℝ) ≤
          (F - 2 + ε) * Real.log (cfQ x n : ℝ)) :
    irrationalityExponent x =
      Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop := by
  rw [← hR]
  exact hmu_of_R_packages hx hR2 hfinite hq htrunc hprofile

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.hmu_of_R_packages
#print axioms Paper4.HmuSkeleton.final_hmu_assembly_contract

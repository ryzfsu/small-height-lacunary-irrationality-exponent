/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Exponent.FiniteClosure
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter
open scoped Topology

theorem hmu_lower_of_truncation_package
    {x : ℝ} {R : EReal}
    {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (htrunc : ∀ ν : ℝ, (ν : EReal) < R →
      ∃ᶠ n : ℕ in atTop, 0 < q n ∧
        |x - (p n : ℝ) / (q n : ℝ)| <
          (q n : ℝ) ^ (-ν)) :
    R ≤ irrationalityExponent x := by
  exact lower_exponent_of_truncation_thresholds hq htrunc

theorem hmu_top_of_truncation_package
    {x : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (htrunc : ∀ ν : ℝ, (ν : EReal) < (⊤ : EReal) →
      ∃ᶠ n : ℕ in atTop, 0 < q n ∧
        |x - (p n : ℝ) / (q n : ℝ)| <
          (q n : ℝ) ^ (-ν)) :
    irrationalityExponent x = ⊤ := by
  apply top_unique
  exact lower_exponent_of_truncation_thresholds hq htrunc

theorem hmu_top_branch
    {x : ℝ} {R : EReal}
    (hRtop : R = (⊤ : EReal))
    {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (htrunc : ∀ ν : ℝ, (ν : EReal) < R →
      ∃ᶠ n : ℕ in atTop, 0 < q n ∧
        |x - (p n : ℝ) / (q n : ℝ)| <
          (q n : ℝ) ^ (-ν)) :
    irrationalityExponent x = R := by
  subst R
  exact hmu_top_of_truncation_package hq htrunc

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.hmu_top_of_truncation_package
#print axioms Paper4.HmuSkeleton.hmu_top_branch

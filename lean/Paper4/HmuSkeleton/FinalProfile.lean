/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.ReducedScaleClosure
public import Paper4.HmuSkeleton.ReducedScale

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter
open scoped Topology

/-- The eventual gap profile of every actual shifted continued-fraction
convergent, obtained from the signed lacunary-series construction through
the rational perturbation theorem and the reduced-denominator scale. -/
theorem actual_cf_profile_of_paper
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (hirr : Irrational (x N u coeff))
    (F : ℝ) (hF2 : 2 ≤ F)
    (hF : (F : EReal) = Filter.limsup
      (fun n => (exponentRatio u n : EReal)) atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      Real.log (cfQ (x N u coeff) (j + 1) : ℝ) -
        Real.log (cfQ (x N u coeff) j : ℝ) ≤
          (F - 2 + ε) * Real.log (cfQ (x N u coeff) j : ℝ) := by
  exact series_cf_profile_of_reduced_scale
    N hN u hu_pos hu_strict coeff hcoeff hheight hgap hirr F hF2 hF
    (reduced_scale_actual N hN u hu_pos hu_strict coeff hcoeff hheight hgap)

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.actual_cf_profile_of_paper

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module
public import Paper4.HmuSkeleton.CoordinateSmall
@[expose] public section
namespace Paper4.HmuSkeleton
open Filter Asymptotics
open scoped Topology

/-- All three remaining profile arithmetic fields follow from reduced_scale
and the elementary coordinate denominator bound. -/
theorem seriesProfileArithmetic_of_reduced_scale_and_bound
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu : ∀ n, 0 < u n) (hstrict : StrictMono u)
    (coeff : ℕ → ℚ) (hc : ∀ n, coeff n ≠ 0)
    (hh : Tendsto (fun n => Real.log (rationalHeight (coeff n) : ℝ) /
      (u n : ℝ)) atTop (𝓝 0))
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 2 - ε ≤ exponentRatio u n)
    (F : ℝ) (hF2 : 2 ≤ F)
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop)
    (hM : Tendsto (fun n => M N u coeff n / t N u n) atTop (𝓝 1))
    (hbound : ∀ n, coordinateDen (trunc N u coeff n) (delta N u coeff n) ≤
      (rationalHeight (coeff (n + 1))) ^ 2 * (D coeff n) ^ 2 *
        N ^ (2 * u n - u (n + 1))) :
    SeriesProfileArithmetic N u coeff F := by
  obtain ⟨hlo, hhi⟩ := step_bounds_of_reduced_scale
    N hN u hu coeff hc hh hgap F hF2 hF hM
  exact ⟨hM, coordinate_small_of_bound_and_reduced_scale
    N hN u hu hstrict coeff hc hh hgap F hF hM hbound, hlo, hhi⟩

/-- Actual CF profile with only the reduced-denominator asymptotic and the
finite exact coordinate bound left as arithmetic inputs. -/
theorem series_cf_profile_of_reduced_scale_and_bound
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu : ∀ n, 0 < u n) (hstrict : StrictMono u)
    (coeff : ℕ → ℚ) (hc : ∀ n, coeff n ≠ 0)
    (hh : Tendsto (fun n => Real.log (rationalHeight (coeff n) : ℝ) /
      (u n : ℝ)) atTop (𝓝 0))
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 2 - ε ≤ exponentRatio u n)
    (hirr : Irrational (x N u coeff))
    (F : ℝ) (hF2 : 2 ≤ F)
    (hF : (F : EReal) = limsup (fun n => (exponentRatio u n : EReal)) atTop)
    (hM : Tendsto (fun n => M N u coeff n / t N u n) atTop (𝓝 1))
    (hbound : ∀ n, coordinateDen (trunc N u coeff n) (delta N u coeff n) ≤
      (rationalHeight (coeff (n + 1))) ^ 2 * (D coeff n) ^ 2 *
        N ^ (2 * u n - u (n + 1))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      Real.log (cfQ (x N u coeff) (j + 1) : ℝ) -
        Real.log (cfQ (x N u coeff) j : ℝ) ≤
          (F - 2 + ε) * Real.log (cfQ (x N u coeff) j : ℝ) := by
  apply series_cf_profile_of_arithmetic N hN u hu hstrict coeff hc hh hgap hirr F hF2
  exact seriesProfileArithmetic_of_reduced_scale_and_bound
    N hN u hu hstrict coeff hc hh hgap F hF2 hF hM hbound

end Paper4.HmuSkeleton
#print axioms Paper4.HmuSkeleton.seriesProfileArithmetic_of_reduced_scale_and_bound

#print axioms Paper4.HmuSkeleton.series_cf_profile_of_reduced_scale_and_bound

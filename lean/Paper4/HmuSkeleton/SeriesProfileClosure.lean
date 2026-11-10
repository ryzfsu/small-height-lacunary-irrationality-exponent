/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.SelectedProfileClosure

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter Asymptotics Lacunary.Transfer
open scoped Topology

/-- The raw-Q separation limit already supplies the Section 7 exponential tail
bound. This uses the same actual truncations as the finite profile. -/
theorem series_tail_exp_bound
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    ∀ᶠ n : ℕ in atTop,
      |x N u coeff - (trunc N u coeff n : ℝ)| ≤ Real.exp (-t N u n) := by
  have hlim := master_raw_tail_mul_Q_tendsto
    N hN u hu_pos hu_strict coeff hcoeff hheight hgap
  have hsmall := (tendsto_order.mp hlim).2 (1 : ℝ) (by norm_num)
  filter_upwards [hsmall] with n hn
  have hQ : (0 : ℝ) < Q N u coeff n := by
    exact_mod_cast Q_pos N (by omega) u coeff n
  have hD : (1 : ℝ) ≤ D coeff n := by
    exact_mod_cast D_pos coeff n
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hexp : Real.exp (t N u n) = (N : ℝ) ^ u n := by
    rw [t, Real.exp_nat_mul, Real.exp_log hNp]
  have hQge : Real.exp (t N u n) ≤ (Q N u coeff n : ℝ) := by
    rw [hexp]
    simp only [Q, Nat.cast_mul, Nat.cast_pow]
    nlinarith [pow_pos hNp (u n)]
  calc
    |x N u coeff - (trunc N u coeff n : ℝ)| ≤ 1 / (Q N u coeff n : ℝ) := by
      apply (le_div_iff₀ hQ).2
      simpa only [x, mul_comm] using hn.le
    _ ≤ 1 / Real.exp (t N u n) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hQge
    _ = Real.exp (-t N u n) := by rw [Real.exp_neg, one_div]

/-- Exact remaining arithmetic input for the actual-series profile closure.
Every field concerns the original truncations and their reduced denominators.
No CF gap or selector conclusion is assumed. -/
structure SeriesProfileArithmetic
    (N : ℕ) (u : ℕ → ℕ) (coeff : ℕ → ℚ) (F : ℝ) : Prop where
  reduced_scale : Tendsto
    (fun n => M N u coeff n / t N u n) atTop (𝓝 1)
  coordinate_small :
    (fun n => Real.log (4 * (coordinateDen
      (trunc N u coeff n) (delta N u coeff n) : ℝ)))
      =o[atTop] (M N u coeff)
  step_lower : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (2 - ε) * M N u coeff n ≤ L N u coeff n
  step_upper : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    L N u coeff n ≤ (F + ε) * M N u coeff n

theorem series_cf_profile_of_arithmetic
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (hirr : Irrational (x N u coeff))
    (F : ℝ) (hF : 2 ≤ F)
    (harith : SeriesProfileArithmetic N u coeff F) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      Real.log (cfQ (x N u coeff) (j + 1) : ℝ) -
        Real.log (cfQ (x N u coeff) j : ℝ) ≤
          (F - 2 + ε) * Real.log (cfQ (x N u coeff) j : ℝ) := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have htpos : ∀ n, 0 < t N u n := by
    intro n
    exact mul_pos (by exact_mod_cast hu_pos n) hlogN
  have ht : Tendsto (t N u) atTop atTop := by
    exact ((tendsto_natCast_atTop_iff).2 hu_strict.tendsto_atTop).atTop_mul_const hlogN
  have hhalf : ∀ᶠ n : ℕ in atTop, t N u n / 2 ≤ M N u coeff n := by
    filter_upwards [(tendsto_order.mp harith.reduced_scale).1
      (1 / 2 : ℝ) (by norm_num)] with n hn
    have hh := (lt_div_iff₀ (htpos n)).1 hn
    linarith
  have hM : Tendsto (M N u coeff) atTop atTop := by
    apply tendsto_atTop_mono' atTop hhalf
    exact ht.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hden : ∀ᶠ n : ℕ in atTop,
      Real.exp (t N u n / 2) ≤ ((trunc N u coeff n).den : ℝ) := by
    filter_upwards [hhalf] with n hn
    have hh := Real.exp_le_exp.mpr hn
    simpa only [M, Real.exp_log (by positivity :
      (0 : ℝ) < ((trunc N u coeff n).den : ℝ))] using hh
  apply actual_profile_of_finite_profiles hirr hF (trunc N u coeff) (t N u)
  · intro i j hij
    have hh := (paper_scale_strictMono N hN u hu_strict).monotone hij
    simpa only [t, mul_comm] using hh
  · intro nbase
    simpa only [t, mul_comm] using
      paper_scale_geometric_after nbase N hN u hu_pos hgap
  · exact (series_tail_exp_bound N hN u hu_pos hu_strict coeff hcoeff hheight hgap).and hden
  · apply finite_profiles_of_rational_perturbation
      (trunc N u coeff) (delta N u coeff) F hF
      (trunc_succ N u coeff) ?_ hM harith.coordinate_small
      harith.step_lower harith.step_upper
    apply Eventually.of_forall
    intro n
    exact div_ne_zero (hcoeff (n + 1))
      (pow_ne_zero _ (by exact_mod_cast (show N ≠ 0 by omega)))

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.series_tail_exp_bound
#print axioms Paper4.HmuSkeleton.series_cf_profile_of_arithmetic

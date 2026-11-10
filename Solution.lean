/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Statement
public import Paper4.Arithmetic.Summability
public import Paper4.Arithmetic.RawRationalSeparation
public import Paper4.Exponent.Formula
public import Paper4.Arithmetic.RawTailAdapter
public import Paper4.Arithmetic.TruncationLower
public import Paper4.Arithmetic.HneGlue
public import Paper4.HmuSkeleton.FinalAssembly
public import Paper4.HmuSkeleton.FinalProfile

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/-- Theorem 1 of *The irrationality exponent of small-height lacunary series*.
Sequence index `j : ℕ` represents the paper's index `j + 1`. -/
theorem theorem_1
    (N : ℕ) (hN : 2 ≤ N)
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ j, coeff j ≠ 0)
    (hheight : Tendsto
      (fun j => Real.log (rationalHeight (coeff j) : ℝ) / (u j : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      2 - ε ≤ exponentRatio u j) :
    Summable (fun j => |term N u coeff j|) ∧
      Irrational (∑' j, term N u coeff j) ∧
      (2 : EReal) ≤ irrationalityExponent (∑' j, term N u coeff j) ∧
      irrationalityExponent (∑' j, term N u coeff j) =
        Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop := by
  have hsum : Summable (fun j => |term N u coeff j|) :=
    summable_term_abs N hN u hu_pos hu_strict coeff hcoeff hheight hgap
  have hirr : Irrational (∑' j, term N u coeff j) := by
    have hlim0 := master_raw_tail_mul_Q_tendsto
      N hN u hu_pos hu_strict coeff hcoeff hheight hgap
    have hlimx : Tendsto
        (fun n => (Q N u coeff n : ℝ) *
          |x N u coeff - (trunc N u coeff n : ℝ)|)
        atTop (𝓝 0) := by
      simpa only [x] using hlim0
    have hlim : Tendsto
        (fun n => (Q N u coeff n : ℝ) *
          |x N u coeff -
            (truncNumerator N u coeff n : ℝ) /
              (Q N u coeff n : ℝ)|)
        atTop (𝓝 0) := by
      apply hlimx.congr'
      filter_upwards [] with n
      rw [trunc_integerized N hN u hu_strict coeff n]
    have hne := eventual_x_ne_trunc_of_signed_tail
      N hN u hu_pos hu_strict coeff hcoeff hheight hgap
    have hQ : ∀ n, 0 < Q N u coeff n := by
      intro n
      exact Q_pos N (by omega) u coeff n
    have hrep : ∀ n, (trunc N u coeff n : ℝ) =
        (truncNumerator N u coeff n : ℝ) / (Q N u coeff n : ℝ) := by
      intro n
      exact trunc_integerized N hN u hu_strict coeff n
    have hsep : ∀ r : ℚ, x N u coeff = (r : ℝ) →
        ∀ᶠ n : ℕ in atTop,
          1 / (r.den : ℝ) ≤
            (Q N u coeff n : ℝ) *
              |x N u coeff - (truncNumerator N u coeff n : ℝ) /
                (Q N u coeff n : ℝ)| := by
      intro r hr
      exact raw_rational_separation hQ hrep hne r hr
    simpa only [x] using
      (irrational_of_tendsto_mul_error_of_ratSep hlim hsep)
  have hmu_lower : (2 : EReal) ≤ irrationalityExponent (∑' j, term N u coeff j) :=
    two_le_irrationalityExponent_cf hirr
  have hmu : irrationalityExponent (∑' j, term N u coeff j) =
      Filter.limsup (fun j => (exponentRatio u j : EReal)) atTop := by
    let R : EReal := Filter.limsup
      (fun j => (exponentRatio u j : EReal)) atTop
    have hR : R = Filter.limsup
        (fun j => (exponentRatio u j : EReal)) atTop := rfl
    have hR2 : (2 : EReal) ≤ R :=
      HmuSkeleton.two_le_exponentRatio_limsup hgap
    have hfinite : R ≠ (⊤ : EReal) → ∃ F : ℝ, (F : EReal) = R := by
      intro htop
      have hbot : R ≠ (⊥ : EReal) := by
        intro hbot
        have hle : (2 : EReal) ≤ (⊥ : EReal) := by
          simpa [hbot] using hR2
        exact (not_le_of_gt (EReal.bot_lt_coe 2)) hle
      exact ⟨R.toReal, EReal.coe_toReal htop hbot⟩
    have hq : Tendsto (Q N u coeff) atTop atTop :=
      tendsto_Q_atTop N hN u hu_pos hu_strict coeff
    have htrunc :
        ∀ ν : ℝ, (ν : EReal) < R → ∃ᶠ n : ℕ in atTop,
          0 < Q N u coeff n ∧
            |x N u coeff - (truncNumerator N u coeff n : ℝ) /
              (Q N u coeff n : ℝ)| <
                (Q N u coeff n : ℝ) ^ (-ν) := by
      exact raw_truncation_lower_of_limsup N hN u hu_pos hu_strict
        coeff hcoeff hheight hgap R hR
    have hprofile :
        ∀ F : ℝ, (F : EReal) = R → (2 : ℝ) ≤ F →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
            Real.log (cfQ (x N u coeff) (n + 1) : ℝ) -
              Real.log (cfQ (x N u coeff) n : ℝ) ≤
                (F - 2 + ε) * Real.log (cfQ (x N u coeff) n : ℝ) := by
      intro F hFR hF2
      exact HmuSkeleton.actual_cf_profile_of_paper
        N hN u hu_pos hu_strict coeff hcoeff hheight hgap hirr F hF2
        (hFR.trans hR)
    have hmu_x : irrationalityExponent (x N u coeff) = R :=
      HmuSkeleton.hmu_of_R_packages
        (x := x N u coeff) (R := R)
        (p := truncNumerator N u coeff) (q := Q N u coeff)
        hirr hR2 hfinite hq htrunc hprofile
    simpa only [x] using hmu_x
  exact ⟨hsum, hirr, hmu_lower, hmu⟩

#print axioms theorem_1

end Paper4

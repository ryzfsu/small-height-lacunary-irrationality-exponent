/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Exponent.Bridge

@[expose] public section

open Filter Set
open scoped Topology

namespace Paper4

/-- Absorb the factor two using a strict exponent gap. -/
theorem rpow_neg_lt_one_div_two_rpow {b ν t : ℝ} (hb : 0 < b)
    (hpow : 2 < b ^ (ν - t)) : b ^ (-ν) < 1 / (2 * b ^ t) := by
  have hlt := mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hb t)
  rw [← Real.rpow_add hb, sub_add_cancel] at hlt
  rw [Real.rpow_neg hb.le, one_div]
  exact (inv_lt_inv₀ (Real.rpow_pos_of_pos hb ν)
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hb t))).2 hlt

/-- Logarithmic ratio control is exactly product-denominator control. -/
theorem cf_product_lt_rpow {b c t : ℝ} (hb : 1 < b) (hc : 0 < c)
    (h : Real.log c / Real.log b < t - 1) : b * c < b ^ t := by
  have hlog : 0 < Real.log b := Real.log_pos hb
  have hc' : c < b ^ (t - 1) := by
    apply (Real.log_lt_log_iff hc (Real.rpow_pos_of_pos (by linarith) _)).1
    rw [Real.log_rpow (by linarith)]
    exact (div_lt_iff₀ hlog).1 h
  calc b * c < b * b ^ (t - 1) := mul_lt_mul_of_pos_left hc' (by linarith)
    _ = b ^ t := by
      calc b * b ^ (t - 1) = b ^ (1 : ℝ) * b ^ (t - 1) := by rw [Real.rpow_one]
        _ = b ^ ((1 : ℝ) + (t - 1)) := (Real.rpow_add (by linarith) _ _).symm
        _ = b ^ t := by congr 1; ring

/-- Monotone denominators place the CF candidate above two. -/
theorem two_le_cfExponentCandidate {q : ℕ → ℕ}
    (hq2 : ∀ n, 2 ≤ q n) (hqmono : ∀ n, q n ≤ q (n + 1)) :
    (2 : EReal) ≤ cfExponentCandidate q := by
  have hratio : ∀ n, (1 : EReal) ≤ (cfLogRatio q n : EReal) := by
    intro n
    apply EReal.coe_le_coe
    rw [cfLogRatio, le_div_iff₀ (Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le (by decide : 1 < 2) (hq2 n))))]
    simpa only [one_mul] using Real.log_le_log
      (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hq2 n)))
      (by exact_mod_cast hqmono n)
  have hlim : (1 : EReal) ≤ limsup (fun n => (cfLogRatio q n : EReal)) atTop :=
    le_limsup_of_frequently_le (Eventually.of_forall hratio).frequently
  calc (2 : EReal) = 1 + 1 := by norm_num
    _ ≤ cfExponentCandidate q := add_le_add le_rfl hlim

/-- The analytic upper direction. The reindexing hypothesis explicitly preserves
unreduced input denominators through `q n ≤ b`, and excludes each finite prefix. -/
theorem irrationalityExponent_le_cfExponentCandidate
    {x : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq2 : ∀ n, 2 ≤ q n) (hqmono : ∀ n, q n ≤ q (n + 1))
    (hlower : ∀ n, 1 / (2 * (q n : ℝ) * (q (n + 1) : ℝ)) ≤
      |x - (p n : ℝ) / (q n : ℝ)|)
    (hreindex : ∀ N : ℕ, ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      |x - (a : ℝ) / (b : ℝ)| < 1 / (2 * (b : ℝ) ^ 2) →
      ∃ n, N ≤ n ∧ q n ≤ b ∧
        (a : ℝ) / (b : ℝ) = (p n : ℝ) / (q n : ℝ)) :
    irrationalityExponent x ≤ cfExponentCandidate q := by
  apply irrationalityExponent_le_iff.2
  intro ν hν
  by_contra! hMν
  obtain ⟨tr, hMt, htν⟩ := EReal.exists_rat_btwn_of_lt hMν
  let t : ℝ := tr
  have htν' : t < ν := EReal.coe_lt_coe_iff.1 htν
  have ht2 : 2 < t := EReal.coe_lt_coe_iff.1
    ((two_le_cfExponentCandidate hq2 hqmono).trans_lt hMt)
  have hL : limsup (fun n => (cfLogRatio q n : EReal)) atTop <
      ((t - 1 : ℝ) : EReal) := by
    by_contra! hbad
    have hc : (t : EReal) ≤ cfExponentCandidate q := by
      calc (t : EReal) = (1 : EReal) + ((t - 1 : ℝ) : EReal) := by
              rw [← EReal.coe_one, ← EReal.coe_add]
              congr 1
              ring
        _ ≤ cfExponentCandidate q := add_le_add le_rfl hbad
    exact (not_le_of_gt hMt) hc
  have hratio : ∀ᶠ n : ℕ in atTop, cfLogRatio q n < t - 1 := by
    simpa only [EReal.coe_lt_coe_iff] using eventually_lt_of_limsup_lt hL
  obtain ⟨N, hN⟩ := eventually_atTop.1 hratio
  have hνt : ∀ᶠ b : ℕ in atTop, 2 < (b : ℝ) ^ (ν - t) :=
    ((tendsto_rpow_atTop (sub_pos.2 htν')).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 2)
  have hν2 : ∀ᶠ b : ℕ in atTop, 2 < (b : ℝ) ^ (ν - 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < ν - 2)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 2)
  obtain ⟨b, ⟨⟨hbt, hb2⟩, hbi⟩, a, hbpos, herr⟩ :=
    (((hνt.and hν2).and (hreindex N)).and_frequently hν).exists
  have hbpos' : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hgood : |x - (a : ℝ) / (b : ℝ)| < 1 / (2 * (b : ℝ) ^ 2) := by
    apply herr.trans
    simpa only [Real.rpow_two] using
      rpow_neg_lt_one_div_two_rpow hbpos' hb2
  obtain ⟨n, hnN, hnb, heq⟩ := hbi a hgood
  have hqn : (1 : ℝ) < q n := by exact_mod_cast
    (lt_of_lt_of_le (by decide : 1 < 2) (hq2 n))
  have hqnpos : (0 : ℝ) < q n := by linarith
  have hqnext : (0 : ℝ) < q (n + 1) := by exact_mod_cast
    (lt_of_lt_of_le (by decide : 0 < 2) (hq2 (n + 1)))
  have hprod : (q n : ℝ) * (q (n + 1) : ℝ) < (q n : ℝ) ^ t :=
    cf_product_lt_rpow hqn hqnext (hN n hnN)
  have hrpow : (q n : ℝ) ^ t ≤ (b : ℝ) ^ t :=
    Real.rpow_le_rpow hqnpos.le (by exact_mod_cast hnb) (by linarith)
  have hden : 2 * (q n : ℝ) * (q (n + 1) : ℝ) < 2 * (b : ℝ) ^ t := by
    nlinarith
  have hfrac : 1 / (2 * (b : ℝ) ^ t) <
      1 / (2 * (q n : ℝ) * (q (n + 1) : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) hden
  have hlarge : (b : ℝ) ^ (-ν) < |x - (a : ℝ) / (b : ℝ)| := by
    rw [heq]
    exact (rpow_neg_lt_one_div_two_rpow hbpos' hbt).trans
      (hfrac.trans_le (hlower n))
  exact (not_lt_of_ge herr.le) hlarge

/-- Complete analytic CF formula from its arithmetic approximation package. -/
theorem irrationalityExponent_eq_cfExponentCandidate
    {x : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hq2 : ∀ n, 2 ≤ q n) (hqmono : ∀ n, q n ≤ q (n + 1))
    (hupper : ∀ᶠ n : ℕ in atTop,
      |x - (p n : ℝ) / (q n : ℝ)| ≤
        1 / ((q n : ℝ) * (q (n + 1) : ℝ)))
    (hlower : ∀ n, 1 / (2 * (q n : ℝ) * (q (n + 1) : ℝ)) ≤
      |x - (p n : ℝ) / (q n : ℝ)|)
    (hreindex : ∀ N : ℕ, ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      |x - (a : ℝ) / (b : ℝ)| < 1 / (2 * (b : ℝ) ^ 2) →
      ∃ n, N ≤ n ∧ q n ≤ b ∧
        (a : ℝ) / (b : ℝ) = (p n : ℝ) / (q n : ℝ)) :
    irrationalityExponent x = cfExponentCandidate q := by
  exact le_antisymm
    (irrationalityExponent_le_cfExponentCandidate hq2 hqmono hlower hreindex)
    (cfExponentCandidate_le_irrationalityExponent hq hq2 hupper)

#print axioms irrationalityExponent_eq_cfExponentCandidate

end Paper4

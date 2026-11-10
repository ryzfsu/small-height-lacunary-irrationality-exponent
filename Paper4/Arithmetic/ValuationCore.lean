/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic

public section

namespace Lacunary.Valuation

variable {p : ℕ} [Fact p.Prime]

/-- A finite sum of nonzero rationals whose valuations all exceed `v` is either zero,
or nonzero with valuation still exceeding `v`. Signs are unrestricted. -/
theorem sum_range_zero_or_padicVal_gt {n : ℕ} {F : ℕ → ℚ} {v : ℤ}
    (hne : ∀ i, i < n → F i ≠ 0)
    (hval : ∀ i, i < n → v < padicValRat p (F i)) :
    (∑ i ∈ Finset.range n, F i = 0) ∨
      (∑ i ∈ Finset.range n, F i ≠ 0 ∧
        v < padicValRat p (∑ i ∈ Finset.range n, F i)) := by
  revert hne hval
  induction n with
  | zero =>
      intro hne hval
      left
      simp
  | succ n ih =>
      intro hne hval
      rw [Finset.sum_range_succ]
      have hneN : F n ≠ 0 := hne n (Nat.lt_succ_self n)
      have hvalN : v < padicValRat p (F n) := hval n (Nat.lt_succ_self n)
      have hneOld : ∀ i, i < n → F i ≠ 0 := by
        intro i hi
        exact hne i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have hvalOld : ∀ i, i < n → v < padicValRat p (F i) := by
        intro i hi
        exact hval i (Nat.lt_trans hi (Nat.lt_succ_self n))
      rcases ih hneOld hvalOld with hzero | ⟨hneSum, hvalSum⟩
      · right
        constructor
        · simpa [hzero] using hneN
        · simpa [hzero] using hvalN
      · by_cases htotal : (∑ i ∈ Finset.range n, F i) + F n = 0
        · exact Or.inl htotal
        · right
          constructor
          · exact htotal
          · have hmin := padicValRat.min_le_padicValRat_add (p := p) htotal
            exact lt_of_lt_of_le (lt_min hvalSum hvalN) hmin

/-- If the last term is the unique strict minimum-valuation term, the whole finite sum
is nonzero and has exactly the valuation of that last term. This handles signed terms. -/
theorem sum_range_last_padicVal_eq {n : ℕ} {F : ℕ → ℚ}
    (hne : ∀ i, i ≤ n → F i ≠ 0)
    (hval : ∀ i, i < n → padicValRat p (F n) < padicValRat p (F i)) :
    (∑ i ∈ Finset.range (n + 1), F i ≠ 0) ∧
      padicValRat p (∑ i ∈ Finset.range (n + 1), F i) = padicValRat p (F n) := by
  have hprefix := sum_range_zero_or_padicVal_gt (p := p) (F := F)
    (v := padicValRat p (F n))
    (fun i hi => hne i (Nat.le_of_lt hi)) hval
  rcases hprefix with hzero | ⟨hnePrefix, hvalPrefix⟩
  · constructor
    · rw [Finset.sum_range_succ, hzero]
      simpa using hne n (Nat.le_refl n)
    · rw [Finset.sum_range_succ, hzero]
      simp
  · have hneN : F n ≠ 0 := hne n (Nat.le_refl n)
    have htotal : (∑ i ∈ Finset.range n, F i) + F n ≠ 0 := by
      intro hzero
      have heq : F n = -(∑ i ∈ Finset.range n, F i) := by
        apply eq_neg_iff_add_eq_zero.mpr
        simpa [add_comm] using hzero
      have heqv : padicValRat p (F n) =
          padicValRat p (∑ i ∈ Finset.range n, F i) := by
        rw [heq, padicValRat.neg]
      rw [heqv] at hvalPrefix
      exact (lt_irrefl _ hvalPrefix)
    have htotal' : F n + (∑ i ∈ Finset.range n, F i) ≠ 0 := by
      intro hz
      apply htotal
      simpa [add_comm] using hz
    have hvalTotal := padicValRat.add_eq_of_lt (p := p) htotal' hneN hnePrefix hvalPrefix
    constructor
    · rw [Finset.sum_range_succ]
      exact htotal
    · rw [Finset.sum_range_succ, add_comm]
      exact hvalTotal



variable {p : ℕ} [Fact p.Prime]

/-- A finite sum of signed terms above a valuation threshold is either zero
or remains above the threshold. Zero terms are allowed. -/
theorem sum_zero_or_padicVal_gt {ι : Type*} {s : Finset ι} {F : ι → ℚ} {v : ℤ}
    (hval : ∀ i ∈ s, F i ≠ 0 → v < padicValRat p (F i)) :
    (∑ i ∈ s, F i) = 0 ∨
      ((∑ i ∈ s, F i) ≠ 0 ∧ v < padicValRat p (∑ i ∈ s, F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      left
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hrest : ∀ i ∈ s, F i ≠ 0 → v < padicValRat p (F i) := by
        intro i hi hne
        exact hval i (Finset.mem_insert_of_mem hi) hne
      by_cases hzeroA : F a = 0
      · simpa [hzeroA] using ih hrest
      · have hva := hval a (Finset.mem_insert_self a s) hzeroA
        rcases ih hrest with hzeroS | ⟨hneS, hvS⟩
        · right
          simpa [hzeroS] using And.intro hzeroA hva
        · by_cases hz : F a + (∑ i ∈ s, F i) = 0
          · exact Or.inl hz
          · exact Or.inr ⟨hz, lt_of_lt_of_le (lt_min hva hvS)
              (padicValRat.min_le_padicValRat_add hz)⟩

omit [Fact p.Prime] in
/-- Unequal valuations prevent cancellation, independently of signs. -/
theorem add_ne_zero_of_padicVal_ne {a b : ℚ}
    (hval : padicValRat p a ≠ padicValRat p b) : a + b ≠ 0 := by
  intro hab
  have hb : b = -a := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hab)
  apply hval
  rw [hb, padicValRat.neg]

/-- A unique nonzero minimum-valuation term determines the valuation of a
finite signed sum and proves its nonvanishing. All other terms may be zero. -/
theorem sum_padicVal_eq_of_unique_min {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {F : ι → ℚ} {j : ι} (hj : j ∈ s) (hne : F j ≠ 0)
    (hval : ∀ i ∈ s, i ≠ j → F i ≠ 0 → padicValRat p (F j) < padicValRat p (F i)) :
    (∑ i ∈ s, F i) ≠ 0 ∧
      padicValRat p (∑ i ∈ s, F i) = padicValRat p (F j) := by
  have herase : ∀ i ∈ s.erase j, F i ≠ 0 →
      padicValRat p (F j) < padicValRat p (F i) := by
    intro i hi hni
    exact hval i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi) hni
  have hsum := sum_zero_or_padicVal_gt (p := p) herase
  rw [← Finset.add_sum_erase s F hj]
  rcases hsum with hz | ⟨hneR, hvR⟩
  · simpa [hz] using hne
  · have htotal : F j + (∑ i ∈ s.erase j, F i) ≠ 0 :=
      add_ne_zero_of_padicVal_ne (ne_of_lt hvR)
    exact ⟨htotal, padicValRat.add_eq_of_lt htotal hne hneR hvR⟩

/-- The exact reduced denominator of an arbitrary signed integer fraction. -/
theorem den_int_div_nat (S : ℤ) {Q : ℕ} (hQ : Q ≠ 0) :
    ((S : ℚ) / (Q : ℚ)).den = Q / Nat.gcd S.natAbs Q := by
  rw [← Int.cast_natCast Q, ← Rat.divInt_eq_div, Rat.divInt_ofNat,
    Rat.den_mkRat]
  simp [hQ, Nat.gcd_comm]

/-- Cancellation removes exactly the common gcd from the unreduced denominator. -/
theorem den_int_div_nat_mul_gcd (S : ℤ) {Q : ℕ} (hQ : Q ≠ 0) :
    ((S : ℚ) / (Q : ℚ)).den * Nat.gcd S.natAbs Q = Q := by
  rw [den_int_div_nat S hQ]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_right S.natAbs Q)

/-- The reduced denominator divides every positive common integer denominator. -/
theorem den_int_div_nat_dvd (S : ℤ) {Q : ℕ} (hQ : Q ≠ 0) :
    ((S : ℚ) / (Q : ℚ)).den ∣ Q := by
  rw [den_int_div_nat S hQ]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right S.natAbs Q)

/-- Exact rational valuation before reduction, for any numerator sign. -/
theorem padicVal_int_div_nat {S : ℤ} {Q : ℕ} (hS : S ≠ 0) (hQ : Q ≠ 0) :
    padicValRat p ((S : ℚ) / (Q : ℚ)) =
      (padicValInt p S : ℤ) - (padicValNat p Q : ℤ) := by
  rw [padicValRat.div (Int.cast_ne_zero.mpr hS) (Nat.cast_ne_zero.mpr hQ),
    padicValRat.of_int, padicValRat.of_nat]

/-- Reduced denominators detect the entire negative part of a rational valuation. -/
theorem padicVal_den_eq_neg_min (q : ℚ) :
    (padicValNat p q.den : ℤ) = -min (padicValRat p q) 0 := by
  rcases Rat.num_or_den_zero_padicVal q (Fact.out : p.Prime) with hn | hd
  · simp only [padicValRat_def, hn, Nat.cast_zero, zero_sub]
    have hnonneg : (0 : ℤ) ≤ padicValNat p q.den := Int.natCast_nonneg _
    rw [min_eq_left (neg_nonpos.mpr hnonneg), neg_neg]
  · simp only [padicValRat_def, hd, Nat.cast_zero, sub_zero]
    rw [min_eq_right (Int.natCast_nonneg _), neg_zero]

/-- If the numerator valuation is at most that of the common denominator,
then their exact difference survives in the reduced denominator. -/
theorem padicVal_den_int_div_nat {S : ℤ} {Q : ℕ} (hS : S ≠ 0) (hQ : Q ≠ 0)
    (hle : padicValInt p S ≤ padicValNat p Q) :
    (padicValNat p ((S : ℚ) / (Q : ℚ)).den : ℤ) =
      (padicValNat p Q : ℤ) - (padicValInt p S : ℤ) := by
  rw [padicVal_den_eq_neg_min, padicVal_int_div_nat hS hQ,
    min_eq_left (sub_nonpos.mpr (Int.ofNat_le.mpr hle)), neg_sub]


/-- The signed finite-sum theorem for integer summands, with no rational casts
left in the conclusion. -/
theorem sum_int_padicVal_eq_of_unique_min {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {F : ι → ℤ} {j : ι} (hj : j ∈ s) (hne : F j ≠ 0)
    (hval : ∀ i ∈ s, i ≠ j → F i ≠ 0 → padicValInt p (F j) < padicValInt p (F i)) :
    (∑ i ∈ s, F i) ≠ 0 ∧
      padicValInt p (∑ i ∈ s, F i) = padicValInt p (F j) := by
  have hrat := sum_padicVal_eq_of_unique_min (p := p) (F := fun i => (F i : ℚ)) hj
    (Int.cast_ne_zero.mpr hne) (by
      intro i hi hij hni
      rw [padicValRat.of_int, padicValRat.of_int]
      exact_mod_cast hval i hi hij (Int.cast_ne_zero.mp hni))
  constructor
  · exact_mod_cast hrat.1
  · apply Int.ofNat_inj.mp
    simpa only [← Int.cast_sum, padicValRat.of_int] using hrat.2


/-- Divisibility of every earlier term above the last-term valuation is a
finite certificate for signed noncancellation. -/
theorem sum_int_padicVal_eq_of_divisibility_gap {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {F : ι → ℤ} {j : ι} {k : ℕ} (hj : j ∈ s) (hne : F j ≠ 0)
    (hdiv : ∀ i ∈ s, i ≠ j → (p : ℤ) ^ k ∣ F i)
    (hgap : padicValInt p (F j) < k) :
    (∑ i ∈ s, F i) ≠ 0 ∧
      padicValInt p (∑ i ∈ s, F i) = padicValInt p (F j) := by
  apply sum_int_padicVal_eq_of_unique_min hj hne
  intro i hi hij hni
  have hv := (padicValInt_dvd_iff k (F i)).mp (hdiv i hi hij)
  exact hgap.trans_le (hv.resolve_left hni)

/-- A unique minimum in the actual signed integer construction supplies both
nonvanishing and the exact surviving p-part of its reduced denominator. -/
theorem signed_sum_denominator_certificate {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {F : ι → ℤ} {j : ι} {Q : ℕ} (hQ : Q ≠ 0)
    (hj : j ∈ s) (hne : F j ≠ 0)
    (hval : ∀ i ∈ s, i ≠ j → F i ≠ 0 → padicValInt p (F j) < padicValInt p (F i))
    (hle : padicValInt p (F j) ≤ padicValNat p Q) :
    (∑ i ∈ s, F i) ≠ 0 ∧
      ((((∑ i ∈ s, F i : ℤ) : ℚ) / (Q : ℚ)).den =
        Q / Nat.gcd (∑ i ∈ s, F i).natAbs Q) ∧
      (padicValNat p ((((∑ i ∈ s, F i : ℤ) : ℚ) / (Q : ℚ)).den) : ℤ) =
        (padicValNat p Q : ℤ) - (padicValInt p (F j) : ℤ) := by
  obtain ⟨hneS, hvalS⟩ := sum_int_padicVal_eq_of_unique_min (p := p) hj hne hval
  refine ⟨hneS, den_int_div_nat _ hQ, ?_⟩
  rw [padicVal_den_int_div_nat hneS hQ (hvalS ▸ hle), hvalS]


/-- Cancelling powers before normalization gives the exact divisibility bound
needed by the signed perturbation coordinate. -/
theorem den_scaled_powers_dvd (A : ℤ) {B N : ℕ} (hB : B ≠ 0) (hN : N ≠ 0)
    (u v : ℕ) :
    (((A : ℚ) * (N : ℚ) ^ v) / ((B : ℚ) * (N : ℚ) ^ u)).den ∣ B * N ^ (u - v) := by
  have hnq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rcases le_total u v with huv | hvu
  · have heq : ((A : ℚ) * (N : ℚ) ^ v) / ((B : ℚ) * (N : ℚ) ^ u) =
        ((A * (N : ℤ) ^ (v - u) : ℤ) : ℚ) / (B : ℚ) := by
      rw [show v = (v - u) + u from (Nat.sub_add_cancel huv).symm, pow_add]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero u hnq)]
      simp
    rw [heq, Nat.sub_eq_zero_of_le huv, pow_zero, mul_one]
    exact den_int_div_nat_dvd _ hB
  · have heq : ((A : ℚ) * (N : ℚ) ^ v) / ((B : ℚ) * (N : ℚ) ^ u) =
        (A : ℚ) / ((B * N ^ (u - v) : ℕ) : ℚ) := by
      rw [show u = (u - v) + v from (Nat.sub_add_cancel hvu).symm, pow_add]
      simp only [Nat.cast_mul, Nat.cast_pow]
      rw [← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero v hnq)]
      simp
    rw [heq]
    exact den_int_div_nat_dvd _ (mul_ne_zero hB (pow_ne_zero _ hN))

/-- Reduction can only improve the denominator cost of a scaled power ratio. -/
theorem den_scaled_powers_le (A : ℤ) {B N : ℕ} (hB : B ≠ 0) (hN : N ≠ 0)
    (u v : ℕ) :
    (((A : ℚ) * (N : ℚ) ^ v) / ((B : ℚ) * (N : ℚ) ^ u)).den ≤ B * N ^ (u - v) := by
  apply Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hB) (pow_pos (Nat.pos_of_ne_zero hN) _))
  exact den_scaled_powers_dvd A hB hN u v


end Lacunary.Valuation

namespace Lacunary.Valuation


/-- The cancellation cost of a denominator N^u D is bounded using only D and
numerator valuations at the fixed prime divisors of N. No exact gcd extraction
or sign condition is needed. -/
theorem gcd_pow_mul_dvd_cost {A N D : ℕ} (hA : A ≠ 0) (hN : N ≠ 0)
    (hD : D ≠ 0) (u : ℕ) :
    Nat.gcd A (N ^ u * D) ∣ D * ∏ p ∈ N.primeFactors, p ^ padicValNat p A := by
  let B := ∏ p ∈ N.primeFactors, p ^ padicValNat p A
  have hB : B ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hQ : N ^ u * D ≠ 0 := mul_ne_zero (pow_ne_zero _ hN) hD
  have hG : Nat.gcd A (N ^ u * D) ≠ 0 := Nat.gcd_ne_zero_right hQ
  apply (Nat.factorization_prime_le_iff_dvd hG (mul_ne_zero hD hB)).mp
  intro p hp
  have hleA := (Nat.factorization_le_iff_dvd hG hA).mpr
    (Nat.gcd_dvd_left A (N ^ u * D)) p
  by_cases hpN : p ∣ N
  · have hpmem : p ∈ N.primeFactors := hp.mem_primeFactors hpN hN
    have hpB : p ^ padicValNat p A ∣ B := Finset.dvd_prod_of_mem _ hpmem
    have hvB : padicValNat p A ≤ B.factorization p :=
      (hp.pow_dvd_iff_le_factorization hB).mp hpB
    have hleB : B.factorization p ≤ (D * B).factorization p :=
      Nat.factorization_le_factorization_mul_right hD p
    exact hleA.trans (by rw [Nat.factorization_def A hp]; exact hvB.trans hleB)
  · have hleQ := (Nat.factorization_le_iff_dvd hG hQ).mpr
      (Nat.gcd_dvd_right A (N ^ u * D)) p
    have hfactorQ : (N ^ u * D).factorization p = D.factorization p := by
      rw [Nat.factorization_mul (pow_ne_zero _ hN) hD, Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hpN]
      simp
    rw [hfactorQ] at hleQ
    exact hleQ.trans (Nat.factorization_le_factorization_mul_left hB p)

/-- A size bound suitable for logarithmic estimates of the cancellation cost. -/
theorem gcd_pow_mul_le_cost {A N D : ℕ} (hA : A ≠ 0) (hN : N ≠ 0)
    (hD : D ≠ 0) (u : ℕ) :
    Nat.gcd A (N ^ u * D) ≤ D * ∏ p ∈ N.primeFactors, p ^ padicValNat p A := by
  apply Nat.le_of_dvd
  · apply Nat.pos_of_ne_zero
    apply mul_ne_zero hD
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  · exact gcd_pow_mul_dvd_cost hA hN hD u


/-- The cancellation-cost bound for the actual signed integer numerator. -/
theorem gcd_signed_pow_mul_le_cost {S : ℤ} {N D : ℕ} (hS : S ≠ 0) (hN : N ≠ 0)
    (hD : D ≠ 0) (u : ℕ) :
    Nat.gcd S.natAbs (N ^ u * D) ≤
      D * ∏ p ∈ N.primeFactors, p ^ padicValInt p S := by
  simpa only [padicValInt] using
    gcd_pow_mul_le_cost (Int.natAbs_ne_zero.mpr hS) hN hD u


end Lacunary.Valuation

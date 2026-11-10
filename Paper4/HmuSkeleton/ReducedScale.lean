/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.RawScale
public import Paper4.Arithmetic.ValuationCore
public import Paper4.HmuSkeleton.CoordinateSmall

@[expose] public section

open Filter
open scoped Topology

namespace Paper4.HmuSkeleton

private def lastIntegerTerm (coeff : ℕ → ℚ) (n : ℕ) : ℤ :=
  (coeff n).num * (D coeff n / (coeff n).den : ℤ)

private theorem lastIntegerTerm_ne_zero
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0) (n : ℕ) :
    lastIntegerTerm coeff n ≠ 0 := by
  have hmem : n ∈ Finset.range (n + 1) := by simp
  have hdiv : (coeff n).den ∣ D coeff n := by
    unfold D
    exact Finset.dvd_prod_of_mem (fun i => (coeff i).den) hmem
  have hquot : D coeff n / (coeff n).den ≠ 0 := by
    intro hz
    have hmul := Nat.div_mul_cancel hdiv
    rw [hz] at hmul
    simp only [zero_mul] at hmul
    exact (D_pos coeff n).ne' hmul.symm
  have hnum : (coeff n).num ≠ 0 := Rat.num_ne_zero.mpr (hcoeff n)
  have hquotCast : (D coeff n / (coeff n).den : ℤ) =
      ((D coeff n / (coeff n).den : ℕ) : ℤ) :=
    (Int.natCast_div _ _).symm
  unfold lastIntegerTerm
  rw [hquotCast]
  exact mul_ne_zero hnum (Int.natCast_ne_zero.mpr hquot)

private theorem lastIntegerTerm_log_bound
    (p : ℕ) [Fact p.Prime] (coeff : ℕ → ℚ)
    (hcoeff : ∀ n, coeff n ≠ 0) (n : ℕ) :
    (padicValInt p (lastIntegerTerm coeff n) : ℝ) * Real.log 2 ≤
      Real.log (rationalHeight (coeff n) : ℝ) + Real.log (D coeff n : ℝ) := by
  have hlast : lastIntegerTerm coeff n ≠ 0 := lastIntegerTerm_ne_zero coeff hcoeff n
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvaldiv : p ^ padicValInt p (lastIntegerTerm coeff n) ∣
      (lastIntegerTerm coeff n).natAbs :=
    (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hlast)).2 le_rfl
  have hvalle : p ^ padicValInt p (lastIntegerTerm coeff n) ≤
      (lastIntegerTerm coeff n).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hlast) hvaldiv
  have hpow : 2 ^ padicValInt p (lastIntegerTerm coeff n) ≤
      p ^ padicValInt p (lastIntegerTerm coeff n) :=
    pow_le_pow_left' hp2 _
  have hnum : (coeff n).num.natAbs ≤ rationalHeight (coeff n) := Nat.le_max_left _ _
  have hquot : D coeff n / (coeff n).den ≤ D coeff n := Nat.div_le_self _ _
  have hquotCast : (D coeff n / (coeff n).den : ℤ) =
      ((D coeff n / (coeff n).den : ℕ) : ℤ) :=
    (Int.natCast_div _ _).symm
  have habs : (lastIntegerTerm coeff n).natAbs =
      (coeff n).num.natAbs * (D coeff n / (coeff n).den) := by
    have hquotAbs : (D coeff n / (coeff n).den : ℤ).natAbs =
        D coeff n / (coeff n).den := by
      exact (congrArg Int.natAbs hquotCast).trans (Int.natAbs_natCast _)
    rw [lastIntegerTerm, Int.natAbs_mul, hquotAbs]
  have hsize : (lastIntegerTerm coeff n).natAbs ≤
      rationalHeight (coeff n) * D coeff n := by
    rw [habs]
    exact Nat.mul_le_mul hnum hquot
  have hcast : (2 : ℝ) ^ padicValInt p (lastIntegerTerm coeff n) ≤
      (rationalHeight (coeff n) : ℝ) * (D coeff n : ℝ) := by
    exact_mod_cast hpow.trans (hvalle.trans hsize)
  have hHpos : (0 : ℝ) < (rationalHeight (coeff n) : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (coeff n).den_pos (Nat.le_max_right _ _))
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ padicValInt p (lastIntegerTerm coeff n))
    hcast
  rw [Real.log_pow,
    Real.log_mul hHpos.ne'
      (by exact_mod_cast (D_pos coeff n).ne')] at hlog
  simpa [Nat.cast_mul] using hlog

private theorem lastIntegerTerm_val_div_u_tendsto_zero
    (p : ℕ) [Fact p.Prime]
    (u : ℕ → ℕ) (hu_pos : ∀ n, 0 < u n)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hlogD : Tendsto (fun n => Real.log (D coeff n : ℝ) / (u n : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => (padicValInt p (lastIntegerTerm coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : Tendsto
      (fun n =>
        (Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ) +
          Real.log (D coeff n : ℝ) / (u n : ℝ)) / Real.log 2)
      atTop (𝓝 0) := by
    simpa using (hheight.add hlogD).div_const (Real.log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Eventually.of_forall (fun n => div_nonneg
      (Nat.cast_nonneg _) (by positivity))
  · filter_upwards [] with n
    have hu : (0 : ℝ) < u n := by exact_mod_cast hu_pos n
    have hbound := lastIntegerTerm_log_bound p coeff hcoeff n
    have hscaled := mul_le_mul_of_nonneg_right hbound hu.le
    have hmajor :
        (padicValInt p (lastIntegerTerm coeff n) : ℝ) / (u n : ℝ) ≤
          (Real.log (rationalHeight (coeff n) : ℝ) +
            Real.log (D coeff n : ℝ)) / ((u n : ℝ) * Real.log 2) := by
      rw [div_le_div_iff₀ hu (mul_pos hu hlog2)]
      nlinarith
    have heq :
        (Real.log (rationalHeight (coeff n) : ℝ) +
          Real.log (D coeff n : ℝ)) / ((u n : ℝ) * Real.log 2) =
        (Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ) +
          Real.log (D coeff n : ℝ) / (u n : ℝ)) / Real.log 2 := by
      field_simp
    rw [heq] at hmajor
    exact hmajor

private theorem truncNumerator_unique_min_at_succ
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) (n : ℕ)
    (hval : padicValInt p (lastIntegerTerm coeff (n + 1)) <
      u (n + 1) - u n) :
    truncNumerator N u coeff (n + 1) ≠ 0 ∧
      padicValInt p (truncNumerator N u coeff (n + 1)) =
        padicValInt p (lastIntegerTerm coeff (n + 1)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let F : ℕ → ℤ := fun j =>
    (coeff j).num * (D coeff (n + 1) / (coeff j).den : ℤ) *
      (N ^ (u (n + 1) - u j) : ℤ)
  have hmem : n + 1 ∈ Finset.range (n + 2) := by simp
  have hlast : F (n + 1) = lastIntegerTerm coeff (n + 1) := by
    simp [F, lastIntegerTerm]
  have hlastne : F (n + 1) ≠ 0 := by
    rw [hlast]
    exact lastIntegerTerm_ne_zero coeff hcoeff (n + 1)
  have hsum := Lacunary.Valuation.sum_int_padicVal_eq_of_divisibility_gap
    (p := p) (s := Finset.range (n + 2)) (F := F) (j := n + 1)
    (k := u (n + 1) - u n) hmem hlastne
    (by
      intro j hj hne
      have hjlt : j < n + 1 := by
        have hjrange := Finset.mem_range.mp hj
        omega
      have hujn : u j ≤ u n := hu_strict.monotone (by omega)
      have hexp : u (n + 1) - u n ≤ u (n + 1) - u j := by omega
      have hpow :
          p ^ (u (n + 1) - u n) ∣ N ^ (u (n + 1) - u j) :=
        pow_dvd_pow_of_dvd_of_le hpN hexp
      have hpowZ : (p : ℤ) ^ (u (n + 1) - u n) ∣
          (N : ℤ) ^ (u (n + 1) - u j) := by exact_mod_cast hpow
      simpa [F, mul_assoc] using
        (dvd_mul_of_dvd_right hpowZ
          ((coeff j).num * (D coeff (n + 1) / (coeff j).den : ℤ))))
    (by rw [hlast]; exact hval)
  have hsumEq :
      (∑ j ∈ Finset.range (n + 2), F j) = truncNumerator N u coeff (n + 1) := by
    simp [F, truncNumerator, Nat.add_assoc]
  constructor
  · intro hz
    have hz' : (∑ j ∈ Finset.range (n + 2), F j) = 0 := by simpa [hsumEq] using hz
    exact hsum.1 hz'
  · have hv : padicValInt p (∑ j ∈ Finset.range (n + 2), F j) =
        padicValInt p (lastIntegerTerm coeff (n + 1)) := by
      simpa only [hlast] using hsum.2
    simpa [hsumEq] using hv

private theorem truncNumerator_padicVal_eq_last_eventually
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (coeff : ℕ → ℚ)
    (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (hlogD : Tendsto (fun n => Real.log (D coeff n : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    ∀ᶠ n : ℕ in atTop,
      truncNumerator N u coeff n ≠ 0 ∧
        padicValInt p (truncNumerator N u coeff n) =
          padicValInt p (lastIntegerTerm coeff n) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsmall := lastIntegerTerm_val_div_u_tendsto_zero p u hu_pos coeff hcoeff
    hheight hlogD
  have hsmallShift := hsmall.comp (tendsto_add_atTop_nat 1)
  have hratio := hgap (1 / 2 : ℝ) (by norm_num)
  have hnext : ∀ᶠ n : ℕ in atTop,
      padicValInt p (lastIntegerTerm coeff (n + 1)) < u (n + 1) - u n := by
    filter_upwards [
      (tendsto_order.mp hsmallShift).2 (1 / 3 : ℝ) (by norm_num), hratio]
      with n hv hg
    have hu0 : (0 : ℝ) < u n := by exact_mod_cast hu_pos n
    have hu1 : (0 : ℝ) < u (n + 1) := by exact_mod_cast hu_pos (n + 1)
    have hstep : (u (n + 1) : ℝ) / 3 ≤
        ((u (n + 1) - u n : ℕ) : ℝ) := by
      have hratio' := (le_div_iff₀ hu0).mp hg
      have hmono : u n ≤ u (n + 1) :=
        hu_strict.monotone (Nat.le_succ n)
      rw [Nat.cast_sub hmono]
      nlinarith
    have hv' : (padicValInt p (lastIntegerTerm coeff (n + 1)) : ℝ) <
        (u (n + 1) : ℝ) / 3 := by
      have hmul := (div_lt_iff₀ hu1).mp hv
      nlinarith
    exact_mod_cast lt_of_lt_of_le hv' hstep
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hnext
  filter_upwards [eventually_ge_atTop (J + 1)] with m hm
  have hmpos : 1 ≤ m := by omega
  let n := m - 1
  have hn : n + 1 = m := by dsimp [n]; omega
  have hcert := truncNumerator_unique_min_at_succ N hN u hu_strict coeff hcoeff
    p hp hpN n (hJ n (by dsimp [n]; omega))
  simpa [hn] using hcert

private theorem truncNumerator_nonzero_eventually
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (coeff : ℕ → ℚ)
    (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (hlogD : Tendsto (fun n => Real.log (D coeff n : ℝ) / (u n : ℝ))
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, truncNumerator N u coeff n ≠ 0 := by
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (by omega : N ≠ 1)
  exact (truncNumerator_padicVal_eq_last_eventually N hN u hu_pos hu_strict
    coeff hcoeff hheight hgap hlogD p hp hpN).mono (fun n hn => hn.1)

private theorem truncNumerator_padicVal_div_u_tendsto_zero
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (coeff : ℕ → ℚ)
    (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (hlogD : Tendsto (fun n => Real.log (D coeff n : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    Tendsto
      (fun n => (padicValInt p (truncNumerator N u coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsmall := lastIntegerTerm_val_div_u_tendsto_zero p u hu_pos coeff hcoeff
    hheight hlogD
  have hidAll := truncNumerator_padicVal_eq_last_eventually N hN u hu_pos
    hu_strict coeff hcoeff hheight hgap hlogD p hp hpN
  apply hsmall.congr'
  filter_upwards [hidAll] with n hn
  rw [hn.2]

private theorem log_cancellationGcd_le_actual
    (N : ℕ) (hN : N ≠ 0) (u : ℕ → ℕ) (coeff : ℕ → ℚ)
    (n : ℕ) (hS : truncNumerator N u coeff n ≠ 0) :
    Real.log (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) ≤
      Real.log (D coeff n : ℝ) +
        ∑ p ∈ N.primeFactors,
          (padicValInt p (truncNumerator N u coeff n) : ℝ) * Real.log (p : ℝ) := by
  have hD : 0 < D coeff n := D_pos coeff n
  have hG : 0 < Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) :=
    Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (Nat.ne_of_gt (Q_pos N (by omega) u coeff n)))
  have hcost := Lacunary.Valuation.gcd_signed_pow_mul_le_cost hS hN hD.ne'
    (u n)
  have hp : ∀ p ∈ N.primeFactors,
      (p : ℝ) ^ padicValInt p (truncNumerator N u coeff n) ≠ 0 := by
    intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hcostNat : Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) ≤
      D coeff n * ∏ p ∈ N.primeFactors,
        p ^ padicValInt p (truncNumerator N u coeff n) := by
    simpa only [Q] using hcost
  have hcostR : (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) ≤
      (D coeff n : ℝ) * ∏ p ∈ N.primeFactors,
        (p : ℝ) ^ padicValInt p (truncNumerator N u coeff n) := by
    exact_mod_cast hcostNat
  have hlog := Real.log_le_log (by exact_mod_cast hG) hcostR
  rw [Real.log_mul (by exact_mod_cast hD.ne')
      (Finset.prod_ne_zero_iff.mpr hp), Real.log_prod hp] at hlog
  simpa only [Real.log_pow] using hlog

private theorem cancellationGcd_log_div_u_tendsto_zero_actual
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (coeff : ℕ → ℚ)
    (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n)
    (hlogD : Tendsto (fun n => Real.log (D coeff n : ℝ) / (u n : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => Real.log
        (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) /
          (u n : ℝ))
      atTop (𝓝 0) := by
  have hS := truncNumerator_nonzero_eventually N hN u hu_pos hu_strict coeff
    hcoeff hheight hgap hlogD
  have hval : ∀ p ∈ N.primeFactors,
      Tendsto
        (fun n => (padicValInt p (truncNumerator N u coeff n) : ℝ) /
          (u n : ℝ)) atTop (𝓝 0) := by
    intro p hp
    exact truncNumerator_padicVal_div_u_tendsto_zero N hN u hu_pos hu_strict
      coeff hcoeff hheight hgap hlogD p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
  have hs : Tendsto
      (fun n => ∑ p ∈ N.primeFactors,
        ((padicValInt p (truncNumerator N u coeff n) : ℝ) / (u n : ℝ)) *
          Real.log (p : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul, Finset.sum_const_zero] using
      tendsto_finsetSum N.primeFactors
        (fun p hp => (hval p hp).mul_const (Real.log (p : ℝ)))
  have hmajor : Tendsto
      (fun n => Real.log (D coeff n : ℝ) / (u n : ℝ) +
        ∑ p ∈ N.primeFactors,
          ((padicValInt p (truncNumerator N u coeff n) : ℝ) / (u n : ℝ)) *
            Real.log (p : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlogD.add hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor ?_ ?_
  · filter_upwards with n
    have hG : 0 < Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) :=
      Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right
        (Nat.ne_of_gt (Q_pos N (by omega) u coeff n)))
    have hGone : 1 ≤ Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hG)
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hGone)) (by positivity)
  · filter_upwards [hS] with n hn
    have hlog := log_cancellationGcd_le_actual N (by omega) u coeff n hn
    have hdiv := div_le_div_of_nonneg_right hlog
      (by exact_mod_cast (hu_pos n).le : 0 ≤ (u n : ℝ))
    simpa only [add_div, Finset.sum_div, mul_div_right_comm] using hdiv

private theorem trunc_den_gcd_mul_actual
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (n : ℕ) :
    (trunc N u coeff n).den *
        Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) =
      Q N u coeff n := by
  have hQ : Q N u coeff n ≠ 0 := Nat.ne_of_gt (Q_pos N (by omega) u coeff n)
  have htrunc : trunc N u coeff n =
      (truncNumerator N u coeff n : ℚ) / (Q N u coeff n : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    have h := trunc_integerized N hN u hu_strict coeff n
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using h
  rw [htrunc]
  exact Lacunary.Valuation.den_int_div_nat_mul_gcd _ hQ

/-- The concrete reduced truncation denominator has scale `t`: the only
  cancellation at primes outside `N` is covered by `D`, while each prime
  dividing `N` sees a unique least-valuation final summand in `S_n`. -/
theorem reduced_scale_actual
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (hcoeff : ∀ n, coeff n ≠ 0)
    (hheight : Tendsto
      (fun n => Real.log (rationalHeight (coeff n) : ℝ) / (u n : ℝ))
      atTop (𝓝 0))
    (hgap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      2 - ε ≤ exponentRatio u n) :
    Tendsto (fun n => M N u coeff n / t N u n) atTop (𝓝 1) := by
  have hheightSum := profile_height_sum_div_tendsto_zero
    u hu_pos hu_strict coeff hheight hgap
  have hlogD := log_D_div_u_tendsto_zero_of_height_sum
    u hu_pos coeff hheightSum
  have hlogQ := log_Q_div_t_tendsto_one_of_log_D
    N hN u hu_pos coeff hlogD
  have hlogG := cancellationGcd_log_div_u_tendsto_zero_actual
    N hN u hu_pos hu_strict coeff hcoeff hheight hgap hlogD
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogG_t : Tendsto
      (fun n => Real.log
        (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) /
          t N u n) atTop (𝓝 0) := by
    have h : Tendsto
        (fun n => Real.log
          (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) /
            (u n : ℝ) / Real.log (N : ℝ)) atTop (𝓝 0) := by
      simpa only [zero_div] using hlogG.div_const (Real.log (N : ℝ))
    apply h.congr'
    filter_upwards [] with n
    dsimp [t]
    have hu0 : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu_pos n).ne'
    field_simp
  have hsub := hlogQ.sub hlogG_t
  have hsub' : Tendsto
      (fun n => Real.log (Q N u coeff n : ℝ) / t N u n -
        Real.log (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) /
          t N u n) atTop (𝓝 1) := by
    simpa only [sub_zero] using hsub
  apply hsub'.congr'
  filter_upwards [] with n
  have hprod := trunc_den_gcd_mul_actual N hN u hu_strict coeff n
  have hprodR : ((trunc N u coeff n).den : ℝ) *
      (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) =
        (Q N u coeff n : ℝ) := by exact_mod_cast hprod
  have hden0 : ((trunc N u coeff n).den : ℝ) ≠ 0 := by positivity
  have hG0 : (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_ne_zero_right (Nat.ne_of_gt (Q_pos N (by omega) u coeff n)))
  have hlogProd :
      Real.log ((trunc N u coeff n).den : ℝ) +
        Real.log (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) =
          Real.log (Q N u coeff n : ℝ) := by
    rw [← Real.log_mul hden0 hG0, hprodR]
  have hMIdentity : M N u coeff n / t N u n =
      Real.log (Q N u coeff n : ℝ) / t N u n -
        Real.log (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) /
          t N u n := by
    rw [M, show Real.log ((trunc N u coeff n).den : ℝ) =
      Real.log (Q N u coeff n : ℝ) -
        Real.log (Nat.gcd (truncNumerator N u coeff n).natAbs (Q N u coeff n) : ℝ) by linarith]
    ring
  exact hMIdentity.symm

#print axioms reduced_scale_actual

end Paper4.HmuSkeleton

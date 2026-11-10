/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.RawScale
public import Paper4.Arithmetic.ValuationCore
public import Paper4.HmuSkeleton.PerturbationCases
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

/-- A signed coefficient is cleared by multiplying numerator and denominator
by its signed numerator before applying the scaled-power denominator bound. -/
theorem coordinate_den_trunc_delta_le
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (n : ℕ) (hcoeff : coeff (n + 1) ≠ 0) :
    coordinateDen (trunc N u coeff n) (delta N u coeff n) ≤
      (coeff (n + 1)).num.natAbs ^ 2 * (D coeff n) ^ 2 *
        N ^ (2 * u n - u (n + 1)) := by
  let V : ℕ := (trunc N u coeff n).den
  let C : ℚ := coeff (n + 1)
  let G : ℕ := Q N u coeff n / V
  let A : ℤ := C.num * (C.den : ℤ) * (G : ℤ) ^ 2
  let B : ℕ := C.num.natAbs ^ 2 * (D coeff n) ^ 2
  have hN0 : N ≠ 0 := by omega
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hVdvd : V ∣ Q N u coeff n := by
    exact trunc_den_dvd_Q N hN0 u hu_strict.monotone coeff n
  have hVGnat : V * G = Q N u coeff n := by
    dsimp [G]
    exact Nat.mul_div_cancel' hVdvd
  have hVGnat' : V * G = N ^ u n * D coeff n := by
    simpa [Q] using hVGnat
  have hVGq : (V : ℚ) * (G : ℚ) =
      (N : ℚ) ^ u n * (D coeff n : ℚ) := by
    exact_mod_cast hVGnat'
  have hVq : (V : ℚ) ≠ 0 := by
    exact_mod_cast (trunc N u coeff n).den_pos.ne'
  have hDq : (D coeff n : ℚ) ≠ 0 := by
    exact_mod_cast (D_pos coeff n).ne'
  have hGq : (G : ℚ) ≠ 0 := by
    intro hG
    rw [hG, mul_zero] at hVGq
    exact (mul_ne_zero (pow_ne_zero _ hNq) hDq) hVGq.symm
  have hnum : C.num ≠ 0 := (Rat.num_ne_zero).2 (by simpa [C] using hcoeff)
  have hnumq : (C.num : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hnum
  have hdenq : (C.den : ℚ) ≠ 0 := by
    exact_mod_cast C.den_pos.ne'
  have hpow : (N : ℚ) ^ (2 * u n) = ((N : ℚ) ^ u n) ^ 2 := by
    rw [show 2 * u n = u n * 2 by omega, pow_mul]
  have hVGsq : (V : ℚ) ^ 2 * (G : ℚ) ^ 2 =
      (N : ℚ) ^ (2 * u n) * (D coeff n : ℚ) ^ 2 := by
    calc
      (V : ℚ) ^ 2 * (G : ℚ) ^ 2 = ((V : ℚ) * (G : ℚ)) ^ 2 := by ring
      _ = ((N : ℚ) ^ u n * (D coeff n : ℚ)) ^ 2 :=
        congrArg (fun z : ℚ => z ^ 2) hVGq
      _ = (N : ℚ) ^ (2 * u n) * (D coeff n : ℚ) ^ 2 := by
        rw [hpow]
        ring
  have hnumSq : (C.num.natAbs : ℚ) ^ 2 = (C.num : ℚ) ^ 2 := by
    have hh : (C.num.natAbs : ℤ) ^ 2 = C.num ^ 2 := Int.natAbs_pow_two C.num
    have hhq := congrArg (fun z : ℤ => (z : ℚ)) hh
    simpa only [Int.cast_pow, Int.cast_natCast] using hhq
  have hAq : (A : ℚ) =
      (C.num : ℚ) * (C.den : ℚ) * (G : ℚ) ^ 2 := by
    dsimp [A]
    push_cast
    rfl
  have hBq : (B : ℚ) =
      (C.num : ℚ) ^ 2 * (D coeff n : ℚ) ^ 2 := by
    dsimp [B]
    push_cast
    rw [hnumSq]
  have hdelta : delta N u coeff n =
      (C.num : ℚ) / (C.den : ℚ) / (N : ℚ) ^ u (n + 1) := by
    change C / (N : ℚ) ^ u (n + 1) = _
    rw [Rat.num_div_den]
  have hrecip :
      1 / ((V : ℚ) ^ 2 * delta N u coeff n) =
        ((A : ℚ) * (N : ℚ) ^ u (n + 1)) /
          ((B : ℚ) * (N : ℚ) ^ (2 * u n)) := by
    rw [hdelta, hAq, hBq, hpow]
    field_simp [hnumq, hdenq, hNq, hVq, hDq, hGq]
    rw [hpow] at hVGsq
    nlinarith [hVGsq]
  have hB : B ≠ 0 := by
    dsimp [B]
    exact mul_ne_zero
      (pow_ne_zero _ (Int.natAbs_ne_zero.mpr hnum))
      (pow_ne_zero _ (D_pos coeff n).ne')
  unfold coordinateDen
  change (1 / ((V : ℚ) ^ 2 * delta N u coeff n)).den ≤ _
  rw [hrecip]
  have hscaled := Lacunary.Valuation.den_scaled_powers_le A hB hN0
    (2 * u n) (u (n + 1))
  simpa [A, B, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled

/-- The corresponding coefficient-height bound follows from `num ≤ height`. -/
theorem coordinate_den_trunc_delta_height_le
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_strict : StrictMono u)
    (coeff : ℕ → ℚ) (n : ℕ) (hcoeff : coeff (n + 1) ≠ 0) :
    coordinateDen (trunc N u coeff n) (delta N u coeff n) ≤
      rationalHeight (coeff (n + 1)) ^ 2 * (D coeff n) ^ 2 *
        N ^ (2 * u n - u (n + 1)) := by
  calc
    coordinateDen (trunc N u coeff n) (delta N u coeff n) ≤
        (coeff (n + 1)).num.natAbs ^ 2 * (D coeff n) ^ 2 *
          N ^ (2 * u n - u (n + 1)) :=
      coordinate_den_trunc_delta_le N hN u hu_strict coeff n hcoeff
    _ ≤ rationalHeight (coeff (n + 1)) ^ 2 * (D coeff n) ^ 2 *
          N ^ (2 * u n - u (n + 1)) := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_left (Nat.le_max_left _ _) _

#print axioms coordinate_den_trunc_delta_le
#print axioms coordinate_den_trunc_delta_height_le

end Paper4.HmuSkeleton

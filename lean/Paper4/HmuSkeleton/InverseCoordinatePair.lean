/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.ReversalBridge
public import Paper4.HmuSkeleton.InverseCoordinateDeterminant
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical

theorem inverse_coordinate_pair
    (α δ : ℚ) (hV : 2 ≤ α.den) (hδ : δ ≠ 0)
    (G : CFGap ((α + δ : ℚ) : ℝ))
    (hnear : |((α + δ : ℚ) : ℝ) - (G.value : ℝ)| <
      |(δ : ℝ)| / 2) :
    ∃ h k : ℤ,
      h = (-1 : ℤ) ^ (rationalLength α + 1) *
        (G.value.num * ((penult α).den : ℤ) -
          (penult α).num * (G.value.den : ℤ)) ∧
      k = (-1 : ℤ) ^ (rationalLength α + 1) *
        (α.num * (G.value.den : ℤ) -
          G.value.num * (α.den : ℤ)) ∧
      α.num * h + (penult α).num * k = G.value.num ∧
      (α.den : ℤ) * h + (penult α).den * k =
        (G.value.den : ℤ) ∧
      k ≠ 0 ∧
      Nat.Coprime h.natAbs k.natAbs ∧
      ((G.value.den : ℝ) * (α.den : ℝ) *
          (|(δ : ℝ)| / 2) ≤ |(k : ℝ)| ∧
        |(k : ℝ)| ≤ (G.value.den : ℝ) * (α.den : ℝ) *
          ((3 / 2 : ℝ) * |(δ : ℝ)|)) := by
  classical
  let e : ℤ := (-1 : ℤ) ^ (rationalLength α + 1)
  let h : ℤ :=
    e * (G.value.num * ((penult α).den : ℤ) -
      (penult α).num * (G.value.den : ℤ))
  let k : ℤ :=
    e * (α.num * (G.value.den : ℤ) -
      G.value.num * (α.den : ℤ))

  have he : e * e = 1 := by
    dsimp [e]
    rw [← mul_pow]
    norm_num

  have hdet :
      α.num * ((penult α).den : ℤ) -
        (penult α).num * (α.den : ℤ) = e :=
    inverse_coordinate_determinant α hV

  have hrow1 :
      α.num * h + (penult α).num * k =
        G.value.num := by
    calc
      α.num * h + (penult α).num * k =
          (α.num * ((penult α).den : ℤ) -
            (penult α).num * (α.den : ℤ)) *
            e * G.value.num := by
              dsimp [h, k]
              ring
      _ = G.value.num := by
        rw [hdet, he]
        ring

  have hrow2 :
      (α.den : ℤ) * h + (penult α).den * k =
        (G.value.den : ℤ) := by
    calc
      (α.den : ℤ) * h + (penult α).den * k =
          (α.num * ((penult α).den : ℤ) -
            (penult α).num * (α.den : ℤ)) *
            e * (G.value.den : ℤ) := by
              dsimp [h, k]
              ring
      _ = (G.value.den : ℤ) := by
        rw [hdet, he]
        ring

  have hcop : Nat.Coprime h.natAbs k.natAbs := by
    let t : ℕ := Nat.gcd h.natAbs k.natAbs

    have hth : (t : ℤ) ∣ h := by
      apply (Int.natCast_dvd).2
      exact Nat.gcd_dvd_left _ _

    have htk : (t : ℤ) ∣ k := by
      apply (Int.natCast_dvd).2
      exact Nat.gcd_dvd_right _ _

    obtain ⟨u, hu⟩ := hth
    obtain ⟨v, hv⟩ := htk

    have ht_num : (t : ℤ) ∣ G.value.num := by
      refine ⟨α.num * u + (penult α).num * v, ?_⟩
      calc
        G.value.num =
            α.num * h + (penult α).num * k :=
          hrow1.symm
        _ = (t : ℤ) *
              (α.num * u + (penult α).num * v) := by
          rw [hu, hv]
          ring

    have ht_den : (t : ℤ) ∣ (G.value.den : ℤ) := by
      refine ⟨(α.den : ℤ) * u +
        ((penult α).den : ℤ) * v, ?_⟩
      calc
        (G.value.den : ℤ) =
            (α.den : ℤ) * h + (penult α).den * k :=
          hrow2.symm
        _ = (t : ℤ) *
              ((α.den : ℤ) * u +
                ((penult α).den : ℤ) * v) := by
          rw [hu, hv]
          ring

    have ht_num_nat : t ∣ G.value.num.natAbs :=
      (Int.natCast_dvd).1 ht_num

    have ht_den_nat : t ∣ G.value.den := by
      simpa using (Int.natCast_dvd).1 ht_den

    have ht_one : t = 1 :=
      Nat.eq_one_of_dvd_coprimes
        G.value.reduced ht_num_nat ht_den_nat

    change h.natAbs.gcd k.natAbs = 1
    exact ht_one

  have hdα : (0 : ℝ) < (α.den : ℝ) := by
    exact_mod_cast (by omega : 0 < α.den)

  have hdG : (0 : ℝ) < (G.value.den : ℝ) := by
    exact_mod_cast
      (Nat.pos_of_ne_zero G.value.den_nz)

  have hαnum :
      (α.den : ℝ) * (α : ℝ) =
        (α.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp [ne_of_gt hdα] <;> ring

  have hGnum :
      (G.value.den : ℝ) * (G.value : ℝ) =
        (G.value.num : ℝ) := by
    have hGcast : (G.value : ℝ) =
        (G.value.num : ℝ) / (G.value.den : ℝ) :=
      Rat.cast_def G.value
    calc
      (G.value.den : ℝ) * (G.value : ℝ) =
          (G.value.den : ℝ) *
            ((G.value.num : ℝ) / (G.value.den : ℝ)) :=
        congrArg (fun y : ℝ => (G.value.den : ℝ) * y) hGcast
      _ = (G.value.num : ℝ) := by
        field_simp [ne_of_gt hdG]

  have hdiff :
      (G.value.den : ℝ) * (α.den : ℝ) *
          ((α : ℝ) - (G.value : ℝ)) =
        (α.num : ℝ) * (G.value.den : ℝ) -
          (G.value.num : ℝ) * (α.den : ℝ) := by
    calc
      _ = (G.value.den : ℝ) *
            ((α.den : ℝ) * (α : ℝ)) -
          (α.den : ℝ) *
            ((G.value.den : ℝ) * (G.value : ℝ)) := by
          ring
      _ = (α.num : ℝ) * (G.value.den : ℝ) -
            (G.value.num : ℝ) * (α.den : ℝ) := by
          rw [hαnum, hGnum]
          ring

  have heabs : |(e : ℝ)| = 1 := by
    simp [e, abs_pow]

  have hkreal :
      (k : ℝ) = (e : ℝ) *
        ((α.num : ℝ) * (G.value.den : ℝ) -
          (G.value.num : ℝ) * (α.den : ℝ)) := by
    simp only [k, Int.cast_mul, Int.cast_sub,
      Int.cast_natCast]

  have hkabs :
      |(k : ℝ)| =
        |(α.num : ℝ) * (G.value.den : ℝ) -
          (G.value.num : ℝ) * (α.den : ℝ)| := by
    rw [hkreal, abs_mul, heabs, one_mul]

  have hkmetric :
      |(k : ℝ)| =
        (G.value.den : ℝ) * (α.den : ℝ) *
          |(α : ℝ) - (G.value : ℝ)| := by
    calc
      |(k : ℝ)| =
          |(α.num : ℝ) * (G.value.den : ℝ) -
            (G.value.num : ℝ) * (α.den : ℝ)| :=
        hkabs
      _ = |(G.value.den : ℝ) * (α.den : ℝ) *
            ((α : ℝ) - (G.value : ℝ))| := by
          rw [hdiff]
      _ = (G.value.den : ℝ) * (α.den : ℝ) *
            |(α : ℝ) - (G.value : ℝ)| := by
          rw [abs_mul, abs_mul,
            abs_of_pos hdG, abs_of_pos hdα]

  have hnear' :
      |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| <
        |(δ : ℝ)| / 2 := by
    simpa only [Rat.cast_add] using hnear

  have htriLower :
      |(δ : ℝ)| ≤
        |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| +
          |(α : ℝ) - (G.value : ℝ)| := by
    calc
      |(δ : ℝ)| =
          |((α : ℝ) + (δ : ℝ) - (G.value : ℝ)) +
            ((G.value : ℝ) - (α : ℝ))| := by
          congr 1
          ring
      _ ≤ |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| +
            |(G.value : ℝ) - (α : ℝ)| :=
          abs_add_le _ _
      _ = |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| +
            |(α : ℝ) - (G.value : ℝ)| := by
          rw [abs_sub_comm (G.value : ℝ) (α : ℝ)]

  have htriUpper :
      |(α : ℝ) - (G.value : ℝ)| ≤
        |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| +
          |(δ : ℝ)| := by
    calc
      |(α : ℝ) - (G.value : ℝ)| =
          |((α : ℝ) + (δ : ℝ) - (G.value : ℝ)) +
            (-(δ : ℝ))| := by
          congr 1
          ring
      _ ≤ |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| +
            |-(δ : ℝ)| :=
          abs_add_le _ _
      _ = |(α : ℝ) + (δ : ℝ) - (G.value : ℝ)| +
            |(δ : ℝ)| := by
          rw [abs_neg]

  have hdistLower :
      |(δ : ℝ)| / 2 ≤
        |(α : ℝ) - (G.value : ℝ)| := by
    linarith

  have hdistUpper :
      |(α : ℝ) - (G.value : ℝ)| ≤
        (3 / 2 : ℝ) * |(δ : ℝ)| := by
    linarith

  have hδR : (δ : ℝ) ≠ 0 := by
    exact_mod_cast hδ

  have hδabs : (0 : ℝ) < |(δ : ℝ)| :=
    abs_pos.mpr hδR

  have hdistPos :
      0 < |(α : ℝ) - (G.value : ℝ)| := by
    linarith

  have hkabsPos : 0 < |(k : ℝ)| := by
    rw [hkmetric]
    exact mul_pos (mul_pos hdG hdα) hdistPos

  have hk_ne : k ≠ 0 := by
    intro hk
    simp [hk] at hkabsPos

  have hdenNonneg :
      0 ≤ (G.value.den : ℝ) * (α.den : ℝ) :=
    mul_nonneg (le_of_lt hdG) (le_of_lt hdα)

  refine ⟨h, k, rfl, rfl, hrow1, hrow2,
    hk_ne, hcop, ?_⟩

  constructor
  · calc
      (G.value.den : ℝ) * (α.den : ℝ) *
          (|(δ : ℝ)| / 2) ≤
        (G.value.den : ℝ) * (α.den : ℝ) *
          |(α : ℝ) - (G.value : ℝ)| :=
        mul_le_mul_of_nonneg_left hdistLower hdenNonneg
      _ = |(k : ℝ)| := hkmetric.symm
  · calc
      |(k : ℝ)| =
          (G.value.den : ℝ) * (α.den : ℝ) *
            |(α : ℝ) - (G.value : ℝ)| :=
        hkmetric
      _ ≤ (G.value.den : ℝ) * (α.den : ℝ) *
            ((3 / 2 : ℝ) * |(δ : ℝ)|) :=
        mul_le_mul_of_nonneg_left hdistUpper hdenNonneg

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.inverse_coordinate_pair

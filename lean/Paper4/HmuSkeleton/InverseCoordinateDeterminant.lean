/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.ReversalBridge
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical

theorem inverse_coordinate_determinant (r : ℚ) (hden : 2 ≤ r.den) :
    r.num * (penult r).den - (penult r).num * (r.den : ℤ) =
      (-1 : ℤ) ^ (rationalLength r + 1) := by
  have hlen : 0 < rationalLength r :=
    (length_pos_iff_den_gt_one r).2 (by omega)
  let n := rationalLength r - 1
  have hn : n < rationalLength r := by dsimp [n]; omega
  have hn_add : n + 1 = rationalLength r := by
    dsimp [n]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hlen.ne')
  have hnt : ¬(GenContFract.of (r : ℝ)).TerminatedAt n :=
    rationalLength_not_terminated r hn
  have hpen := penult_spec r hden
  have hpen_pair := nonterminal_num_den hpen hnt
  have hpen_pair' :
      (GenContFract.of (r : ℝ)).nums n = ((penult r).num : ℝ) ∧
      (GenContFract.of (r : ℝ)).dens n = ((penult r).den : ℝ) := by
    simpa [n] using hpen_pair
  have hterminal := rationalLength_num_den r
  have hdet := determinant (x := (r : ℝ)) (n := n) hnt
  rw [hn_add, hpen_pair'.1, hterminal.2, hpen_pair'.2, hterminal.1] at hdet
  have hdetZ : (penult r).num * (r.den : ℤ) -
      (penult r).den * r.num = (-1 : ℤ) ^ rationalLength r := by
    exact_mod_cast hdet
  calc
    r.num * (penult r).den - (penult r).num * (r.den : ℤ) =
        -((penult r).num * (r.den : ℤ) - (penult r).den * r.num) := by ring
    _ = -((-1 : ℤ) ^ rationalLength r) := by rw [hdetZ]
    _ = (-1 : ℤ) ^ (rationalLength r + 1) := by
      rw [pow_succ]
      ring

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.inverse_coordinate_determinant

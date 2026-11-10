/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.CF.Bridge
import Mathlib.Tactic

@[expose] public section

namespace Lacunary.CFCanonical

open GenContFract Lacunary.CFBridge

/-- Termination occurs exactly at and after the canonical terminal index. -/
theorem terminated_iff (r : ℚ) (n : ℕ) :
    (GenContFract.of (r : ℝ)).TerminatedAt n ↔ rationalLength r ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact rationalLength_not_terminated r (Nat.lt_of_not_ge hn) h
  · intro h
    exact terminated_stable h (rationalLength_terminated r)

/-- The canonical terminal index is the least index at which the input is attained. -/
theorem convergent_eq_iff (r : ℚ) (n : ℕ) :
    (GenContFract.of (r : ℝ)).convs n = (r : ℝ) ↔ rationalLength r ≤ n := by
  constructor
  · intro heq
    by_contra hn
    have hnt := rationalLength_not_terminated r (Nat.lt_of_not_ge hn)
    have hlo := error_lower hnt
    rw [heq, sub_self, abs_zero] at hlo
    have hpos : 0 < 1 / ((GenContFract.of (r : ℝ)).dens n *
        ((GenContFract.of (r : ℝ)).dens (n + 1) +
          (GenContFract.of (r : ℝ)).dens n)) := by
      have hd := dens_pos (r : ℝ) n
      have hdnext := dens_pos (r : ℝ) (n + 1)
      positivity
    exact (not_le_of_gt hpos) hlo
  · intro hn
    exact (GenContFract.of_correctness_of_terminatedAt ((terminated_iff r n).2 hn)).symm

/-- The integer case is exactly the case with no noninitial quotient. -/
theorem length_eq_zero_iff_den_eq_one (r : ℚ) :
    rationalLength r = 0 ↔ r.den = 1 := by
  constructor
  · intro h
    have hd := (rationalLength_num_den r).2
    rw [h, GenContFract.zeroth_den_eq_one] at hd
    exact_mod_cast hd.symm
  · intro hd
    have hrat : (r.num : ℚ) = r := Rat.coe_int_num_of_den_eq_one hd
    have hreal : (r : ℝ) = (r.num : ℝ) := by exact_mod_cast hrat.symm
    have ht : (GenContFract.of (r : ℝ)).TerminatedAt 0 := by
      apply of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
      rw [hreal]
      simp [IntFractPair.stream, IntFractPair.of]
    exact Nat.eq_zero_of_le_zero ((terminated_iff r 0).1 ht)

/-- Nonintegral rational inputs have a positive terminal index. -/
theorem length_pos_iff_den_gt_one (r : ℚ) :
    0 < rationalLength r ↔ 1 < r.den := by
  have hp : 0 < r.den := r.den_pos
  have hz := length_eq_zero_iff_den_eq_one r
  omega

/-- Every later continuant remains the exact reduced numerator-denominator pair. -/
theorem terminal_num_den (r : ℚ) {n : ℕ} (hn : rationalLength r ≤ n) :
    (GenContFract.of (r : ℝ)).nums n = (r.num : ℝ) ∧
      (GenContFract.of (r : ℝ)).dens n = (r.den : ℝ) := by
  rw [nums_stable_of_terminated hn (rationalLength_terminated r),
    dens_stable_of_terminated hn (rationalLength_terminated r)]
  exact rationalLength_num_den r

/-- The finite canonical quotient list starts with the integer part. -/
theorem expansion_head (r : ℚ) :
    (rationalExpansion r).head? = some ⌊(r : ℝ)⌋ := by
  simp [rationalExpansion, List.ofFn_succ]

/-- Interpret a nonempty integer quotient list as a finite simple continued fraction. -/
noncomputable def fromQuotients (a : List ℤ) : GenContFract ℝ :=
  ⟨((a.headD 0 : ℤ) : ℝ), Stream'.Seq.ofList
    (a.tail.map fun (z : ℤ) => (⟨1, (z : ℝ)⟩ : GenContFract.Pair ℝ))⟩

/-- The finite fraction in the bridge is exactly the fraction encoded by its integer list. -/
theorem fromQuotients_expansion (r : ℚ) :
    fromQuotients (rationalExpansion r) = rationalFiniteCF r := by
  apply GenContFract.ext
  · simp [fromQuotients, rationalExpansion, rationalFiniteCF, List.ofFn_succ]
  · simp [fromQuotients, rationalExpansion, rationalFiniteCF, List.ofFn_succ,
      List.map_ofFn, Function.comp_def]

/-- Evaluating the actual canonical quotient list returns the input rational. -/
theorem expansion_value (r : ℚ) :
    (fromQuotients (rationalExpansion r)).convs (rationalLength r) = (r : ℝ) := by
  rw [fromQuotients_expansion]
  exact rationalFiniteCF_value r

/-- An assembled certificate for the canonical finite expansion of a rational. -/
structure Certificate (r : ℚ) where
  terminalIndex : ℕ
  quotients : List ℤ
  length_eq : quotients.length = terminalIndex + 1
  nonempty : quotients ≠ []
  head_eq : quotients.head? = some ⌊(r : ℝ)⌋
  positive : ∀ (i : ℕ) (hi : i < quotients.length), 0 < i → 1 ≤ quotients[i]
  last_ge_two : 0 < terminalIndex → 2 ≤ quotients.getLast nonempty
  finiteCF : GenContFract ℝ
  from_quotients : finiteCF = fromQuotients quotients
  eq_of : finiteCF = GenContFract.of (r : ℝ)
  termination : ∀ n : ℕ, finiteCF.TerminatedAt n ↔ terminalIndex ≤ n
  value : finiteCF.convs terminalIndex = (r : ℝ)
  numerator : finiteCF.nums terminalIndex = (r.num : ℝ)
  denominator : finiteCF.dens terminalIndex = (r.den : ℝ)

/-- The Euclidean algorithm supplies a canonical finite certificate for every rational. -/
noncomputable def canonical (r : ℚ) : Certificate r where
  terminalIndex := rationalLength r
  quotients := rationalExpansion r
  length_eq := rationalExpansion_length r
  nonempty := rationalExpansion_ne_nil r
  head_eq := expansion_head r
  positive := (rationalExpansion_regular r).1
  last_ge_two := (rationalExpansion_regular r).2
  finiteCF := rationalFiniteCF r
  from_quotients := (fromQuotients_expansion r).symm
  eq_of := rationalFiniteCF_eq r
  termination := by intro n; rw [rationalFiniteCF_eq]; exact terminated_iff r n
  value := rationalFiniteCF_value r
  numerator := by rw [rationalFiniteCF_eq]; exact (rationalLength_num_den r).1
  denominator := by rw [rationalFiniteCF_eq]; exact (rationalLength_num_den r).2

/-- Reduced coordinates and an actual next denominator require only nonzero error. -/
theorem next_denominator {x : ℝ} {r : ℚ} {n : ℕ}
    (hconv : (GenContFract.of x).convs n = (r : ℝ)) (hne : x ≠ (r : ℝ)) :
    (GenContFract.of x).nums n = (r.num : ℝ) ∧
      (GenContFract.of x).dens n = (r.den : ℝ) ∧
      ∃ d : ℕ, 0 < d ∧ r.den ≤ d ∧
        (GenContFract.of x).dens (n + 1) = (d : ℝ) ∧
        1 / ((r.den : ℝ) * ((d : ℝ) + (r.den : ℝ))) ≤ |x - (r : ℝ)| ∧
        |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * (d : ℝ)) := by
  have hnt : ¬(GenContFract.of x).TerminatedAt n := by
    apply not_terminated_of_ne
    simpa only [hconv] using hne
  exact ⟨(nonterminal_num_den hconv hnt).1,
    (nonterminal_num_den hconv hnt).2, convergent_next_den hconv hnt⟩

end Lacunary.CFCanonical

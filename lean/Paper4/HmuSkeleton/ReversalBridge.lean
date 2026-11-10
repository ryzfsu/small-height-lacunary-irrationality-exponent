/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.CF.Canonical
public import Paper4.CF.Continuants
public import Paper4.CF.Gap
public import Paper4.CF.Irrational
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical
open Lacunary.Reversal

/- The positive tail is the actual quotient list after the integer part. -/
noncomputable def canonicalTail (r : ℚ) : List ℕ :=
  List.ofFn fun i : Fin (rationalLength r) =>
    (rationalQuotient r (i.val + 1)).toNat

theorem canonicalTail_length (r : ℚ) :
    (canonicalTail r).length = rationalLength r := by
  simp [canonicalTail]

theorem canonicalTail_positive (r : ℚ) :
    ∀ a ∈ canonicalTail r, 0 < a := by
  intro a ha
  simp only [canonicalTail, List.mem_ofFn] at ha
  rcases ha with ⟨i, rfl⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  have hq : 1 ≤ rationalQuotient r (i.val + 1) :=
    rationalQuotient_pos r (n := i.val + 1)
      (Nat.zero_lt_succ i.val) (Nat.succ_le_of_lt i.isLt)
  have hle : rationalQuotient r (i.val + 1) ≤ 0 :=
    Int.toNat_eq_zero.mp hzero
  omega

/- Actual Mathlib denominators are identified with the list continuants. -/
theorem actual_prefix_continuant_den (r : ℚ) {n : ℕ}
    (hn : n ≤ rationalLength r) :
    (GenContFract.of (r : ℝ)).dens n =
      (prefixDenom (canonicalTail r) n : ℝ) := by
  let as := canonicalTail r
  have haslen : as.length = rationalLength r := by
    dsimp [as]
    exact canonicalTail_length r
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [prefixDenom_zero]
  | one =>
      obtain ⟨ip, hstream⟩ := rational_stream_exists r (by omega)
      have hget :
          (GenContFract.of (r : ℝ)).s.get? 0 =
            some (⟨1, ip.b⟩ : GenContFract.Pair ℝ) := by
        simpa using
          (get?_of_eq_some_of_succ_get?_intFractPair_stream
            (v := (r : ℝ)) (n := 0) hstream)
      have hden :
          (GenContFract.of (r : ℝ)).dens 1 = (ip.b : ℝ) := by
        simpa using (first_den_eq hget)
      have htake : as.take 1 = as.take 0 ++ [as[0]] := by
        exact List.take_succ_eq_append_getElem (l := as) (i := 0) (by omega)
      have hentry : as[0] = (rationalQuotient r 1).toNat := by
        simp [as, canonicalTail]
      have hfinite : prefixDenom as 1 = (rationalQuotient r 1).toNat := by
        calc
          prefixDenom as 1 = continuant (as.take 1) := rfl
          _ = continuant (as.take 0 ++ [as[0]]) := by rw [htake]
          _ = as[0] * continuant (as.take 0) +
                previousContinuant (as.take 0) :=
            continuant_concat _ _
          _ = (rationalQuotient r 1).toNat := by
            rw [hentry]
            simp
      have hq : 1 ≤ rationalQuotient r 1 :=
        rationalQuotient_pos r (n := 1) (by omega) (by omega)
      have hqb : 0 ≤ ip.b := by
        rw [← rationalQuotient_eq hstream]
        omega
      have hcast :
          ((rationalQuotient r 1).toNat : ℝ) = (ip.b : ℝ) := by
        rw [rationalQuotient_eq hstream]
        exact_mod_cast (Int.toNat_of_nonneg hqb)
      have hfiniteR :
          (prefixDenom as 1 : ℝ) =
            ((rationalQuotient r 1).toNat : ℝ) := by
        exact_mod_cast hfinite
      calc
        (GenContFract.of (r : ℝ)).dens 1 = (ip.b : ℝ) := hden
        _ = ((rationalQuotient r 1).toNat : ℝ) := hcast.symm
        _ = (prefixDenom as 1 : ℝ) := hfiniteR.symm
  | more k ihk ihk1 =>
      obtain ⟨ip, hstream⟩ := rational_stream_exists r hn
      have hget :
          (GenContFract.of (r : ℝ)).s.get? (k + 1) =
            some (⟨1, ip.b⟩ : GenContFract.Pair ℝ) := by
        simpa [Nat.add_assoc] using
          (get?_of_eq_some_of_succ_get?_intFractPair_stream
            (v := (r : ℝ)) (n := k + 1) hstream)
      have hprev :
          (GenContFract.of (r : ℝ)).dens k =
            (prefixDenom as k : ℝ) :=
        ihk (by omega)
      have hcurr :
          (GenContFract.of (r : ℝ)).dens (k + 1) =
            (prefixDenom as (k + 1) : ℝ) :=
        ihk1 (by omega)
      have hrec :
          (GenContFract.of (r : ℝ)).dens (k + 2) =
            (ip.b : ℝ) * (prefixDenom as (k + 1) : ℝ) +
              1 * (prefixDenom as k : ℝ) := by
        simpa using
          (dens_recurrence (g := GenContFract.of (r : ℝ)) (n := k)
            hget hprev hcurr)
      have htake :
          as.take (k + 2) = as.take (k + 1) ++ [as[k + 1]] := by
        simpa [Nat.add_assoc] using
          (List.take_succ_eq_append_getElem (by omega))
      have hentry :
          as[k + 1] = (rationalQuotient r (k + 2)).toNat := by
        simp [as, canonicalTail]
      have hfinite :
          prefixDenom as (k + 2) =
            (rationalQuotient r (k + 2)).toNat *
                prefixDenom as (k + 1) +
              prefixDenom as k := by
        calc
          prefixDenom as (k + 2) =
              continuant (as.take (k + 2)) := rfl
          _ = continuant (as.take (k + 1) ++ [as[k + 1]]) := by
            rw [htake]
          _ = as[k + 1] * continuant (as.take (k + 1)) +
                previousContinuant (as.take (k + 1)) :=
            continuant_concat _ _
          _ = (rationalQuotient r (k + 2)).toNat *
                prefixDenom as (k + 1) +
                prefixDenom as k := by
            rw [hentry,
              previousContinuant_take as (n := k + 1) (by omega)]
            simp [prevDenom, prefixDenom]
      have hq : 1 ≤ rationalQuotient r (k + 2) :=
        rationalQuotient_pos r (n := k + 2) (by omega) (by omega)
      have hqb : 0 ≤ ip.b := by
        rw [← rationalQuotient_eq hstream]
        omega
      have hcast :
          ((rationalQuotient r (k + 2)).toNat : ℝ) =
            (ip.b : ℝ) := by
        rw [rationalQuotient_eq hstream]
        exact_mod_cast (Int.toNat_of_nonneg hqb)
      have hfiniteR :
          (prefixDenom as (k + 2) : ℝ) =
            ((rationalQuotient r (k + 2)).toNat : ℝ) *
                (prefixDenom as (k + 1) : ℝ) +
              (prefixDenom as k : ℝ) := by
        exact_mod_cast hfinite
      calc
        (GenContFract.of (r : ℝ)).dens (k + 2) =
            (ip.b : ℝ) * (prefixDenom as (k + 1) : ℝ) +
              1 * (prefixDenom as k : ℝ) := hrec
        _ = (prefixDenom as (k + 2) : ℝ) := by
          rw [← hcast, one_mul, ← hfiniteR]

theorem actual_terminal_continuant_den (r : ℚ) :
    prefixDenom (canonicalTail r) (rationalLength r) = r.den := by
  have hprefix := actual_prefix_continuant_den r
    (n := rationalLength r) le_rfl
  have hterminal := (rationalLength_num_den r).2
  have hcast :
      (prefixDenom (canonicalTail r) (rationalLength r) : ℝ) =
        (r.den : ℝ) := by
    calc
      (prefixDenom (canonicalTail r) (rationalLength r) : ℝ) =
          (GenContFract.of (r : ℝ)).dens (rationalLength r) := hprefix.symm
      _ = (r.den : ℝ) := hterminal
  exact_mod_cast hcast

/- The canonical reversal may fold a terminal `1`; this is the exact finite
   value used by the actual Mathlib expansion, not a free rational. -/
noncomputable def penult (r : ℚ) : ℚ :=
  Paper4.cfRat (r : ℝ) (rationalLength r - 1)

noncomputable def reversePoint (r : ℚ) : ℚ :=
  ((penult r).den : ℚ) / (r.den : ℚ)

theorem penult_spec (r : ℚ) (hden : 2 ≤ r.den) :
    (GenContFract.of (r : ℝ)).convs (rationalLength r - 1) =
      (penult r : ℝ) := by
  simpa [penult] using
    (Paper4.cfRat_spec (r : ℝ) (rationalLength r - 1))

theorem reversePoint_eq_canonical_reverse_value (r : ℚ) (hden : 2 ≤ r.den) :
    reversePoint r =
      finiteValue (canonicalReverseWord (canonicalTail r)) := by
  have hlen : 0 < rationalLength r :=
    (Lacunary.CFCanonical.length_pos_iff_den_gt_one r).2 (by omega)
  have hconv := penult_spec r hden
  have hnt : ¬(GenContFract.of (r : ℝ)).TerminatedAt (rationalLength r - 1) :=
    rationalLength_not_terminated r (by omega)
  have hdenconv := (nonterminal_num_den hconv hnt).2
  have hprefix := actual_prefix_continuant_den r (n := rationalLength r - 1) (by omega)
  have hcast :
      (prefixDenom (canonicalTail r) (rationalLength r - 1) : ℝ) =
        ((penult r).den : ℝ) := by
    exact hprefix.symm.trans hdenconv
  have hnat :
      prefixDenom (canonicalTail r) (rationalLength r - 1) = (penult r).den := by
    exact_mod_cast hcast
  have hprev :
      prevDenom (prefixDenom (canonicalTail r)) (canonicalTail r).length =
        (penult r).den := by
    rw [canonicalTail_length]
    simpa [prevDenom, Nat.ne_of_gt hlen] using hnat
  have hcont : continuant (canonicalTail r) = r.den := by
    calc
      continuant (canonicalTail r) =
          prefixDenom (canonicalTail r) (canonicalTail r).length :=
        (prefixDenom_length (canonicalTail r)).symm
      _ = prefixDenom (canonicalTail r) (rationalLength r) := by
        rw [canonicalTail_length]
      _ = r.den := actual_terminal_continuant_den r
  rw [finiteValue_canonicalReverseWord_eq_previous
    (canonicalTail r) (canonicalTail_positive r)]
  simp [reversePoint, hprev, hcont]
end Paper4.HmuSkeleton

namespace Paper4.HmuSkeleton.WordRecognition

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical
open Lacunary.Reversal

noncomputable def wordCF (a0 : ℤ) (as : List ℕ) : GenContFract ℝ :=
  ⟨(a0 : ℝ), Stream'.Seq.ofList
    (as.map (fun a : ℕ => (⟨1, (a : ℝ)⟩ : GenContFract.Pair ℝ)))⟩

theorem wordCF_s_get {a0 : ℤ} {as : List ℕ} {n : ℕ}
    (hn : n < as.length) :
    (wordCF a0 as).s.get? n = some (⟨1, (as[n] : ℝ)⟩ : GenContFract.Pair ℝ) := by
  simp only [wordCF, Stream'.Seq.ofList_get?]
  simp [List.getElem?_map, List.getElem?_eq_getElem hn]

theorem wordCF_dens_prefix (a0 : ℤ) (as : List ℕ) (n : ℕ)
    (hn : n ≤ as.length) :
    (wordCF a0 as).dens n = (prefixDenom as n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · simp [wordCF, prefixDenom]
      · cases as with
        | nil => simp at hn
        | cons a as =>
            have hs0 : (wordCF a0 (a :: as)).s.get? 0 =
                some (⟨1, (a : ℝ)⟩ : GenContFract.Pair ℝ) :=
              wordCF_s_get (a0 := a0) (as := a :: as) (n := 0) (by simp)
            rw [GenContFract.first_den_eq hs0]
            simp [prefixDenom]
      · have hpn : n ≤ as.length := by omega
        have hpn1 : n + 1 ≤ as.length := by omega
        have hdn := ih n (by omega) hpn
        have hdn1 := ih (n + 1) (by omega) hpn1
        have hs : (wordCF a0 as).s.get? (n + 1) =
            some (⟨1, (as[n + 1] : ℝ)⟩ : GenContFract.Pair ℝ) :=
          wordCF_s_get (a0 := a0) (as := as) (n := n + 1) (by omega)
        have hrec := GenContFract.dens_recurrence (g := wordCF a0 as)
          (n := n) hs hdn hdn1
        have hprefix : prefixDenom as (n + 2) =
            as[n + 1] * prefixDenom as (n + 1) + prefixDenom as n := by
          unfold prefixDenom
          rw [List.take_succ_eq_append_getElem (by omega : n + 1 < as.length),
            continuant_concat]
          rw [previousContinuant_take as hpn1]
          rfl
        rw [hrec, hprefix]
        norm_num

theorem finiteValue_nonneg_of_pos {as : List ℕ}
    (hpos : ∀ a ∈ as, 0 < a) : 0 ≤ finiteValue as := by
  induction as with
  | nil => simp [finiteValue]
  | cons a as ih =>
      have htail : 0 ≤ finiteValue as := ih (fun b hb => hpos b (by simp [hb]))
      have ha : (0 : ℚ) < a := by exact_mod_cast hpos a (by simp)
      rw [finiteValue]
      positivity

theorem finiteValue_pos_of_pos {as : List ℕ} (hne : as ≠ [])
    (hpos : ∀ a ∈ as, 0 < a) : 0 < finiteValue as := by
  induction as with
  | nil => exact False.elim (hne rfl)
  | cons a as ih =>
      have htail : 0 ≤ finiteValue as :=
        finiteValue_nonneg_of_pos (fun b hb => hpos b (by simp [hb]))
      have ha : (0 : ℚ) < a := by exact_mod_cast hpos a (by simp)
      rw [finiteValue]
      positivity

theorem finiteValue_lt_one_of_pos_last_ge_two {as : List ℕ}
    (hpos : ∀ a ∈ as, 0 < a)
    (hlast : ∃ bs a, as = bs ++ [a] ∧ 2 ≤ a) :
    finiteValue as < 1 := by
  rcases as with _ | ⟨a, as⟩
  · simp at hlast
  · have htail : ∀ b ∈ as, 0 < b := by
      intro b hb
      exact hpos b (by simp [hb])
    have ha : (1 : ℚ) ≤ a := by
      exact_mod_cast hpos a (by simp)
    have hposTail : 0 ≤ finiteValue as :=
      finiteValue_nonneg_of_pos htail
    have hden : (1 : ℚ) < (a : ℚ) + finiteValue as := by
      cases as with
      | nil =>
          have ha2 : 2 ≤ a := by
            rcases hlast with ⟨bs, z, has, hz⟩
            have : bs = [] := by
              cases bs with
              | nil => rfl
              | cons b bs => simp_all
            subst bs
            simp_all
          have ha2' : (2 : ℚ) ≤ a := by exact_mod_cast ha2
          simp only [finiteValue, List.nil_eq]
          linarith
      | cons b bs =>
          have htailpos : 0 < finiteValue (b :: bs) :=
            finiteValue_pos_of_pos (by simp) (fun z hz => hpos z (by simp [hz]))
          change (1 : ℚ) < (a : ℚ) + finiteValue (b :: bs)
          linarith
    rw [finiteValue]
    exact inv_lt_one_of_one_lt₀ hden

theorem gcf_s_add_int {a : ℤ} {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    (GenContFract.of ((a : ℝ) + v)).s = (GenContFract.of v).s := by
  apply Stream'.Seq.ext
  intro n
  cases n with
  | zero =>
      have hfr : Int.fract ((a : ℝ) + v) = v := by
        rw [Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
      have hfrv : Int.fract v = v := Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩
      change (GenContFract.of ((a : ℝ) + v)).s.head =
        (GenContFract.of v).s.head
      rw [GenContFract.of_s_head, GenContFract.of_s_head]
      · simp [hfr, hfrv]
      · rw [hfrv]
        exact ne_of_gt hv0
      · rw [hfr]
        exact ne_of_gt hv0
  | succ n =>
      have hfr : Int.fract ((a : ℝ) + v) = v := by
        rw [Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
      have hfrv : Int.fract v = v := Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩
      rw [GenContFract.of_s_succ, GenContFract.of_s_succ]
      simp [hfr, hfrv]

theorem last_ge_two_of_cons {a : ℕ} {as : List ℕ}
    (h : ∃ bs z, a :: as = bs ++ [z] ∧ 2 ≤ z) (has : as ≠ []) :
    ∃ bs z, as = bs ++ [z] ∧ 2 ≤ z := by
  rcases as with _ | ⟨b, bs⟩
  · contradiction
  rcases h with ⟨cs, z, hcs, hz⟩
  cases cs with
  | nil => simp at hcs
  | cons c cs =>
      have htail : b :: bs = cs ++ [z] := by
        injection hcs with hca htail
      exact ⟨cs, z, htail, hz⟩

theorem of_finiteValue_eq_wordCF {as : List ℕ}
    (hpos : ∀ a ∈ as, 0 < a)
    (hlast : ∃ bs a, as = bs ++ [a] ∧ 2 ≤ a) :
    GenContFract.of (finiteValue as : ℝ) = wordCF 0 as := by
  induction as with
  | nil =>
      simp at hlast
  | cons a as ih =>
      have ha : (0 : ℚ) < a := by exact_mod_cast hpos a (by simp)
      have hposTail : ∀ b ∈ as, 0 < b := by
        intro b hb
        exact hpos b (by simp [hb])
      have hval : (0 : ℚ) < finiteValue (a :: as) :=
        finiteValue_pos_of_pos (by simp) hpos
      have hval_lt : finiteValue (a :: as) < 1 :=
        finiteValue_lt_one_of_pos_last_ge_two hpos hlast
      have hq : (0 : ℝ) < (finiteValue (a :: as) : ℝ) := by exact_mod_cast hval
      have hq_lt : (finiteValue (a :: as) : ℝ) < 1 := by exact_mod_cast hval_lt
      have hfrq : Int.fract (finiteValue (a :: as) : ℝ) =
          (finiteValue (a :: as) : ℝ) :=
        Int.fract_eq_self.mpr ⟨hq.le, hq_lt⟩
      have hfloorq : ⌊(finiteValue (a :: as) : ℝ)⌋ = 0 := by
        refine Int.floor_eq_on_Ico (R := ℝ) (0 : ℤ) _ ?_
        constructor
        · exact_mod_cast hq.le
        · norm_num
          exact hq_lt
      apply GenContFract.ext
      · rw [GenContFract.of_h_eq_floor, hfloorq]
        rfl
      · apply Stream'.Seq.ext
        intro n
        cases n with
        | zero =>
            change (GenContFract.of (finiteValue (a :: as) : ℝ)).s.head = _
            by_cases has : as = []
            · subst as
              have ha2 : 2 ≤ a := by
                rcases hlast with ⟨bs, z, hs, hz⟩
                cases bs with
                | nil => simp_all
                | cons b bs => simp_all
              have hqinv : (finiteValue [a] : ℝ)⁻¹ = a := by
                simp [finiteValue]
              rw [GenContFract.of_s_head]
              · rw [hfrq, hqinv]
                rw [wordCF_s_get (a0 := (0 : ℤ)) (as := [a]) (n := 0) (by simp)]
                norm_num
              · rw [hfrq]
                exact ne_of_gt hq
            · have htail_last := last_ge_two_of_cons hlast has
              have hih := ih hposTail htail_last
              have hv : (0 : ℝ) < (finiteValue as : ℝ) := by
                exact_mod_cast finiteValue_pos_of_pos has hposTail
              have hvlt : (finiteValue as : ℝ) < 1 := by
                exact_mod_cast finiteValue_lt_one_of_pos_last_ge_two hposTail htail_last
              have hqinv : (finiteValue (a :: as) : ℝ)⁻¹ =
                  (a : ℝ) + (finiteValue as : ℝ) := by
                rw [finiteValue]
                simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast]
                field_simp
              have hfloorinv :
                  ⌊(finiteValue (a :: as) : ℝ)⁻¹⌋ = (a : ℤ) := by
                rw [hqinv]
                apply Int.floor_eq_iff.mpr
                constructor <;> push_cast <;> linarith
              rw [GenContFract.of_s_head]
              · rw [hfrq, hfloorinv]
                simp [wordCF]
              · rw [hfrq]
                exact ne_of_gt hq
        | succ n =>
            rw [GenContFract.of_s_succ]
            rw [hfrq]
            have hqinv : (finiteValue (a :: as) : ℝ)⁻¹ =
                (a : ℝ) + (finiteValue as : ℝ) := by
              rw [finiteValue]
              simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast]
              field_simp
            rw [hqinv]
            by_cases has_nonempty : as ≠ []
            · have htail_last := last_ge_two_of_cons hlast has_nonempty
              have hv : (0 : ℝ) < (finiteValue as : ℝ) := by
                exact_mod_cast finiteValue_pos_of_pos has_nonempty hposTail
              have hvlt : (finiteValue as : ℝ) < 1 := by
                exact_mod_cast finiteValue_lt_one_of_pos_last_ge_two hposTail htail_last
              have hsadd := gcf_s_add_int (a := (a : ℤ)) hv hvlt
              have hih := ih hposTail htail_last
              have hseq := congrArg (fun g : GenContFract ℝ => g.s.get? n) hih
              have hsadd_n := congrArg (fun s : Stream'.Seq (GenContFract.Pair ℝ) => s.get? n) hsadd
              calc
                (GenContFract.of ((a : ℝ) + (finiteValue as : ℝ))).s.get? n =
                    (GenContFract.of (finiteValue as : ℝ)).s.get? n := hsadd_n
                _ = (wordCF 0 as).s.get? n := hseq
                _ = (wordCF 0 (a :: as)).s.get? (n + 1) := by
                  simp [wordCF, Stream'.Seq.ofList_get?]
            · have has_nil : as = [] := by simpa using has_nonempty
              subst as
              have ha_cast : (a : ℝ) = ((a : ℤ) : ℝ) := by norm_num
              simp only [finiteValue, Rat.cast_zero, add_zero]
              rw [ha_cast]
              have hz : (GenContFract.of ((a : ℤ) : ℝ)).s = Stream'.Seq.nil :=
                GenContFract.of_s_of_int (K := ℝ) (a := (a : ℤ))
              rw [hz]
              simp [wordCF]

end Paper4.HmuSkeleton.WordRecognition

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical
open Lacunary.Reversal
open Paper4.HmuSkeleton.WordRecognition

theorem actual_reverse_gap_recognition {r : ℚ} (hden : 2 ≤ r.den)
    {a g : ℝ} (hgap : LogGap (reversePoint r : ℝ) a g) :
    ∃ i, i < (canonicalReverseWord (canonicalTail r)).length ∧
      a = Real.log
        (prefixDenom (canonicalReverseWord (canonicalTail r)) i : ℝ) ∧
      g = Real.log
        (prefixDenom (canonicalReverseWord (canonicalTail r)) (i + 1) : ℝ) -
        Real.log (prefixDenom (canonicalReverseWord (canonicalTail r)) i : ℝ) := by
  let as : List ℕ := canonicalReverseWord (canonicalTail r)
  have hposTail : ∀ b ∈ canonicalTail r, 0 < b := canonicalTail_positive r
  have hV : 2 ≤ continuant (canonicalTail r) := by
    have hcont : continuant (canonicalTail r) = r.den := by
      calc
        continuant (canonicalTail r) =
            prefixDenom (canonicalTail r) (canonicalTail r).length :=
          (prefixDenom_length (canonicalTail r)).symm
        _ = prefixDenom (canonicalTail r) (rationalLength r) := by
          rw [canonicalTail_length]
        _ = r.den := actual_terminal_continuant_den r
    rw [hcont]
    exact hden
  have has_pos : ∀ b ∈ as, 0 < b := by
    intro b hb
    exact canonicalReverseWord_pos (canonicalTail r) hposTail b hb
  have hlast : ∃ bs b, as = bs ++ [b] ∧ 2 ≤ b := by
    dsimp [as]
    exact canonicalReverseWord_last_ge_two (canonicalTail r) hposTail hV
  have hword : GenContFract.of (finiteValue as : ℝ) = wordCF 0 as :=
    of_finiteValue_eq_wordCF has_pos hlast
  have hrev : reversePoint r = finiteValue as := by
    dsimp [as]
    exact reversePoint_eq_canonical_reverse_value r hden
  have hrevR : (reversePoint r : ℝ) = (finiteValue as : ℝ) := by
    exact_mod_cast hrev
  have hcf : GenContFract.of (reversePoint r : ℝ) = wordCF 0 as := by
    rw [hrevR]
    exact hword
  rcases hgap with ⟨G, ha, hg⟩
  have hterm_word : (wordCF 0 as).TerminatedAt as.length := by
    change (Stream'.Seq.ofList
      (as.map (fun b : ℕ => (⟨1, (b : ℝ)⟩ : GenContFract.Pair ℝ)))).TerminatedAt as.length
    simpa using Stream'.Seq.terminatedAt_ofList
      (as.map (fun b : ℕ => (⟨1, (b : ℝ)⟩ : GenContFract.Pair ℝ)))
  have hidx : G.index < as.length := by
    by_contra hnot
    have hle : as.length ≤ G.index := Nat.le_of_not_gt hnot
    have hterm_actual : (GenContFract.of (reversePoint r : ℝ)).TerminatedAt G.index := by
      rw [hcf]
      exact GenContFract.terminated_stable hle hterm_word
    exact G.nonterminal hterm_actual
  have hpair := nonterminal_num_den G.value_eq G.nonterminal
  have hvalR : (G.value.den : ℝ) = (prefixDenom as G.index : ℝ) := by
    calc
      (G.value.den : ℝ) =
          (GenContFract.of (reversePoint r : ℝ)).dens G.index := hpair.2.symm
      _ = (wordCF 0 as).dens G.index := by rw [hcf]
      _ = (prefixDenom as G.index : ℝ) :=
        wordCF_dens_prefix 0 as G.index (by omega)
  have hnextR : (G.nextDen : ℝ) = (prefixDenom as (G.index + 1) : ℝ) := by
    calc
      (G.nextDen : ℝ) =
          (GenContFract.of (reversePoint r : ℝ)).dens (G.index + 1) := G.nextDen_eq.symm
      _ = (wordCF 0 as).dens (G.index + 1) := by rw [hcf]
      _ = (prefixDenom as (G.index + 1) : ℝ) :=
        wordCF_dens_prefix 0 as (G.index + 1) (by omega)
  have hval : G.value.den = prefixDenom as G.index := by exact_mod_cast hvalR
  have hnext : G.nextDen = prefixDenom as (G.index + 1) := by exact_mod_cast hnextR
  refine ⟨G.index, ?_, ?_, ?_⟩
  · simpa [as] using hidx
  · simpa [as, CFGap.left, hval] using ha
  · simpa [as, CFGap.width, CFGap.right, CFGap.left, hval, hnext] using hg

end Paper4.HmuSkeleton

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical
open Lacunary.Reversal

/- Parameterized reversal helper: the prefix index and both endpoint
   denominators are tied to the concrete canonical reversed word. The actual
   recognition premise is proved by actual_reverse_gap_recognition and
   supplied to actual_reversal_profile below. -/
theorem actual_reversal_profile_conditional {r : ℚ} {a g : ℝ}
    (hden : 2 ≤ r.den)
    (hgap : LogGap (reversePoint r : ℝ) a g)
    (hreverse_gap :
      ∀ {a g : ℝ}, LogGap (reversePoint r : ℝ) a g →
        ∃ i, i < (canonicalReverseWord (canonicalTail r)).length ∧
          a = Real.log
            (prefixDenom (canonicalReverseWord (canonicalTail r)) i : ℝ) ∧
          g = Real.log
            (prefixDenom (canonicalReverseWord (canonicalTail r)) (i + 1) : ℝ) -
            Real.log (prefixDenom (canonicalReverseWord (canonicalTail r)) i : ℝ)) :
    ∃ c d : ℝ, LogGap (r : ℝ) c (d - c) ∧
      |a - (Real.log (r.den : ℝ) - d)| ≤ Real.log 2 ∧
      |(a + g) - (Real.log (r.den : ℝ) - c)| ≤ Real.log 2 := by
  rcases hreverse_gap hgap with ⟨i, hi, ha, hg⟩
  have htail_len : (canonicalTail r).length = rationalLength r :=
    canonicalTail_length r
  have hV : continuant (canonicalTail r) = r.den := by
    calc
      continuant (canonicalTail r) =
          prefixDenom (canonicalTail r) (canonicalTail r).length :=
        (prefixDenom_length (canonicalTail r)).symm
      _ = prefixDenom (canonicalTail r) (rationalLength r) := by
        rw [htail_len]
      _ = r.den := actual_terminal_continuant_den r
  rcases prefixDenom_canonicalReversed_gap
      (canonicalTail r) (canonicalTail_positive r) hi with
    ⟨j, hj, hlo, hhi⟩
  have hjR : j < rationalLength r := by
    rw [← htail_len]
    exact hj
  let G : CFGap (r : ℝ) := rationalGapAt r (n := j) hjR
  have hGj : G.index = j := by
    rfl
  have hvcast : (G.value.den : ℝ) =
      (prefixDenom (canonicalTail r) j : ℝ) := by
    calc
      (G.value.den : ℝ) =
          (GenContFract.of (r : ℝ)).dens G.index :=
        (nonterminal_num_den G.value_eq G.nonterminal).2.symm
      _ = (GenContFract.of (r : ℝ)).dens j := by rw [hGj]
      _ = (prefixDenom (canonicalTail r) j : ℝ) :=
        actual_prefix_continuant_den r (by omega)
  have hv : G.value.den = prefixDenom (canonicalTail r) j := by
    exact_mod_cast hvcast
  have hnextcast : (G.nextDen : ℝ) =
      (prefixDenom (canonicalTail r) (j + 1) : ℝ) := by
    calc
      (G.nextDen : ℝ) =
          (GenContFract.of (r : ℝ)).dens (G.index + 1) := G.nextDen_eq.symm
      _ = (GenContFract.of (r : ℝ)).dens (j + 1) := by rw [hGj]
      _ = (prefixDenom (canonicalTail r) (j + 1) : ℝ) :=
        actual_prefix_continuant_den r (by omega)
  have hnext : G.nextDen = prefixDenom (canonicalTail r) (j + 1) := by
    exact_mod_cast hnextcast
  have hOrig : LogGap (r : ℝ)
      (Real.log (prefixDenom (canonicalTail r) j : ℝ))
      (Real.log (prefixDenom (canonicalTail r) (j + 1) : ℝ) -
        Real.log (prefixDenom (canonicalTail r) j : ℝ)) := by
    refine ⟨G, ?_, ?_⟩
    · simp only [CFGap.left, hv]
    · simp only [CFGap.width, CFGap.right, CFGap.left, hv, hnext]
  have hag : a + g =
      Real.log (prefixDenom (canonicalReverseWord (canonicalTail r)) (i + 1) : ℝ) := by
    rw [ha, hg]
    ring
  refine ⟨Real.log (prefixDenom (canonicalTail r) j : ℝ),
    Real.log (prefixDenom (canonicalTail r) (j + 1) : ℝ), hOrig, ?_, ?_⟩
  · simpa [ha, hV] using hlo
  · simpa [hag, hV] using hhi

end Paper4.HmuSkeleton

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical
open Lacunary.Reversal

theorem actual_reversal_profile_concrete {r : ℚ} {a g : ℝ}
    (hden : 2 ≤ r.den)
    (hgap : LogGap (reversePoint r : ℝ) a g) :
    ∃ c d : ℝ, LogGap (r : ℝ) c (d - c) ∧
      |a - (Real.log (r.den : ℝ) - d)| ≤ Real.log 2 ∧
      |(a + g) - (Real.log (r.den : ℝ) - c)| ≤ Real.log 2 := by
  exact actual_reversal_profile_conditional hden hgap
    (fun {a g} h => actual_reverse_gap_recognition hden h)

end Paper4.HmuSkeleton

namespace Paper4.HmuSkeleton

open GenContFract
open Lacunary.CFBridge
open Lacunary.CFCanonical
open Lacunary.Reversal

/- Paper §3, finite reversal lemma, equation `eq:reversal`: every actual
   reverse-point gap corresponds to an old gap, with both endpoint errors at
   most log 2. The canonical reversed word includes the final-1 merge.
   The actual gap relation is the shared `Paper4.CF.Gap.LogGap`. -/
theorem actual_reversal_profile {r : ℚ} {a g : ℝ}
    (hden : 2 ≤ r.den)
    (hgap : LogGap (reversePoint r : ℝ) a g) :
    ∃ c d : ℝ, LogGap (r : ℝ) c (d - c) ∧
      |a - (Real.log (r.den : ℝ) - d)| ≤ Real.log 2 ∧
      |(a + g) - (Real.log (r.den : ℝ) - c)| ≤ Real.log 2 := by
  exact actual_reversal_profile_conditional hden hgap
    (fun {a g} hgap => actual_reverse_gap_recognition hden hgap)

/- The same paper lemma with its endpoint range 0 ≤ c ≤ d ≤ log V,
   obtained from the actual old-gap membership and rational_gap_range. -/
theorem actual_reversal_profile_from_continuants {r : ℚ} {a g : ℝ}
    (hden : 2 ≤ r.den)
    (hgap : LogGap (reversePoint r : ℝ) a g) :
    ∃ c d : ℝ, LogGap (r : ℝ) c (d - c) ∧
      0 ≤ c ∧ c ≤ d ∧ d ≤ Real.log (r.den : ℝ) ∧
      |a - (Real.log (r.den : ℝ) - d)| ≤ Real.log 2 ∧
      |(a + g) - (Real.log (r.den : ℝ) - c)| ≤ Real.log 2 := by
  rcases actual_reversal_profile (r := r) (a := a) (g := g) hden hgap with
    ⟨c, d, hcd, ha, hg⟩
  rcases rational_gap_range hcd with ⟨hc, hwidth, hsum⟩
  refine ⟨c, d, hcd, hc, ?_, ?_, ha, hg⟩
  · linarith
  · linarith

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.actual_reverse_gap_recognition
#print axioms Paper4.HmuSkeleton.actual_reversal_profile_conditional
#print axioms Paper4.HmuSkeleton.actual_reversal_profile_concrete
#print axioms Paper4.HmuSkeleton.actual_reversal_profile
#print axioms Paper4.HmuSkeleton.actual_reversal_profile_from_continuants

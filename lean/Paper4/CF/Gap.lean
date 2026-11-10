/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.CF.Bridge
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

@[expose] public section

namespace Paper4

open GenContFract
open Lacunary.CFBridge

/-- A nonterminal convergent together with its actual next denominator. -/
structure CFGap (x : ℝ) where
  index : ℕ
  value : ℚ
  nextDen : ℕ
  nonterminal : ¬ (GenContFract.of x).TerminatedAt index
  value_eq : (GenContFract.of x).convs index = (value : ℝ)
  nextDen_eq : (GenContFract.of x).dens (index + 1) = (nextDen : ℝ)

noncomputable def CFGap.left {x : ℝ} (G : CFGap x) : ℝ :=
  Real.log (G.value.den : ℝ)

noncomputable def CFGap.right {x : ℝ} (G : CFGap x) : ℝ :=
  Real.log (G.nextDen : ℝ)

noncomputable def CFGap.width {x : ℝ} (G : CFGap x) : ℝ :=
  G.right - G.left

def LogGap (x a g : ℝ) : Prop :=
  ∃ G : CFGap x, a = G.left ∧ g = G.width

/-- The rational data attached to a fixed nonterminal index.  This is used
only to enumerate the finite set of gaps of a rational target. -/
noncomputable def rationalGapAt (r : ℚ) {n : ℕ}
    (hn : n < rationalLength r) : CFGap (r : ℝ) := by
  let hnt : ¬(GenContFract.of (r : ℝ)).TerminatedAt n :=
    rationalLength_not_terminated r hn
  let q : ℚ := Classical.choose
    (GenContFract.exists_rat_eq_nth_conv (r : ℝ) n)
  have hq : (GenContFract.of (r : ℝ)).convs n = (q : ℝ) :=
    Classical.choose_spec (GenContFract.exists_rat_eq_nth_conv (r : ℝ) n)
  let d : ℕ := Classical.choose (exists_nat_den (r : ℝ) (n + 1))
  have hd : (GenContFract.of (r : ℝ)).dens (n + 1) = (d : ℝ) := by
    exact (Classical.choose_spec (exists_nat_den (r : ℝ) (n + 1))).2
  exact
    { index := n
      value := q
      nextDen := d
      nonterminal := hnt
      value_eq := hq
      nextDen_eq := hd }

noncomputable def rationalGapPair (r : ℚ)
    (i : Fin (rationalLength r)) : ℝ × ℝ :=
  let G := rationalGapAt r (n := i.val) i.isLt
  (G.left, G.width)

theorem CFGap.data_eq_of_index {x : ℝ} {G H : CFGap x}
    (hi : G.index = H.index) : G.value = H.value ∧ G.nextDen = H.nextDen := by
  exact ⟨Rat.cast_injective (G.value_eq.symm.trans
      ((congrArg (fun n => (GenContFract.of x).convs n) hi).trans H.value_eq)),
    Nat.cast_injective (G.nextDen_eq.symm.trans
      ((congrArg (fun n => (GenContFract.of x).dens (n + 1)) hi).trans H.nextDen_eq))⟩

theorem cfGap_bounds {x : ℝ} (G : CFGap x) :
    0 < G.nextDen ∧ G.value.den ≤ G.nextDen ∧
      1 / ((G.value.den : ℝ) * ((G.nextDen : ℝ) + G.value.den)) ≤
        |x - (G.value : ℝ)| ∧
      |x - (G.value : ℝ)| ≤ 1 / ((G.value.den : ℝ) * G.nextDen) := by
  obtain ⟨d, hdpos, hdle, hdeq, hlo, hup⟩ :=
    convergent_next_den G.value_eq G.nonterminal
  have hd : d = G.nextDen := Nat.cast_injective (hdeq.symm.trans G.nextDen_eq)
  subst d
  exact ⟨hdpos, hdle, hlo, hup⟩

theorem cfGap_legendre {x : ℝ} {r : ℚ} (hne : x ≠ (r : ℝ))
    (h : |x - (r : ℝ)| < 1 / (2 * (r.den : ℝ)^2)) :
    ∃ G : CFGap x, G.value = r := by
  obtain ⟨n, d, hconv, hnt, hdpos, hrd, hdeq, _, _⟩ :=
    legendre_next_den h hne
  let G : CFGap x :=
    { index := n
      value := r
      nextDen := d
      nonterminal := hnt
      value_eq := hconv
      nextDen_eq := hdeq }
  exact ⟨G, rfl⟩

private theorem rationalGapAt_index (r : ℚ) {n : ℕ}
    (hn : n < rationalLength r) :
    (rationalGapAt r (n := n) hn).index = n := by
  rfl

private theorem rational_gap_index_lt (r : ℚ) {G : CFGap (r : ℝ)}
    (hG : ¬(GenContFract.of (r : ℝ)).TerminatedAt G.index) :
      G.index < rationalLength r := by
  by_contra h
  have hle : rationalLength r ≤ G.index := Nat.le_of_not_gt h
  exact hG (GenContFract.terminated_stable hle (rationalLength_terminated r))

private theorem rationalGapAt_data_eq {r : ℚ} {G : CFGap (r : ℝ)}
    (hG : ¬(GenContFract.of (r : ℝ)).TerminatedAt G.index) :
    G.value = (rationalGapAt r (n := G.index)
      (rational_gap_index_lt r hG)).value ∧
      G.nextDen = (rationalGapAt r (n := G.index)
        (rational_gap_index_lt r hG)).nextDen := by
  apply CFGap.data_eq_of_index
  exact (rationalGapAt_index r (rational_gap_index_lt r hG)).symm

theorem rational_gap_finite (r : ℚ) :
    Set.Finite {z : ℝ × ℝ | LogGap (r : ℝ) z.1 z.2} := by
  let f : Fin (rationalLength r) → ℝ × ℝ := rationalGapPair r
  have hf : (Set.range f).Finite := Set.finite_range f
  apply hf.subset
  intro z hz
  change LogGap (r : ℝ) z.1 z.2 at hz
  rcases hz with ⟨G, ha, hg⟩
  have hidx := rational_gap_index_lt r G.nonterminal
  let i : Fin (rationalLength r) := ⟨G.index, hidx⟩
  refine ⟨i, ?_⟩
  have hdata := rationalGapAt_data_eq (r := r) G.nonterminal
  have hv : G.left = (rationalGapAt r (n := i.val) i.isLt).left := by
    simp only [CFGap.left, hdata.1]
  have hw : G.width = (rationalGapAt r (n := i.val) i.isLt).width := by
    have hd := hdata.2
    simp only [CFGap.width, CFGap.right, CFGap.left, hdata.1, hd]
  exact Prod.ext (ha.trans hv).symm (hg.trans hw).symm

theorem rational_gap_range {r : ℚ} {a g : ℝ}
    (h : LogGap (r : ℝ) a g) :
    0 ≤ a ∧ 0 ≤ g ∧ a + g ≤ Real.log (r.den : ℝ) := by
  rcases h with ⟨G, ha, hg⟩
  have hidx : G.index < rationalLength r := rational_gap_index_lt r G.nonterminal
  have hnext_idx : G.index + 1 ≤ rationalLength r := by omega
  have hpair := nonterminal_num_den G.value_eq G.nonterminal
  have hval_pos : 0 < (G.value.den : ℝ) := by
    exact_mod_cast G.value.den_pos
  have hnext_pos : 0 < (G.nextDen : ℝ) := by
    have hp := (cfGap_bounds G).1
    exact_mod_cast hp
  have hval_one : (1 : ℝ) ≤ G.value.den := by
    exact_mod_cast (Nat.succ_le_iff.2 G.value.den_pos)
  have hden_mono : (G.nextDen : ℝ) ≤ (r.den : ℝ) := by
    have hm : (GenContFract.of (r : ℝ)).dens (G.index + 1) ≤
        (GenContFract.of (r : ℝ)).dens (rationalLength r) := by
      have hmono : Monotone (GenContFract.of (r : ℝ)).dens :=
        monotone_nat_of_le_succ (fun n => of_den_mono)
      exact hmono hnext_idx
    rw [G.nextDen_eq, (rationalLength_num_den r).2] at hm
    exact hm
  have hleft : 0 ≤ G.left := by
    rw [CFGap.left]
    exact Real.log_nonneg hval_one
  have hwidth : 0 ≤ G.width := by
    rw [CFGap.width, CFGap.right, CFGap.left]
    exact sub_nonneg.mpr (Real.log_le_log hval_pos (by
      have hm : (G.value.den : ℝ) ≤ (G.nextDen : ℝ) := by
        exact_mod_cast (cfGap_bounds G).2.1
      exact hm))
  have hsum : G.left + G.width = G.right :=
    (add_comm G.left G.width).trans (sub_add_cancel G.right G.left)
  have hright : G.right ≤ Real.log (r.den : ℝ) := by
    rw [CFGap.right]
    exact Real.log_le_log hnext_pos hden_mono
  refine ⟨by simpa [ha] using hleft, by simpa [hg] using hwidth, ?_⟩
  calc
    a + g = G.left + G.width := by rw [ha, hg]
    _ = G.right := hsum
    _ ≤ Real.log (r.den : ℝ) := hright

end Paper4

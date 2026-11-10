/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Mathlib

@[expose] public section

namespace Lacunary.Reversal

def prevDenom (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else f (n - 1)

def SplitProfile (m V : ℕ) (q r : ℕ → ℕ) : Prop :=
  ∀ j, j ≤ m →
    V = q j * r (m - j) + prevDenom q j * prevDenom r (m - j)

theorem prevDenom_le {f : ℕ → ℕ} (hf : Monotone f) (n : ℕ) :
    prevDenom f n ≤ f n := by
  by_cases hn : n = 0
  · simp [prevDenom, hn]
  · simp [prevDenom, hn]
    exact hf (Nat.sub_le n 1)

theorem split_mul_bounds {m V : ℕ} {q r : ℕ → ℕ}
    (hsplit : SplitProfile m V q r)
    (hqmono : Monotone q) (hrmono : Monotone r)
    {j : ℕ} (hj : j ≤ m) :
    q j * r (m - j) ≤ V ∧ V ≤ 2 * (q j * r (m - j)) := by
  let P := q j * r (m - j)
  let Q := prevDenom q j * prevDenom r (m - j)
  have hQ : Q ≤ P := by
    dsimp [P, Q]
    exact Nat.mul_le_mul (prevDenom_le hqmono j) (prevDenom_le hrmono (m - j))
  have hsplit' : V = P + Q := by
    simpa [P, Q] using hsplit j hj
  constructor <;> omega

theorem log_close_of_mul_bounds {q r V : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hV : 0 < V)
    (hprod : q * r ≤ V ∧ V ≤ 2 * (q * r)) :
    |Real.log (r : ℝ) - (Real.log (V : ℝ) - Real.log (q : ℝ))| ≤ Real.log 2 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hVR : 0 < (V : ℝ) := by exact_mod_cast hV
  have hprodR : (q : ℝ) * (r : ℝ) ≤ (V : ℝ) := by exact_mod_cast hprod.1
  have hVRprod : (V : ℝ) ≤ (2 : ℝ) * ((q : ℝ) * (r : ℝ)) := by
    exact_mod_cast hprod.2
  have hlogprod : Real.log (q : ℝ) + Real.log (r : ℝ) ≤ Real.log (V : ℝ) := by
    calc
      Real.log (q : ℝ) + Real.log (r : ℝ) = Real.log ((q : ℝ) * (r : ℝ)) := by
        rw [Real.log_mul (ne_of_gt hqR) (ne_of_gt hrR)]
      _ ≤ Real.log (V : ℝ) := Real.log_le_log (mul_pos hqR hrR) hprodR
  have hlogupper : Real.log (V : ℝ) ≤ Real.log 2 + Real.log (q : ℝ) + Real.log (r : ℝ) := by
    calc
      Real.log (V : ℝ) ≤ Real.log ((2 : ℝ) * ((q : ℝ) * (r : ℝ))) :=
        Real.log_le_log hVR hVRprod
      _ = Real.log 2 + Real.log (q : ℝ) + Real.log (r : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (mul_ne_zero (ne_of_gt hqR) (ne_of_gt hrR)),
          Real.log_mul (ne_of_gt hqR) (ne_of_gt hrR)]
        ring
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  apply abs_le.mpr
  constructor <;> linarith

theorem split_log_close {m V : ℕ} {q r : ℕ → ℕ}
    (hsplit : SplitProfile m V q r)
    (hqmono : Monotone q) (hrmono : Monotone r)
    (hqpos : ∀ j, j ≤ m → 0 < q j)
    (hrpos : ∀ j, j ≤ m → 0 < r j)
    (hVpos : 0 < V)
    {j : ℕ} (hj : j ≤ m) :
    |Real.log (r (m - j) : ℝ) -
      (Real.log (V : ℝ) - Real.log (q j : ℝ))| ≤ Real.log 2 := by
  have hb := split_mul_bounds hsplit hqmono hrmono hj
  exact log_close_of_mul_bounds (hqpos j hj) (hrpos (m - j) (Nat.sub_le _ _))
    hVpos hb

theorem gap_correspondence {m i : ℕ} {M : ℝ} {lq lr : ℕ → ℝ}
    (hi : i < m)
    (hclose : ∀ j, j ≤ m →
      |lr (m - j) - (M - lq j)| ≤ Real.log 2)
    (hmono : Monotone lq) (hzero : lq 0 = 0) (hend : lq m = M) :
    ∃ c d : ℝ, 0 ≤ c ∧ c ≤ d ∧ d ≤ M ∧
      |lr i - (M - d)| ≤ Real.log 2 ∧
      |lr (i + 1) - (M - c)| ≤ Real.log 2 := by
  let j := m - i - 1
  let k := m - i
  have hkidx : m - k = i := by dsimp [k]; omega
  have hjidx : m - j = i + 1 := by dsimp [j]; omega
  have hjk : j ≤ k := by dsimp [j, k]; omega
  have hjle : j ≤ m := by dsimp [j]; omega
  have hkle : k ≤ m := by dsimp [k]; omega
  refine ⟨lq j, lq k, ?_, hmono hjk, ?_, ?_, ?_⟩
  · simpa only [hzero] using hmono (Nat.zero_le j)
  · simpa only [hend] using hmono hkle
  · simpa only [hkidx] using hclose k hkle
  · simpa only [hjidx] using hclose j hjle

/-- The only extra endpoint fact needed when reversal ends in a noncanonical `1`.
The canonical merge deletes `r_(m-1)` and uses the merged gap `r_(m-2) -> r_m`.
For `a₁ = 1`, `q₁ = 1`, so its upper endpoint is exactly `M`. -/
theorem merged_last_gap {m : ℕ} {M : ℝ} {lq lr : ℕ → ℝ}
    (hm : 2 ≤ m)
    (hclose : ∀ j, j ≤ m →
      |lr (m - j) - (M - lq j)| ≤ Real.log 2)
    (hmono : Monotone lq)
    (hzero : lq 0 = 0) (hone : lq 1 = 0) (hend : lq m = M) :
    ∃ c d : ℝ, 0 ≤ c ∧ c ≤ d ∧ d ≤ M ∧
      |lr (m - 2) - (M - d)| ≤ Real.log 2 ∧
      |lr m - (M - c)| ≤ Real.log 2 := by
  have hlow := hclose 2 hm
  have hup := hclose 0 (Nat.zero_le m)
  have hcd : lq 1 ≤ lq 2 := hmono (by omega)
  have hdm : lq 2 ≤ M := by rw [← hend]; exact hmono (by omega)
  refine ⟨lq 1, lq 2, by rw [hone], hcd, hdm, ?_, ?_⟩
  · simpa using hlow
  · simpa [hzero, hone] using hup

end Lacunary.Reversal


namespace Lacunary.Reversal

/-- The symmetric digit matrix for a finite simple continued fraction. -/
def quotientMatrix (a : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![a, 1; 1, 0]

/-- The continuant matrix of a finite word of partial quotients. -/
def continuantMatrix (as : List ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  (as.map quotientMatrix).prod

/-- The continuant, normalized by `K [] = 1`. -/
def continuant (as : List ℕ) : ℕ := continuantMatrix as 0 0

/-- The previous denominator, normalized to zero for the empty word. -/
def previousContinuant (as : List ℕ) : ℕ := continuantMatrix as 0 1

@[simp] theorem quotientMatrix_transpose (a : ℕ) :
    (quotientMatrix a).transpose = quotientMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quotientMatrix]

@[simp] theorem continuantMatrix_nil : continuantMatrix [] = 1 := by
  simp [continuantMatrix]

@[simp] theorem continuant_nil : continuant [] = 1 := by
  simp [continuant]

@[simp] theorem previousContinuant_nil : previousContinuant [] = 0 := by
  simp [previousContinuant]

@[simp] theorem continuantMatrix_singleton (a : ℕ) :
    continuantMatrix [a] = quotientMatrix a := by
  simp [continuantMatrix]

@[simp] theorem continuant_singleton (a : ℕ) : continuant [a] = a := by
  simp [continuant, quotientMatrix]

@[simp] theorem previousContinuant_singleton (a : ℕ) :
    previousContinuant [a] = 1 := by
  simp [previousContinuant, quotientMatrix]

@[simp] theorem continuantMatrix_append (as bs : List ℕ) :
    continuantMatrix (as ++ bs) = continuantMatrix as * continuantMatrix bs := by
  simp [continuantMatrix, List.map_append, List.prod_append]

/-- Reversing a word transposes its continuant matrix. -/
theorem continuantMatrix_reverse (as : List ℕ) :
    continuantMatrix as.reverse = (continuantMatrix as).transpose := by
  simp [continuantMatrix, Matrix.transpose_list_prod, List.map_reverse, List.map_map,
    Function.comp_def]

/-- The continuant is invariant under reversal, including the empty word. -/
@[simp] theorem continuant_reverse (as : List ℕ) :
    continuant as.reverse = continuant as := by
  simp [continuant, continuantMatrix_reverse, Matrix.transpose_apply]

/-- The lower-left entry is the previous denominator of the reversed word. -/
theorem continuantMatrix_lower_left (as : List ℕ) :
    continuantMatrix as 1 0 = previousContinuant as.reverse := by
  simp [previousContinuant, continuantMatrix_reverse, Matrix.transpose_apply]

/-- The exact continuant split formula, with zero previous denominators at endpoints. -/
theorem continuant_append (as bs : List ℕ) :
    continuant (as ++ bs) =
      continuant as * continuant bs +
        previousContinuant as * previousContinuant bs.reverse := by
  simp [continuant, previousContinuant, continuantMatrix_append,
    continuantMatrix_reverse, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem previousContinuant_concat (as : List ℕ) (a : ℕ) :
    previousContinuant (as ++ [a]) = continuant as := by
  simp [previousContinuant, continuant, continuantMatrix_append, quotientMatrix,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The standard two-term recurrence for finite denominator continuants. -/
theorem continuant_concat (as : List ℕ) (a : ℕ) :
    continuant (as ++ [a]) = a * continuant as + previousContinuant as := by
  simp [continuant_append, Nat.mul_comm]

/-- Denominators attached to the prefixes of a finite word, constant after its length. -/
def prefixDenom (as : List ℕ) (n : ℕ) : ℕ := continuant (as.take n)

@[simp] theorem prefixDenom_zero (as : List ℕ) : prefixDenom as 0 = 1 := by
  simp [prefixDenom]

@[simp] theorem prefixDenom_length (as : List ℕ) :
    prefixDenom as as.length = continuant as := by
  simp [prefixDenom]

/-- The off-diagonal matrix entry agrees with the papers previous-index convention. -/
theorem previousContinuant_take (as : List ℕ) {n : ℕ} (hn : n ≤ as.length) :
    previousContinuant (as.take n) = prevDenom (prefixDenom as) n := by
  cases n with
  | zero => simp [prevDenom]
  | succ n =>
    rw [List.take_succ_eq_append_getElem (by omega : n < as.length),
      previousContinuant_concat]
    simp [prevDenom, prefixDenom]

/-- A finite word and its reverse satisfy the precise split identity used in Section 3. -/
theorem prefixDenom_splitProfile (as : List ℕ) :
    SplitProfile as.length (continuant as) (prefixDenom as) (prefixDenom as.reverse) := by
  intro j hj
  have hrev : as.reverse.take (as.length - j) = (as.drop j).reverse :=
    (List.reverse_drop (l := as) (i := j)).symm
  have hprevq := previousContinuant_take as hj
  have hprevr := previousContinuant_take as.reverse
    (n := as.length - j) (by simp)
  rw [← hprevq, ← hprevr]
  simp only [prefixDenom, hrev]
  simpa only [List.reverse_reverse, List.take_append_drop, continuant_reverse] using
    continuant_append (as.take j) (as.drop j)

end Lacunary.Reversal

namespace Lacunary.Reversal

/-- Positive partial quotients make the finite denominator profile nondecreasing. -/
theorem prefixDenom_monotone (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    Monotone (prefixDenom as) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < as.length
  · unfold prefixDenom
    rw [List.take_succ_eq_append_getElem hn, continuant_concat]
    have ha : 1 ≤ as[n] := hpos as[n] (List.getElem_mem hn)
    calc
      continuant (as.take n) ≤ as[n] * continuant (as.take n) := by nlinarith
      _ ≤ as[n] * continuant (as.take n) + previousContinuant (as.take n) :=
        Nat.le_add_right _ _
  · simp [prefixDenom, List.take_of_length_le (by omega : as.length ≤ n),
      List.take_of_length_le (by omega : as.length ≤ n + 1)]

/-- All finite denominator continuants are positive, including the empty prefix. -/
theorem prefixDenom_pos (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) (n : ℕ) :
    0 < prefixDenom as n := by
  have h := prefixDenom_monotone as hpos (Nat.zero_le n)
  simpa using (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) h)

theorem continuant_pos (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    0 < continuant as := by
  simpa using prefixDenom_pos as hpos as.length

/-- Section 3 endpoint estimate for the actual finite list denominator profiles. -/
theorem prefixDenom_log_close (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a)
    {j : ℕ} (hj : j ≤ as.length) :
    |Real.log (prefixDenom as.reverse (as.length - j) : ℝ) -
      (Real.log (continuant as : ℝ) - Real.log (prefixDenom as j : ℝ))| ≤
        Real.log 2 := by
  have hrpos : ∀ a ∈ as.reverse, 0 < a := by simpa using hpos
  apply split_log_close (prefixDenom_splitProfile as)
    (prefixDenom_monotone as hpos) (prefixDenom_monotone as.reverse hrpos)
    (fun n _ => prefixDenom_pos as hpos n)
    (fun n _ => prefixDenom_pos as.reverse hrpos n)
    (continuant_pos as hpos) hj

/-- Reversal sends each actual adjacent gap to an actual adjacent original gap. -/
theorem prefixDenom_reversed_gap (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a)
    {i : ℕ} (hi : i < as.length) :
    ∃ j, j < as.length ∧
      |Real.log (prefixDenom as.reverse i : ℝ) -
        (Real.log (continuant as : ℝ) -
          Real.log (prefixDenom as (j + 1) : ℝ))| ≤ Real.log 2 ∧
      |Real.log (prefixDenom as.reverse (i + 1) : ℝ) -
        (Real.log (continuant as : ℝ) -
          Real.log (prefixDenom as j : ℝ))| ≤ Real.log 2 := by
  let j := as.length - i - 1
  have hj : j < as.length := by dsimp [j]; omega
  have hk : as.length - (j + 1) = i := by dsimp [j]; omega
  have hl : as.length - j = i + 1 := by dsimp [j]; omega
  refine ⟨j, hj, ?_, ?_⟩
  · simpa only [hk] using prefixDenom_log_close as hpos (j := j + 1) (by omega)
  · simpa only [hl] using prefixDenom_log_close as hpos (j := j) (by omega)

/-- The profile starts at logarithm zero and ends at the logarithm of its denominator. -/
theorem prefixDenom_log_range (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a)
    {j : ℕ} (hj : j ≤ as.length) :
    0 ≤ Real.log (prefixDenom as j : ℝ) ∧
      Real.log (prefixDenom as j : ℝ) ≤ Real.log (continuant as : ℝ) := by
  constructor
  · apply Real.log_nonneg
    exact_mod_cast prefixDenom_monotone as hpos (Nat.zero_le j)
  · apply Real.log_le_log
    · exact_mod_cast prefixDenom_pos as hpos j
    · exact_mod_cast (show prefixDenom as j ≤ continuant as by
        simpa using prefixDenom_monotone as hpos hj)

/-- Folding a terminal `a,1` to `a+1` preserves the whole first matrix column. -/
theorem continuantMatrix_fold_last_one (as : List ℕ) (a : ℕ) (i : Fin 2) :
    continuantMatrix (as ++ [a, 1]) i 0 =
      continuantMatrix (as ++ [a + 1]) i 0 := by
  have hsplit : as ++ [a, 1] = (as ++ [a]) ++ [1] := by simp
  rw [hsplit, continuantMatrix_append, continuantMatrix_append]
  simp [continuantMatrix_append, quotientMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[simp] theorem continuant_fold_last_one (as : List ℕ) (a : ℕ) :
    continuant (as ++ [a, 1]) = continuant (as ++ [a + 1]) :=
  continuantMatrix_fold_last_one as a 0

/-- Before the folded endpoint, the denominator profiles are literally equal. -/
theorem prefixDenom_fold_last_one (as : List ℕ) (a : ℕ) {i : ℕ}
    (hi : i ≤ as.length) :
    prefixDenom (as ++ [a, 1]) i = prefixDenom (as ++ [a + 1]) i := by
  simp [prefixDenom, List.take_append_of_le_length hi]

/-- The canonicalized reversed denominator list deletes only the penultimate denominator. -/
theorem prefixDenom_fold_last_one_profile (as : List ℕ) (a : ℕ) :
    (∀ i, i ≤ as.length →
      prefixDenom (as ++ [a + 1]) i = prefixDenom (as ++ [a, 1]) i) ∧
    prefixDenom (as ++ [a + 1]) (as.length + 1) =
      prefixDenom (as ++ [a, 1]) (as.length + 2) := by
  constructor
  · exact fun i hi => (prefixDenom_fold_last_one as a hi).symm
  · have hlen1 : (as ++ [a + 1]).length = as.length + 1 := by simp
    have hlen2 : (as ++ [a, 1]).length = as.length + 2 := by simp
    rw [← hlen1, ← hlen2, prefixDenom_length, prefixDenom_length]
    exact (continuant_fold_last_one as a).symm

end Lacunary.Reversal

namespace Lacunary.Reversal

/-- Numerator of the finite simple continued fraction `[0; as]`. -/
def fractionNumerator (as : List ℕ) : ℕ := continuantMatrix as 1 0

@[simp] theorem fractionNumerator_nil : fractionNumerator [] = 0 := by
  simp [fractionNumerator]

@[simp] theorem fractionNumerator_cons (a : ℕ) (as : List ℕ) :
    fractionNumerator (a :: as) = continuant as := by
  simp [fractionNumerator, continuant, continuantMatrix, quotientMatrix,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem continuant_cons (a : ℕ) (as : List ℕ) :
    continuant (a :: as) = a * continuant as + fractionNumerator as := by
  simp [fractionNumerator, continuant, continuantMatrix, quotientMatrix,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- Consecutive continuants are coprime; this uses no positivity hypothesis. -/
theorem fractionNumerator_coprime (as : List ℕ) :
    Nat.Coprime (fractionNumerator as) (continuant as) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    rw [fractionNumerator_cons, continuant_cons, Nat.coprime_mul_right_add_right]
    exact ih.symm

/-- Recursive evaluation of a finite simple continued fraction `[0; as]`. -/
def finiteValue : List ℕ → ℚ
  | [] => 0
  | a :: as => ((a : ℚ) + finiteValue as)⁻¹

/-- The finite matrix construction computes the usual recursive fraction value. -/
theorem finiteValue_eq (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    finiteValue as = (fractionNumerator as : ℚ) / (continuant as : ℚ) := by
  revert hpos
  induction as with
  | nil => intro _; simp [finiteValue]
  | cons a as ih =>
    intro hpos
    have htail : ∀ b ∈ as, 0 < b := fun b hb => hpos b (by simp [hb])
    have hK : (continuant as : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (continuant_pos as htail))
    rw [finiteValue, ih htail, fractionNumerator_cons, continuant_cons]
    push_cast
    rw [show (a : ℚ) + (fractionNumerator as : ℚ) / (continuant as : ℚ) =
      ((a : ℚ) * (continuant as : ℚ) + (fractionNumerator as : ℚ)) /
        (continuant as : ℚ) by field_simp]
    rw [inv_div]

/-- The continuant is the reduced rational denominator, with no hidden cancellation. -/
theorem finiteValue_den (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    (finiteValue as).den = continuant as := by
  rw [finiteValue_eq as hpos]
  simpa using (Rat.den_div_eq_of_coprime
    (a := (fractionNumerator as : ℤ)) (b := (continuant as : ℤ))
    (by exact_mod_cast continuant_pos as hpos)
    (by simpa using fractionNumerator_coprime as))

/-- The matrix fold also preserves the reduced finite fraction value. -/
theorem finiteValue_fold_last_one (as : List ℕ) (a : ℕ)
    (hpos : ∀ b ∈ as, 0 < b) (ha : 0 < a) :
    finiteValue (as ++ [a, 1]) = finiteValue (as ++ [a + 1]) := by
  have hleft : ∀ b ∈ as ++ [a, 1], 0 < b := by
    intro b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl | rfl
    · exact hpos b hb
    · exact ha
    · norm_num
  have hright : ∀ b ∈ as ++ [a + 1], 0 < b := by
    intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hpos b hb
    · omega
  rw [finiteValue_eq _ hleft, finiteValue_eq _ hright]
  rw [continuant_fold_last_one]
  congr 1
  exact congrArg Nat.cast (continuantMatrix_fold_last_one as a 1)

/-- The final merged gap in the canonical reversed word corresponds to original gap 1.
Every earlier gap has the unmodified reversed gap correspondence. -/
theorem prefixDenom_folded_reversed_gap (a : ℕ) (as : List ℕ)
    (hpos : ∀ b ∈ 1 :: a :: as, 0 < b)
    {i : ℕ} (hi : i < (as.reverse ++ [a + 1]).length) :
    ∃ j, j < (1 :: a :: as).length ∧
      |Real.log (prefixDenom (as.reverse ++ [a + 1]) i : ℝ) -
        (Real.log (continuant (1 :: a :: as) : ℝ) -
          Real.log (prefixDenom (1 :: a :: as) (j + 1) : ℝ))| ≤ Real.log 2 ∧
      |Real.log (prefixDenom (as.reverse ++ [a + 1]) (i + 1) : ℝ) -
        (Real.log (continuant (1 :: a :: as) : ℝ) -
          Real.log (prefixDenom (1 :: a :: as) j : ℝ))| ≤ Real.log 2 := by
  have hrev : (1 :: a :: as).reverse = as.reverse ++ [a, 1] := by
    simp [List.reverse_cons, List.append_assoc]
  have hlow {k : ℕ} (hk : k ≤ as.length) :
      prefixDenom (as.reverse ++ [a + 1]) k = prefixDenom (1 :: a :: as).reverse k := by
    rw [hrev]
    exact (prefixDenom_fold_last_one as.reverse a (by simpa using hk)).symm
  by_cases hi0 : i < as.length
  · obtain ⟨j, hj, hlo, hhi⟩ := prefixDenom_reversed_gap (1 :: a :: as) hpos
      (i := i) (by simp; omega)
    refine ⟨j, hj, ?_, ?_⟩
    · rw [hlow (by omega)]
      exact hlo
    · rw [hlow (by omega)]
      exact hhi
  · have hi1 : i = as.length := by
      have hilen : i < as.length + 1 := by simpa using hi
      omega
    subst i
    refine ⟨1, by simp, ?_, ?_⟩
    · rw [hlow (by omega)]
      simpa [List.length_cons] using
        prefixDenom_log_close (1 :: a :: as) hpos (j := 2) (by simp)
    · have hlen : (as.reverse ++ [a + 1]).length = as.length + 1 := by simp
      have htop : prefixDenom (as.reverse ++ [a + 1]) (as.length + 1) =
          continuant (1 :: a :: as) := by
        rw [← hlen, prefixDenom_length, ← continuant_fold_last_one as.reverse a,
          ← hrev, continuant_reverse]
      have hone : prefixDenom (1 :: a :: as) 1 = 1 := by simp [prefixDenom]
      rw [htop, hone]
      simpa using (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

end Lacunary.Reversal

namespace Lacunary.Reversal

/-- The matrix profile consists of actual reduced denominators of finite convergents. -/
theorem prefixDenom_eq_finiteValue_den (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) (n : ℕ) :
    prefixDenom as n = (finiteValue (as.take n)).den := by
  exact (finiteValue_den (as.take n) (fun a ha => hpos a (List.mem_of_mem_take ha))).symm

/-- Reverse the quotient word and fold a final pair ending in one when necessary. -/
def canonicalReverseWord (as : List ℕ) : List ℕ :=
  match as with
  | a :: b :: bs => if a = 1 then bs.reverse ++ [b + 1] else as.reverse
  | _ => as.reverse

theorem canonicalReverseWord_pos (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    ∀ a ∈ canonicalReverseWord as, 0 < a := by
  cases as with
  | nil => simp [canonicalReverseWord]
  | cons a as =>
    cases as with
    | nil => simpa [canonicalReverseWord] using hpos
    | cons b bs =>
      by_cases ha : a = 1
      · intro c hc
        simp only [canonicalReverseWord, ite_eq_left ha, List.mem_append, List.mem_reverse,
          List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact hpos c (by simp [hc])
        · omega
      · simpa only [canonicalReverseWord, ite_eq_right ha, List.mem_reverse] using hpos

/-- The reversed and canonically folded word retains the original reduced denominator. -/
theorem continuant_canonicalReverseWord (as : List ℕ) :
    continuant (canonicalReverseWord as) = continuant as := by
  cases as with
  | nil => simp [canonicalReverseWord]
  | cons a as =>
    cases as with
    | nil => simp [canonicalReverseWord]
    | cons b bs =>
      by_cases ha : a = 1
      · subst a
        simp only [canonicalReverseWord]
        calc
          continuant (bs.reverse ++ [b + 1]) = continuant (bs.reverse ++ [b, 1]) :=
            (continuant_fold_last_one bs.reverse b).symm
          _ = continuant (1 :: b :: bs).reverse := by
            simp only [List.reverse_cons, List.append_assoc, List.cons_append,
              List.nil_append]
          _ = continuant (1 :: b :: bs) := continuant_reverse _
      · simp only [canonicalReverseWord, ite_eq_right ha]
        exact continuant_reverse _

theorem finiteValue_canonicalReverseWord_den (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    (finiteValue (canonicalReverseWord as)).den = (finiteValue as).den := by
  rw [finiteValue_den _ (canonicalReverseWord_pos as hpos), finiteValue_den as hpos,
    continuant_canonicalReverseWord]

/-- For denominator at least two, the reversed word is nonempty and ends in a quotient
at least two, so the output really has canonical finite simple-CF form. -/
theorem canonicalReverseWord_last_ge_two (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a)
    (hV : 2 ≤ continuant as) :
    ∃ bs a, canonicalReverseWord as = bs ++ [a] ∧ 2 ≤ a := by
  cases as with
  | nil => simp at hV
  | cons a as =>
    cases as with
    | nil => exact ⟨[], a, by simp [canonicalReverseWord], by simpa using hV⟩
    | cons b bs =>
      by_cases ha : a = 1
      · have hb : 0 < b := hpos b (by simp)
        exact ⟨bs.reverse, b + 1, by simp [canonicalReverseWord, ha], by omega⟩
      · have ha0 : 0 < a := hpos a (by simp)
        exact ⟨(b :: bs).reverse, a,
          by simp [canonicalReverseWord, ha, List.reverse_cons], by omega⟩

/-- Full finite-list reversal gap theorem, including canonical folding of the final one.
No abstract split identity, monotonicity, or coprimality is assumed. -/
theorem prefixDenom_canonicalReversed_gap (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a)
    {i : ℕ} (hi : i < (canonicalReverseWord as).length) :
    ∃ j, j < as.length ∧
      |Real.log (prefixDenom (canonicalReverseWord as) i : ℝ) -
        (Real.log (continuant as : ℝ) - Real.log (prefixDenom as (j + 1) : ℝ))| ≤
          Real.log 2 ∧
      |Real.log (prefixDenom (canonicalReverseWord as) (i + 1) : ℝ) -
        (Real.log (continuant as : ℝ) - Real.log (prefixDenom as j : ℝ))| ≤
          Real.log 2 := by
  cases as with
  | nil => simp [canonicalReverseWord] at hi
  | cons a as =>
    cases as with
    | nil =>
      simpa only [canonicalReverseWord] using prefixDenom_reversed_gap [a] hpos hi
    | cons b bs =>
      by_cases ha : a = 1
      · subst a
        have hi1 : i < (bs.reverse ++ [b + 1]).length := by
          simpa [canonicalReverseWord] using hi
        simpa [canonicalReverseWord] using
          prefixDenom_folded_reversed_gap b bs hpos hi1
      · have hi1 : i < (a :: b :: bs).length := by
          simpa only [canonicalReverseWord, ite_eq_right ha, List.length_reverse] using hi
        simpa [canonicalReverseWord, ha] using
          prefixDenom_reversed_gap (a :: b :: bs) hpos hi1

end Lacunary.Reversal

namespace Lacunary.Reversal

/-- Adding the integer part does not alter any finite convergent denominator. -/
theorem finiteConvergent_den (a0 : ℤ) (as : List ℕ)
    (hpos : ∀ a ∈ as, 0 < a) (n : ℕ) :
    ((a0 : ℚ) + finiteValue (as.take n)).den = prefixDenom as n := by
  rw [Rat.intCast_add_den, ← prefixDenom_eq_finiteValue_den as hpos n]

/-- Section 3 for a concrete finite quotient word: canonical reversed fraction, same
reduced denominator, and reflected endpoints of actual adjacent original gaps. -/
theorem finite_reversal_profile (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a)
    (hV : 2 ≤ continuant as) :
    (finiteValue (canonicalReverseWord as)).den = (finiteValue as).den ∧
    (∃ bs a, canonicalReverseWord as = bs ++ [a] ∧ 2 ≤ a) ∧
    ∀ i, i < (canonicalReverseWord as).length →
      ∃ j, j < as.length ∧
        0 ≤ Real.log (prefixDenom as j : ℝ) ∧
        Real.log (prefixDenom as j : ℝ) ≤ Real.log (prefixDenom as (j + 1) : ℝ) ∧
        Real.log (prefixDenom as (j + 1) : ℝ) ≤ Real.log (continuant as : ℝ) ∧
        |Real.log (prefixDenom (canonicalReverseWord as) i : ℝ) -
          (Real.log (continuant as : ℝ) - Real.log (prefixDenom as (j + 1) : ℝ))| ≤
            Real.log 2 ∧
        |Real.log (prefixDenom (canonicalReverseWord as) (i + 1) : ℝ) -
          (Real.log (continuant as : ℝ) - Real.log (prefixDenom as j : ℝ))| ≤
            Real.log 2 := by
  refine ⟨finiteValue_canonicalReverseWord_den as hpos,
    canonicalReverseWord_last_ge_two as hpos hV, ?_⟩
  intro i hi
  obtain ⟨j, hj, hlo, hhi⟩ := prefixDenom_canonicalReversed_gap as hpos hi
  refine ⟨j, hj, (prefixDenom_log_range as hpos hj.le).1, ?_,
    (prefixDenom_log_range as hpos (by omega : j + 1 ≤ as.length)).2, hlo, hhi⟩
  exact Real.log_le_log (by exact_mod_cast prefixDenom_pos as hpos j)
    (by exact_mod_cast prefixDenom_monotone as hpos (Nat.le_succ j))

end Lacunary.Reversal


namespace Lacunary.Reversal

@[simp] theorem fractionNumerator_reverse (as : List ℕ) :
    fractionNumerator as.reverse = previousContinuant as := by
  simp [fractionNumerator, previousContinuant, continuantMatrix_reverse,
    Matrix.transpose_apply]

/-- The unmerged reversed fraction is exactly the penultimate denominator over the final one. -/
theorem finiteValue_reverse_eq (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    finiteValue as.reverse = (previousContinuant as : ℚ) / (continuant as : ℚ) := by
  rw [finiteValue_eq as.reverse (by simpa using hpos), fractionNumerator_reverse,
    continuant_reverse]

/-- Canonical folding changes no fraction value. -/
theorem finiteValue_canonicalReverseWord_eq_reverse (as : List ℕ)
    (hpos : ∀ a ∈ as, 0 < a) :
    finiteValue (canonicalReverseWord as) = finiteValue as.reverse := by
  cases as with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons b bs =>
      by_cases ha : a = 1
      · subst a
        have hb : 0 < b := hpos b (by simp)
        have htail : ∀ c ∈ bs.reverse, 0 < c := by
          intro c hc
          exact hpos c (by simpa using Or.inr (Or.inr (List.mem_reverse.mp hc)))
        have hrev : (1 :: b :: bs).reverse = bs.reverse ++ [b, 1] := by
          simp [List.reverse_cons, List.append_assoc]
        simpa only [canonicalReverseWord, hrev, ite_true] using
          (finiteValue_fold_last_one bs.reverse b htail hb).symm
      · simp only [canonicalReverseWord, ite_eq_right ha]

/-- The output is precisely the rational `q_(m-1) / V` used in the paper. -/
theorem finiteValue_canonicalReverseWord_eq_previous (as : List ℕ)
    (hpos : ∀ a ∈ as, 0 < a) :
    finiteValue (canonicalReverseWord as) =
      (prevDenom (prefixDenom as) as.length : ℚ) / (continuant as : ℚ) := by
  rw [finiteValue_canonicalReverseWord_eq_reverse as hpos, finiteValue_reverse_eq as hpos]
  have hprev := previousContinuant_take as (n := as.length) le_rfl
  simpa only [List.take_length] using congrArg
    (fun n : ℕ => (n : ℚ) / (continuant as : ℚ)) hprev

end Lacunary.Reversal

#print axioms Lacunary.Reversal.prefixDenom_splitProfile
#print axioms Lacunary.Reversal.prefixDenom_log_close
#print axioms Lacunary.Reversal.finiteValue_den
#print axioms Lacunary.Reversal.finiteConvergent_den
#print axioms Lacunary.Reversal.prefixDenom_folded_reversed_gap
#print axioms Lacunary.Reversal.finite_reversal_profile
#print axioms Lacunary.Reversal.finiteValue_canonicalReverseWord_eq_previous

/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Statement

@[expose] public section

open Filter Set
open scoped Topology

namespace Paper4

/-- Admissibility is downward closed without changing the unit constant. -/
theorem exponentAdmissible_mono {x ν η : ℝ}
    (h : exponentAdmissible x ν) (hην : η ≤ ν) : exponentAdmissible x η := by
  apply h.mono
  rintro q ⟨p, hq, hp⟩
  refine ⟨p, hq, hp.trans_le ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hq
  · linarith

/-- Each admitted real exponent lies below the extended supremum. -/
theorem le_irrationalityExponent_of_admissible {x ν : ℝ}
    (h : exponentAdmissible x ν) : (ν : EReal) ≤ irrationalityExponent x := by
  exact le_sSup ⟨ν, h, rfl⟩

/-- Every real exponent strictly below the supremum is admissible. -/
theorem exponentAdmissible_of_lt_irrationalityExponent {x ν : ℝ}
    (h : (ν : EReal) < irrationalityExponent x) : exponentAdmissible x ν := by
  obtain ⟨_, ⟨η, hη, rfl⟩, hνη⟩ := (lt_sSup_iff).1 h
  exact exponentAdmissible_mono hη (EReal.coe_lt_coe_iff.1 hνη).le

/-- A direct upper-bound interface, valid also for infinite proposed values. -/
theorem irrationalityExponent_le_iff {x : ℝ} {M : EReal} :
    irrationalityExponent x ≤ M ↔
      ∀ ν : ℝ, exponentAdmissible x ν → (ν : EReal) ≤ M := by
  constructor
  · intro h ν hν
    exact (le_irrationalityExponent_of_admissible hν).trans h
  · intro h
    exact sSup_le (by rintro _ ⟨ν, hν, rfl⟩; exact h ν hν)

/-- Strictly-below threshold hypotheses determine the lower bound, including `⊤`. -/
theorem le_irrationalityExponent_of_threshold {x : ℝ} {M : EReal}
    (h : ∀ ν : ℝ, (ν : EReal) < M → exponentAdmissible x ν) :
    M ≤ irrationalityExponent x := by
  refine (le_sSup_iff_forall_lt).2 ?_
  intro z hz
  obtain ⟨r, hzr, hrM⟩ := EReal.exists_rat_btwn_of_lt hz
  exact ⟨(r : ℝ), ⟨(r : ℝ), h (r : ℝ) hrM, rfl⟩, hzr⟩

/-- This is the exact order-theoretic closure interface used in Section 8. -/
theorem irrationalityExponent_eq_of_thresholds {x : ℝ} {M : EReal}
    (hlower : ∀ ν : ℝ, (ν : EReal) < M → exponentAdmissible x ν)
    (hupper : ∀ ν : ℝ, exponentAdmissible x ν → (ν : EReal) ≤ M) :
    irrationalityExponent x = M := by
  exact le_antisymm (irrationalityExponent_le_iff.2 hupper)
    (le_irrationalityExponent_of_threshold hlower)

/-- Infinite exponent is exactly admissibility of every finite exponent. -/
theorem irrationalityExponent_eq_top_iff {x : ℝ} :
    irrationalityExponent x = ⊤ ↔ ∀ ν : ℝ, exponentAdmissible x ν := by
  constructor
  · intro h ν
    apply exponentAdmissible_of_lt_irrationalityExponent
    rw [h]
    exact EReal.coe_lt_top _
  · intro h
    exact top_unique (le_irrationalityExponent_of_threshold (fun ν _ => h ν))

/-- Failure of admissibility is precisely an eventual lower bound for all fractions. -/
theorem not_exponentAdmissible_iff {x ν : ℝ} :
    ¬ exponentAdmissible x ν ↔
      ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, 0 < q →
        (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)| := by
  simp only [exponentAdmissible, not_frequently, not_exists, not_and, not_lt]

/-- A denominator sequence tending to infinity transports frequent approximations. -/
theorem exponentAdmissible_of_sequence {x ν : ℝ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (h : ∃ᶠ n : ℕ in atTop, ∃ p : ℤ, 0 < q n ∧
      |x - (p : ℝ) / (q n : ℝ)| < (q n : ℝ) ^ (-ν)) :
    exponentAdmissible x ν := by
  exact hq.frequently h

/-- Removing an arbitrary positive approximation constant only costs a strict exponent drop. -/
theorem exponentAdmissible_of_liouvilleWith {x ν η : ℝ}
    (h : LiouvilleWith ν x) (hην : η < ν) : exponentAdmissible x η := by
  have hη := h.frequently_lt_rpow_neg hην
  exact ((eventually_gt_atTop 0).and_frequently hη).mono (by
    rintro q ⟨hq, p, _, hp⟩
    exact ⟨p, hq, hp⟩)

/-- For an irrational input, unit-constant admissibility implies `LiouvilleWith`. -/
theorem liouvilleWith_of_exponentAdmissible {x ν : ℝ} (hx : Irrational x)
    (h : exponentAdmissible x ν) : LiouvilleWith ν x := by
  refine ⟨1, h.mono ?_⟩
  rintro q ⟨p, hq, hp⟩
  refine ⟨p, ?_, ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hx.ne_rat (p / q)
  · simpa [Real.rpow_neg (Nat.cast_nonneg q), one_div] using hp

/-- Constant-one exponents and constant-allowed exponents have the same supremum
for irrational inputs. No assertion about endpoint membership is required. -/
theorem irrationalityExponent_eq_liouville_sSup {x : ℝ} (hx : Irrational x) :
    irrationalityExponent x =
      sSup (Set.image (fun ν : ℝ => (ν : EReal)) {ν | LiouvilleWith ν x}) := by
  apply le_antisymm
  · exact irrationalityExponent_le_iff.2 (fun ν hν =>
      le_sSup ⟨ν, liouvilleWith_of_exponentAdmissible hx hν, rfl⟩)
  · refine sSup_le ?_
    rintro z ⟨ν, hν, rfl⟩
    apply le_irrationalityExponent_of_threshold
    intro η hην
    exact exponentAdmissible_of_liouvilleWith hν (EReal.coe_lt_coe_iff.1 hην)

/-- Every real number admits all exponents strictly below one. -/
theorem exponentAdmissible_of_lt_one (x : ℝ) {ν : ℝ} (hν : ν < 1) :
    exponentAdmissible x ν :=
  exponentAdmissible_of_liouvilleWith (liouvilleWith_one x) hν

/-- The custom exponent is never `⊥`. -/
theorem one_le_irrationalityExponent (x : ℝ) :
    (1 : EReal) ≤ irrationalityExponent x := by
  apply le_irrationalityExponent_of_threshold
  intro ν hν
  exact exponentAdmissible_of_lt_one x (EReal.coe_lt_coe_iff.1 hν)

#print axioms irrationalityExponent_eq_of_thresholds
#print axioms irrationalityExponent_eq_liouville_sSup

end Paper4

namespace Paper4

/-- Finite translation is an order automorphism of the extended reals. -/
noncomputable def erealTranslate (a : ℝ) : EReal ≃o EReal where
  toFun := fun x => (a : EReal) + x
  invFun := fun x => ((-a : ℝ) : EReal) + x
  left_inv := by intro x; induction x <;> simp only [EReal.add_bot, EReal.coe_add_top, ← EReal.coe_add, neg_add_cancel_left]
  right_inv := by intro x; induction x <;> simp only [EReal.add_bot, EReal.coe_add_top, ← EReal.coe_add, add_neg_cancel_left]
  map_rel_iff' := (EReal.addLECancellable_coe a).add_le_add_iff_left

/-- Translating by a finite value commutes with the extended-real limsup. -/
theorem ereal_add_limsup (a : ℝ) (v : ℕ → EReal) :
    (a : EReal) + limsup v atTop =
      limsup (fun n => (a : EReal) + v n) atTop :=
  (erealTranslate a).limsup_apply

/-- Frequent real approximation orders yield the corresponding extended lower bound. -/
theorem limsup_le_irrationalityExponent_of_approximations
    {x : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ} {a : ℕ → ℝ}
    (hq : Tendsto q atTop atTop)
    (happrox : ∀ᶠ n : ℕ in atTop,
      |x - (p n : ℝ) / (q n : ℝ)| ≤ (q n : ℝ) ^ (-a n)) :
    limsup (fun n => (a n : EReal)) atTop ≤ irrationalityExponent x := by
  apply le_irrationalityExponent_of_threshold
  intro ν hν
  have hfreq : ∃ᶠ n : ℕ in atTop, ν < a n := by
    simpa only [EReal.coe_lt_coe_iff] using
      (frequently_lt_of_lt_limsup (by isBoundedDefault) hν)
  have hq2 : ∀ᶠ n : ℕ in atTop, 1 < q n :=
    hq.eventually (eventually_gt_atTop 1)
  apply exponentAdmissible_of_sequence hq
  refine ((happrox.and hq2).and_frequently hfreq).mono ?_
  rintro n ⟨⟨hn, hqn⟩, hνn⟩
  refine ⟨p n, Nat.zero_lt_of_lt hqn, hn.trans_lt ?_⟩
  exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hqn) (by linarith)

/-- Shifted consecutive denominator ratio; callers supply positive logarithms. -/
noncomputable def cfLogRatio (q : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (q (n + 1) : ℝ) / Real.log (q n : ℝ)

/-- The continued-fraction exponent candidate is genuinely extended real. -/
noncomputable def cfExponentCandidate (q : ℕ → ℕ) : EReal :=
  (1 : EReal) + limsup (fun n => (cfLogRatio q n : EReal)) atTop

/-- Exact logarithmic rewriting of the standard upper error bound. -/
theorem cf_upper_error_eq_rpow {b c : ℝ} (hb : 1 < b) (hc : 0 < c) :
    1 / (b * c) = b ^ (-(1 + Real.log c / Real.log b)) := by
  have hlog : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  rw [Real.rpow_neg (by linarith), Real.rpow_add (by linarith), Real.rpow_one]
  have hc' : b ^ (Real.log c / Real.log b) = c := by
    rw [Real.rpow_def_of_pos (by linarith)]
    convert Real.exp_log hc using 1
    congr 1
    field_simp
  rw [hc', one_div]

/-- The CF lower direction needs only diverging denominators and the usual upper
error estimate. It covers an infinite denominator-ratio limsup. -/
theorem cfExponentCandidate_le_irrationalityExponent
    {x : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hq2 : ∀ n, 2 ≤ q n)
    (happrox : ∀ᶠ n : ℕ in atTop,
      |x - (p n : ℝ) / (q n : ℝ)| ≤
        1 / ((q n : ℝ) * (q (n + 1) : ℝ))) :
    cfExponentCandidate q ≤ irrationalityExponent x := by
  have herr : ∀ᶠ n : ℕ in atTop,
      |x - (p n : ℝ) / (q n : ℝ)| ≤
        (q n : ℝ) ^ (-(1 + cfLogRatio q n)) := by
    apply happrox.mono
    intro n hn
    rw [cfLogRatio, ← cf_upper_error_eq_rpow
      (b := (q n : ℝ)) (c := (q (n + 1) : ℝ))
      (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (hq2 n)))
      (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hq2 (n + 1))))]
    exact hn
  have h := limsup_le_irrationalityExponent_of_approximations hq herr
  change (1 : ℝ) + limsup (fun n => (cfLogRatio q n : EReal)) atTop ≤ _
  rw [ereal_add_limsup]
  simpa only [EReal.coe_add, EReal.coe_one] using h

#print axioms cfExponentCandidate_le_irrationalityExponent

end Paper4

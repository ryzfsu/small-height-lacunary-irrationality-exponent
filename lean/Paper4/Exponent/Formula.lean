/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Exponent.CF
public import Paper4.CF.Irrational

@[expose] public section

open Filter
open scoped Topology

namespace Paper4

/-- Standard continued-fraction formula for the exact custom exponent from
`Paper4.Statement`. The shift ensures that logarithms have positive arguments
strictly larger than one. Both sides take values in `EReal`. -/
theorem irrationalityExponent_cf_formula {x : ℝ} (hx : Irrational x) :
    irrationalityExponent x = (1 : EReal) +
      limsup (fun n => ((Real.log (cfQ x (n + 1) : ℝ) /
        Real.log (cfQ x n : ℝ) : ℝ) : EReal)) atTop := by
  exact irrationalityExponent_eq_cfExponentCandidate
    (cfQ_tendsto hx) (cfQ_ge_two hx) (cfQ_mono hx)
    (Eventually.of_forall (cf_upper hx)) (cf_lower hx)
    (cf_legendre_eventually hx)

/-- The usual universal lower bound follows from the same actual CF package. -/
theorem two_le_irrationalityExponent_cf {x : ℝ} (hx : Irrational x) :
    (2 : EReal) ≤ irrationalityExponent x := by
  rw [irrationalityExponent_cf_formula hx]
  exact two_le_cfExponentCandidate (cfQ_ge_two hx) (cfQ_mono hx)

/-- An infinite CF ratio limsup is exactly an infinite custom exponent. -/
theorem irrationalityExponent_top_iff_cf_limsup_top {x : ℝ} (hx : Irrational x) :
    irrationalityExponent x = ⊤ ↔
      limsup (fun n => ((Real.log (cfQ x (n + 1) : ℝ) /
        Real.log (cfQ x n : ℝ) : ℝ) : EReal)) atTop = ⊤ := by
  rw [irrationalityExponent_cf_formula hx]
  simp [← EReal.coe_one, EReal.add_eq_top_iff]

/-- The formula may be converted to real values only after excluding `⊤`.
There is no hidden finite-valued assumption in the extended formula above. -/
theorem irrationalityExponent_cf_formula_toReal {x : ℝ} (hx : Irrational x)
    (hfinite : limsup (fun n => (cfLogRatio (cfQ x) n : EReal)) atTop ≠ ⊤) :
    (irrationalityExponent x).toReal = 1 +
      (limsup (fun n => (cfLogRatio (cfQ x) n : EReal)) atTop).toReal := by
  have hformula : irrationalityExponent x = cfExponentCandidate (cfQ x) :=
    irrationalityExponent_cf_formula hx
  have hbot : limsup (fun n => (cfLogRatio (cfQ x) n : EReal)) atTop ≠ ⊥ := by
    intro h
    have hmu : irrationalityExponent x = ⊥ := by
      rw [hformula, cfExponentCandidate, h]
      simp
    have htwo := two_le_irrationalityExponent_cf hx
    rw [hmu] at htwo
    exact EReal.coe_ne_bot 2 (le_bot_iff.1 htwo)
  rw [hformula, cfExponentCandidate, ← EReal.coe_one,
    EReal.toReal_add (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1) hfinite hbot]
  simp

#print axioms irrationalityExponent_cf_formula
#print axioms two_le_irrationalityExponent_cf
#print axioms irrationalityExponent_top_iff_cf_limsup_top
#print axioms irrationalityExponent_cf_formula_toReal

end Paper4

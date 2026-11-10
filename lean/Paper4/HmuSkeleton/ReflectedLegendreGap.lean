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

theorem reflected_legendre_gap_witness {x : ℝ} {r : ℚ}
    (hne : x ≠ (r : ℝ))
    (hcut : |x - (r : ℝ)| * (r.den : ℝ) ^ 2 < 1 / 8) :
    ∃ H : CFGap x,
      H.value = r ∧
      (GenContFract.of x).convs H.index = (r : ℝ) ∧
      ¬(GenContFract.of x).TerminatedAt H.index ∧
      0 < H.nextDen ∧
      r.den ≤ H.nextDen ∧
      (GenContFract.of x).dens H.index = (r.den : ℝ) ∧
      (GenContFract.of x).dens (H.index + 1) = (H.nextDen : ℝ) ∧
      1 / ((r.den : ℝ) * ((H.nextDen : ℝ) + (r.den : ℝ))) ≤
        |x - (r : ℝ)| ∧
      |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * (H.nextDen : ℝ)) := by
  have hden : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hleg : |x - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r.den : ℝ) ^ 2)).2
    nlinarith [hcut]
  obtain ⟨H, hvalue⟩ := cfGap_legendre hne hleg
  have hbounds := cfGap_bounds H
  have hpair := Lacunary.CFBridge.nonterminal_num_den H.value_eq H.nonterminal
  refine ⟨H, hvalue, ?_, H.nonterminal, hbounds.1,
    ?_, ?_, H.nextDen_eq, ?_, ?_⟩
  · simpa [hvalue] using H.value_eq
  · simpa [hvalue] using hbounds.2.1
  · simpa [hvalue] using hpair.2
  · simpa [hvalue] using hbounds.2.2.1
  · simpa [hvalue] using hbounds.2.2.2

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.reflected_legendre_gap_witness

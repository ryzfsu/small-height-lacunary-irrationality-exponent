/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.Arithmetic.Definitions

@[expose] public section

open Filter
open Asymptotics
open scoped Topology

namespace Paper4

private theorem trunc_den_le_height (q : ℚ) : q.den ≤ rationalHeight q :=
  le_max_right _ _

private theorem trunc_rat_sum_den_dvd_common {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (bound : ℕ)
    (hbound : ∀ i ∈ s, (f i).den ∣ bound) :
    (∑ i ∈ s, f i).den ∣ bound := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (Rat.add_den_dvd_lcm _ _).trans
        (Nat.lcm_dvd (hbound i (by simp))
          (ih (fun j hj => hbound j (by simp [hj]))))

private theorem trunc_rat_term_den_dvd (N : ℕ) (hN : N ≠ 0)
    (q : ℚ) (n : ℕ) :
    (q / (N : ℚ) ^ n).den ∣ q.den * N ^ n := by
  have hp : N ^ n ≠ 0 := pow_ne_zero _ hN
  simpa [div_eq_mul_inv, Nat.cast_pow, Rat.inv_natCast_den, hN] using
    Rat.mul_den_dvd q ((N ^ n : ℕ) : ℚ)⁻¹

/-- Every truncation denominator divides the explicit unreduced denominator `Q`.
Only monotonicity of the exponents is needed to place each earlier power into the
last power. -/
theorem trunc_den_dvd_Q
    (N : ℕ) (hN : N ≠ 0) (u : ℕ → ℕ) (hu : Monotone u)
    (c : ℕ → ℚ) (n : ℕ) :
    (trunc N u c n).den ∣ Q N u c n := by
  unfold Q D
  apply trunc_rat_sum_den_dvd_common
  intro j hj
  have hjn : j ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hprod : (c j).den ∣ ∏ i ∈ Finset.range (n + 1), (c i).den :=
    Finset.dvd_prod_of_mem _ hj
  have hpow : N ^ u j ∣ N ^ u n := pow_dvd_pow N (hu hjn)
  exact (trunc_rat_term_den_dvd N hN (c j) (u j)).trans (by
    simpa [Nat.mul_comm] using Nat.mul_dvd_mul hprod hpow)

/-- The reduced truncation denominator is bounded by the height product. -/
theorem trunc_den_le_Q_height
    (N : ℕ) (hN : 0 < N) (u : ℕ → ℕ) (hu : Monotone u)
    (c : ℕ → ℚ) (n : ℕ) :
    (trunc N u c n).den ≤
      N ^ u n * ∏ j ∈ Finset.range (n + 1), rationalHeight (c j) := by
  have hcommon : 0 < N ^ u n * ∏ j ∈ Finset.range (n + 1), (c j).den := by
    apply Nat.mul_pos (pow_pos hN _)
    exact Finset.prod_pos (fun i hi => (c i).den_pos)
  apply (Nat.le_of_dvd hcommon (trunc_den_dvd_Q N hN.ne' u hu c n)).trans
  exact Nat.mul_le_mul_left _
    (Finset.prod_le_prod (fun i hi => trunc_den_le_height (c i)))

private theorem log_D_eq_sum_log_den (c : ℕ → ℚ) (n : ℕ) :
    Real.log (D c n : ℝ) =
      ∑ j ∈ Finset.range (n + 1), Real.log ((c j).den : ℝ) := by
  unfold D
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro i hi
  exact_mod_cast (c i).den_nz

private theorem log_D_le_sum_log_height (c : ℕ → ℚ) (n : ℕ) :
    Real.log (D c n : ℝ) ≤
      ∑ j ∈ Finset.range (n + 1),
        Real.log (rationalHeight (c j) : ℝ) := by
  rw [log_D_eq_sum_log_den]
  apply Finset.sum_le_sum
  intro i hi
  apply Real.log_le_log
  · exact_mod_cast (c i).den_pos
  · exact_mod_cast trunc_den_le_height (c i)

/-- The coefficient-height prefix estimate transfers to the concrete denominator
product.  The height-prefix input is intentionally explicit: it is supplied by
`Arithmetic.HeightSum` when that module is integrated. -/
theorem log_D_div_u_tendsto_zero_of_height_sum
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (c : ℕ → ℚ)
    (hheight_sum : Tendsto
      (fun n =>
        (∑ j ∈ Finset.range (n + 1),
          Real.log (rationalHeight (c j) : ℝ)) / (u n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (D c n : ℝ) / (u n : ℝ))
      atTop (𝓝 0) := by
  have hnonneg : ∀ n, 0 ≤ Real.log (D c n : ℝ) / (u n : ℝ) := by
    intro n
    apply div_nonneg
    · exact Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (D_pos c n).ne'))
    · exact_mod_cast (hu_pos n).le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hheight_sum ?_ ?_
  · filter_upwards with n
    exact hnonneg n
  · filter_upwards with n
    have hden : 0 ≤ (u n : ℝ) := by exact_mod_cast (hu_pos n).le
    exact div_le_div_of_nonneg_right (log_D_le_sum_log_height c n) hden

/-- The preceding ratio statement in the asymptotic notation used by the
arithmetic interfaces. -/
theorem log_D_isLittleO_u_of_height_sum
    (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (c : ℕ → ℚ)
    (hheight_sum : Tendsto
      (fun n =>
        (∑ j ∈ Finset.range (n + 1),
          Real.log (rationalHeight (c j) : ℝ)) / (u n : ℝ))
      atTop (𝓝 0)) :
    (fun n => Real.log (D c n : ℝ)) =o[atTop] (fun n => (u n : ℝ)) := by
  apply Asymptotics.isLittleO_of_tendsto
  · intro n hn
    have hne : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu_pos n).ne'
    exact (hne hn).elim
  · simpa only [Function.comp_apply] using
      log_D_div_u_tendsto_zero_of_height_sum u hu_pos c hheight_sum

private theorem log_Q_eq_scale_add_log_D
    (N : ℕ) (hN : 0 < N) (u : ℕ → ℕ) (c : ℕ → ℚ) (n : ℕ) :
    Real.log (Q N u c n : ℝ) =
      (u n : ℝ) * Real.log (N : ℝ) + Real.log (D c n : ℝ) := by
  unfold Q
  rw [Nat.cast_mul, Nat.cast_pow]
  rw [Real.log_mul (by exact_mod_cast (pow_ne_zero _ hN.ne'))
    (by exact_mod_cast (D_pos c n).ne')]
  rw [Real.log_pow]

/-- The raw common denominator has logarithmic scale `t` up to a vanishing
height-product correction. -/
theorem log_Q_div_t_tendsto_one_of_log_D
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (c : ℕ → ℚ)
    (hlogD : Tendsto (fun n => Real.log (D c n : ℝ) / (u n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (Q N u c n : ℝ) / t N u n)
      atTop (𝓝 1) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by decide) hN
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hbase : Tendsto
      (fun n => (1 : ℝ) +
        (Real.log (D c n : ℝ) / (u n : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (hlogD.div_const (Real.log (N : ℝ))))
  apply hbase.congr'
  filter_upwards [] with n
  have hu0 : (u n : ℝ) ≠ 0 := by exact_mod_cast (hu_pos n).ne'
  rw [t, log_Q_eq_scale_add_log_D N hNpos u c n]
  field_simp [hu0, ne_of_gt hlogN]

/-- Convenience wrapper using the explicit cumulative height input. -/
theorem log_Q_div_t_tendsto_one_of_height_sum
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (hu_pos : ∀ j, 0 < u j)
    (c : ℕ → ℚ)
    (hheight_sum : Tendsto
      (fun n =>
        (∑ j ∈ Finset.range (n + 1),
          Real.log (rationalHeight (c j) : ℝ)) / (u n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (Q N u c n : ℝ) / t N u n)
      atTop (𝓝 1) := by
  apply log_Q_div_t_tendsto_one_of_log_D N hN u hu_pos c
  exact log_D_div_u_tendsto_zero_of_height_sum u hu_pos c hheight_sum

/-- The unreduced common denominator diverges along any strictly increasing
positive exponent sequence. -/
theorem tendsto_Q_atTop
    (N : ℕ) (hN : 2 ≤ N) (u : ℕ → ℕ) (_hu_pos : ∀ j, 0 < u j)
    (hu_strict : StrictMono u) (c : ℕ → ℚ) :
    Tendsto (fun n => Q N u c n) atTop atTop := by
  have hpow : Tendsto (fun n => N ^ u n) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℕ) < N by omega)).comp hu_strict.tendsto_atTop
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hpow.eventually (eventually_ge_atTop b)] with n hn
  change b ≤ N ^ u n * D c n
  exact hn.trans (Nat.le_mul_of_pos_right _ (D_pos c n))

end Paper4

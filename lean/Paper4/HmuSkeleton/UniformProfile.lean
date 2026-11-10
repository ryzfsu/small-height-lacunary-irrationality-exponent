/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.HmuSkeleton.PerturbationCases
public import Mathlib
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter Asymptotics
open scoped Topology

def ProfileStepCases (κ F η M A C k a g : ℝ) : Prop :=
  g ≤ C ∨
  (∃ g₀, g₀ ≤ κ * a + A + C * k ∧ g ≤ g₀ + C) ∨
  (a = M ∧ g ≤ (F - 2 + η) * M) ∨
  (g ≤ 2 * η * M ∧ (1 - 2 * η) * M ≤ a) ∨
  (∃ c g₀, g₀ ≤ κ * c + A + C * k ∧
    g ≤ g₀ + 2 * η * M ∧ g₀ - 2 * η * M ≤ a - c ∧
    (1 - 2 * η) * M ≤ a)

theorem profile_step {κ F η M A C k a g : ℝ}
    (hκ : 0 < κ) (hF : 2 ≤ F) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (hA : C ≤ A) (hk : 0 ≤ k) (ha : 0 ≤ a)
    (htop : 2 * η ≤ κ - (F - 2))
    (hsmall : 16 * (1 + κ) * η ≤ κ)
    (hreflect : 32 * (1 + κ) * η ≤ κ ^ 2)
    (hcases : ProfileStepCases κ F η M A C k a g) :
    g ≤ κ * a + A + C * (k + 1) := by
  have hA0 : 0 ≤ A := le_trans hC hA
  have hκa : 0 ≤ κ * a := mul_nonneg hκ.le ha
  have hCk : 0 ≤ C * k := mul_nonneg hC hk
  have hreserve : 0 ≤ A + C * (k + 1) := by nlinarith
  have hs : 2 * η ≤ κ * (1 - 2 * η) := by nlinarith
  have hsM := mul_le_mul_of_nonneg_right hs hM
  rcases hcases with hb | hi | hc | hshort | hr
  · nlinarith
  · rcases hi with ⟨g₀, hg₀, hg⟩
    nlinarith
  · rcases hc with ⟨rfl, hg⟩
    have he : F - 2 + η ≤ κ := by linarith
    have heM := mul_le_mul_of_nonneg_right he hM
    nlinarith
  · rcases hshort with ⟨hg, hloc⟩
    have hlocκ := mul_le_mul_of_nonneg_left hloc hκ.le
    nlinarith
  · rcases hr with ⟨c, g₀, hold, hg, hshift, hloc⟩
    by_cases hlarge : κ * M / 4 ≤ g₀
    · have he : (2 + 2 * κ) * η ≤ κ ^ 2 / 4 := by nlinarith
      have heM := mul_le_mul_of_nonneg_right he hM
      have hlargeκ := mul_le_mul_of_nonneg_left hlarge hκ.le
      have hshiftκ := mul_le_mul_of_nonneg_left hshift hκ.le
      nlinarith
    · have hsmallgap : g₀ < κ * M / 4 := lt_of_not_ge hlarge
      have he : κ / 4 + 2 * η ≤ κ * (1 - 2 * η) := by nlinarith
      have heM := mul_le_mul_of_nonneg_right he hM
      have hlocκ := mul_le_mul_of_nonneg_left hloc hκ.le
      nlinarith

theorem profile_all_stages
    (Gap : ℕ → ℝ → ℝ → Prop) (M η : ℕ → ℝ) (κ F A C : ℝ)
    (hκ : 0 < κ) (hF : 2 ≤ F) (hC : 0 ≤ C) (hA : C ≤ A)
    (hη : ∀ n, 0 ≤ η n) (hM : ∀ n, 0 ≤ M n)
    (htop : ∀ n, 2 * η n ≤ κ - (F - 2))
    (hsmall : ∀ n, 16 * (1 + κ) * η n ≤ κ)
    (hreflect : ∀ n, 32 * (1 + κ) * η n ≤ κ ^ 2)
    (hendpoints : ∀ n a g, Gap n a g → 0 ≤ a)
    (hbase : ∀ a g, Gap 0 a g → g ≤ κ * a + A)
    (hstep : ∀ n a g, Gap (n + 1) a g →
      GapTransition Gap n F (η n) (M n) C a g) :
    ∀ n a g, Gap n a g → g ≤ κ * a + A + C * n := by
  intro n
  induction n with
  | zero =>
      intro a g hg
      simpa using hbase a g hg
  | succ n ih =>
      intro a g hg
      have hc : ProfileStepCases κ F (η n) (M n) A C (n : ℝ) a g := by
        rcases hstep n a g hg with hb | hi | hcentral | hshort | hr
        · exact Or.inl hb
        · rcases hi with ⟨g₀, hold, hwidth⟩
          exact Or.inr (Or.inl ⟨g₀, ih a g₀ hold, hwidth⟩)
        · exact Or.inr (Or.inr (Or.inl hcentral))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hshort)))
        · rcases hr with ⟨c, g₀, hold, hwidth, hshift, hloc⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨c, g₀, ih c g₀ hold, hwidth, hshift, hloc⟩)))
      have hp := profile_step hκ hF (hη n) (hM n) hC hA
        (show 0 ≤ (n : ℝ) by positivity) (hendpoints (n + 1) a g hg)
        (htop n) (hsmall n) (hreflect n) hc
      simpa only [Nat.cast_add, Nat.cast_one] using hp

noncomputable def profileTolerance
    (M L E : ℕ → ℝ) (F c₀ : ℝ) (n : ℕ) : ℝ :=
  max 0 (max ((2 * M n - L n) / M n)
    (max ((L n - F * M n) / M n) (max (E n / M n) (c₀ / M n))))

theorem select_profile_tolerance
    {M L E : ℕ → ℝ} {F c₀ : ℝ}
    (hM : Tendsto M atTop atTop) (hE : E =o[atTop] M)
    (hLlo : ∀ ε > 0, ∀ᶠ n in atTop, (2 - ε) * M n ≤ L n)
    (hLhi : ∀ ε > 0, ∀ᶠ n in atTop, L n ≤ (F + ε) * M n) :
    Tendsto (profileTolerance M L E F c₀) atTop (𝓝 0) ∧
    ∀ᶠ n in atTop,
      0 < M n ∧
      -profileTolerance M L E F c₀ n * M n ≤ L n - 2 * M n ∧
      L n - 2 * M n ≤ (F - 2 + profileTolerance M L E F c₀ n) * M n ∧
      E n ≤ profileTolerance M L E F c₀ n * M n ∧
      c₀ ≤ profileTolerance M L E F c₀ n * M n := by
  have hMpos : ∀ᶠ n in atTop, 0 < M n :=
    hM.eventually (eventually_gt_atTop 0)

  have hD : Tendsto (fun n => E n / M n) atTop (𝓝 0) :=
    hE.tendsto_div_nhds_zero

  have hC : Tendsto (fun n => c₀ / M n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := c₀)).mul
        (tendsto_inv_atTop_zero.comp hM)

  have hA : ∀ ε > 0, ∀ᶠ n in atTop,
      (2 * M n - L n) / M n ≤ ε := by
    intro ε hε
    filter_upwards [hMpos, hLlo ε hε] with n hnM hnL
    rw [div_le_iff₀ hnM]
    nlinarith

  have hB : ∀ ε > 0, ∀ᶠ n in atTop,
      (L n - F * M n) / M n ≤ ε := by
    intro ε hε
    filter_upwards [hMpos, hLhi ε hε] with n hnM hnL
    rw [div_le_iff₀ hnM]
    nlinarith

  have hPupper : ∀ ε > 0, ∀ᶠ n in atTop,
      profileTolerance M L E F c₀ n ≤ ε := by
    intro ε hε
    have hDε : ∀ᶠ n in atTop, E n / M n ≤ ε :=
      (hD.eventually (Iio_mem_nhds hε)).mono fun _ hn => hn.le
    have hCε : ∀ᶠ n in atTop, c₀ / M n ≤ ε :=
      (hC.eventually (Iio_mem_nhds hε)).mono fun _ hn => hn.le
    filter_upwards [hA ε hε, hB ε hε, hDε, hCε] with n ha hb hd hc
    change max 0 (max ((2 * M n - L n) / M n)
      (max ((L n - F * M n) / M n)
        (max (E n / M n) (c₀ / M n)))) ≤ ε
    simp only [max_le_iff]
    exact ⟨le_of_lt hε, ha, hb, hd, hc⟩

  have htol : Tendsto (profileTolerance M L E F c₀) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    filter_upwards [hPupper (ε / 2) hε2] with n hn
    have hp0 : 0 ≤ profileTolerance M L E F c₀ n := by
      unfold profileTolerance
      exact le_max_left _ _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hp0]
    exact lt_of_le_of_lt hn (by linarith)

  refine ⟨htol, ?_⟩
  filter_upwards [hMpos] with n hnM
  refine ⟨hnM, ?_, ?_, ?_, ?_⟩
  · have hq : (2 * M n - L n) / M n ≤
        profileTolerance M L E F c₀ n := by
      unfold profileTolerance
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hm := (div_le_iff₀ hnM).1 hq
    nlinarith
  · have hq : (L n - F * M n) / M n ≤
        profileTolerance M L E F c₀ n := by
      unfold profileTolerance
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hm := (div_le_iff₀ hnM).1 hq
    nlinarith
  · have hq : E n / M n ≤ profileTolerance M L E F c₀ n := by
      unfold profileTolerance
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _)))
    exact (div_le_iff₀ hnM).1 hq
  · have hq : c₀ / M n ≤ profileTolerance M L E F c₀ n := by
      unfold profileTolerance
      exact le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _)))
    exact (div_le_iff₀ hnM).1 hq

theorem eventually_profile_tolerance_small
    {η : ℕ → ℝ} {κ F : ℝ}
    (hη : Tendsto η atTop (𝓝 0)) (hF : 2 ≤ F) (hκ : F - 2 < κ) :
    ∀ᶠ n in atTop,
      2 * η n ≤ κ - (F - 2) ∧
      16 * (1 + κ) * η n ≤ κ ∧
      32 * (1 + κ) * η n ≤ κ ^ 2 := by
  have hk : 0 < κ := by linarith
  have ht : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa using hη.const_mul 2
  have hs : Tendsto (fun n => 16 * (1 + κ) * η n) atTop (𝓝 0) := by
    simpa using hη.const_mul (16 * (1 + κ))
  have hr : Tendsto (fun n => 32 * (1 + κ) * η n) atTop (𝓝 0) := by
    simpa using hη.const_mul (32 * (1 + κ))
  filter_upwards [(tendsto_order.1 ht).2 (κ - (F - 2)) (by linarith),
    (tendsto_order.1 hs).2 κ hk,
    (tendsto_order.1 hr).2 (κ ^ 2) (sq_pos_of_pos hk)] with n hn hs hr
  exact ⟨hn.le, hs.le, hr.le⟩

theorem finite_gap_base_constant
    {Gap : ℕ → ℝ → ℝ → Prop} (n₀ : ℕ) (κ C : ℝ)
    (hfinite : Set.Finite {p : ℝ × ℝ | Gap n₀ p.1 p.2}) :
    ∃ A : ℝ, C ≤ A ∧ ∀ a g, Gap n₀ a g → g ≤ κ * a + A := by
  classical
  let f : ℝ × ℝ → ℝ := fun p => p.2 - κ * p.1
  have hfin : Set.Finite (f '' {p : ℝ × ℝ | Gap n₀ p.1 p.2}) :=
    Set.Finite.image f hfinite
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨max C B, le_max_left C B, ?_⟩
  intro a g hGap
  have hmem : (a, g) ∈ {p : ℝ × ℝ | Gap n₀ p.1 p.2} := by
    simpa using hGap
  have hle : g - κ * a ≤ B := by
    apply hB
    exact ⟨(a, g), hmem, rfl⟩
  have hBmax : B ≤ max C B := le_max_right C B
  calc
    g ≤ B + κ * a := (sub_le_iff_le_add).mp hle
    _ ≤ max C B + κ * a := add_le_add_left hBmax (κ * a)
    _ = κ * a + max C B := add_comm _ _

theorem uniform_finite_profile
    (Gap : ℕ → ℝ → ℝ → Prop) (M L E : ℕ → ℝ) (F C c₀ : ℝ)
    (hF : 2 ≤ F) (hC : 0 ≤ C)
    (hM : Tendsto M atTop atTop) (hE : E =o[atTop] M)
    (hLlo : ∀ ε > 0, ∀ᶠ n in atTop, (2 - ε) * M n ≤ L n)
    (hLhi : ∀ ε > 0, ∀ᶠ n in atTop, L n ≤ (F + ε) * M n)
    (hfinite : ∀ n, Set.Finite {p : ℝ × ℝ | Gap n p.1 p.2})
    (hleft : ∀ n a g, Gap n a g → 0 ≤ a)
    (hright : ∀ n a g, Gap n a g → a + g ≤ M n)
    (hpert : ∀ᶠ n in atTop, ∀ a g, Gap (n + 1) a g →
      PerturbationGapCases Gap n (L n) (M n) (E n) C c₀ a g)
    {κ : ℝ} (hκ : F - 2 < κ) :
    ∃ n₀ : ℕ, ∃ A : ℝ, C ≤ A ∧
      ∀ n ≥ n₀, ∀ a g, Gap n a g →
        g ≤ κ * a + A + C * ((n - n₀ : ℕ) : ℝ) := by
  have hk : 0 < κ := by linarith
  let η := profileTolerance M L E F c₀
  rcases select_profile_tolerance (c₀ := c₀) hM hE hLlo hLhi with
    ⟨hηlim, hscales⟩
  have hsmall := eventually_profile_tolerance_small hηlim hF hκ
  rcases eventually_atTop.1 (hscales.and (hsmall.and hpert)) with
    ⟨n₀, htail⟩
  rcases finite_gap_base_constant n₀ κ C (hfinite n₀) with
    ⟨A, hA, hbase⟩
  have hall : ∀ k a g, Gap (n₀ + k) a g →
      g ≤ κ * a + A + C * (k : ℝ) := by
    refine profile_all_stages (fun k => Gap (n₀ + k))
      (fun k => M (n₀ + k)) (fun k => η (n₀ + k))
      κ F A C hk hF hC hA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro k
      change 0 ≤ profileTolerance M L E F c₀ (n₀ + k)
      exact le_max_left _ _
    · intro k
      exact (htail (n₀ + k) (by omega)).1.1.le
    · intro k
      exact (htail (n₀ + k) (by omega)).2.1.1
    · intro k
      exact (htail (n₀ + k) (by omega)).2.1.2.1
    · intro k
      exact (htail (n₀ + k) (by omega)).2.1.2.2
    · intro k a g hg
      exact hleft (n₀ + k) a g hg
    · intro a g hg
      exact hbase a g (by simpa using hg)
    · intro k a g hg
      rcases htail (n₀ + k) (by omega) with
        ⟨⟨hm, hlo, hhi, he, hc⟩, hsm, hp⟩
      have hg' : Gap ((n₀ + k) + 1) a g := by
        simpa [Nat.add_assoc] using hg
      exact perturbation_cases_to_profile_transition hlo hhi he hc
        (hright (n₀ + k)) (hp a g hg')
  refine ⟨n₀, A, hA, ?_⟩
  intro n hn a g hg
  apply hall (n - n₀) a g
  simpa [Nat.add_sub_of_le hn] using hg

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.profile_step
#print axioms Paper4.HmuSkeleton.profile_all_stages
#print axioms Paper4.HmuSkeleton.uniform_finite_profile

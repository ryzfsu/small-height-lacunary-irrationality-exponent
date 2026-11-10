/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
module

public import Paper4.CF.Gap
public import Paper4.CF.Canonical
public import Paper4.HmuSkeleton.InverseCoordinatePair
public import Paper4.HmuSkeleton.ReflectedLegendreGap
public import Paper4.HmuSkeleton.ReflectedEndpointScale
public import Paper4.HmuSkeleton.SelectedGapTail
import Mathlib.Tactic

@[expose] public section

namespace Paper4.HmuSkeleton

open Filter
open Lacunary.CFBridge
open scoped Topology

/- Paper §4, inverse coordinate: B is the reduced denominator of
   zeta = -sigma / (V^2 * delta). Since sigma = ±1, removing this sign gives
   the same denominator. This definition therefore uses 1 / (V^2 * delta). -/
def coordinateDen (α δ : ℚ) : ℕ :=
  (1 / ((α.den : ℚ) ^ 2 * δ)).den

/- Paper §4, rational perturbation lemma: gap-profile consequences in the
   printed order Bounded, Inherited, Central, Short, Reflected. Here a is the
   logarithm of the left denominator, g is the width, and b = a + g.

   With C = log 6, E = log (4B), and c₀ = log (3/2), this retains the old-gap
   membership needed by §6 and both reflected endpoint bounds. The short
   branch exports g ≤ 2E; the paper also displays the sharper intermediate
   bound g ≤ log 12 + 2 log B. The branch cutoff below remains 12B^2. -/
def PerturbationGapCases (Gap : ℕ → ℝ → ℝ → Prop) (n : ℕ)
    (L M E C c₀ a g : ℝ) : Prop :=
  g ≤ C ∨
  (∃ g₀, Gap n a g₀ ∧ g ≤ g₀ + C) ∨
  (a = M ∧ g ≤ L - 2 * M) ∨
  (g ≤ 2 * E ∧ L - M - c₀ ≤ a) ∨
  (∃ c d, Gap n c (d - c) ∧
    |a - (L - d)| ≤ E ∧ |(a + g) - (L - c)| ≤ E ∧
    L - M - c₀ ≤ a)

def BoundedAlternative (C a g : ℝ) : Prop := g ≤ C

def InheritedAlternative (Gap : ℝ → ℝ → Prop) (C a g : ℝ) : Prop :=
  ∃ g₀, Gap a g₀ ∧ g ≤ g₀ + C

def CentralAlternative (L M a g : ℝ) : Prop :=
  a = M ∧ g ≤ L - 2 * M

def ShortAlternative (L M E c₀ a g : ℝ) : Prop :=
  g ≤ 2 * E ∧ L - M - c₀ ≤ a

def ReflectedAlternative (Gap : ℝ → ℝ → Prop)
    (L M E c₀ a g : ℝ) : Prop :=
  ∃ c d, Gap c (d - c) ∧
    |a - (L - d)| ≤ E ∧ |(a + g) - (L - c)| ≤ E ∧
    L - M - c₀ ≤ a

def GapTransition (Gap : ℕ → ℝ → ℝ → Prop) (n : ℕ)
    (F η M C a g : ℝ) : Prop :=
  g ≤ C ∨
  (∃ g₀, Gap n a g₀ ∧ g ≤ g₀ + C) ∨
  (a = M ∧ g ≤ (F - 2 + η) * M) ∨
  (g ≤ 2 * η * M ∧ (1 - 2 * η) * M ≤ a) ∨
  (∃ c g₀, Gap n c g₀ ∧
    g ≤ g₀ + 2 * η * M ∧ g₀ - 2 * η * M ≤ a - c ∧
    (1 - 2 * η) * M ≤ a)

/- Paper §4 proof order: first split at nextDen / value.den ≤ 6, then at
   error ≥ Delta/2, and finally at nextDen / value.den ≤ 12B^2. The callbacks
   assemble the central, short, and reflected branches; rational_perturbation
   below supplies them for the actual rational perturbation. -/
theorem five_way_perturbation
    {α : ℚ} {β a g Δ L M E B : ℝ}
    (hgap : LogGap β a g)
    (hΔ : Δ = |β - (α : ℝ)|)
    (hB : 0 < B)
    (hcentral : ∀ G : CFGap β, a = G.left → g = G.width →
      G.value = α →
      6 < (G.nextDen : ℝ) / (G.value.den : ℝ) →
      Δ / 2 ≤ |β - (G.value : ℝ)| →
      CentralAlternative L M a g)
    (hshort : ∀ G : CFGap β, a = G.left → g = G.width →
      6 < (G.nextDen : ℝ) / (G.value.den : ℝ) →
      |β - (G.value : ℝ)| < Δ / 2 →
      (G.nextDen : ℝ) / (G.value.den : ℝ) ≤ 12 * B ^ 2 →
      ShortAlternative L M E (Real.log (3 / 2 : ℝ)) a g)
    (hreflected : ∀ G : CFGap β, a = G.left → g = G.width →
      6 < (G.nextDen : ℝ) / (G.value.den : ℝ) →
      |β - (G.value : ℝ)| < Δ / 2 →
      12 * B ^ 2 < (G.nextDen : ℝ) / (G.value.den : ℝ) →
      ReflectedAlternative (fun c g => LogGap (α : ℝ) c g)
        L M E (Real.log (3 / 2 : ℝ)) a g) :
    BoundedAlternative (Real.log 6) a g ∨
      InheritedAlternative (fun c g => LogGap (α : ℝ) c g)
        (Real.log 6) a g ∨
      CentralAlternative L M a g ∨
      ShortAlternative L M E (Real.log (3 / 2 : ℝ)) a g ∨
      ReflectedAlternative (fun c g => LogGap (α : ℝ) c g)
        L M E (Real.log (3 / 2 : ℝ)) a g := by
  rcases hgap with ⟨G, ha, hg⟩
  have hden_pos : (0 : ℝ) < (G.value.den : ℝ) := by
    exact_mod_cast G.value.den_pos
  have hnext_pos : (0 : ℝ) < (G.nextDen : ℝ) := by
    exact_mod_cast (cfGap_bounds G).1
  have hwidth_eq : g = Real.log (G.nextDen : ℝ) - Real.log (G.value.den : ℝ) := by
    simpa [hg, CFGap.width, CFGap.right, CFGap.left]
  have hratio_pos : 0 < (G.nextDen : ℝ) / (G.value.den : ℝ) :=
    div_pos hnext_pos hden_pos
  by_cases hratio : (G.nextDen : ℝ) / (G.value.den : ℝ) ≤ 6
  · left
    change g ≤ Real.log 6
    have hlog : Real.log ((G.nextDen : ℝ) / (G.value.den : ℝ)) ≤ Real.log 6 :=
      Real.log_le_log hratio_pos hratio
    rw [Real.log_div (ne_of_gt hnext_pos) (ne_of_gt hden_pos)] at hlog
    linarith
  · have hratio6 : 6 < (G.nextDen : ℝ) / (G.value.den : ℝ) := lt_of_not_ge hratio
    by_cases hfar : Δ / 2 ≤ |β - (G.value : ℝ)|
    · by_cases hvalue : G.value = α
      · exact Or.inr (Or.inr (Or.inl (hcentral G ha hg hvalue hratio6 hfar)))
      · have htri : |(α : ℝ) - (G.value : ℝ)| ≤
            Δ + |β - (G.value : ℝ)| := by
          calc
            |(α : ℝ) - (G.value : ℝ)| =
                |((α : ℝ) - β) + (β - (G.value : ℝ))| := by
                  congr 1 <;> ring
            _ ≤ |(α : ℝ) - β| + |β - (G.value : ℝ)| := abs_add_le _ _
            _ = Δ + |β - (G.value : ℝ)| := by rw [abs_sub_comm, hΔ]
        have hmulupper : 3 * |β - (G.value : ℝ)| ≤
            3 * (1 / ((G.value.den : ℝ) * (G.nextDen : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (cfGap_bounds G).2.2.2 (by norm_num)
        have hqmul : 6 * (G.value.den : ℝ) < (G.nextDen : ℝ) := by
          exact (lt_div_iff₀ hden_pos).mp hratio6
        have hqmul' : 6 * (G.value.den : ℝ) * (G.value.den : ℝ) <
            (G.nextDen : ℝ) * (G.value.den : ℝ) :=
          mul_lt_mul_of_pos_right hqmul hden_pos
        have hsmall : 3 / ((G.value.den : ℝ) * (G.nextDen : ℝ)) <
            1 / (2 * (G.value.den : ℝ) ^ 2) := by
          apply (div_lt_div_iff₀ (mul_pos hden_pos hnext_pos)
            (mul_pos (by norm_num) (sq_pos_of_pos hden_pos))).2
          nlinarith [hqmul']
        have hclose : |(α : ℝ) - (G.value : ℝ)| ≤
            3 / ((G.value.den : ℝ) * (G.nextDen : ℝ)) := by
          calc
            |(α : ℝ) - (G.value : ℝ)| ≤
                Δ + |β - (G.value : ℝ)| := htri
            _ ≤ 3 * |β - (G.value : ℝ)| := by linarith
            _ ≤ 3 * (1 / ((G.value.den : ℝ) * (G.nextDen : ℝ))) := hmulupper
            _ = 3 / ((G.value.den : ℝ) * (G.nextDen : ℝ)) := by ring
        have halpha : |(α : ℝ) - (G.value : ℝ)| <
            1 / (2 * (G.value.den : ℝ) ^ 2) := lt_of_le_of_lt hclose hsmall
        have hne : (α : ℝ) ≠ (G.value : ℝ) := by
          intro hcast
          apply hvalue
          exact (Rat.cast_injective hcast).symm
        obtain ⟨G₀, hG₀value⟩ := cfGap_legendre hne halpha
        have hG₀bounds := cfGap_bounds G₀
        have hG₀value' : (G₀.value : ℝ) = (G.value : ℝ) := by
          exact_mod_cast hG₀value
        have hleft : a = G₀.left := by
          calc
            a = G.left := ha
            _ = G₀.left := by simp [CFGap.left, hG₀value]
        have hcrossbase :
            1 / ((G.value.den : ℝ) * ((G₀.nextDen : ℝ) + G.value.den)) ≤
              3 / ((G.value.den : ℝ) * (G.nextDen : ℝ)) := by
          calc
            1 / ((G.value.den : ℝ) * ((G₀.nextDen : ℝ) + G.value.den)) ≤
                |(α : ℝ) - (G₀.value : ℝ)| := by
                  simpa [hG₀value] using hG₀bounds.2.2.1
            _ = |(α : ℝ) - (G.value : ℝ)| := by rw [hG₀value']
            _ ≤ 3 / ((G.value.den : ℝ) * (G.nextDen : ℝ)) := hclose
        have hq0_pos : (0 : ℝ) < (G₀.nextDen : ℝ) := by exact_mod_cast hG₀bounds.1
        have hcross :
            1 * ((G.value.den : ℝ) * (G.nextDen : ℝ)) ≤
              3 * ((G.value.den : ℝ) * ((G₀.nextDen : ℝ) + G.value.den)) := by
          exact (div_le_div_iff₀
            (mul_pos hden_pos (add_pos hq0_pos hden_pos))
            (mul_pos hden_pos hnext_pos)).mp hcrossbase
        have hQle : (G.nextDen : ℝ) ≤
            3 * ((G₀.nextDen : ℝ) + (G.value.den : ℝ)) := by
          nlinarith [hcross, hden_pos]
        have hQle6 : (G.nextDen : ℝ) ≤ 6 * (G₀.nextDen : ℝ) := by
          nlinarith [hQle, hqmul]
        right
        left
        refine ⟨G₀.width, ⟨G₀, hleft, rfl⟩, ?_⟩
        have hlogQ : Real.log (G.nextDen : ℝ) ≤
            Real.log 6 + Real.log (G₀.nextDen : ℝ) := by
          calc
            Real.log (G.nextDen : ℝ) ≤ Real.log (6 * (G₀.nextDen : ℝ)) :=
              Real.log_le_log hnext_pos (by nlinarith [hQle6])
            _ = Real.log 6 + Real.log (G₀.nextDen : ℝ) := by
              rw [Real.log_mul (by norm_num) (ne_of_gt hq0_pos)]
        have hwidth₀ : G₀.width =
            Real.log (G₀.nextDen : ℝ) - Real.log (G.value.den : ℝ) := by
          simp [CFGap.width, CFGap.right, CFGap.left, hG₀value]
        rw [hwidth_eq, hwidth₀]
        linarith
    · have hnear : |β - (G.value : ℝ)| < Δ / 2 := lt_of_not_ge hfar
      by_cases hsmall : (G.nextDen : ℝ) / (G.value.den : ℝ) ≤ 12 * B ^ 2
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (hshort G ha hg hratio6 hnear hsmall))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (hreflected G ha hg hratio6 hnear (lt_of_not_ge hsmall)))))

/- A direct adapter to the profile induction representation. -/
theorem perturbation_cases_to_profile_transition
    {Gap : ℕ → ℝ → ℝ → Prop} {n : ℕ}
    {L M E C c₀ F η a g : ℝ}
    (hLlo : -η * M ≤ L - 2 * M)
    (hLhi : L - 2 * M ≤ (F - 2 + η) * M)
    (hE : E ≤ η * M) (hc₀ : c₀ ≤ η * M)
    (hold_right : ∀ c g₀, Gap n c g₀ → c + g₀ ≤ M)
    (hcases : PerturbationGapCases Gap n L M E C c₀ a g) :
    GapTransition Gap n F η M C a g := by
  rcases hcases with h | ⟨g₀, hgap, hg⟩ | ⟨ha, hg⟩ | ⟨hg, ha⟩ |
    ⟨c, d, hgap, h₁, h₂, ha⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨g₀, hgap, hg⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ha, le_trans hg hLhi⟩))
  · right
    right
    right
    left
    constructor
    · exact le_trans hg (by linarith [hE])
    · linarith [hLlo, hc₀, ha]
  · right
    right
    right
    right
    refine ⟨c, d - c, hgap, ?_, ?_, ?_⟩
    · have h₁' := (abs_le.mp h₁)
      have h₂' := (abs_le.mp h₂)
      linarith [h₁'.1, h₂'.1, hE]
    · have hd : d ≤ M := by
        have hr := hold_right c (d - c) hgap
        linarith
      linarith [hLlo, hc₀, ha, hd]
    · linarith [hLlo, hc₀, ha]


set_option maxHeartbeats 2000000 in
theorem reflected_r_choice_data
    (alpha delta : ℚ) (hV : 2 ≤ alpha.den) (hdelta : delta ≠ 0)
    (G : CFGap ((alpha + delta : ℚ) : ℝ))
    (hnear : |((alpha + delta : ℚ) : ℝ) - (G.value : ℝ)| < |(delta : ℝ)| / 2)
    (hlarge : 12 * (coordinateDen alpha delta : ℝ) ^ 2 <
      (G.nextDen : ℝ) / (G.value.den : ℝ)) :
    ∃ h k : ℤ, ∃ r : ℚ,
      h = (-1 : ℤ) ^ (rationalLength alpha + 1) *
        (G.value.num * ((penult alpha).den : ℤ) -
          (penult alpha).num * (G.value.den : ℤ)) ∧
      k = (-1 : ℤ) ^ (rationalLength alpha + 1) *
        (alpha.num * (G.value.den : ℤ) -
          G.value.num * (alpha.den : ℤ)) ∧
      k ≠ 0 ∧ Nat.Coprime h.natAbs k.natAbs ∧
      r = - ((((-1 : ℤ) ^ (rationalLength alpha + 1) : ℤ) : ℚ) /
          ((alpha.den : ℚ) ^ 2 * delta)) - (h : ℚ) / (k : ℚ) ∧
      |(k : ℝ)| / (coordinateDen alpha delta : ℝ) ≤ (r.den : ℝ) ∧
      (r.den : ℝ) ≤ (coordinateDen alpha delta : ℝ) * |(k : ℝ)| ∧
      (reversePoint alpha : ℝ) ≠ (r : ℝ) ∧
      |(reversePoint alpha : ℝ) - (r : ℝ)| * (r.den : ℝ) ^ 2 < 1 / 8 ∧
      |(reversePoint alpha : ℝ) - (r : ℝ)| =
        |((alpha + delta : ℚ) : ℝ) - (G.value : ℝ)| * (G.value.den : ℝ) /
          ((alpha.den : ℝ) * |(delta : ℝ)| * |(k : ℝ)|) ∧
      (G.value.den : ℝ) * (alpha.den : ℝ) * (|(delta : ℝ)| / 2) ≤ |(k : ℝ)| ∧
      |(k : ℝ)| ≤ (G.value.den : ℝ) * (alpha.den : ℝ) *
        ((3 / 2 : ℝ) * |(delta : ℝ)|) := by
  classical
  let sigma : ℤ := (-1 : ℤ) ^ (rationalLength alpha + 1)
  let V : ℝ := (alpha.den : ℝ)
  let q : ℝ := (G.value.den : ℝ)
  let Q : ℝ := (G.nextDen : ℝ)
  let B : ℕ := coordinateDen alpha delta
  let Dq : ℚ := (alpha.den : ℚ) ^ 2 * delta
  let zeta : ℚ := -((sigma : ℚ) / Dq)
  obtain ⟨h, k, hh, hk, hrow1, hrow2, hkn, hcop, hKlower, hKupper⟩ :=
    inverse_coordinate_pair alpha delta hV hdelta G hnear
  let r : ℚ := zeta - (h : ℚ) / (k : ℚ)
  have hsigmasqZ : sigma * sigma = 1 := by
    dsimp [sigma]
    rw [← mul_pow]
    norm_num
  have hsigmasq : (sigma : ℝ) * (sigma : ℝ) = 1 := by
    exact_mod_cast hsigmasqZ
  have hsigmabs : |(sigma : ℝ)| = 1 := by
    simp [sigma, abs_pow]
  have hVnat : 0 < alpha.den := by omega
  have hVpos : 0 < V := by
    dsimp [V]
    exact_mod_cast hVnat
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast G.value.den_pos
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (cfGap_bounds G).1
  have hBpos : 0 < B := by
    dsimp [B, coordinateDen]
    exact Rat.den_pos _
  have hBposR : 0 < (B : ℝ) := by exact_mod_cast hBpos
  have hdeltaR : (delta : ℝ) ≠ 0 := by exact_mod_cast hdelta
  have hDq : Dq ≠ 0 := by
    dsimp [Dq]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (ne_of_gt hVnat))) hdelta
  have hbeta : ((alpha + delta : ℚ) : ℝ) = (alpha : ℝ) + (delta : ℝ) := by norm_cast
  have hKpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hkn)
  have hdenU : ((h : ℚ) / (k : ℚ)).den = k.natAbs := by
    by_cases hkpos : 0 < k
    · have hd := Rat.den_div_eq_of_coprime hkpos hcop
      have hd' : ((((h : ℚ) / (k : ℚ)).den : ℤ)) = (k.natAbs : ℤ) := by
        simpa [Int.natAbs_of_nonneg hkpos.le] using hd
      exact_mod_cast hd'
    · have hkneg : k < 0 := by omega
      have hcop' : Nat.Coprime (-h).natAbs (-k).natAbs := by simpa using hcop
      have hd := Rat.den_div_eq_of_coprime (show 0 < -k by omega) hcop'
      have hquot : (h : ℚ) / (k : ℚ) = (-h : ℚ) / (-k : ℚ) := by push_cast; ring
      rw [hquot]
      have hd' : ((((-h : ℚ) / (-k : ℚ)).den : ℤ)) = (k.natAbs : ℤ) := by
        simpa [Int.ofNat_natAbs_of_nonpos (show k ≤ 0 by omega)] using hd
      exact_mod_cast hd'
  have hzetaDenDvd : zeta.den ∣ B := by
    have hzeta : zeta = (-(sigma : ℚ)) * (1 / Dq) := by
      dsimp [zeta]
      field_simp [hDq]
    rw [hzeta]
    calc
      ((-(sigma : ℚ)) * (1 / Dq)).den ∣ (-(sigma : ℚ)).den * (1 / Dq).den :=
        Rat.mul_den_dvd _ _
      _ = B := by simp [B, coordinateDen, Dq]
  have hrupperNat : r.den ≤ B * k.natAbs := by
    have hdiv : r.den ∣ B * k.natAbs := by
      calc
        r.den ∣ zeta.den * ((h : ℚ) / (k : ℚ)).den := by
          simpa [r] using Rat.sub_den_dvd zeta ((h : ℚ) / (k : ℚ))
        _ ∣ B * k.natAbs := by
          simpa [hdenU] using Nat.mul_dvd_mul_right hzetaDenDvd k.natAbs
    exact Nat.le_of_dvd (by positivity) hdiv
  have hrlowerNat : k.natAbs ≤ B * r.den := by
    have hrid : zeta - r = (h : ℚ) / (k : ℚ) := by dsimp [r]; ring
    have hdenid : (zeta - r).den = k.natAbs := by rw [hrid]; exact hdenU
    have hdiv : k.natAbs ∣ B * r.den := by
      calc
        k.natAbs = (zeta - r).den := hdenid.symm
        _ ∣ zeta.den * r.den := Rat.sub_den_dvd zeta r
        _ ∣ B * r.den := Nat.mul_dvd_mul_right hzetaDenDvd _
    exact Nat.le_of_dvd (by positivity) hdiv
  have hrupper : (r.den : ℝ) ≤ (B : ℝ) * |(k : ℝ)| := by
    have ht : (r.den : ℝ) ≤ (B : ℝ) * (k.natAbs : ℝ) := by exact_mod_cast hrupperNat
    simpa using ht
  have hrlower : |(k : ℝ)| / (B : ℝ) ≤ (r.den : ℝ) := by
    have ht : (k.natAbs : ℝ) ≤ (B : ℝ) * (r.den : ℝ) := by exact_mod_cast hrlowerNat
    have ht' : |(k : ℝ)| ≤ (B : ℝ) * (r.den : ℝ) := by simpa using ht
    exact (div_le_iff₀ hBposR).2 (by simpa [mul_comm] using ht')
  have hαnum : (alpha.num : ℝ) = (alpha.den : ℝ) * (alpha : ℝ) := by
    rw [Rat.cast_def]
    field_simp [ne_of_gt (show (0 : ℝ) < (alpha.den : ℝ) by exact_mod_cast hVnat)]
  have hGnum : (G.value.num : ℝ) = q * (G.value : ℝ) := by
    have hc : (G.value : ℝ) = (G.value.num : ℝ) / q := Rat.cast_def G.value
    calc
      (G.value.num : ℝ) = q * ((G.value.num : ℝ) / q) := by field_simp [ne_of_gt hqpos]
      _ = q * (G.value : ℝ) := by rw [← hc]
  have hcross : (alpha.num : ℝ) * q - (G.value.num : ℝ) * V =
      q * V * ((alpha : ℝ) - (G.value : ℝ)) := by
    dsimp [V, q]
    rw [hαnum, hGnum]
    dsimp [q]
    ring
  have hkreal : (k : ℝ) = (sigma : ℝ) *
      ((alpha.num : ℝ) * q - (G.value.num : ℝ) * V) := by
    rw [hk]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    simp [sigma, V, q]
  have hkrel : (k : ℝ) = (sigma : ℝ) * q * V *
      ((alpha : ℝ) - (G.value : ℝ)) := by
    calc
      (k : ℝ) = (sigma : ℝ) *
          ((alpha.num : ℝ) * q - (G.value.num : ℝ) * V) := hkreal
      _ = (sigma : ℝ) * q * V *
          ((alpha : ℝ) - (G.value : ℝ)) := by rw [hcross]; ring
  have hkmetric : |(k : ℝ)| = q * V * |(alpha : ℝ) - (G.value : ℝ)| := by
    rw [hkreal, hcross]
    simp [hsigmabs, abs_mul, abs_of_pos hqpos, abs_of_pos hVpos]
  have hDpos : ((alpha : ℝ) - (G.value : ℝ)) ≠ 0 := by
    intro hz
    rw [hz, abs_zero, mul_zero] at hkmetric
    exact hKpos.ne' hkmetric
  have hDabspos : 0 < |(alpha : ℝ) - (G.value : ℝ)| := abs_pos.mpr hDpos
  have hEpos : 0 < |(alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)| :=
    lt_of_lt_of_le (by positivity : 0 < 1 / (q * (Q + q)))
      (by simpa [q, Q, hbeta] using (cfGap_bounds G).2.2.1)
  have hVne : (V : ℝ) ≠ 0 := ne_of_gt hVpos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hδabspos : 0 < |(delta : ℝ)| := abs_pos.mpr hdeltaR
  have hrow2R : V * (h : ℝ) + ((penult alpha).den : ℝ) * (k : ℝ) = q := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hrow2
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, V, q] using hcast
  have hratio1 : (h : ℝ) / (k : ℝ) + ((penult alpha).den : ℝ) / V =
      q / (V * (k : ℝ)) := by
    field_simp [hVne, (ne_of_gt hKpos)]
    nlinarith [hrow2R]
  have hratio2 : q / (V * (k : ℝ)) = (sigma : ℝ) /
      (V ^ 2 * ((alpha : ℝ) - (G.value : ℝ))) := by
    have hσne : (sigma : ℝ) ≠ 0 := by nlinarith [hsigmasq]
    calc
      q / (V * (k : ℝ)) =
          q / (V * ((sigma : ℝ) *
            q * V * ((alpha : ℝ) - (G.value : ℝ)))) := by
              rw [hkrel]
      _ = 1 / ((sigma : ℝ) * V ^ 2 * ((alpha : ℝ) - (G.value : ℝ))) := by
            field_simp [hVne, hqne, hDpos, hσne]
            <;> ring
      _ = (sigma : ℝ) / (V ^ 2 * ((alpha : ℝ) - (G.value : ℝ))) := by
            field_simp [hVne, hDpos, hσne]
            simpa [pow_two] using hsigmasq.symm
  have hratio : (h : ℝ) / (k : ℝ) + ((penult alpha).den : ℝ) / V =
      (sigma : ℝ) / (V ^ 2 * ((alpha : ℝ) - (G.value : ℝ))) := hratio1.trans hratio2
  have hrevcast : (reversePoint alpha : ℝ) = ((penult alpha).den : ℝ) / V := by
    simp [reversePoint, V]
  have hrcast : (r : ℝ) = -(sigma : ℝ) /
      (V ^ 2 * (delta : ℝ)) - (h : ℝ) / (k : ℝ) := by
    dsimp [r, zeta, Dq, V]
    push_cast
    ring
  have hrevDiff : (reversePoint alpha : ℝ) - (r : ℝ) =
      (sigma : ℝ) * ((alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)) /
        (V ^ 2 * (delta : ℝ) * ((alpha : ℝ) - (G.value : ℝ))) := by
    rw [hrevcast, hrcast]
    have hratio' : ((penult alpha).den : ℝ) / V + (h : ℝ) / (k : ℝ) =
        (sigma : ℝ) / (V ^ 2 * ((alpha : ℝ) - (G.value : ℝ))) := by
      calc
        ((penult alpha).den : ℝ) / V + (h : ℝ) / (k : ℝ) =
            (h : ℝ) / (k : ℝ) + ((penult alpha).den : ℝ) / V := add_comm _ _
        _ = _ := hratio
    calc
      ((penult alpha).den : ℝ) / V -
          (-(sigma : ℝ) / (V ^ 2 * (delta : ℝ)) - (h : ℝ) / (k : ℝ)) =
          (sigma : ℝ) / (V ^ 2 * (delta : ℝ)) +
            (((penult alpha).den : ℝ) / V + (h : ℝ) / (k : ℝ)) := by ring
      _ = (sigma : ℝ) / (V ^ 2 * (delta : ℝ)) +
            (sigma : ℝ) / (V ^ 2 * ((alpha : ℝ) - (G.value : ℝ))) := by
          rw [hratio']
      _ = (sigma : ℝ) * ((alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)) /
            (V ^ 2 * (delta : ℝ) * ((alpha : ℝ) - (G.value : ℝ))) := by
          field_simp [hVne, hDpos, hdeltaR]
          <;> ring
  have hωeq : |(reversePoint alpha : ℝ) - (r : ℝ)| =
      |(alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)| * q /
        (V * |(delta : ℝ)| * |(k : ℝ)|) := by
    rw [hrevDiff]
    simp only [abs_div, abs_mul]
    rw [hsigmabs, abs_of_pos (sq_pos_of_pos hVpos)]
    rw [hkmetric]
    field_simp [hVne, hqne, hδabspos.ne', hDabspos.ne']
  have hbounds := cfGap_bounds G
  have hεupper : |(alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)| ≤ 1 / (q * Q) := by
    simpa [q, Q, hbeta] using hbounds.2.2.2
  have hcut : |(reversePoint alpha : ℝ) - (r : ℝ)| * (r.den : ℝ) ^ 2 < 1 / 8 := by
    have hsmall : (3 / 2 : ℝ) * (B : ℝ) ^ 2 * q / Q < 1 / 8 := by
      apply (div_lt_iff₀ hQpos).2
      have hl' : 12 * (B : ℝ) ^ 2 * q < Q := by
        apply (lt_div_iff₀ hqpos).1
        simpa [B, q, Q] using hlarge
      nlinarith only [hl']
    have hsquare : (r.den : ℝ) ^ 2 ≤ ((B : ℝ) * |(k : ℝ)|) ^ 2 := by
      apply (sq_le_sq₀ (by exact_mod_cast r.den_pos.le)
        (mul_nonneg (by positivity) (abs_nonneg (k : ℝ)))).2
      exact hrupper
    have hcutle : |(reversePoint alpha : ℝ) - (r : ℝ)| * (r.den : ℝ) ^ 2 ≤
        (3 / 2 : ℝ) * (B : ℝ) ^ 2 * q / Q := by
      rw [hωeq]
      have hfactor :
          |(alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)| * q ≤ 1 / Q := by
        calc
          _ ≤ (1 / (q * Q)) * q := mul_le_mul_of_nonneg_right hεupper hqpos.le
          _ = 1 / Q := by field_simp [hqne, hQne]
      have hdenfactor : (r.den : ℝ) ^ 2 /
          (V * |(delta : ℝ)| * |(k : ℝ)|) ≤
          (B : ℝ) ^ 2 * |(k : ℝ)| / (V * |(delta : ℝ)|) := by
        apply (div_le_iff₀ (mul_pos (mul_pos hVpos hδabspos) hKpos)).2
        calc
          (r.den : ℝ) ^ 2 ≤ ((B : ℝ) * |(k : ℝ)|) ^ 2 := hsquare
          _ = ((B : ℝ) ^ 2 * |(k : ℝ)| /
                (V * |(delta : ℝ)|)) *
              (V * |(delta : ℝ)| * |(k : ℝ)|) := by
            field_simp [hVne, hδabspos.ne', hKpos.ne']
            <;> ring
      have hKfactor : |(k : ℝ)| / (V * |(delta : ℝ)|) ≤ (3 / 2 : ℝ) * q := by
        apply (div_le_iff₀ (mul_pos hVpos hδabspos)).2
        calc
          |(k : ℝ)| ≤ (G.value.den : ℝ) * (alpha.den : ℝ) *
              ((3 / 2 : ℝ) * |(delta : ℝ)|) := hKupper
          _ = ((3 / 2 : ℝ) * q) * (V * |(delta : ℝ)|) := by dsimp [q, V]; ring
      calc
        _ = (|(alpha : ℝ) + (delta : ℝ) - (G.value : ℝ)| * q) *
            ((r.den : ℝ) ^ 2 /
              (V * |(delta : ℝ)| * |(k : ℝ)|)) := by ring
        _ ≤ (1 / Q) * ((B : ℝ) ^ 2 * |(k : ℝ)| /
              (V * |(delta : ℝ)|)) :=
            mul_le_mul hfactor hdenfactor (by positivity) (by positivity)
        _ ≤ (1 / Q) * ((B : ℝ) ^ 2 * ((3 / 2 : ℝ) * q)) :=
            by
              have hscaled := mul_le_mul_of_nonneg_left hKfactor (sq_nonneg (B : ℝ))
              have hscaled' := mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ 1 / Q)
              simpa only [mul_div_assoc] using hscaled'
        _ = (3 / 2 : ℝ) * (B : ℝ) ^ 2 * q / Q := by ring
    exact lt_of_le_of_lt hcutle hsmall
  have hne : (reversePoint alpha : ℝ) ≠ (r : ℝ) := by
    apply sub_ne_zero.mp
    apply abs_pos.mp
    rw [hωeq]
    exact div_pos (mul_pos hEpos hqpos) (mul_pos (mul_pos hVpos hδabspos) hKpos)
  refine ⟨h, k, r, hh, hk, hkn, hcop, rfl, hrlower, hrupper, hne, hcut, ?_, hKlower, hKupper⟩
  simpa only [hbeta, q, V] using hωeq


theorem reflected_value_denominator_scale
    {q T B K s : ℝ}
    (hq : 0 < q) (hT : 0 < T) (hB : 0 < B)
    (hKlower : q / (2 * T) ≤ K)
    (hKupper : K ≤ 3 * q / (2 * T))
    (hslower : K / B ≤ s)
    (hsupper : s ≤ B * K) :
    q / (2 * B * T) ≤ s ∧ s ≤ 2 * B * q / T := by
  have h2T : 0 < 2 * T := by positivity
  have h2BT : 0 < 2 * B * T := by positivity
  constructor
  · apply (div_le_iff₀ h2BT).2
    calc
      q ≤ K * (2 * T) :=
        (div_le_iff₀ h2T).1 hKlower
      _ ≤ (s * B) * (2 * T) :=
        mul_le_mul_of_nonneg_right
          ((div_le_iff₀ hB).1 hslower) h2T.le
      _ = s * (2 * B * T) := by ring
  · apply (le_div_iff₀ hT).2
    have h1 : s * T ≤ (B * K) * T :=
      mul_le_mul_of_nonneg_right hsupper hT.le
    have h2 : 2 * (B * K * T) ≤ 3 * (B * q) := by
      calc
        2 * (B * K * T) = B * (K * (2 * T)) := by ring
        _ ≤ B * (3 * q) :=
          mul_le_mul_of_nonneg_left
            ((le_div_iff₀ h2T).1 hKupper) hB.le
        _ = 3 * (B * q) := by ring
    have h3 : 0 ≤ B * q := (mul_pos hB hq).le
    nlinarith only [h1, h2, h3]


private theorem reflected_next_denominator_arithmetic
    {q qNext T B K s S eps omega : ℝ}
    (hq : 0 < q) (hqNext : 0 < qNext) (hT : 0 < T)
    (hB : 0 < B) (hK : 0 < K) (hs : 0 < s) (hS : 0 < S)
    (heps : 0 < eps) (hqmono : q ≤ qNext)
    (hslower : K / B ≤ s) (hsupper : s ≤ B * K)
    (homega : omega = eps * q * T / K)
    (hcfLower : 1 / (q * (qNext + q)) ≤ eps)
    (hcfUpper : eps ≤ 1 / (q * qNext))
    (hscaleLower : 1 / (2 * s * omega) ≤ S)
    (hscaleUpper : S ≤ 1 / (s * omega)) :
    qNext / (2 * B * T) ≤ S ∧ S ≤ 2 * B * qNext / T := by
  have homegapos : 0 < omega := by rw [homega]; positivity
  have hprod : omega * K = eps * q * T := by
    rw [homega]
    field_simp
  have hslo : K ≤ s * B := (div_le_iff₀ hB).1 hslower
  have helo : 1 ≤ eps * (q * (qNext + q)) :=
    (div_le_iff₀ (by positivity)).1 hcfLower
  have heup : eps * (q * qNext) ≤ 1 :=
    (le_div_iff₀ (by positivity)).1 hcfUpper
  have hscaleLo : 1 ≤ S * (2 * s * omega) :=
    (div_le_iff₀ (by positivity)).1 hscaleLower
  have hscaleUp : S * (s * omega) ≤ 1 :=
    (le_div_iff₀ (by positivity)).1 hscaleUpper
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * B * T)).2
    have h1 : s * omega * qNext ≤ B * T := by
      have ha := mul_le_mul_of_nonneg_right hsupper (by positivity : 0 ≤ omega * qNext)
      have hb := mul_le_mul_of_nonneg_right heup (by positivity : 0 ≤ B * T)
      calc
        s * omega * qNext ≤ B * (omega * K) * qNext := by nlinarith [ha]
        _ = B * (eps * (q * qNext)) * T := by rw [hprod]; ring
        _ ≤ B * T := by nlinarith [hb]
    have h2 := mul_le_mul_of_nonneg_right hscaleLo hqNext.le
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * S)
    nlinarith
  · apply (le_div_iff₀ hT).2
    have h1 : T ≤ 2 * B * qNext * (s * omega) := by
      have ha := mul_le_mul_of_nonneg_right hslo homegapos.le
      have hb := mul_le_mul_of_nonneg_right helo hT.le
      have hc : T ≤ s * B * omega * (qNext + q) := by
        have hd := mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ qNext + q)
        rw [show K * omega = eps * q * T by nlinarith [hprod]] at hd
        nlinarith [hb, hd]
      have hd := mul_le_mul_of_nonneg_left hqmono (by positivity : 0 ≤ s * B * omega)
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hS.le
    have h3 := mul_le_mul_of_nonneg_left hscaleUp (by positivity : 0 ≤ 2 * B * qNext)
    nlinarith

theorem reflected_next_denominator_scale_with_cutoff
    {q qNext T B K s S eps omega : ℝ}
    (hq : 0 < q) (hqNext : 0 < qNext) (hT : 0 < T)
    (hB : 0 < B) (hK : 0 < K) (hs : 0 < s) (hS : 0 < S)
    (heps : 0 < eps) (hqQ : q ≤ qNext)
    (hslower : K / B ≤ s) (hsupper : s ≤ B * K)
    (hKupper : K ≤ 3 * q / (2 * T))
    (hcut : 12 * B ^ 2 * q < qNext)
    (homega : omega = eps * q * T / K)
    (hcfLower : 1 / (q * (qNext + q)) ≤ eps)
    (hcfUpper : eps ≤ 1 / (q * qNext))
    (hHlower : 1 / (s * (S + s)) ≤ omega)
    (hHupper : omega ≤ 1 / (s * S)) :
    qNext / (2 * B * T) ≤ S ∧ S ≤ 2 * B * qNext / T := by
  have hsq : s ^ 2 ≤ (B * K) ^ 2 :=
    (sq_le_sq₀ hs.le (mul_nonneg hB.le hK.le)).2 hsupper
  have hfirst : omega * s ^ 2 ≤ eps * q * T * B ^ 2 * K := by
    rw [homega]
    have hfac : 0 ≤ eps * q * T / K := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsq hfac
    calc
      (eps * q * T / K) * s ^ 2 ≤ (eps * q * T / K) * (B * K) ^ 2 := hmul
      _ = eps * q * T * B ^ 2 * K := by
        field_simp [ne_of_gt hK]
        <;> ring
  have hsecond : eps * q * T * B ^ 2 * K ≤
      (3 / 2 : ℝ) * B ^ 2 * eps * q ^ 2 := by
    have hcoeff : 0 ≤ eps * q * T * B ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hKupper hcoeff
    calc
      eps * q * T * B ^ 2 * K ≤
          eps * q * T * B ^ 2 * (3 * q / (2 * T)) := hmul
      _ = (3 / 2 : ℝ) * B ^ 2 * eps * q ^ 2 := by
        field_simp [ne_of_gt hT]
        <;> ring
  have hthird : (3 / 2 : ℝ) * B ^ 2 * eps * q ^ 2 ≤
      (3 / 2 : ℝ) * B ^ 2 * q / qNext := by
    have hcoeff : 0 ≤ (3 / 2 : ℝ) * B ^ 2 * q ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcfUpper hcoeff
    calc
      (3 / 2 : ℝ) * B ^ 2 * eps * q ^ 2 ≤
          ((3 / 2 : ℝ) * B ^ 2 * q ^ 2) * (1 / (q * qNext)) := by
            convert hmul using 1 <;> ring
      _ = (3 / 2 : ℝ) * B ^ 2 * q / qNext := by
        field_simp [ne_of_gt hq, ne_of_gt hqNext]
        <;> ring
  have hlegendreCut : omega * s ^ 2 < 1 / 8 := by
    have hbound : (3 / 2 : ℝ) * B ^ 2 * q / qNext < 1 / 8 := by
      apply (div_lt_iff₀ hqNext).2
      nlinarith [hcut]
    exact lt_of_le_of_lt (le_trans hfirst (le_trans hsecond hthird)) hbound
  have hHlowerProd : 1 ≤ omega * (s * (S + s)) :=
    (div_le_iff₀ (mul_pos hs (add_pos hS hs))).1 hHlower
  have hHupperProd : omega * (s * S) ≤ 1 :=
    (le_div_iff₀ (mul_pos hs hS)).1 hHupper
  have homegaPos : 0 < omega := by rw [homega]; positivity
  have hscaleLower : 1 / (2 * s * omega) ≤ S := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * s * omega)).2
    nlinarith [hHlowerProd, hlegendreCut]
  have hscaleUpper : S ≤ 1 / (s * omega) := by
    apply (le_div_iff₀ (mul_pos hs homegaPos)).2
    nlinarith [hHupperProd]
  exact reflected_next_denominator_arithmetic
    hq hqNext hT hB hK hs hS heps hqQ hslower hsupper homega
    hcfLower hcfUpper hscaleLower hscaleUpper


theorem reflected_endpoints_from_local_H
    {α : ℚ} (hden : 2 ≤ α.den)
    (H : CFGap (reversePoint α : ℝ))
    {q Q B T L : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) (hB : 1 ≤ B) (hT : 0 < T)
    (hscale : Real.log T = L - Real.log (α.den : ℝ))
    (hqlo : q / (2 * B * T) ≤ (H.value.den : ℝ))
    (hqhi : (H.value.den : ℝ) ≤ 2 * B * q / T)
    (hQlo : Q / (2 * B * T) ≤ (H.nextDen : ℝ))
    (hQhi : (H.nextDen : ℝ) ≤ 2 * B * Q / T) :
    ∃ c d : ℝ, LogGap (α : ℝ) c (d - c) ∧
      |Real.log q - (L - d)| ≤ Real.log (4 * B) ∧
      |Real.log Q - (L - c)| ≤ Real.log (4 * B) := by
  rcases actual_reversal_profile hden ⟨H, rfl, rfl⟩ with
    ⟨c, d, hactual, hleft, hright⟩
  have hs : 0 < (H.value.den : ℝ) := by
    exact_mod_cast H.value.den_pos
  have hS : 0 < (H.nextDen : ℝ) := by
    exact_mod_cast (cfGap_bounds H).1
  have hHadd : H.left + H.width = H.right := by
    rw [CFGap.width]
    ring
  have hleft' :
      |Real.log (H.value.den : ℝ) -
        (Real.log (α.den : ℝ) - d)| ≤ Real.log 2 := by
    simpa [CFGap.left] using hleft
  have hright' :
      |Real.log (H.nextDen : ℝ) -
        (Real.log (α.den : ℝ) - c)| ≤ Real.log 2 := by
    rw [hHadd, CFGap.right] at hright
    exact hright
  have hleft_endpoint := reflected_endpoint_scale
    (q := q) (s := (H.value.den : ℝ)) (B := B) (T := T)
    (L := L) (M := Real.log (α.den : ℝ)) (d := d)
    hq hs hB hT hscale hqlo hqhi hleft'
  have hright_endpoint := reflected_endpoint_scale
    (q := Q) (s := (H.nextDen : ℝ)) (B := B) (T := T)
    (L := L) (M := Real.log (α.den : ℝ)) (d := c)
    hQ hS hB hT hscale hQlo hQhi hright'
  exact ⟨c, d, hactual, hleft_endpoint, hright_endpoint⟩



/- Paper §4, rational perturbation lemma, in the five-class profile form
   above. L = -log |delta| and M = log V; delta may have either sign and no
   lower bound on W = 1 / (V^2 * |delta|) is assumed. The reflected witness is
   constructed for the selected near, large-ratio input gap. -/
set_option maxHeartbeats 2000000 in
theorem rational_perturbation
    (α δ : ℚ) (hV : 2 ≤ α.den) (hδ : δ ≠ 0)
    {a g : ℝ}
    (h : LogGap ((α + δ : ℚ) : ℝ) a g) :
    PerturbationGapCases
      (fun _ => LogGap (α : ℝ)) 0
      (-Real.log |(δ : ℝ)|) (Real.log (α.den : ℝ))
      (Real.log (4 * (coordinateDen α δ : ℝ)))
      (Real.log 6) (Real.log (3 / 2 : ℝ)) a g := by
  have hδpos : 0 < |(δ : ℝ)| := abs_pos.mpr (by exact_mod_cast hδ)
  have hVp : 0 < (α.den : ℝ) := by exact_mod_cast α.den_pos
  have hBn : 0 < coordinateDen α δ := Rat.den_pos _
  have hBp : 0 < (coordinateDen α δ : ℝ) := by exact_mod_cast hBn
  have hB1 : (1 : ℝ) ≤ (coordinateDen α δ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hBn)
  have hΔ : |(δ : ℝ)| = |((α + δ : ℚ) : ℝ) - (α : ℝ)| := by
    congr 1
    push_cast
    ring
  have hall := five_way_perturbation
    (L := -Real.log |(δ : ℝ)|) (M := Real.log (α.den : ℝ))
    (E := Real.log (4 * (coordinateDen α δ : ℝ)))
    h hΔ hBp
  apply hall
  · intro G ha hg hval _ _
    constructor
    · simpa [CFGap.left, hval] using ha
    · have hQ : 0 < (G.nextDen : ℝ) := by exact_mod_cast (cfGap_bounds G).1
      have he : |(δ : ℝ)| ≤ 1 / ((α.den : ℝ) * (G.nextDen : ℝ)) := by
        simpa [hval] using (cfGap_bounds G).2.2.2
      have hp := (le_div_iff₀ (mul_pos hVp hQ)).mp he
      have hl := Real.log_le_log (mul_pos hδpos (mul_pos hVp hQ)) hp
      rw [Real.log_one, Real.log_mul hδpos.ne' (mul_pos hVp hQ).ne',
        Real.log_mul hVp.ne' hQ.ne'] at hl
      change g ≤ -Real.log |(δ : ℝ)| - 2 * Real.log (α.den : ℝ)
      have hw : g = Real.log (G.nextDen : ℝ) - Real.log (α.den : ℝ) := by
        simpa [CFGap.width, CFGap.left, CFGap.right, hval] using hg
      linarith
  · intro G ha hg _ hnear hsmall
    constructor
    · have hq : 0 < (G.value.den : ℝ) := by exact_mod_cast G.value.den_pos
      have hQ : 0 < (G.nextDen : ℝ) := by exact_mod_cast (cfGap_bounds G).1
      have hm : (G.nextDen : ℝ) ≤
          (4 * (coordinateDen α δ : ℝ)) ^ 2 * (G.value.den : ℝ) := by
        have hh := (div_le_iff₀ hq).mp hsmall
        nlinarith [sq_nonneg (coordinateDen α δ : ℝ)]
      have hl := Real.log_le_log hQ hm
      rw [Real.log_mul (pow_ne_zero _ (by positivity)) hq.ne',
        Real.log_pow] at hl
      norm_num only [Nat.cast_ofNat] at hl
      change g ≤ 2 * Real.log (4 * (coordinateDen α δ : ℝ))
      have hw : g = Real.log (G.nextDen : ℝ) - Real.log (G.value.den : ℝ) := by
        simpa [CFGap.width, CFGap.left, CFGap.right] using hg
      linarith
    · change -Real.log |(δ : ℝ)| - Real.log (α.den : ℝ) -
          Real.log (3 / 2 : ℝ) ≤ a
      exact (selected_gap_tail_lower α δ G.value hδ hnear).trans_eq
        (by simpa [CFGap.left] using ha.symm)
  · intro G ha hg _ hnear hlarge
    obtain ⟨hcoord, k, r, _, _, hkn, _, _, hrlo, hrhi, hrne, hrcut,
      homega, hKlo, hKhi⟩ := reflected_r_choice_data α δ hV hδ G hnear hlarge
    obtain ⟨H, hHr, _, _, _, _, _, _, hHlo, hHhi⟩ :=
      reflected_legendre_gap_witness hrne hrcut
    let T : ℝ := 1 / ((α.den : ℝ) * |(δ : ℝ)|)
    have hT : 0 < T := by dsimp [T]; positivity
    have hq : 0 < (G.value.den : ℝ) := by exact_mod_cast G.value.den_pos
    have hQ : 0 < (G.nextDen : ℝ) := by exact_mod_cast (cfGap_bounds G).1
    have hK : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hkn)
    have hs : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
    have hS : 0 < (H.nextDen : ℝ) := by exact_mod_cast (cfGap_bounds H).1
    have hKlo' : (G.value.den : ℝ) / (2 * T) ≤ |(k : ℝ)| := by
      calc
        (G.value.den : ℝ) / (2 * T) =
            (G.value.den : ℝ) * (α.den : ℝ) * (|(δ : ℝ)| / 2) := by
          dsimp [T]
          field_simp
          <;> ring
        _ ≤ _ := hKlo
    have hKhi' : |(k : ℝ)| ≤ 3 * (G.value.den : ℝ) / (2 * T) := by
      calc
        |(k : ℝ)| ≤ (G.value.den : ℝ) * (α.den : ℝ) *
            ((3 / 2 : ℝ) * |(δ : ℝ)|) := hKhi
        _ = 3 * (G.value.den : ℝ) / (2 * T) := by
          dsimp [T]
          field_simp
          <;> ring
    have homega' : |(reversePoint α : ℝ) - (r : ℝ)| =
        |((α + δ : ℚ) : ℝ) - (G.value : ℝ)| *
          (G.value.den : ℝ) * T / |(k : ℝ)| := by
      rw [homega]
      dsimp [T]
      ring
    have heps : 0 < |((α + δ : ℚ) : ℝ) - (G.value : ℝ)| := by
      exact lt_of_lt_of_le (by positivity) (cfGap_bounds G).2.2.1
    have hcut : 12 * (coordinateDen α δ : ℝ) ^ 2 * (G.value.den : ℝ) <
        (G.nextDen : ℝ) := (lt_div_iff₀ hq).mp hlarge
    have hmono : (G.value.den : ℝ) ≤ (G.nextDen : ℝ) := by
      exact_mod_cast (cfGap_bounds G).2.1
    obtain ⟨hslo, hshi⟩ := reflected_value_denominator_scale hq hT hBp
      hKlo' hKhi' hrlo hrhi
    obtain ⟨hSlo, hShi⟩ := reflected_next_denominator_scale_with_cutoff
      hq hQ hT hBp hK hs hS heps hmono hrlo hrhi hKhi' hcut homega'
      (cfGap_bounds G).2.2.1 (cfGap_bounds G).2.2.2 hHlo hHhi
    have hscale : Real.log T =
        -Real.log |(δ : ℝ)| - Real.log (α.den : ℝ) := by
      dsimp [T]
      rw [Real.log_div (by norm_num) (mul_ne_zero hVp.ne' hδpos.ne'),
        Real.log_one, Real.log_mul hVp.ne' hδpos.ne']
      ring
    obtain ⟨c, d, hgap, hc, hd⟩ := reflected_endpoints_from_local_H hV H
      hq hQ hB1 hT hscale
      (by simpa [hHr] using hslo) (by simpa [hHr] using hshi) hSlo hShi
    refine ⟨c, d, hgap, ?_, ?_, ?_⟩
    · simpa [ha, CFGap.left] using hc
    · have hab : a + g = Real.log (G.nextDen : ℝ) := by
        rw [ha, hg, CFGap.width, CFGap.right, CFGap.left]
        ring
      simpa only [hab] using hd
    · exact (selected_gap_tail_lower α δ G.value hδ hnear).trans_eq
        (by simpa [CFGap.left] using ha.symm)

end Paper4.HmuSkeleton

#print axioms Paper4.HmuSkeleton.reflected_r_choice_data
#print axioms Paper4.HmuSkeleton.rational_perturbation

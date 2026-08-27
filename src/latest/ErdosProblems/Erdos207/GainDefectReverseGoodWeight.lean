/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGainDefectReverseWeight

/-! # Summing the reverse fourth-moment exposure classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def gainDefectReverseCodeSupport
    {W : Type*} [DecidableEq W] (T : W) (H : Finset W) (q : ℕ) : Finset (Finset W × ℕ) :=
  {H, insert T H} ×ˢ range (q + 1)

theorem GainDefectWitness.reverseCode_mem_support
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}
    (w : GainDefectWitness F G T z) (H : Finset W) (q : ℕ) (hF : w.first.card ≤ q) :
    (w.reverseSecondRoot H, w.reverseFirstRoot.card) ∈ gainDefectReverseCodeSupport T H q := by
  apply mem_product.mpr
  refine ⟨?_, mem_range.mpr (by have h := card_le_card w.reverseFirstRoot_subset; omega)⟩
  by_cases hT : T ∈ w.second
  · simp [GainDefectWitness.reverseSecondRoot, inter_singleton_of_mem hT]
  · simp [GainDefectWitness.reverseSecondRoot, inter_singleton_of_notMem hT]

def gainDefectReverseGoodWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (r s : ℕ) (p : ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ w ∈ (univ : Finset (GainDefectWitness F G T z)).filter
    (fun w ↦ H ⊆ w.remainder ∧ w.ForwardExceptional H ∧
      s + 4 ≤ vortexRootExponent r w.reverseFirstRoot.card +
        vortexRootExponent s (w.reverseSecondRoot H).card), p ^ (w.remainder \ H).card

theorem gainDefectReverseGoodWeight_eq_code_sum
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (q r s : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card ≤ q) :
    gainDefectReverseGoodWeight F G T z H r s p =
      ∑ c ∈ gainDefectReverseCodeSupport T H q,
        if s + 4 ≤ vortexRootExponent r c.2 + vortexRootExponent s c.1.card then
          gainDefectReverseClassWeight F G T z H c.1 c.2 p else 0 := by
  classical
  let code := fun w : GainDefectWitness F G T z ↦ (w.reverseSecondRoot H, w.reverseFirstRoot.card)
  let active := (univ : Finset (GainDefectWitness F G T z)).filter
    (fun w ↦ H ⊆ w.remainder ∧ w.ForwardExceptional H ∧
      s + 4 ≤ vortexRootExponent r w.reverseFirstRoot.card +
        vortexRootExponent s (w.reverseSecondRoot H).card)
  change (∑ w ∈ active, p ^ (w.remainder \ H).card) = _
  calc
    _ = ∑ c ∈ gainDefectReverseCodeSupport T H q,
        ∑ w ∈ active with code w = c, p ^ (w.remainder \ H).card := by
      symm
      apply sum_fiberwise_of_maps_to
      intro w _
      exact w.reverseCode_mem_support H q (hF w.first w.first_mem)
    _ = _ := by
      apply sum_congr rfl
      intro c _
      by_cases hgood : s + 4 ≤ vortexRootExponent r c.2 + vortexRootExponent s c.1.card
      · rw [if_pos hgood]
        have hfibre : {w ∈ active | code w = c} = gainDefectReverseClass F G T z H c.1 c.2 := by
          ext w
          constructor
          · intro hw
            obtain ⟨hw, hc⟩ := mem_filter.mp hw
            have hd := (mem_filter.mp hw).2
            have hQ : w.reverseSecondRoot H = c.1 := congrArg Prod.fst hc
            have hb : w.reverseFirstRoot.card = c.2 := congrArg Prod.snd hc
            exact mem_filter.mpr ⟨mem_univ _, hd.1, hd.2.1, hQ, hb⟩
          · intro hw
            have hd := (mem_filter.mp hw).2
            refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hd.1, hd.2.1, ?_⟩, ?_⟩
            · simpa only [hd.2.2.1, hd.2.2.2] using hgood
            · exact Prod.ext hd.2.2.1 hd.2.2.2
        rw [hfibre]
        rfl
      · rw [if_neg hgood]
        have hfibre : {w ∈ active | code w = c} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hw, hc⟩ := mem_filter.mp hw
          have h := (mem_filter.mp hw).2.2.2
          have hQ : w.reverseSecondRoot H = c.1 := congrArg Prod.fst hc
          have hb : w.reverseFirstRoot.card = c.2 := congrArg Prod.snd hc
          exact hgood (by simpa only [hQ, hb] using h)
        rw [hfibre, sum_empty]

def gainDefectReverseGoodWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  (2 * (q + 1) : ℝ≥0) * ((2 : ℝ≥0) ^ q * ((pairExactBankExtensionCoefficient q B : ℕ) *
    (2 : ℝ≥0) ^ (q + 1) * pairExactBankExtensionCoefficient q B))

theorem gainDefectReverseGoodWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (H : TripleSystemOn V)
    (hr : r ≤ q) (hs : s ≤ q) (hz : 1 ≤ z) :
    gainDefectReverseGoodWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T z H r s (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      gainDefectReverseGoodWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) := by
  classical
  let F := absorberInducedConfigurationsOn q r B
  let G := absorberInducedConfigurationsOn q s B
  let C : ℝ≥0 := pairExactBankExtensionCoefficient q B
  let M : ℝ≥0 := (2 : ℝ≥0) ^ q * (C * 2 ^ (q + 1) * C)
  let N : ℝ≥0 := Fintype.card V + 1
  have hF : ∀ E ∈ F, E.card ≤ q := by
    intro E hE
    rw [absorberInducedConfigurationsOn_fixed_card E hE]
    omega
  rw [gainDefectReverseGoodWeight_eq_code_sum F G T z H q r s _ hF]
  have hsupport : ((gainDefectReverseCodeSupport T H q).card : ℝ≥0) ≤ 2 * (q + 1) := by
    have hc : (gainDefectReverseCodeSupport T H q).card ≤ 2 * (q + 1) := by
      rw [gainDefectReverseCodeSupport, card_product, card_range]
      apply Nat.mul_le_mul_right
      have hc := card_insert_le H ({insert T H} : Finset (Finset (TripleOn V)))
      simpa only [card_singleton] using hc
    exact_mod_cast hc
  calc
    _ ≤ ∑ _c ∈ gainDefectReverseCodeSupport T H q, M * N ^ (z - 1) := by
      apply sum_le_sum
      intro c _
      split_ifs with hgood
      · refine (gainDefectReverseClassWeight_absorberInduced_le q r s z B T H c.1 c.2 hz hgood).trans ?_
        have hp : (2 : ℝ≥0) ^ (s - 2 + 1) ≤ 2 ^ (q + 1) :=
          pow_le_pow_right' (by norm_num) (by omega)
        have hm : (2 : ℝ≥0) ^ (r - 2) ≤ 2 ^ q :=
          pow_le_pow_right' (by norm_num) (by omega)
        change (2 : ℝ≥0) ^ (r - 2) * ((C * 2 ^ (s - 2 + 1) * C) * N ^ (z - 1)) ≤ _
        calc
          _ ≤ (2 : ℝ≥0) ^ q * ((C * 2 ^ (q + 1) * C) * N ^ (z - 1)) :=
            mul_le_mul hm (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp zero_le) zero_le) zero_le)
              zero_le zero_le
          _ = _ := by dsimp only [M]; ring
      · exact zero_le
    _ = (gainDefectReverseCodeSupport T H q).card * (M * N ^ (z - 1)) := by simp
    _ ≤ (2 * (q + 1)) * (M * N ^ (z - 1)) := mul_le_mul_of_nonneg_right hsupport zero_le
    _ = _ := by change _ = (_ * M) * N ^ (z - 1); ring

end

end Erdos207

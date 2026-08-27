/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatExposureCode
import ErdosProblems.Erdos207.AbsorberCommonThreatClassWeight

/-! # Summing the nonexceptional third-moment exposure classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def CommonThreatExposureCode.IsGood
    {W : Type*} (H : Finset W) (r s : ℕ) (c : CommonThreatExposureCode W) : Prop :=
  H.card + c.2.2 + 8 ≤ vortexRootExponent r c.1.1.card + vortexRootExponent s c.2.1

instance {W : Type*} (H : Finset W) (r s : ℕ) (c : CommonThreatExposureCode W) :
    Decidable (c.IsGood H r s) :=
  inferInstanceAs (Decidable
    (H.card + c.2.2 + 8 ≤ vortexRootExponent r c.1.1.card + vortexRootExponent s c.2.1))

def commonThreatGoodWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (r s : ℕ) (p : ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ w ∈ (univ : Finset (CommonThreatWitness F G T T')).filter
    (fun w ↦ H ⊆ w.remainder ∧ (w.exposureCode H).IsGood H r s), p ^ (w.remainder \ H).card

theorem commonThreatGoodWeight_eq_code_sum
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (q r s : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card ≤ q) (hG : ∀ E ∈ G, E.card ≤ q) :
    commonThreatGoodWeight F G T T' H r s p =
      ∑ c ∈ commonThreatExposureCodeSupport T T' H q,
        if c.IsGood H r s then commonThreatExposureClassWeight F G T T' H
          c.1.1 c.1.2 c.2.1 c.2.2 p else 0 := by
  classical
  let active := (univ : Finset (CommonThreatWitness F G T T')).filter
    (fun w ↦ H ⊆ w.remainder ∧ (w.exposureCode H).IsGood H r s)
  change (∑ w ∈ active, p ^ (w.remainder \ H).card) = _
  calc
    _ = ∑ c ∈ commonThreatExposureCodeSupport T T' H q,
        ∑ w ∈ active with w.exposureCode H = c, p ^ (w.remainder \ H).card := by
      symm
      apply sum_fiberwise_of_maps_to
      intro w _
      exact w.exposureCode_mem_support H q (hF w.first w.first_mem) (hG w.second w.second_mem)
    _ = _ := by
      apply sum_congr rfl
      intro c _
      by_cases hgood : c.IsGood H r s
      · rw [if_pos hgood]
        have hfibre : {w ∈ active | w.exposureCode H = c} =
            commonThreatExposureClass F G T T' H c.1.1 c.1.2 c.2.1 c.2.2 := by
          rw [commonThreatExposureClass_eq_code_fibre]
          ext w
          by_cases hcode : w.exposureCode H = c <;> simp [active, hcode, hgood]
        rw [hfibre]
        rfl
      · rw [if_neg hgood]
        have hfibre : {w ∈ active | w.exposureCode H = c} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hw, hcode⟩ := mem_filter.mp hw
          have h := (mem_filter.mp hw).2.2
          rw [hcode] at h
          exact hgood h
        rw [hfibre, sum_empty]

theorem commonThreatGoodWeight_absorberInduced_le_root_size
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (H : TripleSystemOn V)
    (hr : r ≤ q) (hs : s ≤ q) :
    commonThreatGoodWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T T' H r s (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      ((2 ^ (2 * H.card) * (q + 1) ^ 2 : ℕ) : ℝ≥0) *
        (q * ((pairExactBankExtensionCoefficient q B : ℕ) *
          (2 : ℝ≥0) ^ (q + H.card + 1) * pairExactBankExtensionCoefficient q B)) := by
  classical
  let F := absorberInducedConfigurationsOn q r B
  let G := absorberInducedConfigurationsOn q s B
  let C : ℝ≥0 := pairExactBankExtensionCoefficient q B
  let bound : ℝ≥0 := q * (C * 2 ^ (q + H.card + 1) * C)
  have hF : ∀ E ∈ F, E.card ≤ q := by
    intro E hE
    rw [absorberInducedConfigurationsOn_fixed_card E hE]
    omega
  have hG : ∀ E ∈ G, E.card ≤ q := by
    intro E hE
    rw [absorberInducedConfigurationsOn_fixed_card E hE]
    omega
  rw [commonThreatGoodWeight_eq_code_sum F G T T' H q r s _ hF hG]
  calc
    _ ≤ ∑ _c ∈ commonThreatExposureCodeSupport T T' H q, bound := by
      apply sum_le_sum
      intro c hc
      split_ifs with hgood
      · refine (commonThreatExposureClassWeight_absorberInduced_le q r s B T T' H
          c.1.1 c.1.2 c.2.1 c.2.2 hgood).trans ?_
        have hroot := card_second_root_of_mem_commonThreatExposureCodeSupport hc
        change ((r - 2 : ℕ) : ℝ≥0) * (C * 2 ^ (r - 2 + c.1.2.card) * C) ≤ bound
        dsimp only [bound]
        have hrnum : ((r - 2 : ℕ) : ℝ≥0) ≤ q := by
          exact_mod_cast (show r - 2 ≤ q by omega)
        have hpow : (2 : ℝ≥0) ^ (r - 2 + c.1.2.card) ≤ 2 ^ (q + H.card + 1) :=
          pow_le_pow_right' (by norm_num) (by omega)
        exact mul_le_mul hrnum (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow zero_le) zero_le) zero_le zero_le
      · exact zero_le
    _ = (commonThreatExposureCodeSupport T T' H q).card * bound := by simp
    _ ≤ ((2 ^ (2 * H.card) * (q + 1) ^ 2 : ℕ) : ℝ≥0) * bound := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast card_commonThreatExposureCodeSupport_le T T' H q
    _ = _ := rfl

def commonThreatGoodWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  ((2 ^ (4 * q) * (q + 1) ^ 2 : ℕ) : ℝ≥0) *
    (q * ((pairExactBankExtensionCoefficient q B : ℕ) *
      (2 : ℝ≥0) ^ (3 * q + 1) * pairExactBankExtensionCoefficient q B))

theorem commonThreatGoodWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (H : TripleSystemOn V)
    (hr : r ≤ q) (hs : s ≤ q) :
    commonThreatGoodWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T T' H r s (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      commonThreatGoodWeightBound q B := by
  classical
  by_cases hH : H.card ≤ 2 * q
  · refine (commonThreatGoodWeight_absorberInduced_le_root_size q r s B T T' H hr hs).trans ?_
    unfold commonThreatGoodWeightBound
    have hfactor : ((2 ^ (2 * H.card) * (q + 1) ^ 2 : ℕ) : ℝ≥0) ≤
        ((2 ^ (4 * q) * (q + 1) ^ 2 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.mul_le_mul_right ((q + 1) ^ 2)
        (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (by omega : 2 * H.card ≤ 4 * q))
    have hpow : (2 : ℝ≥0) ^ (q + H.card + 1) ≤ 2 ^ (3 * q + 1) :=
      pow_le_pow_right' (by norm_num) (by omega)
    apply mul_le_mul hfactor _ zero_le zero_le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow zero_le) zero_le) zero_le
  · have himpossible : ∀ w : CommonThreatWitness
        (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B) T T',
        ¬ H ⊆ w.remainder := by
      intro w hsub
      have hc := card_le_card hsub
      have hrem := w.remainder_card
      have hf := absorberInducedConfigurationsOn_fixed_card w.first w.first_mem
      have hg := absorberInducedConfigurationsOn_fixed_card w.second w.second_mem
      omega
    simp only [commonThreatGoodWeight, himpossible, false_and, filter_false, sum_empty]
    exact zero_le

end

end Erdos207

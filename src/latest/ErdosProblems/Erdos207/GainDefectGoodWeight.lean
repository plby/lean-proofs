/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExposureCode
import ErdosProblems.Erdos207.AbsorberGainDefectClassWeight

/-! # Summing all forward fourth-moment exposure classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def GainDefectExposureCode.IsGood
    {W : Type*} (H : Finset W) (r s : ℕ) (c : GainDefectExposureCode W) : Prop :=
  H.card + c.2.2 + 8 ≤ vortexRootExponent r c.1.1.card + vortexRootExponent s c.2.1

instance gainDefectExposureCodeIsGoodDecidable
    {W : Type*} (H : Finset W) (r s : ℕ) (c : GainDefectExposureCode W) :
    Decidable (c.IsGood H r s) :=
  inferInstanceAs (Decidable
    (H.card + c.2.2 + 8 ≤ vortexRootExponent r c.1.1.card + vortexRootExponent s c.2.1))

def gainDefectGoodWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (r s : ℕ) (p : ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ w ∈ (univ : Finset (GainDefectWitness F G T z)).filter
    (fun w ↦ H ⊆ w.remainder ∧ (w.exposureCode H).IsGood H r s), p ^ (w.remainder \ H).card

theorem gainDefectGoodWeight_eq_code_sum
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (q r s : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card ≤ q) (hG : ∀ E ∈ G, E.card ≤ q) :
    gainDefectGoodWeight F G T z H r s p =
      ∑ c ∈ gainDefectExposureCodeSupport T H q,
        if c.IsGood H r s then gainDefectExposureClassWeight F G T z H
          c.1.1 c.1.2 c.2.1 c.2.2 p else 0 := by
  classical
  let active := (univ : Finset (GainDefectWitness F G T z)).filter
    (fun w ↦ H ⊆ w.remainder ∧ (w.exposureCode H).IsGood H r s)
  change (∑ w ∈ active, p ^ (w.remainder \ H).card) = _
  calc
    _ = ∑ c ∈ gainDefectExposureCodeSupport T H q,
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
            gainDefectExposureClass F G T z H c.1.1 c.1.2 c.2.1 c.2.2 := by
          rw [gainDefectExposureClass_eq_code_fibre]
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

def gainDefectGoodWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  ((2 ^ (4 * q) * (q + 1) ^ 2 : ℕ) : ℝ≥0) *
    ((2 : ℝ≥0) ^ q * ((pairExactBankExtensionCoefficient q B : ℕ) *
      (2 : ℝ≥0) ^ (3 * q) * pairExactBankExtensionCoefficient q B))

theorem gainDefectGoodWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (H : TripleSystemOn V)
    (hr : r ≤ q) (hs : s ≤ q) (hz : 1 ≤ z) :
    gainDefectGoodWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T z H r s (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      gainDefectGoodWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) := by
  classical
  let F := absorberInducedConfigurationsOn q r B
  let G := absorberInducedConfigurationsOn q s B
  let C : ℝ≥0 := pairExactBankExtensionCoefficient q B
  let M : ℝ≥0 := (2 : ℝ≥0) ^ q * (C * 2 ^ (3 * q) * C)
  let N : ℝ≥0 := Fintype.card V + 1
  have hF : ∀ E ∈ F, E.card ≤ q := by
    intro E hE
    rw [absorberInducedConfigurationsOn_fixed_card E hE]
    omega
  have hG : ∀ E ∈ G, E.card ≤ q := by
    intro E hE
    rw [absorberInducedConfigurationsOn_fixed_card E hE]
    omega
  by_cases hH : H.card ≤ 2 * q
  · rw [gainDefectGoodWeight_eq_code_sum F G T z H q r s _ hF hG]
    have hsupport : ((gainDefectExposureCodeSupport T H q).card : ℝ≥0) ≤
        ((2 ^ (4 * q) * (q + 1) ^ 2 : ℕ) : ℝ≥0) := by
      exact_mod_cast (card_gainDefectExposureCodeSupport_le T H q).trans
        (Nat.mul_le_mul_right ((q + 1) ^ 2)
          (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (by omega : 2 * H.card ≤ 4 * q)))
    calc
      _ ≤ ∑ _c ∈ gainDefectExposureCodeSupport T H q, M * N ^ (z - 1) := by
        apply sum_le_sum
        intro c hc
        split_ifs with hgood
        · refine (gainDefectExposureClassWeight_absorberInduced_le q r s z B T H
            c.1.1 c.1.2 c.2.1 c.2.2 hz hgood).trans ?_
          have hroot := card_second_root_of_mem_gainDefectExposureCodeSupport hc
          have hp : (2 : ℝ≥0) ^ (r - 2 + c.1.2.card) ≤ 2 ^ (3 * q) :=
            pow_le_pow_right' (by norm_num) (by omega)
          have hm : (2 : ℝ≥0) ^ (r - 2) ≤ 2 ^ q :=
            pow_le_pow_right' (by norm_num) (by omega)
          change (2 : ℝ≥0) ^ (r - 2) * ((C * 2 ^ (r - 2 + c.1.2.card) * C) * N ^ (z - 1)) ≤ _
          calc
            _ ≤ (2 : ℝ≥0) ^ q * ((C * 2 ^ (3 * q) * C) * N ^ (z - 1)) :=
              mul_le_mul hm (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp zero_le) zero_le) zero_le)
                zero_le zero_le
            _ = _ := by dsimp only [M]; ring
        · exact zero_le
      _ = (gainDefectExposureCodeSupport T H q).card * (M * N ^ (z - 1)) := by simp
      _ ≤ ((2 ^ (4 * q) * (q + 1) ^ 2 : ℕ) : ℝ≥0) * (M * N ^ (z - 1)) :=
        mul_le_mul_of_nonneg_right hsupport zero_le
      _ = _ := by change _ = (_ * M) * N ^ (z - 1); ring
  · have himpossible : ∀ w : GainDefectWitness F G T z, ¬ H ⊆ w.remainder := by
      intro w hsub
      have hc := card_le_card hsub
      have hrem := w.remainder_card
      have hf := hF w.first w.first_mem
      have hg := hG w.second w.second_mem
      omega
    change gainDefectGoodWeight F G T z H r s _ ≤ _
    simp only [gainDefectGoodWeight, himpossible, false_and, filter_false, sum_empty]
    exact zero_le

end

end Erdos207

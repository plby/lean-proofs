/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightSystem
import ErdosProblems.Erdos207.FiniteSpanCounting

/-! # Polynomial moment-order constants for growing KSSS moments

Unlike the earlier unrestricted powerset estimate, this counts only
intersections of cardinality at most the configuration-size cutoff.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sum_weight_sdiff_le_bounded_subsets_mul
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (U : Finset W) {κ : ℝ≥0} {d : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ) :
    ∑ i, setWeight π (F i \ U) ≤ (((d + 1) * (U.card + 1) ^ d : ℕ) : ℝ≥0) * κ := by
  classical
  have hpartition : (∑ i, setWeight π (F i \ U)) =
      ∑ H ∈ subsetsUpToCard U d, intersectionClassWeight F π U H := by
    calc
      _ = ∑ i, ∑ H ∈ subsetsUpToCard U d,
          if F i ∩ U = H then setWeight π (F i \ H) else 0 := by
        apply sum_congr rfl
        intro i _
        have hmem : F i ∩ U ∈ subsetsUpToCard U d :=
          mem_subsetsUpToCard_iff.mpr ⟨inter_subset_right, (card_le_card inter_subset_left).trans (hcard i)⟩
        rw [sum_eq_single (F i ∩ U)]
        · simp only [if_true]
          congr 1
          ext x
          simp
        · exact fun H _ hne ↦ by simp [hne.symm]
        · exact fun hnot ↦ (hnot hmem).elim
      _ = _ := by unfold intersectionClassWeight; rw [sum_comm]
  rw [hpartition]
  calc
    _ ≤ ∑ _H ∈ subsetsUpToCard U d, κ := sum_le_sum fun H _ ↦
      (intersectionClassWeight_le_extensionWeight F π U H).trans (hκ H)
    _ = (subsetsUpToCard U d).card * κ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_subsetsUpToCard_le U d) zero_le

theorem sum_weight_union_le_bounded_subsets
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) (U : Finset W) {κ : ℝ≥0} {d : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ) :
    ∑ i, setWeight π (U ∪ F i) ≤
      setWeight π U * ((((d + 1) * (U.card + 1) ^ d : ℕ) : ℝ≥0) * κ) := by
  calc
    _ = setWeight π U * ∑ i, setWeight π (F i \ U) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      exact setWeight_union_eq_mul_sdiff π U (F i)
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_weight_sdiff_le_bounded_subsets_mul F π U hcard hκ) zero_le

def boundedIntersectionMomentCoefficient (d s : ℕ) : ℕ := (d + 1) * (s * d + 1) ^ d

theorem sum_tupleWeight_le_bounded_intersections
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (π : W → ℝ≥0) {κ : ℝ≥0} {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ) :
    ∀ t ≤ s, ∑ f : Fin t → I, setWeight π (tupleUnion F f) ≤
      ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ t := by
  intro t hts
  induction t with
  | zero => simp [setWeight]
  | succ t ih =>
      have iht := ih (by omega)
      rw [sum_fin_succ_tuple, sum_comm]
      calc
        _ ≤ ∑ f : Fin t → I, setWeight π (tupleUnion F f) *
            ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) := by
          apply sum_le_sum
          intro f _
          simp only [tupleUnion_cons]
          have hU : (tupleUnion F f).card ≤ s * d :=
            (card_tupleUnion_le F hcard f).trans (Nat.mul_le_mul_right d (by omega))
          have hcoef : (((d + 1) * ((tupleUnion F f).card + 1) ^ d : ℕ) : ℝ≥0) ≤
              (boundedIntersectionMomentCoefficient d s : ℝ≥0) := by
            exact_mod_cast Nat.mul_le_mul_left (d + 1)
              (pow_le_pow_left₀ zero_le (Nat.add_le_add_right hU 1) d)
          calc
            _ = ∑ i : I, setWeight π (tupleUnion F f ∪ F i) := by
              apply sum_congr rfl
              intro i _
              rw [union_comm]
            _ ≤ _ := (sum_weight_union_le_bounded_subsets F π (tupleUnion F f) hcard hκ).trans
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef zero_le) zero_le)
        _ = (∑ f : Fin t → I, setWeight π (tupleUnion F f)) *
            ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) := by rw [sum_mul]
        _ ≤ (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ t) *
            ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) :=
          mul_le_mul_of_nonneg_right iht zero_le
        _ = _ := by rw [pow_succ]

theorem configurationMomentBound_bounded_intersections
    {Ω W I : Type*} [Fintype Ω] [DecidableEq W] [Fintype I]
    (L : FiniteLaw Ω) (F : I → Finset W) (R : Ω → Finset W)
    (π : W → ℝ≥0) (C κ : ℝ≥0) {d s : ℕ}
    (hcard : ∀ i, (F i).card ≤ d) (hκ : HasExtensionBound F π κ)
    (hjoint : ∀ T : Finset W, T.card ≤ s * d →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦ (selectedCount F (R ω)) ^ s) ≤
      C * (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ s) := by
  exact (expectation_selectedCount_pow_le L F R π C hcard hjoint).trans
    (mul_le_mul_of_nonneg_left (sum_tupleWeight_le_bounded_intersections F π hcard hκ s le_rfl) zero_le)

end

end Erdos207

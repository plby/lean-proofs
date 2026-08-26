/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCommonCutoff
import ErdosProblems.Erdos4b.GeneralFourierTensorSquareAsymptotic

/-!
# One coordinate-capturing cutoff for a finite profile family

The common bound captures every nonzero coefficient in the literal
finite tensor combination. The old coefficient-square sum equals its
value at this new cutoff or at any larger one, for every graph.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def selbergTensorFamilyCommonBound {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ) : ℕ :=
  ∑ j ∈ S, ∑ k ∈ S,
    compactProfileTensorCommonBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i)

theorem compactProfileTensorCommonBound_le_family {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ) (L : (ι ⊕ ι) → ℝ)
    {j k : J} (hj : j ∈ S) (hk : k ∈ S) :
    compactProfileTensorCommonBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i) ≤
      selbergTensorFamilyCommonBound S F L := by
  apply (Finset.single_le_sum
    (f := fun k ↦ compactProfileTensorCommonBound
      (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i))
    (fun k hk ↦ Nat.zero_le _) hk).trans
  exact Finset.single_le_sum
    (f := fun j ↦ ∑ k ∈ S,
      compactProfileTensorCommonBound (pairedSelbergProfiles (F j) (F k)) (fun i _ ↦ L i))
    (fun j hj ↦ Nat.zero_le _) hj

theorem selbergTensorFamilyCommonBound_capture_coefficient
    {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (d : (ι ⊕ ι) → ℕ) (hd : ∀ i, 0 < d i)
    (hne : (∑ j ∈ S, selbergTensorCoefficient (F j) L d) ≠ 0) :
    ∀ i, d i ≤ selbergTensorFamilyCommonBound S F L := by
  obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hpair : doubledSelbergProfileTensor (pairedSelbergProfiles (F j) (F j))
      (fun i _ ↦ L i) (fun i _ ↦ d i) ≠ 0 := by
    rw [doubledSelbergProfileTensor_eq_coefficient_mul]
    exact mul_ne_zero hjne hjne
  have hcap := compactProfileTensorCommonBound_capture
    (pairedSelbergProfiles (F j) (F j))
    (hasCompactSupport_pairedSelbergProfiles (F j) (F j) (hF j hj) (hF j hj))
    (fun i _ ↦ L i) (fun i _ ↦ hL i) (fun i _ ↦ d i) (fun i _ ↦ hd i) hpair
  exact fun i ↦ (hcap i false).trans (compactProfileTensorCommonBound_le_family S F L hj hj)

theorem compactSelbergTensorSquareSum_eq_cutoff_of_common_le
    {ι J : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    {B : ℕ} (hB : selbergTensorFamilyCommonBound S F L ≤ B) :
    compactSelbergTensorSquareSum select edges companion S F L =
      cutoffSelbergBilinearSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
          (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d) := by
  rw [compactSelbergTensorSquareSum_eq_pair_sum select edges companion S F hF L hL,
    cutoffSelbergBilinearSum_tensor_sum_square]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have hcompact := hasCompactSupport_pairedSelbergProfiles (F j) (F k) (hF j hj) (hF k hk)
  rw [compactSelbergProfileSum_eq_commonBound select edges companion _ hcompact
    (fun i _ ↦ L i) (fun i _ ↦ hL i)]
  exact cutoffSelbergProfileTensorSum_commonBound_eq_cutoff_of_le select edges companion _
    hcompact (fun i _ ↦ L i) (fun i _ ↦ hL i)
    ((compactProfileTensorCommonBound_le_family S F L hj hk).trans hB)

end

end Erdos4b

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.CRTClose

/-!
# Occupied prime blocks produce close divisors

This file packages the deterministic passage from an equal-sums event on
occupied logarithmic prime blocks to the divisor pair in Erdős Problem 144.
For each occupied label we choose one of its selected prime coordinates.
Choice is harmless here: all conclusions are finite and pointwise.
-/

open scoped BigOperators

namespace Erdos144.BlockCRTClose

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The block labels represented among the selected coordinates `Z`. -/
def occupiedLabels (label : κ → ℕ) (Z : Finset κ) : Finset ℕ :=
  Z.image label

@[simp] theorem mem_occupiedLabels_iff
    (label : κ → ℕ) (Z : Finset κ) (j : ℕ) :
    j ∈ occupiedLabels label Z ↔ ∃ i ∈ Z, label i = j := by
  simp [occupiedLabels]

/-- A canonical (classically chosen) selected prime coordinate carrying an
occupied label. -/
def representative (label : κ → ℕ) (Z : Finset κ)
    (j : ↥(occupiedLabels label Z)) : κ :=
  (Finset.mem_image.mp j.2).choose

theorem representative_mem (label : κ → ℕ) (Z : Finset κ)
    (j : ↥(occupiedLabels label Z)) :
    representative label Z j ∈ Z :=
  (Finset.mem_image.mp j.2).choose_spec.1

theorem label_representative (label : κ → ℕ) (Z : Finset κ)
    (j : ↥(occupiedLabels label Z)) :
    label (representative label Z j) = j :=
  (Finset.mem_image.mp j.2).choose_spec.2

/-- Different occupied labels have different representatives. -/
theorem representative_injective (label : κ → ℕ) (Z : Finset κ) :
    Function.Injective (representative label Z) := by
  intro i j hij
  apply Subtype.ext
  simpa only [← label_representative label Z] using congrArg label hij

/-- The embedding used to transport finite sets of occupied labels to
finite sets of selected prime coordinates. -/
def representativeEmbedding (label : κ → ℕ) (Z : Finset κ) :
    ↥(occupiedLabels label Z) ↪ κ where
  toFun := representative label Z
  inj' := representative_injective label Z

/-- Choose one selected prime coordinate for every label in `A`. -/
def coordinateSet (label : κ → ℕ) (Z : Finset κ)
    (A : Finset ↥(occupiedLabels label Z)) : Finset κ :=
  A.map (representativeEmbedding label Z)

theorem coordinateSet_subset (label : κ → ℕ) (Z : Finset κ)
    (A : Finset ↥(occupiedLabels label Z)) :
    coordinateSet label Z A ⊆ Z := by
  intro i hi
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
  exact representative_mem label Z j

@[simp] theorem card_coordinateSet (label : κ → ℕ) (Z : Finset κ)
    (A : Finset ↥(occupiedLabels label Z)) :
    (coordinateSet label Z A).card = A.card := by
  simp [coordinateSet]

theorem coordinateSet_injective (label : κ → ℕ) (Z : Finset κ) :
    Function.Injective (coordinateSet label Z) := by
  intro A B hAB
  simpa [coordinateSet] using hAB

theorem sum_label_coordinateSet (label : κ → ℕ) (Z : Finset κ)
    (A : Finset ↥(occupiedLabels label Z)) :
    (∑ i ∈ coordinateSet label Z A, label i) = ∑ j ∈ A, (j : ℕ) := by
  rw [coordinateSet, Finset.sum_map]
  exact Finset.sum_congr rfl fun j _hj ↦ label_representative label Z j

/-- The finite good event used in the block CRT model.  The full occupied
set has cardinality at most `L`, and it contains disjoint nonempty subsets
with the same sum of integer block labels. -/
def BlockGood (label : κ → ℕ) (L : ℕ) (Z : Finset κ) : Prop :=
  (occupiedLabels label Z).card ≤ L ∧
    ∃ A B : Finset ↥(occupiedLabels label Z),
      Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
        (∑ j ∈ A, (j : ℕ)) = ∑ j ∈ B, (j : ℕ)

theorem blockGood_witness_ne
    {label : κ → ℕ} {L : ℕ} {Z : Finset κ}
    (hgood : BlockGood label L Z) :
    ∃ A B : Finset ↥(occupiedLabels label Z),
      A ≠ B ∧ A.card ≤ L ∧ B.card ≤ L ∧
        (∑ j ∈ A, (j : ℕ)) = ∑ j ∈ B, (j : ℕ) := by
  obtain ⟨hcard, A, B, hdisj, hA, hB, hsum⟩ := hgood
  refine ⟨A, B, ?_, ?_, ?_, hsum⟩
  · intro hAB
    subst B
    obtain ⟨j, hj⟩ := hA
    exact (Finset.disjoint_left.mp hdisj) hj hj
  · calc
      A.card ≤ Fintype.card ↥(occupiedLabels label Z) := Finset.card_le_univ A
      _ = (occupiedLabels label Z).card := Fintype.card_coe _
      _ ≤ L := hcard
  · calc
      B.card ≤ Fintype.card ↥(occupiedLabels label Z) := Finset.card_le_univ B
      _ = (occupiedLabels label Z).card := Fintype.card_coe _
      _ ≤ L := hcard

variable {p : κ → ℕ} {label : κ → ℕ} {Z : Finset κ}
variable {K : ℝ} {L n : ℕ}

/-- Generic occupied-block transfer.  Divisibility is supplied directly,
so this theorem is usable independently of the particular CRT encoding.
The factor `2` in the resolution condition accounts for at most `L` labels
on each side of the equal-sum relation. -/
theorem hasCloseDivisors_of_blockGood
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hdiv : ∀ i ∈ Z, p i ∣ n)
    (hK : 0 < K)
    (hblock : ∀ i ∈ Z,
      |Real.log (p i : ℝ) - (label i : ℝ) / K| ≤ 1 / K)
    (hresolution : 2 * (L : ℝ) / K < Real.log 2)
    (hgood : BlockGood label L Z) :
    CRTClose.HasCloseDivisors n := by
  letI (i : κ) : NeZero (p i) := ⟨(hprime i).ne_zero⟩
  obtain ⟨A, B, hAB, hAcard, hBcard, hsum⟩ :=
    blockGood_witness_ne hgood
  let A' := coordinateSet label Z A
  let B' := coordinateSet label Z B
  have hA'Z : A' ⊆ Z := coordinateSet_subset label Z A
  have hB'Z : B' ⊆ Z := coordinateSet_subset label Z B
  have hA'B' : A' ≠ B' := by
    intro h
    exact hAB (coordinateSet_injective label Z h)
  have hsumR :
      (∑ i ∈ A', (label i : ℝ) / K) =
        ∑ i ∈ B', (label i : ℝ) / K := by
    have hsumNat :
        (∑ i ∈ A', label i) = ∑ i ∈ B', label i := by
      simpa [A', B', sum_label_coordinateSet] using hsum
    have hsumReal :
        (∑ i ∈ A', (label i : ℝ)) = ∑ i ∈ B', (label i : ℝ) := by
      exact_mod_cast hsumNat
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact congrArg (fun x : ℝ ↦ x / K) hsumReal
  have happrox : ∀ i ∈ A' ∪ B',
      |Real.log (p i : ℝ) - (label i : ℝ) / K| ≤ 1 / K := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiA | hiB
    · exact hblock i (hA'Z hiA)
    · exact hblock i (hB'Z hiB)
  have hcard : A'.card + B'.card ≤ 2 * L := by
    simp only [A', B', card_coordinateSet]
    omega
  have hsmall :
      ((A'.card + B'.card : ℕ) : ℝ) * (1 / K) < Real.log 2 := by
    have hcardR :
        ((A'.card + B'.card : ℕ) : ℝ) ≤ (2 * L : ℕ) := by
      exact_mod_cast hcard
    calc
      ((A'.card + B'.card : ℕ) : ℝ) * (1 / K) ≤
          ((2 * L : ℕ) : ℝ) * (1 / K) :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 2 * (L : ℝ) / K := by push_cast; ring
      _ < Real.log 2 := hresolution
  apply CRTClose.hasCloseDivisors_of_primeProducts hprime hinj
    (fun i hi ↦ hdiv i (hA'Z hi))
    (fun i hi ↦ hdiv i (hB'Z hi))
    hA'B'
  exact (CRTClose.abs_log_primeProduct_sub_le_of_approx
    hprime (fun i ↦ (label i : ℝ) / K) happrox hsumR).trans_lt hsmall

/-! ## Exact CRT specialization -/

variable [(i : κ) → NeZero (p i)]

/-- The occupied-block theorem specialized to the zero set of the exact CRT
product model.  This is the form consumed by `CRTModel.crt_zeroSet_good_hasDensity`. -/
theorem hasCloseDivisors_of_crtBlockGood
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hK : 0 < K)
    (hblock : ∀ i,
      |Real.log (p i : ℝ) - (label i : ℝ) / K| ≤ 1 / K)
    (hresolution : 2 * (L : ℝ) / K < Real.log 2)
    (hgood : BlockGood label L
      (Erdos697.CRTModel.zeroSet p
        (ZMod.prodEquivPi p
          (CRTClose.primeFamily_pairwise_coprime hprime hinj)
          (n : ZMod (∏ i, p i))))) :
    CRTClose.HasCloseDivisors n := by
  let Z := Erdos697.CRTModel.zeroSet p
    (ZMod.prodEquivPi p
      (CRTClose.primeFamily_pairwise_coprime hprime hinj)
      (n : ZMod (∏ i, p i)))
  apply hasCloseDivisors_of_blockGood hprime hinj
    (Z := Z) (K := K) (L := L)
  · intro i hi
    exact (CRTClose.mem_crtZeroSet_iff_dvd hprime hinj i n).mp hi
  · exact hK
  · intro i _hi
    exact hblock i
  · exact hresolution
  · exact hgood

end

end Erdos144.BlockCRTClose

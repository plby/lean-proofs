/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicBoundaryCount

/-!
# Finite exceptional offsets and the remaining good survivors

Only finite union and image upper bounds are used. A good survivor has
at least one small-cofactor representation outside the lower boundary;
uniqueness of its factorization is unnecessary.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def residualPrimeOffsets (E : Finset ℕ) (U y z : ℕ) : Finset ℕ :=
  E.biUnion fun m ↦ (residualPrimeFiber U y z m).image (fun p ↦ m * p)

def residualBoundaryOffsets (E : Finset ℕ) (U y z H : ℕ) : Finset ℕ :=
  E.biUnion fun m ↦ (residualPrimeFiberBelow U y z m H).image (fun p ↦ m * p)

def sourceResidualBadSet (U y z B M H : ℕ) : Finset ℕ :=
  initialSieveSurvivors U y z ∩ (smoothResidualException U y ∪
    (residualPrimeOffsets (residualEvenCofactors M B) U y z ∪
      residualBoundaryOffsets (residualEvenCofactors 0 M) U y z H))

theorem sourceResidualBadSet_subset (U y z B M H : ℕ) :
    sourceResidualBadSet U y z B M H ⊆ initialSieveSurvivors U y z := Finset.inter_subset_left

theorem card_residualPrimeOffsets_le (E : Finset ℕ) (U y z : ℕ) :
    (residualPrimeOffsets E U y z).card ≤ ∑ m ∈ E, (residualPrimeFiber U y z m).card := by
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum fun m _ ↦ Finset.card_image_le

theorem card_residualBoundaryOffsets_le (E : Finset ℕ) (U y z H : ℕ) :
    (residualBoundaryOffsets E U y z H).card ≤
      ∑ m ∈ E, (residualPrimeFiberBelow U y z m H).card := by
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum fun m _ ↦ Finset.card_image_le

theorem card_sourceResidualBadSet_le (U y z B M H : ℕ) :
    (sourceResidualBadSet U y z B M H).card ≤ (smoothResidualException U y).card +
      (∑ m ∈ residualEvenCofactors M B, (residualPrimeFiber U y z m).card) +
      (∑ m ∈ residualEvenCofactors 0 M, (residualPrimeFiberBelow U y z m H).card) := by
  have hinter := Finset.card_le_card
    (show sourceResidualBadSet U y z B M H ⊆ smoothResidualException U y ∪
      (residualPrimeOffsets (residualEvenCofactors M B) U y z ∪
        residualBoundaryOffsets (residualEvenCofactors 0 M) U y z H) from Finset.inter_subset_right)
  have hu := Finset.card_union_le (smoothResidualException U y)
    (residualPrimeOffsets (residualEvenCofactors M B) U y z ∪
      residualBoundaryOffsets (residualEvenCofactors 0 M) U y z H)
  have hv := Finset.card_union_le (residualPrimeOffsets (residualEvenCofactors M B) U y z)
    (residualBoundaryOffsets (residualEvenCofactors 0 M) U y z H)
  have hl := card_residualPrimeOffsets_le (residualEvenCofactors M B) U y z
  have hb := card_residualBoundaryOffsets_le (residualEvenCofactors 0 M) U y z H
  omega

theorem good_initialSurvivor_small_residual_representation
    {U y z B M H i : ℕ} (hy : 2 ≤ y) (hz : 2 ≤ z) (hU : U = z * B)
    (hi : i ∈ initialSieveSurvivors U y z) (hgood : i ∉ sourceResidualBadSet U y z B M H) :
    ∃ m ∈ residualEvenCofactors 0 M, ∃ p ∈ residualPrimeFiber U y z m, H ≤ p ∧ i = m * p := by
  have hnotSmooth : i ∉ smoothResidualException U y := by
    intro hs
    exact hgood (Finset.mem_inter.mpr ⟨hi, Finset.mem_union.mpr (Or.inl hs)⟩)
  obtain ⟨m, p, hp, hip⟩ := initialSieveSurvivor_exists_residualPrimeFiber hi hnotSmooth
  have hd := mem_residualPrimeFiber.mp hp
  have hiPos : 0 < i := (mem_initialSieveSurvivors.mp hi).1
  have hm : 0 < m := by
    by_contra hn
    have hmzero : m = 0 := by omega
    rw [hmzero, zero_mul] at hip
    omega
  have heven := residualCofactor_even hy hz hi hp hip
  have hmB : m ≤ B := by
    have hmul : m * z ≤ B * z := by
      calc
        _ ≤ m * p := Nat.mul_le_mul_left m hd.2.2.1.le
        _ ≤ U := hd.2.2.2.1
        _ = B * z := by rw [hU, mul_comm]
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hmM : m ≤ M := by
    by_contra hn
    have hmLarge : m ∈ residualEvenCofactors M B := mem_residualEvenCofactors.mpr
      ⟨by omega, hmB, heven⟩
    have hlarge : i ∈ residualPrimeOffsets (residualEvenCofactors M B) U y z :=
      Finset.mem_biUnion.mpr ⟨m, hmLarge, Finset.mem_image.mpr ⟨p, hp, hip.symm⟩⟩
    exact hgood (Finset.mem_inter.mpr ⟨hi, Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inl hlarge)))⟩)
  have hmSmall : m ∈ residualEvenCofactors 0 M := mem_residualEvenCofactors.mpr ⟨hm, hmM, heven⟩
  have hHp : H ≤ p := by
    by_contra hn
    have hbelow : p ∈ residualPrimeFiberBelow U y z m H := Finset.mem_filter.mpr ⟨hp, by omega⟩
    have hboundary : i ∈ residualBoundaryOffsets (residualEvenCofactors 0 M) U y z H :=
      Finset.mem_biUnion.mpr ⟨m, hmSmall, Finset.mem_image.mpr ⟨p, hbelow, hip.symm⟩⟩
    exact hgood (Finset.mem_inter.mpr ⟨hi, Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inr hboundary)))⟩)
  exact ⟨m, hmSmall, p, hp, hHp, hip⟩

theorem card_good_initialSurvivors_le_small_fibres
    {U y z B M H : ℕ} (hy : 2 ≤ y) (hz : 2 ≤ z) (hU : U = z * B) :
    (initialSieveSurvivors U y z \ sourceResidualBadSet U y z B M H).card ≤
      ∑ m ∈ residualEvenCofactors 0 M, (residualPrimeFiber U y z m).card := by
  apply le_trans _ (card_residualPrimeOffsets_le (residualEvenCofactors 0 M) U y z)
  apply Finset.card_le_card
  intro i hi
  have hd := Finset.mem_sdiff.mp hi
  obtain ⟨m, hm, p, hp, _, hip⟩ :=
    good_initialSurvivor_small_residual_representation hy hz hU hd.1 hd.2
  exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_image.mpr ⟨p, hp, hip.symm⟩⟩

end

end Erdos4b

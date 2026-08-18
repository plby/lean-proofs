/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.InitialEstimates
import ErdosProblems.Erdos186.PZ.Reduction.NoDimensionIncrease

/-!
# Initial residue-fibre estimate

This is the initial-box analogue of the recurring residue-fibre estimate.
The normalized input lies in a centered difference-coordinate GAP associated
to the normalized original box.  Applying the quotient-fibre argument to the
first CFP witness bounds its progression with no comparison between ranks.
-/

namespace Erdos186.PZ.Reduction

open scoped BigOperators

noncomputable section

namespace CFP.EnhancedCFPWitness

variable {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)

/-- The reserved subset sums remain in the reserve-fold dilation of a
containing difference-coordinate GAP. -/
theorem reserved_subsetSums_subset_differenceDilate
    (Q : Erdos186.GAP d d)
    (hA : A ⊆ (GAP.differenceCoefficientGAP Q).carrier) :
    Erdos186.GAP.subsetSums W.reserved ⊆
      ((GAP.differenceCoefficientGAP Q).dilate s).carrier := by
  apply GAP.subsetSums_subset_dilate_of_zero_mem
    (GAP.differenceCoefficientGAP Q)
    (GAP.zero_mem_differenceCoefficientGAP Q)
  · exact W.reserved_subset.trans hA
  · exact W.reserved_small

/-- Division by the positive CFP dilation cancels the reserve scale and
leaves a fixed `2 * scaleDen` dilation. -/
theorem divided_subsetSum_difference_mem_controlDilation
    (Q : Erdos186.GAP d d)
    (hA : A ⊆ (GAP.differenceCoefficientGAP Q).carrier)
    (q : LatticePoint d)
    (hq : ∃ x ∈ Erdos186.GAP.subsetSums W.reserved,
      ∃ y ∈ Erdos186.GAP.subsetSums W.reserved,
        ∀ j, x j - y j = (k : ℤ) * q j) :
    q ∈ ((GAP.differenceCoefficientGAP Q).dilate
      (2 * W.scaleDen)).carrier := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hq
  have hxQ := GAP.mem_dilate_differenceCoefficientGAP_iff Q s x |>.mp
    (reserved_subsetSums_subset_differenceDilate W Q hA hx)
  have hyQ := GAP.mem_dilate_differenceCoefficientGAP_iff Q s y |>.mp
    (reserved_subsetSums_subset_differenceDilate W Q hA hy)
  rw [GAP.mem_dilate_differenceCoefficientGAP_iff]
  intro i
  let radius : ℕ := Q.widths i - 1
  have hs : s ≤ W.scaleDen * k := by
    calc
      s = 1 * s := by simp
      _ ≤ W.scaleNum * s :=
        Nat.mul_le_mul_right _ W.scaleNum_pos
      _ ≤ W.scaleDen * k := W.scale_lower
  have hboundNat : 2 * s * radius ≤
      k * (2 * W.scaleDen * radius) := by
    calc
      2 * s * radius ≤ 2 * (W.scaleDen * k) * radius :=
        Nat.mul_le_mul_right radius (Nat.mul_le_mul_left 2 hs)
      _ = k * (2 * W.scaleDen * radius) := by ring
  have hk : (0 : ℤ) < k := by exact_mod_cast W.k_pos
  have hboundZ : ((2 * s * radius : ℕ) : ℤ) ≤
      ((k * (2 * W.scaleDen * radius) : ℕ) : ℤ) := by
    exact_mod_cast hboundNat
  have hupperMul : (k : ℤ) * q i ≤
      (k : ℤ) * (2 * W.scaleDen * radius : ℕ) := by
    rw [← hxy i]
    have hxi := (hxQ i).2
    have hyi := (hyQ i).1
    calc
      x i - y i ≤ ((2 * s * radius : ℕ) : ℤ) := by
        dsimp [radius] at hxi hyi ⊢
        linarith
      _ ≤ ((k * (2 * W.scaleDen * radius) : ℕ) : ℤ) := hboundZ
      _ = (k : ℤ) * (2 * W.scaleDen * radius : ℕ) := by
        push_cast
        ring
  have hlowerMul : (k : ℤ) *
      (-(2 * W.scaleDen * radius : ℕ) : ℤ) ≤ (k : ℤ) * q i := by
    rw [← hxy i]
    have hxi := (hxQ i).1
    have hyi := (hyQ i).2
    calc
      (k : ℤ) * (-(2 * W.scaleDen * radius : ℕ) : ℤ) =
          -((k * (2 * W.scaleDen * radius) : ℕ) : ℤ) := by
        push_cast
        ring
      _ ≤ -((2 * s * radius : ℕ) : ℤ) := neg_le_neg hboundZ
      _ ≤ x i - y i := by
        dsimp [radius] at hxi hyi ⊢
        linarith
  constructor
  · exact le_of_mul_le_mul_left hlowerMul hk
  · exact le_of_mul_le_mul_left hupperMul hk

/-- General residue-fibre volume bound for a witness whose input lies in a
difference-coordinate GAP. -/
theorem noDimensionIncrease_of_subset_differenceGAP
    (Q : Erdos186.GAP d d)
    (hA : A ⊆ (GAP.differenceCoefficientGAP Q).carrier) :
    W.progression.volume ≤
      2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * Q.volume)) := by
  let sums := Erdos186.GAP.subsetSums W.reserved
  let control := ((GAP.differenceCoefficientGAP Q).dilate
    (2 * W.scaleDen)).carrier
  have hcontain : ∀ n : (W.progression.dilate k).Coord,
      (fun j ↦ W.translatePoint j +
        (W.progression.dilate k).coordPoint n j) ∈ sums := by
    intro n
    apply W.covered
    rw [CFP.mem_translate_iff]
    exact ⟨(W.progression.dilate k).coordPoint n,
      (W.progression.dilate k).coordPoint_mem_carrier n, rfl⟩
  have hfiber : W.progression.volume ≤ 2 ^ W.rank * control.card := by
    exact DiscreteJohn.volume_le_pow_two_mul_card_of_translate_containment
      W.progression W.progression_proper W.k_pos W.translatePoint sums control
      hcontain (divided_subsetSum_difference_mem_controlDilation W Q hA)
  calc
    W.progression.volume ≤ 2 ^ W.rank * control.card := hfiber
    _ ≤ 2 ^ W.rank * ((GAP.differenceCoefficientGAP Q).dilate
          (2 * W.scaleDen)).volume :=
      Nat.mul_le_mul_left _ (Erdos186.GAP.card_carrier_le_volume _)
    _ ≤ 2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d *
          (GAP.differenceCoefficientGAP Q).volume) :=
      Nat.mul_le_mul_left _ (Erdos186.GAP.volume_dilate_le _ _)
    _ ≤ 2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * Q.volume)) := by
      exact Nat.mul_le_mul_left _ <| Nat.mul_le_mul_left _ <|
        GAP.differenceCoefficientGAP_volume_le Q

end CFP.EnhancedCFPWitness

/-- The normalized input is contained in the centered coordinate difference
GAP associated to the normalized original box. -/
theorem normalizeSet_subset_initialDifferenceGAP
    {d : ℕ} (B : CFP.IntegerBox d)
    {A : Finset (LatticePoint d)} (hA : A.Nonempty)
    (hAB : A ⊆ B.carrier) :
    normalizeSet B A ⊆
      (GAP.differenceCoefficientGAP
        (CFP.IntegerBox.toGAP (normalizedBox B)
          (normalized_nonempty B (hA.mono hAB)))).carrier := by
  let hB : B.carrier.Nonempty := hA.mono hAB
  let hNB : (normalizedBox B).carrier.Nonempty := normalized_nonempty B hB
  let Q := CFP.IntegerBox.toGAP (normalizedBox B) hNB
  intro y hy
  have hyQ : y ∈ Q.carrier := by
    change y ∈ (CFP.IntegerBox.toGAP (normalizedBox B) hNB).carrier
    rw [CFP.IntegerBox.toGAP_carrier]
    exact normalizeSet_subset_normalized B hAB hy
  obtain ⟨n, hn⟩ := Erdos186.GAP.mem_carrier_iff.mp hyQ
  have hn' : gapCoordLattice Q n = y := by
    funext i
    have hi := congrFun hn i
    change (CFP.IntegerBox.toGAP (normalizedBox B) hNB).coordPoint n i =
      y i at hi
    rw [CFP.IntegerBox.toGAP_coordPoint] at hi
    simpa [normalizedBox, gapCoordLattice] using hi
  have hycoef : y ∈ (gapCoefficientBox Q).carrier := by
    rw [← hn']
    exact gapCoordLattice_mem_coefficientBox Q n
  have hzero : (0 : LatticePoint d) ∈ (gapCoefficientBox Q).carrier := by
    rw [← GAP.coefficientGAP_carrier]
    let n : (GAP.coefficientGAP Q).Coord :=
      fun i ↦ ⟨0, (GAP.coefficientGAP Q).width_pos i⟩
    refine Erdos186.GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
    rw [GAP.coefficientGAP_coordPoint]
    funext i
    simp [gapCoordLattice, n]
  simpa using GAP.sub_mem_differenceCoefficientGAP_of_mem Q hycoef hzero

/-- Initial no-rank-comparison estimate with the original box cardinality
shown explicitly. -/
theorem initial_noDimensionIncrease
    {d s D k loss : ℕ} (B : CFP.IntegerBox d)
    {A : Finset (LatticePoint d)} (hA : A.Nonempty)
    (hAB : A ⊆ B.carrier)
    (W : CFP.EnhancedCFPWitness (normalizeSet B A) s D k loss) :
    W.progression.volume ≤
      2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * B.carrier.card)) := by
  let hB : B.carrier.Nonempty := hA.mono hAB
  let hNB : (normalizedBox B).carrier.Nonempty := normalized_nonempty B hB
  let Q := CFP.IntegerBox.toGAP (normalizedBox B) hNB
  calc
    W.progression.volume ≤ 2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * Q.volume)) :=
      CFP.EnhancedCFPWitness.noDimensionIncrease_of_subset_differenceGAP
        W Q (normalizeSet_subset_initialDifferenceGAP B hA hAB)
    _ = 2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * B.carrier.card)) := by
      have hQvol : Q.volume = B.carrier.card := by
        calc
          Q.volume = (normalizedBox B).carrier.card :=
            CFP.IntegerBox.toGAP_volume (normalizedBox B) hNB
          _ = B.carrier.card := card_normalized B
      exact congrArg (fun n : ℕ ↦ 2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * n))) hQvol

end

end Erdos186.PZ.Reduction

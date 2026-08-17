/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.PartitionRemainders

/-!
# Cardinality bounds for the partition remainders
-/

namespace Erdos95.RemainderBounds

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionCells
open Erdos95.PartitionStep Erdos95.PartitionRemainders
open Erdos95.RichPointCombinatorics Erdos95.GuthStructure
open Erdos95.SurfaceFactors Erdos95.WallFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

theorem card_lowResidualPoints_le_sum
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    (lowResidualPoints L S p c r cellF).card ≤
      ∑ sign ∈ lowSigns L S p c r,
        (residualRichPoints (cellLines L S p sign) (cellF sign) r).card := by
  classical
  exact Finset.card_biUnion_le

/-- The large-richness lemma summed over the high cells. -/
theorem root_pair_mul_card_highCellRichPoints_le
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ) :
    r * (r - 1) * (highCellRichPoints L S p c r).card ≤
      2 * r * ∑ sign ∈ highSigns L S p c r,
        (cellLines L S p sign).card := by
  classical
  calc
    r * (r - 1) * (highCellRichPoints L S p c r).card ≤
        r * (r - 1) * ∑ sign ∈ highSigns L S p c r,
          (signCell S p sign ∩ richPoints (cellLines L S p sign) r).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ ≤ r * (r - 1) * ∑ sign ∈ highSigns L S p c r,
          (richPoints (cellLines L S p sign) r).card := by
      gcongr with sign hsign
      exact (show
        signCell S p sign ∩ richPoints (cellLines L S p sign) r ⊆
          richPoints (cellLines L S p sign) r by
        exact Finset.inter_subset_right)
    _ = ∑ sign ∈ highSigns L S p c r,
          r * (r - 1) *
            (richPoints (cellLines L S p sign) r).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ sign ∈ highSigns L S p c r,
          2 * r * (cellLines L S p sign).card := by
      apply Finset.sum_le_sum
      intro sign hsign
      have hlarge := (mem_highSigns_iff.mp hsign).2
      have hprop := richness_mul_card_le_two_mul_lines
        (cellLines L S p sign) r hlarge
      calc
        r * (r - 1) *
            (richPoints (cellLines L S p sign) r).card =
            (r - 1) *
              (r * (richPoints (cellLines L S p sign) r).card) := by ring
        _ ≤ (r - 1) * (2 * (cellLines L S p sign).card) := by
          gcongr
        _ ≤ r * (2 * (cellLines L S p sign).card) := by gcongr; omega
        _ = 2 * r * (cellLines L S p sign).card := by ring
    _ = 2 * r * ∑ sign ∈ highSigns L S p c r,
        (cellLines L S p sign).card := by rw [Finset.mul_sum]

theorem root_pair_mul_card_highCellRichPoints_le_crossing
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (c r : ℕ) :
    r * (r - 1) * (highCellRichPoints L S p c r).card ≤
      2 * r * (L.card * ((partitionPolynomial p).totalDegree + 1)) := by
  refine (root_pair_mul_card_highCellRichPoints_le L S p c r).trans ?_
  gcongr
  calc
    ∑ sign ∈ highSigns L S p c r, (cellLines L S p sign).card ≤
        ∑ sign : Fin J → Bool, (cellLines L S p sign).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (show highSigns L S p c r ⊆ (Finset.univ : Finset (Fin J → Bool)) by
          exact fun _ _ ↦ Finset.mem_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ L.card * ((partitionPolynomial p).totalDegree + 1) :=
      sum_card_cellLines_le L S p

/-- The wall remainder is controlled by the lines crossing the irreducible
factors of the partition wall. -/
theorem root_pair_mul_card_wallRemainder_le
    (L : Finset LineIndex) (S : Finset Space) {J : ℕ}
    (p : Fin J → Poly3) (r : ℕ) (hr : 2 ≤ r)
    (hp : ∀ j, p j ≠ 0)
    (hSrich : S ⊆ richPoints L r) :
    r * (r - 1) * (wallRemainder L S p r).card ≤
      2 * r * ((partitionPolynomial p).totalDegree * L.card) := by
  classical
  let T := wallRemainder L S p r
  have hQ : partitionPolynomial p ≠ 0 := partitionPolynomial_ne_zero p hp
  have hloss := strict_loss_mul_card_le_wall_degree_mul_lines
    hQ (two_le_reducedRichness r)
    (S := T) (L := L) (r := r) (r' := reducedRichness r)
    (fun x hx ↦ (mem_richPoints_iff.mp
      (hSrich (mem_wallPoints_iff.mp (Finset.mem_sdiff.mp hx).1).1)).2)
    (fun x hx ↦ (Finset.mem_sdiff.mp hx).2)
    (fun x hx ↦ (mem_wallPoints_iff.mp (Finset.mem_sdiff.mp hx).1).2)
  have hrLoss := richness_le_two_mul_loss hr
  calc
    r * (r - 1) * T.card = (r - 1) * (r * T.card) := by ring
    _ ≤ (r - 1) *
        (2 * (r - (reducedRichness r - 1)) * T.card) := by
      gcongr
    _ = 2 * (r - 1) *
        ((r - (reducedRichness r - 1)) * T.card) := by ring
    _ ≤ 2 * (r - 1) *
        ((partitionPolynomial p).totalDegree * L.card) := by gcongr
    _ ≤ 2 * r * ((partitionPolynomial p).totalDegree * L.card) := by
      gcongr
      omega

end Erdos95.RemainderBounds

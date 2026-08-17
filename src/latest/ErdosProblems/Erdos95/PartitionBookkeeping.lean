/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.PartitionStep

/-!
# Cardinality bookkeeping for a partitioning step

The bad cells are those whose entering-line family is too large.  The total
line--cell incidence estimate bounds their number, while bisection bounds
their union by a fixed fraction of the point set.
-/

namespace Erdos95.PartitionBookkeeping

open Erdos95.ES Erdos95.Partitioning Erdos95.CellLines

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Sign cells with at least a `1/c` fraction of all lines, in
denominator-free form. -/
noncomputable def badSigns (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) (c : ℕ) : Finset (Fin J → Bool) := by
  classical
  exact Finset.univ.filter fun sign ↦
    L.card ≤ c * (cellLines L S p sign).card

theorem mem_badSigns_iff {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {c : ℕ} {sign : Fin J → Bool} :
    sign ∈ badSigns L S p c ↔
      L.card ≤ c * (cellLines L S p sign).card := by
  classical
  simp [badSigns]

/-- The points lying in one of the bad strict sign cells. -/
noncomputable def badCellPoints (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) (c : ℕ) : Finset Space3 := by
  classical
  exact (badSigns L S p c).biUnion (signCell S p)

theorem mem_badCellPoints_iff {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {c : ℕ} {x : Space3} :
    x ∈ badCellPoints L S p c ↔
      ∃ sign ∈ badSigns L S p c, x ∈ signCell S p sign := by
  classical
  simp [badCellPoints]

theorem sum_bad_cellLines_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c : ℕ) :
    ∑ sign ∈ badSigns L S p c, (cellLines L S p sign).card ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  calc
    ∑ sign ∈ badSigns L S p c, (cellLines L S p sign).card ≤
        ∑ sign : Fin J → Bool, (cellLines L S p sign).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ L.card * ((partitionPolynomial p).totalDegree + 1) :=
      sum_card_cellLines_le L S p

/-- There are at most `c(deg Q+1)` bad cells. -/
theorem card_badSigns_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c : ℕ) (hL : 0 < L.card) :
    (badSigns L S p c).card ≤
      c * ((partitionPolynomial p).totalDegree + 1) := by
  classical
  have hlower :
      L.card * (badSigns L S p c).card ≤
        c * ∑ sign ∈ badSigns L S p c,
          (cellLines L S p sign).card := by
    calc
      L.card * (badSigns L S p c).card =
          ∑ _sign ∈ badSigns L S p c, L.card := by
        simp [Nat.mul_comm]
      _ ≤ ∑ sign ∈ badSigns L S p c,
          c * (cellLines L S p sign).card := by
        apply Finset.sum_le_sum
        intro sign hsign
        exact mem_badSigns_iff.mp hsign
      _ = c * ∑ sign ∈ badSigns L S p c,
          (cellLines L S p sign).card := by
        rw [Finset.mul_sum]
  have hupper := Nat.mul_le_mul_left c (sum_bad_cellLines_le L S p c)
  have hcombined :
      L.card * (badSigns L S p c).card ≤
        L.card * (c * ((partitionPolynomial p).totalDegree + 1)) := by
    calc
      L.card * (badSigns L S p c).card ≤
          c * ∑ sign ∈ badSigns L S p c,
            (cellLines L S p sign).card := hlower
      _ ≤ c * (L.card * ((partitionPolynomial p).totalDegree + 1)) := hupper
      _ = L.card * (c * ((partitionPolynomial p).totalDegree + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hcombined hL

theorem card_badCellPoints_le_sum
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c : ℕ) :
    (badCellPoints L S p c).card ≤
      ∑ sign ∈ badSigns L S p c, (signCell S p sign).card := by
  classical
  exact Finset.card_biUnion_le

/-- If every strict cell has at most `1/R` of the input points, the union of
bad cells has at most `c(deg Q+1)/R` of them. -/
theorem mul_card_badCellPoints_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c R : ℕ) (hL : 0 < L.card)
    (hcells : ∀ sign : Fin J → Bool,
      R * (signCell S p sign).card ≤ S.card) :
    R * (badCellPoints L S p c).card ≤
      (c * ((partitionPolynomial p).totalDegree + 1)) * S.card := by
  classical
  calc
    R * (badCellPoints L S p c).card ≤
        R * ∑ sign ∈ badSigns L S p c,
          (signCell S p sign).card :=
      Nat.mul_le_mul_left R (card_badCellPoints_le_sum L S p c)
    _ = ∑ sign ∈ badSigns L S p c,
          R * (signCell S p sign).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _sign ∈ badSigns L S p c, S.card := by
      apply Finset.sum_le_sum
      intro sign _hsign
      exact hcells sign
    _ = (badSigns L S p c).card * S.card := by simp
    _ ≤ (c * ((partitionPolynomial p).totalDegree + 1)) * S.card := by
      gcongr
      exact card_badSigns_le L S p c hL

/-- A convenient half-size corollary used in the iteration. -/
theorem two_mul_card_badCellPoints_le
    (L : Finset LineIndex) (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (c R : ℕ) (hL : 0 < L.card)
    (hRpos : 0 < R)
    (hR : 2 * (c * ((partitionPolynomial p).totalDegree + 1)) ≤ R)
    (hcells : ∀ sign : Fin J → Bool,
      R * (signCell S p sign).card ≤ S.card) :
    2 * (badCellPoints L S p c).card ≤ S.card := by
  let A := c * ((partitionPolynomial p).totalDegree + 1)
  have hmain := mul_card_badCellPoints_le L S p c R hL hcells
  by_cases hA : A = 0
  · have hbad : (badCellPoints L S p c).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.le_of_mul_le_mul_left
      · simpa [A, hA] using hmain
      · exact hRpos
    simp [hbad]
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA
    have hscaled :
        A * (2 * (badCellPoints L S p c).card) ≤ A * S.card := by
      calc
        A * (2 * (badCellPoints L S p c).card) =
            (2 * A) * (badCellPoints L S p c).card := by ring
        _ ≤ R * (badCellPoints L S p c).card :=
          Nat.mul_le_mul_right _ hR
        _ ≤ A * S.card := by simpa [A] using hmain
    exact Nat.le_of_mul_le_mul_left hscaled hApos

end Erdos95.PartitionBookkeeping

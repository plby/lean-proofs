/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.SignCells

/-!
# Lines entering strict polynomial sign cells

This file proves the finite line--cell incidence estimate used in the
low-degree partitioning induction.  A line contained in the product wall
enters no strict cell; every other line enters at most `degree + 1` cells.
-/

open scoped BigOperators

namespace Erdos95.CellLines

open Erdos95.Algebraic Erdos95.ES Erdos95.Partitioning Erdos95.SignCells

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- The lines of `L` which pass through a selected point in a strict sign
cell. -/
noncomputable def cellLines (L : Finset LineIndex)
    (S : Finset Space3) {J : ℕ} (p : Fin J → Poly3)
    (sign : Fin J → Bool) : Finset LineIndex := by
  classical
  exact L.filter fun l ↦ ∃ x ∈ signCell S p sign, OnLine l.1 l.2 x

theorem mem_cellLines_iff {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {sign : Fin J → Bool}
    {l : LineIndex} :
    l ∈ cellLines L S p sign ↔
      l ∈ L ∧ ∃ x ∈ signCell S p sign, OnLine l.1 l.2 x := by
  classical
  simp [cellLines]

theorem sign_mem_lineSignPatterns_of_mem_cellLines
    {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {sign : Fin J → Bool}
    {l : LineIndex} (hl : l ∈ cellLines L S p sign) :
    sign ∈ lineSignPatterns p l.1 l.2 := by
  obtain ⟨_hlL, x, hxcell, t, rfl⟩ := mem_cellLines_iff.mp hl
  apply mem_lineSignPatterns_iff.mpr
  refine ⟨t, ?_⟩
  exact (mem_signCell_iff.mp hxcell).2

theorem lineRestriction_partitionPolynomial_ne_zero_of_mem_cellLines
    {L : Finset LineIndex} {S : Finset Space3}
    {J : ℕ} {p : Fin J → Poly3} {sign : Fin J → Bool}
    {l : LineIndex} (hl : l ∈ cellLines L S p sign) :
    lineRestriction (partitionPolynomial p)
      (linePoint l.1 l.2 0) (lineDirection l.1 l.2) ≠ 0 := by
  exact lineRestriction_partitionPolynomial_ne_zero_of_mem_lineSignPatterns
    (sign_mem_lineSignPatterns_of_mem_cellLines hl)

/-- The finite relation of a sign cell and a line entering it. -/
noncomputable def cellLineIncidences (L : Finset LineIndex)
    (S : Finset Space3) {J : ℕ} (p : Fin J → Poly3) :
    Finset (Σ _sign : (Fin J → Bool), LineIndex) := by
  classical
  exact (Finset.univ : Finset (Fin J → Bool)).sigma
    (fun sign ↦ cellLines L S p sign)

/-- The same incidence relation, with the order reversed and enlarged to
all sign patterns realized by each line. -/
noncomputable def realizedLinePatterns (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly3) :
    Finset (Σ _l : LineIndex, (Fin J → Bool)) := by
  classical
  exact L.sigma fun l ↦ lineSignPatterns p l.1 l.2

theorem card_cellLineIncidences_le_realizedLinePatterns
    (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) :
    (cellLineIncidences L S p).card ≤ (realizedLinePatterns L p).card := by
  classical
  let swap : (Σ _sign : (Fin J → Bool), LineIndex) →
      (Σ _l : LineIndex, (Fin J → Bool)) := fun z ↦ ⟨z.2, z.1⟩
  apply Finset.card_le_card_of_injOn swap
  · intro z hz
    rcases z with ⟨sign, l⟩
    change ⟨sign, l⟩ ∈ cellLineIncidences L S p at hz
    rw [cellLineIncidences, Finset.mem_sigma] at hz
    have hz' : l ∈ cellLines L S p sign := hz.2
    change ⟨l, sign⟩ ∈ realizedLinePatterns L p
    simp only [realizedLinePatterns, Finset.mem_sigma]
    exact ⟨(mem_cellLines_iff.mp hz').1,
      sign_mem_lineSignPatterns_of_mem_cellLines hz'⟩
  · intro z hz w hw hzw
    rcases z with ⟨sign, l⟩
    rcases w with ⟨sign', l'⟩
    simp only [swap] at hzw
    injection hzw
    subst l'
    subst sign'
    rfl

theorem card_realizedLinePatterns_le
    (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly3) :
    (realizedLinePatterns L p).card ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  classical
  rw [realizedLinePatterns, Finset.card_sigma]
  calc
    (∑ l ∈ L, (lineSignPatterns p l.1 l.2).card) ≤
        ∑ _l ∈ L, ((partitionPolynomial p).totalDegree + 1) := by
      apply Finset.sum_le_sum
      intro l hl
      by_cases hpat : (lineSignPatterns p l.1 l.2).Nonempty
      · obtain ⟨sign, hsign⟩ := hpat
        exact card_lineSignPatterns_le p l.1 l.2
          (lineRestriction_partitionPolynomial_ne_zero_of_mem_lineSignPatterns
            hsign)
      · simp only [Finset.not_nonempty_iff_eq_empty] at hpat
        rw [hpat]
        simp
    _ = L.card * ((partitionPolynomial p).totalDegree + 1) := by simp

/-- Sum form of the line--cell incidence bound. -/
theorem sum_card_cellLines_le
    (L : Finset LineIndex) (S : Finset Space3)
    {J : ℕ} (p : Fin J → Poly3) :
    (∑ sign : Fin J → Bool, (cellLines L S p sign).card) ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  rw [← Finset.card_sigma]
  change (cellLineIncidences L S p).card ≤ _
  exact (card_cellLineIncidences_le_realizedLinePatterns L S p).trans
    (card_realizedLinePatterns_le L p)

end Erdos95.CellLines

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Defs
import ErdosProblems.Erdos760

/-!
# Erdős Problem 63: finite-to-infinite bridges

This file isolates the compactness and degeneracy part of the solution.  Its only
combinatorial input is `FinitePowerTailTheorem`: a finite graph whose average
degree is sufficiently large contains a cycle of length `2 ^ n` for an exponent
`n` beyond any prescribed lower bound.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The exact infinite-chromatic-number hypothesis for an arbitrary graph. -/
def HasInfiniteChromaticNumber {V : Type u} (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = ⊤

/-- The exponents of powers of two occurring as cycle lengths in `G`. -/
def powerCycleExponents {V : Type u} (G : SimpleGraph V) : Set ℕ :=
  {n | HasCycleLength G (2 ^ n)}

/-- A universe-polymorphic finite high-average-degree input sufficient for Problem 63.

The inequality says that the average degree of `H` is at least `d`, without using
division.  The threshold `d` may depend on the desired lower bound for the
power-of-two exponent, but not on the finite graph. -/
def FinitePowerTailTheorem : Prop :=
  ∀ lower : ℕ, ∃ d : ℕ, 0 < d ∧
    ∀ {W : Type u} [Fintype W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      AvgDegreeAtLeast H d →
        ∃ n : ℕ, lower ≤ n ∧ HasCycleLength H (2 ^ n)

/-- Infinite chromatic number is witnessed by a finite subgraph that is not
`d`-colorable.  This is the de Bruijn--Erdős compactness step. -/
lemma exists_finite_subgraph_not_colorable {V : Type u} (G : SimpleGraph V)
    (hG : HasInfiniteChromaticNumber G) (d : ℕ) :
    ∃ G' : G.Subgraph, G'.verts.Finite ∧ ¬G'.coe.Colorable d := by
  unfold HasInfiniteChromaticNumber at hG
  by_contra! h
  have hcolor : G.Colorable d :=
    nonempty_hom_of_forall_finite_subgraph_hom
      (F := completeGraph (Fin d)) fun G' hG' ↦ (h G' hG').some
  have hle := hcolor.chromaticNumber_le
  rw [hG] at hle
  exact ENat.natCast_ne_top d (top_unique hle)

/-- A finite non-`d`-colorable graph has a nonempty induced subgraph of minimum
degree at least `d`. -/
lemma exists_induced_core {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) (hnotcolor : ¬G.Colorable d) :
    ∃ S : Finset V, S.Nonempty ∧
      ∀ v : (S : Set V), d ≤ (G.induce (S : Set V)).degree v := by
  have hnotdegenerate :
      ¬(∀ S : Finset V, S.Nonempty →
          ∃ v ∈ S, (S.filter fun w ↦ G.Adj v w).card < d) := by
    intro hdegenerate
    exact hnotcolor
      (Erdos760.SimpleGraph.colorable_of_degenerate G d hd hdegenerate)
  push_neg at hnotdegenerate
  obtain ⟨S, hS, hdegree⟩ := hnotdegenerate
  refine ⟨S, hS, ?_⟩
  intro v
  have hv : d ≤ (S.filter fun w ↦ G.Adj v w).card := hdegree v v.property
  calc
    d ≤ (S.filter fun w ↦ G.Adj v w).card := hv
    _ = (G.induce (S : Set V)).degree v := by
      rw [← card_neighborFinset_eq_degree]
      let e : (S : Set V) ↪ V := Function.Embedding.subtype _
      have heq :
          ((G.induce (S : Set V)).neighborFinset v).map e =
            S.filter fun w ↦ G.Adj v w := by
        ext w
        simp [e, and_comm]
      rw [← heq, Finset.card_map]

/-- The minimum-degree core supplied by `exists_induced_core` satisfies the
division-free average-degree inequality used by `FinitePowerTailTheorem`. -/
lemma induced_core_average_degree {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) {d : ℕ}
    (hdegree : ∀ v : (S : Set V), d ≤ (G.induce (S : Set V)).degree v) :
    AvgDegreeAtLeast (G.induce (S : Set V)) d := by
  simpa [AvgDegreeAtLeast, Nat.mul_comm] using
    (Finset.sum_le_sum fun v (_hv : v ∈ (Finset.univ : Finset (S : Set V))) ↦ hdegree v)

/-- Conditional downstream bridge: the finite high-average-degree power-tail
theorem implies that every infinite-chromatic graph has power-of-two cycle
exponents above every prescribed bound. -/
theorem unbounded_powerCycleExponents_of_finitePowerTail {V : Type u}
    (hfinite : FinitePowerTailTheorem.{u}) (G : SimpleGraph V)
    (hG : HasInfiniteChromaticNumber G) :
    ∀ lower : ℕ, ∃ n : ℕ, lower ≤ n ∧ n ∈ powerCycleExponents G := by
  intro lower
  obtain ⟨d, hd, htail⟩ := hfinite lower
  obtain ⟨G', hG'finite, hG'color⟩ := exists_finite_subgraph_not_colorable G hG d
  let : Fintype G'.verts := hG'finite.fintype
  let : DecidableRel G'.coe.Adj := Classical.decRel G'.coe.Adj
  obtain ⟨S, hS, hdegree⟩ := exists_induced_core G'.coe hd hG'color
  let : Nonempty (S : Set G'.verts) := hS.to_subtype
  let H := G'.coe.induce (S : Set G'.verts)
  have havg : AvgDegreeAtLeast H d :=
    induced_core_average_degree G'.coe S hdegree
  obtain ⟨n, hn, hncycle⟩ := htail H havg
  refine ⟨n, hn, ?_⟩
  change HasCycleLength G (2 ^ n)
  have hlength : 2 < 2 ^ n := by
    have hthree := hncycle.three_le
    omega
  have hcopyH : cycleGraph (2 ^ n) ⊑ H :=
    (hasCycleLength_iff_cycleGraph_isContained hlength).mp hncycle
  have hcopyG : cycleGraph (2 ^ n) ⊑ G :=
    (hcopyH.trans ⟨Copy.induce G'.coe (S : Set G'.verts)⟩).trans G'.coe_isContained
  exact (hasCycleLength_iff_cycleGraph_isContained hlength).mpr hcopyG

/-- Hence the set of exponents is infinite, which is the quantifier appearing
in Erdős Problem 63. -/
theorem infinite_powerCycleExponents_of_finitePowerTail {V : Type u}
    (hfinite : FinitePowerTailTheorem.{u}) (G : SimpleGraph V)
    (hG : HasInfiniteChromaticNumber G) :
    (powerCycleExponents G).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro lower
  obtain ⟨n, hn, hnmem⟩ :=
    unbounded_powerCycleExponents_of_finitePowerTail hfinite G hG (lower + 1)
  exact ⟨n, hnmem, by omega⟩

end

end Erdos63

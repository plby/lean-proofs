/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos767.RelativeLowDegree
import ErdosProblems.Erdos767.ErdosGallai

/-!
# Dirac's circumference theorem and the Erdős--Gallai edge bound

This is the public entry point for the graph-theoretic engine used in the
formalization of Erdős Problem 767.  The proof above it formalizes the
best-lollipop/aligned-fan argument, including both terminal-neighbor cases.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos767Dirac

open SimpleGraph
open Erdos767Scratch

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The geometric principle consumed by the Erdős--Gallai induction,
derived from the best-lollipop relative low-degree theorem. -/
theorem diracCircumferencePrinciple :
    E767EGConditional.DiracCircumferencePrinciple.{u} := by
  intro W _ _ H _ c hc hcard hpre hdelete hcycle
  have hcard3 : 3 ≤ Fintype.card W := by omega
  let : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hconn : H.Connected := ⟨hpre⟩
  have hdelconn : ∀ w : W, (H.induce ({w}ᶜ : Set W)).Connected := by
    intro w
    let : Nonempty ({w}ᶜ : Set W) := Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set, Set.card_singleton]
      omega)
    exact ⟨hdelete w⟩
  have hTwo : Erdos58.TwoConnected H := ⟨hcard3, hconn, hdelconn⟩
  obtain ⟨B⟩ := BestLollipop.exists_bestLollipop hTwo
  have hcyclelen : B.cycle.length ≤ c :=
    hcycle B.cycleBase B.cycle B.cycle_isCycle
  have hnotspan : B.cycle.support.toFinset ≠ (Finset.univ : Finset W) := by
    intro hspan
    have hcarrier :=
      Erdos767LongestCycle.cycleCarrier_card B.cycle_isCycle
    rw [hspan, Finset.card_univ] at hcarrier
    omega
  have hpos := B.tail_length_pos_of_cycle_not_spanning hTwo hnotspan
  refine ⟨B.terminal, ?_⟩
  exact (B.relative_low_degree hTwo hpos).trans hcyclelen

/-- Erdős--Gallai's sharp edge bound for graphs of bounded circumference. -/
theorem erdosGallai_cycle
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ)
    (hc : 2 ≤ c) (hcycle : E767EGConditional.CycleLengthAtMost G c) :
    2 * G.edgeFinset.card ≤ c * (Fintype.card V - 1) :=
  E767EGConditional.erdosGallai_cycle_conditional
    diracCircumferencePrinciple G c hc hcycle

/-- A nonspanning longest cycle in a two-connected graph can be replaced by
a (possibly different) longest cycle with an exterior vertex whose doubled
degree is at most the common longest-cycle length. -/
theorem exists_nonspanning_longestCycle_lowDegree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTwo : Erdos58.TwoConnected G)
    {z : V} {q : G.Walk z z}
    (hq : Erdos767LongestCycle.IsLongestCycle q)
    (hqlt : q.length < Fintype.card V) :
    ∃ (w : V) (r : G.Walk w w) (v : V),
      Erdos767LongestCycle.IsLongestCycle r ∧
        v ∉ r.support ∧ 2 * G.degree v ≤ r.length := by
  obtain ⟨B⟩ := BestLollipop.exists_bestLollipop hTwo
  have hlen : B.cycle.length = q.length := by
    apply Nat.le_antisymm
    · exact hq.2 B.cycle B.cycle_isCycle
    · exact B.cycle_maximal q hq.1
  have hnotspan : B.cycle.support.toFinset ≠ (Finset.univ : Finset V) := by
    intro hspan
    have hcarrier :=
      Erdos767LongestCycle.cycleCarrier_card B.cycle_isCycle
    rw [hspan, Finset.card_univ] at hcarrier
    omega
  have hpos := B.tail_length_pos_of_cycle_not_spanning hTwo hnotspan
  refine ⟨B.cycleBase, B.cycle, B.terminal, B.isLongestCycle, ?_,
    B.relative_low_degree hTwo hpos⟩
  exact B.toLollipop.terminal_not_mem_cycle hpos

/-- Dirac's circumference theorem in minimum-degree form. -/
theorem exists_cycle_length_ge_min_card_two_mul
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hTwo : Erdos58.TwoConnected G) (k : ℕ)
    (hdegree : ∀ v : V, k ≤ G.degree v) :
    ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧
      min (Fintype.card V) (2 * k) ≤ C.length :=
  Erdos767Scratch.exists_cycle_length_ge_min_card_two_mul hTwo k hdegree

#print axioms diracCircumferencePrinciple
#print axioms erdosGallai_cycle
#print axioms exists_nonspanning_longestCycle_lowDegree
#print axioms exists_cycle_length_ge_min_card_two_mul

end

end Erdos767Dirac

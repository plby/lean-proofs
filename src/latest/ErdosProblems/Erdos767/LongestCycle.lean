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
import Mathlib
import ErdosProblems.Erdos58.Menger

/-!
# Finite longest paths and cycles for Erdős Problem 767

This file contains the small, self-contained maximum-path and maximum-cycle
interface used by the proof of Erdős Problem 767.  Keeping it local prevents
the formalization from depending on another Erdős-problem development.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos767LongestCycle

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path of maximum length among all paths in the graph. -/
def IsLongestPath {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧
    ∀ ⦃u v : V⦄ (q : G.Walk u v), q.IsPath → q.length ≤ p.length

/-- Every nonempty finite graph has a longest path. -/
theorem exists_isLongestPath [Nonempty V] :
    ∃ (a b : V) (p : G.Walk a b), IsLongestPath p := by
  obtain ⟨a, b, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  exact ⟨a, b, p, hp, fun {_ _} q hq ↦ hmax _ _ q hq⟩

/-- Every neighbor of the terminal endpoint of a longest path already lies
on the path. -/
theorem IsLongestPath.end_neighbor_mem_support {a b z : V}
    {p : G.Walk a b} (hp : IsLongestPath p) (hbz : G.Adj b z) :
    z ∈ p.support := by
  by_contra hz
  have hlonger : (p.concat hbz).IsPath := hp.1.concat hz hbz
  have hle := hp.2 (p.concat hbz) hlonger
  simp at hle

/-- The terminal neighbor set of a longest path lies in its support with the
terminal endpoint removed. -/
theorem IsLongestPath.neighborFinset_end_subset_erase {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.neighborFinset b ⊆ p.support.toFinset.erase b := by
  intro z hz
  have hbz : G.Adj b z := (G.mem_neighborFinset b z).mp hz
  exact Finset.mem_erase.mpr
    ⟨hbz.ne.symm, List.mem_toFinset.mpr (hp.end_neighbor_mem_support hbz)⟩

/-- The degree of the terminal endpoint is at most the length of a longest
path. -/
theorem IsLongestPath.degree_end_le_length {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.degree b ≤ p.length := by
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset b).card ≤ (p.support.toFinset.erase b).card :=
      Finset.card_le_card hp.neighborFinset_end_subset_erase
    _ = p.length := by
      rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr p.end_mem_support)]
      rw [List.toFinset_card_of_nodup hp.1.support_nodup, p.length_support]
      omega

/-- A genuine cycle of maximum length. -/
def IsLongestCycle {z : V} (c : G.Walk z z) : Prop :=
  c.IsCycle ∧
    ∀ ⦃z' : V⦄ (c' : G.Walk z' z'), c'.IsCycle → c'.length ≤ c.length

/-- The length of a simple cycle is at most the order of the graph. -/
lemma isCycle_length_le_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hsub : c.support.tail.toFinset ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ] at hcard
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]
    omega
  simpa [hlen] using hcard

/-- The finite set of lengths of genuine cycles in `G`. -/
def cycleLengths (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun m ↦
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = m

lemma mem_cycleLengths_iff {m : ℕ} :
    m ∈ cycleLengths G ↔
      ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = m := by
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · rintro ⟨z, c, hc, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (isCycle_length_le_card hc)),
      ⟨z, c, hc, rfl⟩⟩

/-- A finite two-connected graph has a longest cycle. -/
theorem exists_isLongestCycle (hTwo : Erdos58.TwoConnected G) :
    ∃ (z : V) (c : G.Walk z z), IsLongestCycle c := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by
    have := hTwo.card_three_le
    omega)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hyx⟩ := hTwo.exists_ne x
  obtain ⟨p, hp⟩ := hTwo.connected.exists_isPath x y
  have hpnon : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hyx.symm
  have hxp : G.Adj x p.snd := p.adj_snd hpnon
  obtain ⟨c₀, hc₀, -⟩ := hTwo.exists_cycle_through_edge hxp
  have hnonempty : (cycleLengths G).Nonempty := by
    exact ⟨c₀.length, mem_cycleLengths_iff.mpr ⟨x, c₀, hc₀, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image (cycleLengths G) id hnonempty
  obtain ⟨z, c, hc, hcm⟩ := mem_cycleLengths_iff.mp hm
  subst m
  refine ⟨z, c, hc, ?_⟩
  intro z' c' hc'
  have hc'mem := mem_cycleLengths_iff.mpr ⟨z', c', hc', rfl⟩
  simpa using hmax c'.length hc'mem

/-- The finite carrier of a genuine cycle has cardinality equal to its
length: the base vertex is the sole repetition in the closed support. -/
lemma cycleCarrier_card {z : V} {c : G.Walk z z} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hz : z ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  rw [← c.cons_tail_support, List.toFinset_cons, Finset.insert_eq_of_mem
    (List.mem_toFinset.mpr hz), List.toFinset_card_of_nodup hc.support_nodup]
  rw [List.length_tail, c.length_support]
  omega

/-- A cycle lifted to the graph induced on its carrier is Hamiltonian. -/
lemma induced_cycle_isHamiltonianCycle {z : V} {c : G.Walk z z}
    (hc : c.IsCycle) :
    let C := c.support.toFinset
    let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
      List.mem_toFinset.mpr hx
    (c.induce (C : Set V) hC).IsHamiltonianCycle := by
  dsimp only
  let C := c.support.toFinset
  let hC : ∀ x ∈ c.support, x ∈ (C : Set V) := fun x hx ↦
    List.mem_toFinset.mpr hx
  let q := c.induce (C : Set V) hC
  have hmap : q.map
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom = c := by
    change (c.induce (C : Set V) hC).map
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom = c
    exact SimpleGraph.Walk.map_induce c hC
  have hqcycle : q.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (p := q)
      (f := (SimpleGraph.Embedding.induce (G := G) (C : Set V)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (C : Set V)).injective).mp
    rw [hmap]
    exact hc
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hqcycle, ?_⟩
  have hcardC : Fintype.card (C : Set V) = c.length := by
    exact (Fintype.card_coe C).trans (cycleCarrier_card hc)
  change q.length = Fintype.card (C : Set V)
  rw [hcardC]
  have hlength := congrArg SimpleGraph.Walk.length hmap
  rw [SimpleGraph.Walk.length_map] at hlength
  exact hlength

end

end Erdos767LongestCycle

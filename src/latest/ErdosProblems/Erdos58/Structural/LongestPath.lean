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
import ErdosProblems.Erdos58.Independent
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
# A longest path outside a designated odd cycle

This file packages the elementary longest-path step in Gyárfás's proof.
For a designated `LongestOddCycle C`, its exterior is the complement of
`C.carrier`.  Provided that exterior is nonempty, the finite induced graph
has a simple path of maximum possible length.  At either endpoint, every
neighbor which is still in the exterior must already occur on the path:
otherwise one can add that neighbor and obtain a longer simple path.

The certificate below deliberately stores a walk in the *induced* graph.
Consequently avoidance of the designated cycle is true by construction,
rather than being an extra hypothesis carried by every later use.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The graph induced by the vertices outside a designated longest odd
cycle. -/
abbrev exteriorGraph (C : LongestOddCycle G) : SimpleGraph ↑(C.carrierᶜ) :=
  G.induce C.carrierᶜ

/-- A globally longest simple path in the graph induced outside `C`.

`maximal` compares against paths with arbitrary endpoints, not merely paths
having the same endpoints as `path`.  This is the form needed for the
endpoint-extension argument. -/
structure LongestExteriorPath (C : LongestOddCycle G) where
  first : ↑(C.carrierᶜ)
  last : ↑(C.carrierᶜ)
  path : (exteriorGraph C).Walk first last
  isPath : path.IsPath
  maximal : ∀ {x y : ↑(C.carrierᶜ)} (q : (exteriorGraph C).Walk x y),
    q.IsPath → q.length ≤ path.length

namespace LongestExteriorPath

variable {C : LongestOddCycle G}

/-- The inclusion of the exterior induced graph into the ambient graph. -/
abbrev exteriorEmbedding (C : LongestOddCycle G) : exteriorGraph C ↪g G :=
  SimpleGraph.Embedding.induce C.carrierᶜ

/-- The selected exterior path, regarded as an ambient walk. -/
def ambientPath (P : LongestExteriorPath C) :=
  P.path.map (SimpleGraph.Embedding.induce (G := G) C.carrierᶜ).toHom

@[simp] lemma ambientPath_length (P : LongestExteriorPath C) :
    P.ambientPath.length = P.path.length := by
  rcases P with ⟨first, last, path, isPath, maximal⟩
  simpa only [ambientPath] using
    (SimpleGraph.Walk.length_map
      (SimpleGraph.Embedding.induce (G := G) C.carrierᶜ).toHom path)

lemma ambientPath_isPath (P : LongestExteriorPath C) :
    P.ambientPath.IsPath := by
  exact P.isPath.map (SimpleGraph.Embedding.induce (G := G) C.carrierᶜ).injective

@[simp] lemma ambientPath_support (P : LongestExteriorPath C) :
    P.ambientPath.support = P.path.support.map ((↑) : ↑(C.carrierᶜ) → V) := by
  rcases P with ⟨first, last, path, isPath, maximal⟩
  rw [ambientPath, SimpleGraph.Walk.support_map]
  apply List.map_congr_left
  intro x _hx
  rfl

/-- Every vertex used by the ambient form of the path is outside the
designated cycle. -/
lemma ambientPath_avoids_cycle (P : LongestExteriorPath C) {v : V}
    (hv : v ∈ P.ambientPath.support) : v ∉ C.carrier := by
  rw [P.ambientPath_support, List.mem_map] at hv
  obtain ⟨w, _hw, rfl⟩ := hv
  exact w.property

/-- A vertex of the exterior adjacent to the first endpoint already occurs
on the selected path. -/
lemma first_neighbor_mem_support (P : LongestExteriorPath C)
    {w : ↑(C.carrierᶜ)} (hw : (exteriorGraph C).Adj P.first w) :
    w ∈ P.path.support := by
  by_contra hmem
  have hlonger : (P.path.cons hw.symm).IsPath := P.isPath.cons hmem
  have hle := P.maximal (P.path.cons hw.symm) hlonger
  simp at hle

/-- A vertex of the exterior adjacent to the last endpoint already occurs on
the selected path. -/
lemma last_neighbor_mem_support (P : LongestExteriorPath C)
    {w : ↑(C.carrierᶜ)} (hw : (exteriorGraph C).Adj P.last w) :
    w ∈ P.path.support := by
  by_contra hmem
  have hlonger : (P.path.concat hw).IsPath := P.isPath.concat hmem hw
  have hle := P.maximal (P.path.concat hw) hlonger
  simp at hle

/-- Neighbor-set form of `first_neighbor_mem_support`. -/
lemma first_neighborSet_subset_support (P : LongestExteriorPath C) :
    (exteriorGraph C).neighborSet P.first ⊆ {w | w ∈ P.path.support} := by
  intro w hw
  exact P.first_neighbor_mem_support hw

/-- Neighbor-set form of `last_neighbor_mem_support`. -/
lemma last_neighborSet_subset_support (P : LongestExteriorPath C) :
    (exteriorGraph C).neighborSet P.last ⊆ {w | w ∈ P.path.support} := by
  intro w hw
  exact P.last_neighbor_mem_support hw

/-- Ambient form of the first-endpoint maximality fact. -/
lemma first_exterior_neighbor_mem_ambient_support (P : LongestExteriorPath C)
    {w : V} (hwout : w ∈ C.carrierᶜ) (hw : G.Adj (P.first : V) w) :
    w ∈ P.ambientPath.support := by
  let w' : ↑(C.carrierᶜ) := ⟨w, hwout⟩
  have hmem : w' ∈ P.path.support :=
    P.first_neighbor_mem_support (SimpleGraph.induce_adj.2 hw)
  rw [P.ambientPath_support, List.mem_map]
  exact ⟨w', hmem, rfl⟩

/-- Ambient form of the last-endpoint maximality fact. -/
lemma last_exterior_neighbor_mem_ambient_support (P : LongestExteriorPath C)
    {w : V} (hwout : w ∈ C.carrierᶜ) (hw : G.Adj (P.last : V) w) :
    w ∈ P.ambientPath.support := by
  let w' : ↑(C.carrierᶜ) := ⟨w, hwout⟩
  have hmem : w' ∈ P.path.support :=
    P.last_neighbor_mem_support (SimpleGraph.induce_adj.2 hw)
  rw [P.ambientPath_support, List.mem_map]
  exact ⟨w', hmem, rfl⟩

/-- The two ambient endpoint-neighbor facts in a single reusable statement. -/
lemma endpoint_exterior_neighbors_mem_ambient_support
    (P : LongestExteriorPath C) {w : V} (hwout : w ∈ C.carrierᶜ) :
    (G.Adj (P.first : V) w → w ∈ P.ambientPath.support) ∧
      (G.Adj (P.last : V) w → w ∈ P.ambientPath.support) := by
  exact ⟨P.first_exterior_neighbor_mem_ambient_support hwout,
    P.last_exterior_neighbor_mem_ambient_support hwout⟩

/-- The exterior neighbors of the first endpoint, as an ambient finset. -/
def firstExteriorNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) : Finset V :=
  by
    classical
    exact (G.neighborFinset (P.first : V)).filter fun w ↦ w ∈ C.carrierᶜ

/-- The cycle neighbors of the first endpoint, as an ambient finset. -/
def firstCycleNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) : Finset V :=
  by
    classical
    exact (G.neighborFinset (P.first : V)).filter fun w ↦ w ∈ C.carrier

/-- The exterior neighbors of the last endpoint, as an ambient finset. -/
def lastExteriorNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) : Finset V :=
  by
    classical
    exact (G.neighborFinset (P.last : V)).filter fun w ↦ w ∈ C.carrierᶜ

/-- The cycle neighbors of the last endpoint, as an ambient finset. -/
def lastCycleNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) : Finset V :=
  by
    classical
    exact (G.neighborFinset (P.last : V)).filter fun w ↦ w ∈ C.carrier

@[simp] lemma mem_firstExteriorNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) (w : V) :
    w ∈ P.firstExteriorNeighbors ↔
      G.Adj (P.first : V) w ∧ w ∈ C.carrierᶜ := by
  simp [firstExteriorNeighbors]

@[simp] lemma mem_firstCycleNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) (w : V) :
    w ∈ P.firstCycleNeighbors ↔
      G.Adj (P.first : V) w ∧ w ∈ C.carrier := by
  simp [firstCycleNeighbors]

@[simp] lemma mem_lastExteriorNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) (w : V) :
    w ∈ P.lastExteriorNeighbors ↔
      G.Adj (P.last : V) w ∧ w ∈ C.carrierᶜ := by
  simp [lastExteriorNeighbors]

@[simp] lemma mem_lastCycleNeighbors [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) (w : V) :
    w ∈ P.lastCycleNeighbors ↔
      G.Adj (P.last : V) w ∧ w ∈ C.carrier := by
  simp [lastCycleNeighbors]

/-- The ambient degree of the first endpoint splits into cycle and exterior
neighbors. -/
lemma card_firstCycleNeighbors_add_card_firstExteriorNeighbors
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (P : LongestExteriorPath C) :
    P.firstCycleNeighbors.card + P.firstExteriorNeighbors.card =
      G.degree (P.first : V) := by
  rw [← G.card_neighborFinset_eq_degree]
  classical
  rw [firstCycleNeighbors, firstExteriorNeighbors]
  simpa [Finset.filter_filter, and_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset (P.first : V))
      (fun w ↦ w ∈ C.carrier))

/-- The analogous degree split at the last endpoint. -/
lemma card_lastCycleNeighbors_add_card_lastExteriorNeighbors
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (P : LongestExteriorPath C) :
    P.lastCycleNeighbors.card + P.lastExteriorNeighbors.card =
      G.degree (P.last : V) := by
  rw [← G.card_neighborFinset_eq_degree]
  classical
  rw [lastCycleNeighbors, lastExteriorNeighbors]
  simpa [Finset.filter_filter, and_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset (P.last : V))
      (fun w ↦ w ∈ C.carrier))

/-- Every exterior neighbor of the first endpoint occurs on the ambient
path. -/
lemma firstExteriorNeighbors_subset_support [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) :
    ↑P.firstExteriorNeighbors ⊆ {w : V | w ∈ P.ambientPath.support} := by
  intro w hw
  have hw' : w ∈ P.firstExteriorNeighbors := hw
  rw [P.mem_firstExteriorNeighbors] at hw'
  exact P.first_exterior_neighbor_mem_ambient_support hw'.2 hw'.1

/-- Every exterior neighbor of the last endpoint occurs on the ambient
path. -/
lemma lastExteriorNeighbors_subset_support [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (P : LongestExteriorPath C) :
    ↑P.lastExteriorNeighbors ⊆ {w : V | w ∈ P.ambientPath.support} := by
  intro w hw
  have hw' : w ∈ P.lastExteriorNeighbors := hw
  rw [P.mem_lastExteriorNeighbors] at hw'
  exact P.last_exterior_neighbor_mem_ambient_support hw'.2 hw'.1

/-- A longest exterior path exists whenever the exterior is nonempty. -/
theorem exists_of_exterior_nonempty [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hE : C.carrierᶜ.Nonempty) :
    Nonempty (LongestExteriorPath C) := by
  let x : ↑(C.carrierᶜ) := ⟨hE.choose, hE.choose_spec⟩
  let : Nonempty ↑(C.carrierᶜ) := ⟨x⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length (exteriorGraph C)
  exact ⟨⟨u, v, p, hp, fun q hq ↦ hmax _ _ q hq⟩⟩

/-- If the exterior is not independent, a longest exterior path exists and
has at least one edge. -/
theorem exists_positive_of_not_independent [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hE : ¬ G.IsIndepSet C.carrierᶜ) :
    ∃ P : LongestExteriorPath C, 0 < P.path.length := by
  classical
  have hnonempty : C.carrierᶜ.Nonempty := by
    by_contra hempty
    apply hE
    intro x hx
    exact (hempty ⟨x, hx⟩).elim
  obtain ⟨P⟩ := exists_of_exterior_nonempty (C := C) hnonempty
  have hadj : ∃ x y : ↑(C.carrierᶜ), (exteriorGraph C).Adj x y := by
    by_contra h
    apply hE
    intro x hx y hy _hxy hadj
    exact h ⟨⟨x, hx⟩, ⟨y, hy⟩, SimpleGraph.induce_adj.2 hadj⟩
  obtain ⟨x, y, hxy⟩ := hadj
  have hone : hxy.toWalk.length ≤ P.path.length :=
    P.maximal hxy.toWalk hxy.isPath_toWalk
  have hpos : 0 < P.path.length := by
    have hone' : 1 ≤ P.path.length := by simpa using hone
    omega
  exact ⟨P, hpos⟩

lemma first_ne_last_of_path_positive (P : LongestExteriorPath C)
    (hpos : 0 < P.path.length) : P.first ≠ P.last := by
  intro h
  have hnil : P.path.Nil := P.isPath.nil_iff_eq.mpr h
  have hzero : P.path.length = 0 := hnil.length_eq_zero
  omega

end LongestExteriorPath

end

end Erdos58.Structural

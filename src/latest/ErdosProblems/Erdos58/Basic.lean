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
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Order.Interval.Set.Nat

/-!
# Erdős Problem 58: cycle-length infrastructure

This file records the elementary interface between odd cycle lengths, cycles
represented by closed walks, and copies of cycle graphs.  It also supplies the
finite-cardinality facts and the exact calculation for complete graphs that
are used in the resolution of Erdős Problem 58.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

noncomputable section

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

/-- The set of odd lengths of (simple) cycles in `G`.

A cycle is represented in Mathlib by a nonempty closed walk whose edges and
all vertices apart from the repeated endpoint are distinct. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  {n | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

@[simp] lemma mem_oddCycleLengths {n : ℕ} :
    n ∈ oddCycleLengths G ↔
      Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n :=
  Iff.rfl

lemma odd_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : Odd n :=
  hn.1

lemma three_le_of_mem_oddCycleLengths {n : ℕ} (hn : n ∈ oddCycleLengths G) : 3 ≤ n := by
  obtain ⟨_, v, p, hp, rfl⟩ := hn
  exact hp.three_le_length

/-- A number is an odd cycle length precisely when it is odd, is at least
three, and its cycle graph occurs as a (not necessarily induced) copy. -/
lemma mem_oddCycleLengths_iff_odd_and_two_lt_and_cycleGraph_isContained {n : ℕ} :
    n ∈ oddCycleLengths G ↔
      Odd n ∧ 2 < n ∧ SimpleGraph.cycleGraph n ⊑ G := by
  constructor
  · rintro ⟨hn, v, p, hp, rfl⟩
    exact ⟨hn, hp.three_le_length,
      (SimpleGraph.cycleGraph_isContained_iff hp.three_le_length).2 ⟨v, p, hp, rfl⟩⟩
  · rintro ⟨hn, hn3, hcopy⟩
    obtain ⟨v, p, hp, hlen⟩ :=
      (SimpleGraph.cycleGraph_isContained_iff hn3).1 hcopy
    exact ⟨hn, v, p, hp, hlen⟩

lemma mem_oddCycleLengths_iff_cycleGraph_isContained {n : ℕ}
    (hn : 3 ≤ n) :
    n ∈ oddCycleLengths G ↔ Odd n ∧ SimpleGraph.cycleGraph n ⊑ G := by
  rw [mem_oddCycleLengths_iff_odd_and_two_lt_and_cycleGraph_isContained]
  constructor
  · rintro ⟨hodd, -, hcopy⟩
    exact ⟨hodd, hcopy⟩
  · rintro ⟨hodd, hcopy⟩
    exact ⟨hodd, by omega, hcopy⟩

alias mem_oddCycleLengths_iff_cycleGraph_isContained_of_three_le :=
  mem_oddCycleLengths_iff_cycleGraph_isContained

/-- Injective graph homomorphisms preserve every odd cycle length.  The
injectivity assumption is necessary: an arbitrary graph homomorphism can
identify nonadjacent vertices of a cycle. -/
lemma oddCycleLengths_mono_hom (f : G →g H) (hf : Function.Injective f) :
    oddCycleLengths G ⊆ oddCycleLengths H := by
  rintro n ⟨hn, v, p, hp, rfl⟩
  exact ⟨hn, f v, p.map f, hp.map hf, by simp⟩

/-- Copies of graphs preserve every odd cycle length. -/
lemma oddCycleLengths_mono_copy (f : SimpleGraph.Copy G H) :
    oddCycleLengths G ⊆ oddCycleLengths H :=
  oddCycleLengths_mono_hom f.toHom f.injective

/-- Graph containment preserves every odd cycle length. -/
lemma oddCycleLengths_mono_isContained (h : G ⊑ H) :
    oddCycleLengths G ⊆ oddCycleLengths H :=
  oddCycleLengths_mono_copy h.some

/-- Passing to a supergraph on the same vertex type cannot destroy an odd
cycle length. -/
lemma oddCycleLengths_mono (h : G ≤ G') :
    oddCycleLengths G ⊆ oddCycleLengths G' := by
  rintro n ⟨hn, v, p, hp, rfl⟩
  exact ⟨hn, v, p.mapLe h, hp.mapLe h, p.length_mapLe h⟩

/-- Every odd cycle in an induced graph is an odd cycle in the ambient graph. -/
lemma oddCycleLengths_induce_subset (G : SimpleGraph V) (s : Set V) :
    oddCycleLengths (G.induce s) ⊆ oddCycleLengths G :=
  oddCycleLengths_mono_hom (SimpleGraph.Embedding.induce (G := G) s).toHom
    (SimpleGraph.Embedding.induce (G := G) s).injective

/-- The coercion of a subgraph cannot have an odd cycle length absent from
the ambient graph. -/
lemma oddCycleLengths_subgraph_subset (G' : G.Subgraph) :
    oddCycleLengths G'.coe ⊆ oddCycleLengths G :=
  oddCycleLengths_mono_isContained G'.coe_isContained

/-- A cycle in a finite graph has at most as many edges as the graph has
vertices. -/
lemma length_le_natCard_of_isCycle [Finite V] {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) : p.length ≤ Nat.card V := by
  let _ := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  have h := hp.support_nodup.length_le_card
  rw [List.length_tail, p.length_support] at h
  omega

lemma mem_oddCycleLengths_le_natCard [Finite V] {n : ℕ}
    (hn : n ∈ oddCycleLengths G) : n ≤ Nat.card V := by
  obtain ⟨_, v, p, hp, rfl⟩ := hn
  exact length_le_natCard_of_isCycle hp

/-- A finite graph has only finitely many odd cycle lengths. -/
lemma oddCycleLengths_finite [Finite V] (G : SimpleGraph V) :
    (oddCycleLengths G).Finite :=
  (Set.finite_le_nat (Nat.card V)).subset fun _ hn ↦
    mem_oddCycleLengths_le_natCard hn

/-- Odd-cycle-length cardinality is monotone under injective graph
homomorphisms into a finite graph. -/
lemma ncard_oddCycleLengths_mono_hom [Finite W] (f : G →g H)
    (hf : Function.Injective f) :
    (oddCycleLengths G).ncard ≤ (oddCycleLengths H).ncard :=
  Set.ncard_le_ncard (oddCycleLengths_mono_hom f hf) (oddCycleLengths_finite H)

lemma ncard_oddCycleLengths_mono_isContained [Finite W] (h : G ⊑ H) :
    (oddCycleLengths G).ncard ≤ (oddCycleLengths H).ncard :=
  Set.ncard_le_ncard (oddCycleLengths_mono_isContained h) (oddCycleLengths_finite H)

lemma ncard_oddCycleLengths_induce_le [Finite V] (G : SimpleGraph V) (s : Set V) :
    (oddCycleLengths (G.induce s)).ncard ≤ (oddCycleLengths G).ncard :=
  Set.ncard_le_ncard (oddCycleLengths_induce_subset G s) (oddCycleLengths_finite G)

/-- A coarse but convenient cardinal bound on the set of odd cycle lengths. -/
lemma ncard_oddCycleLengths_le_natCard [Finite V] (G : SimpleGraph V) :
    (oddCycleLengths G).ncard ≤ Nat.card V := by
  refine (Set.ncard_le_ncard ?_ (Set.finite_Icc 1 (Nat.card V))).trans ?_
  · intro n hn
    have hn3 := three_le_of_mem_oddCycleLengths hn
    exact ⟨by omega, mem_oddCycleLengths_le_natCard hn⟩
  · rw [Set.ncard_Icc_nat]
    omega

/-- The complete graph on `n` vertices has precisely the odd cycle lengths
between `3` and `n`. -/
theorem oddCycleLengths_completeGraph (n : ℕ) :
    oddCycleLengths (SimpleGraph.completeGraph (Fin n)) =
      {m : ℕ | Odd m ∧ 3 ≤ m ∧ m ≤ n} := by
  ext m
  rw [mem_oddCycleLengths_iff_odd_and_two_lt_and_cycleGraph_isContained]
  simp only [Set.mem_ofPred_eq, SimpleGraph.isContained_top_iff,
    Fin.nonempty_embedding_iff]
  constructor
  · rintro ⟨hodd, hm3, hmn⟩
    exact ⟨hodd, by omega, hmn⟩
  · rintro ⟨hodd, hm3, hmn⟩
    exact ⟨hodd, by omega, hmn⟩

/-- Thus `K_(2k+2)` has exactly the `k` odd cycle lengths
`3, 5, ..., 2k+1`. -/
theorem oddCycleLengths_completeGraph_two_mul_add_two (k : ℕ) :
    oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * k + 2))) =
      Set.range (fun i : Fin k ↦ 2 * (i : ℕ) + 3) := by
  rw [oddCycleLengths_completeGraph]
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hmodd, hm3, hmle⟩
    obtain ⟨j, rfl⟩ := hmodd
    have hj : j - 1 < k := by omega
    refine ⟨⟨j - 1, hj⟩, ?_⟩
    change 2 * (j - 1) + 3 = 2 * j + 1
    omega
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    refine ⟨⟨(i : ℕ) + 1, by omega⟩, by omega, by omega⟩

/-- Exact complete-graph lower bound used in the equality case of Erdős
Problem 58. -/
@[simp] theorem ncard_oddCycleLengths_completeGraph_two_mul_add_two (k : ℕ) :
    (oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * k + 2)))).ncard = k := by
  rw [oddCycleLengths_completeGraph_two_mul_add_two]
  rw [Set.ncard_range_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    change 2 * (i : ℕ) + 3 = 2 * (j : ℕ) + 3 at hij
    omega

end

end Erdos58

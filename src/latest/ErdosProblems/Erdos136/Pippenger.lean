/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.Hypergraph
import ErdosProblems.Erdos136.Freedman
import ErdosProblems.Erdos136.BernoulliFreedman

/-!
# Finite matching and nibble infrastructure

This file develops the deterministic part of the Pippenger--Frankl--Rödl
matching argument for the finite hypergraph representation used by
`ErdosProblems.Erdos136.Hypergraph`.

The central deterministic result says that a maximum matching either covers
the whole finite ground set or has size at least the minimum degree divided by
`r` times the maximum pair-codegree.  This is the strongest conclusion that
follows from maximality and the two local degree hypotheses alone.  The final
section gives a finite-probability-space extraction lemma from the Freedman
bound.  It is the interface needed by each round of a random nibble.
-/

namespace Erdos136

open Finset
open scoped BigOperators symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Covered vertices and maximum matchings -/

/-- The vertices covered by a finite family of hyperedges. -/
def coveredVertices (M : Hypergraph V) : Finset V :=
  M.biUnion id

@[simp] theorem mem_coveredVertices {M : Hypergraph V} {v : V} :
    v ∈ coveredVertices M ↔ ∃ e ∈ M, v ∈ e := by
  simp [coveredVertices]

theorem edge_subset_coveredVertices {M : Hypergraph V} {e : Finset V}
    (he : e ∈ M) : e ⊆ coveredVertices M := by
  intro v hv
  exact mem_coveredVertices.mpr ⟨e, he, hv⟩

theorem disjoint_edge_of_disjoint_coveredVertices {M : Hypergraph V}
    {e f : Finset V} (h : Disjoint e (coveredVertices M)) (hf : f ∈ M) :
    Disjoint e f :=
  Finset.disjoint_of_subset_right (edge_subset_coveredVertices hf) h

/-- The finite set of all matchings contained in `H`. -/
noncomputable def matchingFamilies (H : Hypergraph V) : Finset (Hypergraph V) := by
  classical
  exact H.powerset.filter (IsMatching H)

@[simp] theorem mem_matchingFamilies {H M : Hypergraph V} :
    M ∈ matchingFamilies H ↔ IsMatching H M := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h⟩

theorem matchingFamilies_nonempty (H : Hypergraph V) :
    (matchingFamilies H).Nonempty := by
  classical
  exact ⟨∅, mem_matchingFamilies.mpr (isMatching_empty H)⟩

/-- A maximum-cardinality matching exists because the host hypergraph is
finite.  The second conclusion is its universal cardinality property. -/
theorem exists_maximum_matching (H : Hypergraph V) :
    ∃ M, IsMatching H M ∧ ∀ N, IsMatching H N → N.card ≤ M.card := by
  classical
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image (matchingFamilies H) Finset.card
      (matchingFamilies_nonempty H)
  refine ⟨M, mem_matchingFamilies.mp hM, ?_⟩
  intro N hN
  exact hmax N (mem_matchingFamilies.mpr hN)

/-- A maximum matching is maximal: every host edge meets a covered vertex. -/
theorem maximum_matching_meets_covered {H M : Hypergraph V}
    (hM : IsMatching H M)
    (hmax : ∀ N, IsMatching H N → N.card ≤ M.card)
    (hempty : ∅ ∉ H) :
    ∀ e ∈ H, ¬Disjoint e (coveredVertices M) := by
  intro e heH hedisj
  have heM : e ∉ M := by
    intro he
    have hene : e.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun heq =>
      hempty (heq ▸ heH))
    obtain ⟨v, hv⟩ := hene
    exact Finset.disjoint_left.mp hedisj hv
      (edge_subset_coveredVertices he hv)
  have hins : IsMatching H (insert e M) := by
    rw [isMatching_insert_iff]
    refine ⟨heH, hM, ?_⟩
    intro f hf hfe
    exact disjoint_edge_of_disjoint_coveredVertices hedisj hf
  have hle := hmax (insert e M) hins
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

/-- A pairwise-disjoint `r`-uniform family covers exactly `r` vertices per
edge. -/
theorem card_coveredVertices_of_uniform_matching {H M : Hypergraph V} {r : ℕ}
    (hH : IsUniform H r) (hM : IsMatching H M) :
    (coveredVertices M).card = M.card * r := by
  have hpair : ((M : Set (Finset V))).PairwiseDisjoint id := by
    intro e he f hf hef
    exact hM.2 he hf hef
  rw [coveredVertices, Finset.card_biUnion hpair]
  calc
    ∑ e ∈ M, e.card = ∑ _e ∈ M, r := by
      apply Finset.sum_congr rfl
      intro e he
      exact hH e (hM.1 he)
    _ = M.card * r := by simp

/-! ## The maximal-matching codegree count -/

/-- All edges at `u` meet the covered set of a maximum matching.  Counting
them through a chosen covered vertex bounds the degree of an uncovered vertex
by the sum of its pair-codegrees with covered vertices. -/
theorem degree_le_sum_pair_codegrees_of_maximum {H M : Hypergraph V}
    (hM : IsMatching H M)
    (hmax : ∀ N, IsMatching H N → N.card ≤ M.card)
    (hempty : ∅ ∉ H)
    {u : V} (_hu : u ∉ coveredVertices M) :
    degree H u ≤
      ∑ w ∈ coveredVertices M, codegree H {u, w} := by
  let star : Hypergraph V := H.filter fun e => u ∈ e
  let through : V → Hypergraph V := fun w => H.filter fun e => {u, w} ⊆ e
  have hsub : star ⊆ (coveredVertices M).biUnion through := by
    intro e he
    have heH : e ∈ H := (Finset.mem_filter.mp he).1
    have hue : u ∈ e := (Finset.mem_filter.mp he).2
    have hinter : ¬Disjoint e (coveredVertices M) :=
      maximum_matching_meets_covered hM hmax hempty e heH
    rw [Finset.not_disjoint_iff] at hinter
    obtain ⟨w, hwe, hwcov⟩ := hinter
    apply Finset.mem_biUnion.mpr
    refine ⟨w, hwcov, Finset.mem_filter.mpr ⟨heH, ?_⟩⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hue, hwe⟩
  calc
    degree H u = star.card := rfl
    _ ≤ ((coveredVertices M).biUnion through).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ w ∈ coveredVertices M, (through w).card :=
      Finset.card_biUnion_le
    _ = ∑ w ∈ coveredVertices M, codegree H {u, w} := by rfl

/-- The preceding sum is at most `|covered M| * L` under a pair-codegree
bound. -/
theorem degree_le_covered_mul_codegree_of_maximum {H M : Hypergraph V}
    (hM : IsMatching H M)
    (hmax : ∀ N, IsMatching H N → N.card ≤ M.card)
    (hempty : ∅ ∉ H)
    {L : ℕ} (hcodeg : MaxCodegreeLE H 2 L)
    {u : V} (hu : u ∉ coveredVertices M) :
    degree H u ≤ (coveredVertices M).card * L := by
  refine (degree_le_sum_pair_codegrees_of_maximum hM hmax hempty hu).trans ?_
  calc
    ∑ w ∈ coveredVertices M, codegree H {u, w}
        ≤ ∑ _w ∈ coveredVertices M, L := by
          apply Finset.sum_le_sum
          intro w hw
          have huw : u ≠ w := by
            intro h
            subst w
            exact hu hw
          apply hcodeg {u, w}
          simp [huw]
    _ = (coveredVertices M).card * L := by simp

/-- Deterministic core bound.  A maximum matching in an `r`-uniform
hypergraph either covers every vertex or satisfies
`D ≤ r * |M| * L`, where `D` is the minimum degree and `L` the maximum
pair-codegree. -/
theorem exists_matching_minDegree_le_or_covers
    [Fintype V] (H : Hypergraph V) {r D L : ℕ}
    (hH : IsUniform H r) (hr : 0 < r) (hmin : MinDegreeGE H D)
    (hcodeg : MaxCodegreeLE H 2 L) :
    ∃ M, IsMatching H M ∧
      (D ≤ M.card * r * L ∨ coveredVertices M = Finset.univ) := by
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matching H
  have hempty : ∅ ∉ H := by
    intro he
    have := hH ∅ he
    simp at this
    omega
  refine ⟨M, hM, ?_⟩
  by_cases hcov : coveredVertices M = Finset.univ
  · exact Or.inr hcov
  · left
    have hex : ∃ u : V, u ∉ coveredVertices M := by
      by_contra hnot
      push Not at hnot
      apply hcov
      ext u
      simp [hnot u]
    obtain ⟨u, hucov⟩ := hex
    have hdeg :=
      degree_le_covered_mul_codegree_of_maximum hM hmax hempty hcodeg hucov
    have hD := hmin u
    rw [card_coveredVertices_of_uniform_matching hH hM] at hdeg
    exact hD.trans hdeg

/-- A convenient lower-bound form when the numerical hypotheses rule out a
small matching. -/
theorem exists_matching_card_ge_of_minDegree
    [Fintype V] (H : Hypergraph V) {r D L target : ℕ}
    (hH : IsUniform H r) (hr : 0 < r)
    (hmin : MinDegreeGE H D) (hcodeg : MaxCodegreeLE H 2 L)
    (hnum : target * r * L < D)
    (huniv : target * r < Fintype.card V) :
    ∃ M, IsMatching H M ∧ target < M.card := by
  obtain ⟨M, hM, hbound | hcover⟩ :=
    exists_matching_minDegree_le_or_covers H hH hr hmin hcodeg
  · refine ⟨M, hM, ?_⟩
    by_contra hnot
    have hMt : M.card ≤ target := Nat.le_of_not_gt hnot
    have : M.card * r * L ≤ target * r * L := by
      gcongr
    omega
  · refine ⟨M, hM, ?_⟩
    have hcard := card_coveredVertices_of_uniform_matching hH hM
    rw [hcover, Finset.card_univ] at hcard
    by_contra hnot
    have hMt : M.card ≤ target := Nat.le_of_not_gt hnot
    have : Fintype.card V ≤ target * r := by
      rw [hcard]
      gcongr
    omega

/-! ## The maximum-degree baseline -/

/-- Host edges meeting `e`. -/
def edgeNeighborhood (H : Hypergraph V) (e : Finset V) : Hypergraph V :=
  H.filter fun f => ¬Disjoint e f

@[simp] theorem mem_edgeNeighborhood {H : Hypergraph V} {e f : Finset V} :
    f ∈ edgeNeighborhood H e ↔ f ∈ H ∧ ¬Disjoint e f := by
  simp [edgeNeighborhood]

/-- An edge meeting `e` contains one of its vertices, so the neighborhood of
`e` is covered by the union of the vertex stars indexed by `e`. -/
theorem edgeNeighborhood_subset_biUnion_stars (H : Hypergraph V)
    (e : Finset V) :
    edgeNeighborhood H e ⊆
      e.biUnion (fun v => H.filter fun f => v ∈ f) := by
  intro f hf
  obtain ⟨hfH, hinter⟩ := mem_edgeNeighborhood.mp hf
  rw [Finset.not_disjoint_iff] at hinter
  obtain ⟨v, hve, hvf⟩ := hinter
  exact Finset.mem_biUnion.mpr
    ⟨v, hve, Finset.mem_filter.mpr ⟨hfH, hvf⟩⟩

theorem card_edgeNeighborhood_le_sum_degrees (H : Hypergraph V)
    (e : Finset V) :
    (edgeNeighborhood H e).card ≤ ∑ v ∈ e, degree H v := by
  calc
    (edgeNeighborhood H e).card
        ≤ (e.biUnion (fun v => H.filter fun f => v ∈ f)).card :=
      Finset.card_le_card (edgeNeighborhood_subset_biUnion_stars H e)
    _ ≤ ∑ v ∈ e, (H.filter fun f => v ∈ f).card := Finset.card_biUnion_le
    _ = ∑ v ∈ e, degree H v := by rfl

theorem card_edgeNeighborhood_le_mul {H : Hypergraph V} {e : Finset V}
    {r D : ℕ} (hecard : e.card = r) (hmaxdeg : MaxDegreeLE H D) :
    (edgeNeighborhood H e).card ≤ r * D := by
  refine (card_edgeNeighborhood_le_sum_degrees H e).trans ?_
  calc
    ∑ v ∈ e, degree H v ≤ ∑ _v ∈ e, D := by
      apply Finset.sum_le_sum
      intro v hv
      exact hmaxdeg v
    _ = r * D := by simp [hecard]

/-- A maximum matching controls the entire edge set by the union of the
neighborhoods of its members. -/
theorem host_subset_biUnion_neighborhoods_of_maximum {H M : Hypergraph V}
    (hM : IsMatching H M)
    (hmax : ∀ N, IsMatching H N → N.card ≤ M.card)
    (hempty : ∅ ∉ H) :
    H ⊆ M.biUnion (edgeNeighborhood H) := by
  intro e heH
  have hinter := maximum_matching_meets_covered hM hmax hempty e heH
  rw [Finset.not_disjoint_iff] at hinter
  obtain ⟨v, hve, hvcov⟩ := hinter
  obtain ⟨f, hfM, hvf⟩ := mem_coveredVertices.mp hvcov
  apply Finset.mem_biUnion.mpr
  refine ⟨f, hfM, mem_edgeNeighborhood.mpr ⟨heH, ?_⟩⟩
  rw [Finset.not_disjoint_iff]
  exact ⟨v, hvf, hve⟩

/-- The standard greedy baseline: if all host edges have size `r` and the
maximum vertex degree is `D`, a maximum matching `M` satisfies
`|H| ≤ |M| r D`. -/
theorem exists_matching_host_card_le_mul (H : Hypergraph V) {r D : ℕ}
    (hH : IsUniform H r) (hr : 0 < r) (hmaxdeg : MaxDegreeLE H D) :
    ∃ M, IsMatching H M ∧ H.card ≤ M.card * r * D := by
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matching H
  have hempty : ∅ ∉ H := by
    intro he
    have := hH ∅ he
    simp at this
    omega
  refine ⟨M, hM, ?_⟩
  calc
    H.card ≤ (M.biUnion (edgeNeighborhood H)).card :=
      Finset.card_le_card
        (host_subset_biUnion_neighborhoods_of_maximum hM hmax hempty)
    _ ≤ ∑ e ∈ M, (edgeNeighborhood H e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ M, r * D := by
      apply Finset.sum_le_sum
      intro e heM
      exact card_edgeNeighborhood_le_mul (hH e (hM.1 heM)) hmaxdeg
    _ = M.card * r * D := by simp [Nat.mul_assoc]

/-- Double-count incidences between vertices and hyperedges. -/
theorem sum_degrees_eq_sum_edge_cards [Fintype V] (H : Hypergraph V) :
    ∑ v, degree H v = ∑ e ∈ H, e.card := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  simp

/-- Consequently, minimum degree `D` in an `r`-uniform host gives
`|V| D ≤ |H| r`. -/
theorem vertex_mul_minDegree_le_host_mul_uniform [Fintype V]
    (H : Hypergraph V) {r D : ℕ} (hH : IsUniform H r)
    (hmin : MinDegreeGE H D) :
    Fintype.card V * D ≤ H.card * r := by
  calc
    Fintype.card V * D = ∑ _v : V, D := by simp
    _ ≤ ∑ v : V, degree H v := by
      apply Finset.sum_le_sum
      intro v hv
      exact hmin v
    _ = ∑ e ∈ H, e.card := sum_degrees_eq_sum_edge_cards H
    _ = ∑ _e ∈ H, r := by
      apply Finset.sum_congr rfl
      intro e he
      exact hH e he
    _ = H.card * r := by simp

/-- For an exactly `D`-regular `r`-uniform finite hypergraph, the elementary
maximum-matching argument covers at least a `1/r` fraction of the vertices.
The Pippenger nibble improves the right side from `|M| r²` to
`(1+o(1)) |M| r`. -/
theorem exists_matching_vertex_card_le_card_mul_sq
    [Fintype V] (H : Hypergraph V) {r D : ℕ}
    (hH : IsUniform H r) (hr : 0 < r) (hD : 0 < D)
    (hmin : MinDegreeGE H D) (hmax : MaxDegreeLE H D) :
    ∃ M, IsMatching H M ∧ Fintype.card V ≤ M.card * r ^ 2 := by
  obtain ⟨M, hM, hhost⟩ := exists_matching_host_card_le_mul H hH hr hmax
  have hinc := vertex_mul_minDegree_le_host_mul_uniform H hH hmin
  refine ⟨M, hM, ?_⟩
  have hmul : Fintype.card V * D ≤ (M.card * r ^ 2) * D := by
    calc
      Fintype.card V * D ≤ H.card * r := hinc
      _ ≤ (M.card * r * D) * r := Nat.mul_le_mul_right r hhost
      _ = (M.card * r ^ 2) * D := by ring
  exact Nat.le_of_mul_le_mul_right hmul hD

/-! ## One fixed nibble round -/

section NibbleRound

variable [Fintype V]

/-- A marking assigns one independent bit to each edge of the current host. -/
abbrev EdgeMarking (H : Hypergraph V) := {e // e ∈ H} → Bool

/-- A canonical enumeration of the current edge coordinates.  Keeping the
coordinate type at exactly `H.card` is important in a conditional nibble
round: marks on edges which have already disappeared must not contribute to
the martingale variance budget. -/
noncomputable def edgeEquivFin (H : Hypergraph V) :
    {e // e ∈ H} ≃ Fin H.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe H)

/-- Interpret a Boolean vector indexed by `Fin H.card` as marks on `H`. -/
noncomputable def markingOfBits (H : Hypergraph V)
    (bits : Fin H.card → Bool) : EdgeMarking H :=
  fun e => bits (edgeEquivFin H e)

/-- Read an edge marking in the canonical finite coordinate order. -/
noncomputable def bitsOfMarking (H : Hypergraph V)
    (mark : EdgeMarking H) : Fin H.card → Bool :=
  fun i => mark ((edgeEquivFin H).symm i)

@[simp] theorem markingOfBits_bitsOfMarking (H : Hypergraph V)
    (mark : EdgeMarking H) :
    markingOfBits H (bitsOfMarking H mark) = mark := by
  funext e
  simp [markingOfBits, bitsOfMarking]

@[simp] theorem bitsOfMarking_markingOfBits (H : Hypergraph V)
    (bits : Fin H.card → Bool) :
    bitsOfMarking H (markingOfBits H bits) = bits := by
  funext i
  simp [markingOfBits, bitsOfMarking]

/-- Replace one coordinate of a Boolean vector. -/
def replaceBit {n : ℕ} (bits : Fin n → Bool) (i : Fin n) (b : Bool) :
    Fin n → Bool :=
  Function.update bits i b

@[simp] theorem replaceBit_apply_same {n : ℕ} (bits : Fin n → Bool)
    (i : Fin n) (b : Bool) : replaceBit bits i b i = b := by
  simp [replaceBit]

theorem replaceBit_apply_of_ne {n : ℕ} (bits : Fin n → Bool)
    {i j : Fin n} (hji : j ≠ i) (b : Bool) :
    replaceBit bits i b j = bits j := by
  simp [replaceBit, hji]

/-- The marked host edges. -/
def markedEdges (H : Hypergraph V) (mark : EdgeMarking H) : Hypergraph V := by
  classical
  exact H.filter fun e => ∃ he : e ∈ H, mark ⟨e, he⟩ = true

@[simp] theorem mem_markedEdges {H : Hypergraph V} {mark : EdgeMarking H}
    {e : Finset V} :
    e ∈ markedEdges H mark ↔ ∃ he : e ∈ H, mark ⟨e, he⟩ = true := by
  classical
  simp [markedEdges]

/-- A marked edge is accepted when no distinct marked edge meets it. -/
def isolatedMarkedEdges (H : Hypergraph V) (mark : EdgeMarking H) :
    Hypergraph V :=
  (markedEdges H mark).filter fun e =>
    ∀ f ∈ markedEdges H mark, f ≠ e → Disjoint e f

@[simp] theorem mem_isolatedMarkedEdges {H : Hypergraph V}
    {mark : EdgeMarking H} {e : Finset V} :
    e ∈ isolatedMarkedEdges H mark ↔
      e ∈ markedEdges H mark ∧
        ∀ f ∈ markedEdges H mark, f ≠ e → Disjoint e f := by
  simp [isolatedMarkedEdges]

/-- The isolated marked edges always form a matching. -/
theorem isolatedMarkedEdges_isMatching (H : Hypergraph V)
    (mark : EdgeMarking H) :
    IsMatching H (isolatedMarkedEdges H mark) := by
  refine ⟨?_, ?_⟩
  · intro e he
    exact (mem_markedEdges.mp (mem_isolatedMarkedEdges.mp he).1).choose
  · intro e he f hf hef
    exact (mem_isolatedMarkedEdges.mp he).2 f
      (mem_isolatedMarkedEdges.mp hf).1 hef.symm

/-- Delete all host edges meeting a prescribed vertex set. -/
def deleteVertices (H : Hypergraph V) (S : Finset V) : Hypergraph V :=
  H.filter fun e => Disjoint e S

@[simp] theorem mem_deleteVertices {H : Hypergraph V} {S e : Finset V} :
    e ∈ deleteVertices H S ↔ e ∈ H ∧ Disjoint e S := by
  simp [deleteVertices]

/-- Residual hypergraph after one isolated-edge nibble. -/
def nibbleResidual (H : Hypergraph V) (mark : EdgeMarking H) : Hypergraph V :=
  deleteVertices H (coveredVertices (isolatedMarkedEdges H mark))

theorem nibbleResidual_subset (H : Hypergraph V) (mark : EdgeMarking H) :
    nibbleResidual H mark ⊆ H := by
  intro e he
  exact (mem_deleteVertices.mp he).1

theorem nibbleResidual_uniform {H : Hypergraph V} {r : ℕ}
    (hH : IsUniform H r) (mark : EdgeMarking H) :
    IsUniform (nibbleResidual H mark) r :=
  hH.mono (nibbleResidual_subset H mark)

theorem nibbleResidual_codegree_le (H : Hypergraph V)
    (mark : EdgeMarking H) (s : Finset V) :
    codegree (nibbleResidual H mark) s ≤ codegree H s :=
  codegree_mono_hypergraph (nibbleResidual_subset H mark) s

theorem nibbleResidual_maxCodegreeLE {H : Hypergraph V} {j L : ℕ}
    (hcodeg : MaxCodegreeLE H j L) (mark : EdgeMarking H) :
    MaxCodegreeLE (nibbleResidual H mark) j L := by
  intro s hs
  exact (nibbleResidual_codegree_le H mark s).trans (hcodeg s hs)

/-- Edges counted by the potential residual degree at `x`. -/
def potentialResidualEdges (H : Hypergraph V) (mark : EdgeMarking H)
    (x : V) : Hypergraph V :=
  H.filter fun e =>
    x ∈ e ∧ Disjoint (e.erase x)
      (coveredVertices (isolatedMarkedEdges H mark))

@[simp] theorem mem_potentialResidualEdges {H : Hypergraph V}
    {mark : EdgeMarking H} {x : V} {e : Finset V} :
    e ∈ potentialResidualEdges H mark x ↔
      e ∈ H ∧ x ∈ e ∧ Disjoint (e.erase x)
        (coveredVertices (isolatedMarkedEdges H mark)) := by
  simp [potentialResidualEdges]

/-- The potential residual degree of `x` ignores whether `x` itself is
covered.  It counts the old edges at `x` whose other seven vertices survive.
On the event that `x` survives, it is exactly the residual degree.  This
potential has small coordinate influence even for a mark on an edge through
`x`. -/
def potentialResidualDegree (H : Hypergraph V) (mark : EdgeMarking H)
    (x : V) : ℕ :=
  (potentialResidualEdges H mark x).card

theorem potentialResidualDegree_eq_degree_of_not_covered
    (H : Hypergraph V) (mark : EdgeMarking H) (x : V)
    (hx : x ∉ coveredVertices (isolatedMarkedEdges H mark)) :
    potentialResidualDegree H mark x = degree (nibbleResidual H mark) x := by
  apply congrArg Finset.card
  ext e
  constructor
  · intro he
    have heH := (Finset.mem_filter.mp he).1
    have hxe := (Finset.mem_filter.mp he).2.1
    have hdisjErase := (Finset.mem_filter.mp he).2.2
    refine Finset.mem_filter.mpr ⟨?_, hxe⟩
    refine mem_deleteVertices.mpr ⟨heH, ?_⟩
    rw [Finset.disjoint_left]
    intro y hye hycov
    by_cases hyx : y = x
    · exact hx (hyx ▸ hycov)
    · exact Finset.disjoint_left.mp hdisjErase
        (Finset.mem_erase.mpr ⟨hyx, hye⟩) hycov
  · intro he
    have heRes := (Finset.mem_filter.mp he).1
    have hxe := (Finset.mem_filter.mp he).2
    obtain ⟨heH, hdisj⟩ := mem_deleteVertices.mp heRes
    refine Finset.mem_filter.mpr ⟨heH, hxe, ?_⟩
    exact Finset.disjoint_of_subset_left (Finset.erase_subset x e) hdisj

/-- Accepted edges remain a matching in the original host, and the next
residual is vertex-disjoint from them. -/
theorem isolated_and_residual_disjoint (H : Hypergraph V)
    (mark : EdgeMarking H) {e f : Finset V}
    (he : e ∈ isolatedMarkedEdges H mark)
    (hf : f ∈ nibbleResidual H mark) : Disjoint e f := by
  have hecov := edge_subset_coveredVertices he
  have hfdisj := (mem_deleteVertices.mp hf).2
  exact Finset.disjoint_of_subset_left hecov hfdisj.symm

/-! ### Coordinate influence of one nibble round -/

/-- Two markings agree away from one distinguished edge-coordinate. -/
def MarkingsAgreeOff {H : Hypergraph V} (a : {e // e ∈ H})
    (mark mark' : EdgeMarking H) : Prop :=
  ∀ b, b ≠ a → mark b = mark' b

theorem MarkingsAgreeOff.symm {H : Hypergraph V} {a : {e // e ∈ H}}
    {mark mark' : EdgeMarking H} (h : MarkingsAgreeOff a mark mark') :
    MarkingsAgreeOff a mark' mark := by
  intro b hba
  exact (h b hba).symm

/-- Replacing one bit in the canonical product representation changes only
the corresponding edge mark. -/
theorem markingsAgreeOff_markingOfBits_replaceBit (H : Hypergraph V)
    (bits : Fin H.card → Bool) (i : Fin H.card) (b : Bool) :
    MarkingsAgreeOff ((edgeEquivFin H).symm i)
      (markingOfBits H bits) (markingOfBits H (replaceBit bits i b)) := by
  intro a hai
  have hcoord : edgeEquivFin H a ≠ i := by
    intro h
    apply hai
    apply (edgeEquivFin H).injective
    simpa using h
  simp [markingOfBits, replaceBit, hcoord]

theorem mem_markedEdges_iff_of_agreeOff {H : Hypergraph V}
    {a : {e // e ∈ H}} {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark')
    {e : Finset V} (heH : e ∈ H) (hea : e ≠ a.1) :
    e ∈ markedEdges H mark ↔ e ∈ markedEdges H mark' := by
  rw [mem_markedEdges, mem_markedEdges]
  constructor
  · rintro ⟨he0, hemark⟩
    refine ⟨heH, ?_⟩
    have hmarkeq := hagree ⟨e, he0⟩
      (fun h => hea (Subtype.ext_iff.mp h))
    simpa using hmarkeq.symm.trans hemark
  · rintro ⟨he0, hemark⟩
    refine ⟨heH, ?_⟩
    have hmarkeq := hagree ⟨e, he0⟩
      (fun h => hea (Subtype.ext_iff.mp h))
    simpa using hmarkeq.trans hemark

/-- If changing one mark destroys the isolated status of another edge, that
edge must meet the changed coordinate. -/
theorem isolatedMarkedEdges_lost_meets_coordinate
    {H : Hypergraph V} {a : {e // e ∈ H}}
    {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark')
    {e : Finset V} (he : e ∈ isolatedMarkedEdges H mark)
    (he' : e ∉ isolatedMarkedEdges H mark') :
    e = a.1 ∨ ¬Disjoint e a.1 := by
  classical
  by_cases hea : e = a.1
  · exact Or.inl hea
  · right
    have heH : e ∈ H := (isolatedMarkedEdges_isMatching H mark).1 he
    have hemarked' : e ∈ markedEdges H mark' :=
      (mem_markedEdges_iff_of_agreeOff hagree heH hea).mp
        (mem_isolatedMarkedEdges.mp he).1
    have hfail : ¬∀ f ∈ markedEdges H mark', f ≠ e → Disjoint e f := by
      intro hall
      exact he' (mem_isolatedMarkedEdges.mpr ⟨hemarked', hall⟩)
    push Not at hfail
    obtain ⟨f, hfmarked', hfe, hinter⟩ := hfail
    have hfH : f ∈ H := (mem_markedEdges.mp hfmarked').choose
    by_cases hfa : f = a.1
    · simpa [hfa] using hinter
    · have hfmarked : f ∈ markedEdges H mark :=
        (mem_markedEdges_iff_of_agreeOff hagree hfH hfa).mpr hfmarked'
      exact (hinter ((mem_isolatedMarkedEdges.mp he).2 f hfmarked hfe)).elim

/-- In a matching, a subfamily all of whose edges meet `a` has at most
`|a|` members. -/
theorem matching_card_le_edge_card_of_meets {H M : Hypergraph V}
    (hM : IsMatching H M) (a : Finset V)
    (hmeets : ∀ e ∈ M, ¬Disjoint e a) : M.card ≤ a.card := by
  classical
  let hit (e : {e // e ∈ M}) : V :=
    Classical.choose (Finset.not_disjoint_iff.mp (hmeets e.1 e.2))
  have hit_mem_edge (e : {e // e ∈ M}) : hit e ∈ e.1 :=
    (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (hmeets e.1 e.2))).1
  have hit_mem_a (e : {e // e ∈ M}) : hit e ∈ a :=
    (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (hmeets e.1 e.2))).2
  let F : {e // e ∈ M} → {v // v ∈ a} :=
    fun e => ⟨hit e, hit_mem_a e⟩
  have hFinj : Function.Injective F := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    have hdisj := hM.2 e.2 f.2 hne
    have hhit : hit e = hit f := congrArg Subtype.val hef
    exact Finset.disjoint_left.mp hdisj (hit_mem_edge e)
      (hhit ▸ hit_mem_edge f)
  have := Fintype.card_le_of_injective F hFinj
  simpa using this

/-- At most `2|a|` accepted edges can change when the mark at `a` is
toggled.  Each side of the symmetric difference is a matching whose members
all meet `a`. -/
theorem card_symmDiff_isolatedMarkedEdges_le
    {H : Hypergraph V} {a : {e // e ∈ H}}
    {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark') (ha : a.1.Nonempty) :
    ((isolatedMarkedEdges H mark) ∆
      (isolatedMarkedEdges H mark')).card ≤ 2 * a.1.card := by
  classical
  let M := isolatedMarkedEdges H mark
  let M' := isolatedMarkedEdges H mark'
  have hleftMatch : IsMatching H (M \ M') :=
    (isolatedMarkedEdges_isMatching H mark).mono (Finset.sdiff_subset)
  have hrightMatch : IsMatching H (M' \ M) :=
    (isolatedMarkedEdges_isMatching H mark').mono (Finset.sdiff_subset)
  have hleft : (M \ M').card ≤ a.1.card := by
    apply matching_card_le_edge_card_of_meets hleftMatch a.1
    intro e he
    have heM := (Finset.mem_sdiff.mp he).1
    have heM' := (Finset.mem_sdiff.mp he).2
    rcases isolatedMarkedEdges_lost_meets_coordinate hagree heM heM' with
      hea | hinter
    · subst e
      exact Finset.not_disjoint_iff.mpr
        ⟨ha.choose, ha.choose_spec, ha.choose_spec⟩
    · exact hinter
  have hright : (M' \ M).card ≤ a.1.card := by
    apply matching_card_le_edge_card_of_meets hrightMatch a.1
    intro e he
    have heM' := (Finset.mem_sdiff.mp he).1
    have heM := (Finset.mem_sdiff.mp he).2
    rcases isolatedMarkedEdges_lost_meets_coordinate hagree.symm heM' heM with
      hea | hinter
    · subst e
      exact Finset.not_disjoint_iff.mpr
        ⟨ha.choose, ha.choose_spec, ha.choose_spec⟩
    · exact hinter
  calc
    (M ∆ M').card = ((M \ M') ∪ (M' \ M)).card := rfl
    _ ≤ (M \ M').card + (M' \ M).card :=
      Finset.card_union_le (M \ M') (M' \ M)
    _ ≤ a.1.card + a.1.card := Nat.add_le_add hleft hright
    _ = 2 * a.1.card := by omega

theorem coveredVertices_symmDiff_subset_covered_symmDiff
    (M M' : Hypergraph V) :
    (coveredVertices M ∆ coveredVertices M') ⊆
      coveredVertices (M ∆ M') := by
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with ⟨hvM, hvM'⟩ | ⟨hvM', hvM⟩
  · obtain ⟨e, heM, hve⟩ := mem_coveredVertices.mp hvM
    apply mem_coveredVertices.mpr
    refine ⟨e, Finset.mem_symmDiff.mpr (Or.inl ⟨heM, ?_⟩), hve⟩
    intro heM'
    exact hvM' (mem_coveredVertices.mpr ⟨e, heM', hve⟩)
  · obtain ⟨e, heM', hve⟩ := mem_coveredVertices.mp hvM'
    apply mem_coveredVertices.mpr
    refine ⟨e, Finset.mem_symmDiff.mpr (Or.inr ⟨heM', ?_⟩), hve⟩
    intro heM
    exact hvM (mem_coveredVertices.mpr ⟨e, heM, hve⟩)

/-- In the 8-uniform application, toggling one mark changes the covered set
on at most 128 vertices. -/
theorem card_symmDiff_covered_isolated_le
    {H : Hypergraph V} (hH : IsUniform H 8)
    {a : {e // e ∈ H}} {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark') :
    (coveredVertices (isolatedMarkedEdges H mark) ∆
      coveredVertices (isolatedMarkedEdges H mark')).card ≤ 128 := by
  let M := isolatedMarkedEdges H mark
  let M' := isolatedMarkedEdges H mark'
  have ha8 : a.1.card = 8 := hH a.1 a.2
  have hane : a.1.Nonempty := by
    apply Finset.card_pos.mp
    rw [ha8]
    norm_num
  have hfamily : (M ∆ M').card ≤ 16 := by
    simpa [ha8] using card_symmDiff_isolatedMarkedEdges_le hagree hane
  calc
    (coveredVertices M ∆ coveredVertices M').card
        ≤ (coveredVertices (M ∆ M')).card :=
      Finset.card_le_card (coveredVertices_symmDiff_subset_covered_symmDiff M M')
    _ ≤ ∑ e ∈ M ∆ M', e.card := Finset.card_biUnion_le
    _ = ∑ _e ∈ M ∆ M', 8 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mem_symmDiff] at he
      rcases he with ⟨heM, -⟩ | ⟨heM', -⟩
      · exact hH e ((isolatedMarkedEdges_isMatching H mark).1 heM)
      · exact hH e ((isolatedMarkedEdges_isMatching H mark').1 heM')
    _ = (M ∆ M').card * 8 := by simp
    _ ≤ 16 * 8 := Nat.mul_le_mul_right 8 hfamily
    _ = 128 := by norm_num

/-- An edge whose potential-survival status changes contains, besides `x`,
a vertex whose covered status changed. -/
theorem potentialEdges_symmDiff_subset_pairLinks
    {H : Hypergraph V} {mark mark' : EdgeMarking H} (x : V) :
    (potentialResidualEdges H mark x ∆
      potentialResidualEdges H mark' x) ⊆
      ((coveredVertices (isolatedMarkedEdges H mark) ∆
        coveredVertices (isolatedMarkedEdges H mark')).erase x).biUnion
        (fun y => H.filter fun e => {x, y} ⊆ e) := by
  intro e he
  rw [Finset.mem_symmDiff] at he
  rcases he with ⟨he, he'⟩ | ⟨he', he⟩
  · have hdata := mem_potentialResidualEdges.mp he
    have hnotdisj : ¬Disjoint (e.erase x)
        (coveredVertices (isolatedMarkedEdges H mark')) := by
      intro hd
      exact he' (mem_potentialResidualEdges.mpr
        ⟨hdata.1, hdata.2.1, hd⟩)
    rw [Finset.not_disjoint_iff] at hnotdisj
    obtain ⟨y, hyerase, hycov'⟩ := hnotdisj
    have hycov : y ∉ coveredVertices (isolatedMarkedEdges H mark) := by
      intro hy
      exact Finset.disjoint_left.mp hdata.2.2 hyerase hy
    have hychange : y ∈ coveredVertices (isolatedMarkedEdges H mark) ∆
        coveredVertices (isolatedMarkedEdges H mark') :=
      Finset.mem_symmDiff.mpr (Or.inr ⟨hycov', hycov⟩)
    have hyx : y ≠ x := (Finset.mem_erase.mp hyerase).1
    apply Finset.mem_biUnion.mpr
    refine ⟨y, Finset.mem_erase.mpr ⟨hyx, hychange⟩,
      Finset.mem_filter.mpr ⟨hdata.1, ?_⟩⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hdata.2.1, (Finset.mem_erase.mp hyerase).2⟩
  · have hdata := mem_potentialResidualEdges.mp he'
    have hnotdisj : ¬Disjoint (e.erase x)
        (coveredVertices (isolatedMarkedEdges H mark)) := by
      intro hd
      exact he (mem_potentialResidualEdges.mpr
        ⟨hdata.1, hdata.2.1, hd⟩)
    rw [Finset.not_disjoint_iff] at hnotdisj
    obtain ⟨y, hyerase, hycov⟩ := hnotdisj
    have hycov' : y ∉ coveredVertices (isolatedMarkedEdges H mark') := by
      intro hy
      exact Finset.disjoint_left.mp hdata.2.2 hyerase hy
    have hychange : y ∈ coveredVertices (isolatedMarkedEdges H mark) ∆
        coveredVertices (isolatedMarkedEdges H mark') :=
      Finset.mem_symmDiff.mpr (Or.inl ⟨hycov, hycov'⟩)
    have hyx : y ≠ x := (Finset.mem_erase.mp hyerase).1
    apply Finset.mem_biUnion.mpr
    refine ⟨y, Finset.mem_erase.mpr ⟨hyx, hychange⟩,
      Finset.mem_filter.mpr ⟨hdata.1, ?_⟩⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hdata.2.1, (Finset.mem_erase.mp hyerase).2⟩

/-- The potential degree has coordinate oscillation at most `128 Δ₂` in
the 8-uniform nibble. -/
theorem abs_potentialResidualDegree_sub_le
    {H : Hypergraph V} (hH : IsUniform H 8) {L : ℕ}
    (hcodeg : MaxCodegreeLE H 2 L)
    {a : {e // e ∈ H}} {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark') (x : V) :
    |(potentialResidualDegree H mark x : ℝ) -
      (potentialResidualDegree H mark' x : ℝ)| ≤ 128 * L := by
  let A := potentialResidualEdges H mark x
  let B := potentialResidualEdges H mark' x
  let C := (coveredVertices (isolatedMarkedEdges H mark) ∆
    coveredVertices (isolatedMarkedEdges H mark')).erase x
  let links : V → Hypergraph V := fun y => H.filter fun e => {x, y} ⊆ e
  have hC : C.card ≤ 128 := by
    exact (Finset.card_erase_le.trans
      (card_symmDiff_covered_isolated_le hH hagree))
  have hsymm : (A ∆ B).card ≤ C.card * L := by
    calc
      (A ∆ B).card ≤ (C.biUnion links).card :=
        Finset.card_le_card (potentialEdges_symmDiff_subset_pairLinks x)
      _ ≤ ∑ y ∈ C, (links y).card := Finset.card_biUnion_le
      _ = ∑ y ∈ C, codegree H {x, y} := by rfl
      _ ≤ ∑ _y ∈ C, L := by
        apply Finset.sum_le_sum
        intro y hy
        apply hcodeg {x, y}
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        simp [hyx.symm]
      _ = C.card * L := by simp
  have hsymm128 : (A ∆ B).card ≤ 128 * L :=
    hsymm.trans (Nat.mul_le_mul_right L hC)
  have hAB : A.card ≤ (A ∆ B).card + B.card := by
    calc
      A.card ≤ (A \ B).card + B.card := Finset.card_le_card_sdiff_add_card
      _ ≤ (A ∆ B).card + B.card := by
        exact Nat.add_le_add_right
          (Finset.card_le_card
            (Finset.symmDiff_subset_sdiff (s := A) (t := B))) B.card
  have hBA : B.card ≤ (A ∆ B).card + A.card := by
    calc
      B.card ≤ (B \ A).card + A.card := Finset.card_le_card_sdiff_add_card
      _ ≤ (A ∆ B).card + A.card := by
        exact Nat.add_le_add_right
          (Finset.card_le_card
            (Finset.symmDiff_subset_sdiff' (s := A) (t := B))) A.card
  have hreal : |(A.card : ℝ) - (B.card : ℝ)| ≤ ((A ∆ B).card : ℝ) := by
    have hABr : (A.card : ℝ) ≤ ((A ∆ B).card : ℝ) + (B.card : ℝ) := by
      exact_mod_cast hAB
    have hBAr : (B.card : ℝ) ≤ ((A ∆ B).card : ℝ) + (A.card : ℝ) := by
      exact_mod_cast hBA
    rw [abs_le]
    constructor <;> linarith
  exact hreal.trans (by exact_mod_cast hsymm128)

/-! ### Local influence weights -/

/-- Number of edges at `x` whose non-root vertices meet `g`.  These are
exactly the potential-degree summands which can be changed when the covered
status of vertices of `g` changes. -/
def rootInfluenceEdges (H : Hypergraph V) (x : V) (g : Finset V) :
    Hypergraph V :=
  H.filter fun e => x ∈ e ∧ ¬Disjoint (e.erase x) g

def rootInfluenceWeight (H : Hypergraph V) (x : V) (g : Finset V) : ℕ :=
  (rootInfluenceEdges H x g).card

/-- Every potential edge whose status changes is charged to an accepted edge
whose membership changed. -/
theorem potentialEdges_symmDiff_subset_changedInfluences
    {H : Hypergraph V} {mark mark' : EdgeMarking H} (x : V) :
    (potentialResidualEdges H mark x ∆
      potentialResidualEdges H mark' x) ⊆
      ((isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark').biUnion
        (rootInfluenceEdges H x)) := by
  intro e he
  rw [Finset.mem_symmDiff] at he
  rcases he with ⟨he, he'⟩ | ⟨he', he⟩
  · have hdata := mem_potentialResidualEdges.mp he
    have hnotdisj : ¬Disjoint (e.erase x)
        (coveredVertices (isolatedMarkedEdges H mark')) := by
      intro hd
      exact he' (mem_potentialResidualEdges.mpr
        ⟨hdata.1, hdata.2.1, hd⟩)
    rw [Finset.not_disjoint_iff] at hnotdisj
    obtain ⟨y, hyerase, hycov'⟩ := hnotdisj
    have hycov : y ∉ coveredVertices (isolatedMarkedEdges H mark) := by
      intro hy
      exact Finset.disjoint_left.mp hdata.2.2 hyerase hy
    have hychange : y ∈ coveredVertices (isolatedMarkedEdges H mark) ∆
        coveredVertices (isolatedMarkedEdges H mark') :=
      Finset.mem_symmDiff.mpr (Or.inr ⟨hycov', hycov⟩)
    have hybig := coveredVertices_symmDiff_subset_covered_symmDiff
      (isolatedMarkedEdges H mark) (isolatedMarkedEdges H mark') hychange
    obtain ⟨g, hgchange, hyg⟩ := mem_coveredVertices.mp hybig
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hgchange, Finset.mem_filter.mpr ⟨hdata.1, hdata.2.1, ?_⟩⟩
    exact Finset.not_disjoint_iff.mpr ⟨y, hyerase, hyg⟩
  · have hdata := mem_potentialResidualEdges.mp he'
    have hnotdisj : ¬Disjoint (e.erase x)
        (coveredVertices (isolatedMarkedEdges H mark)) := by
      intro hd
      exact he (mem_potentialResidualEdges.mpr
        ⟨hdata.1, hdata.2.1, hd⟩)
    rw [Finset.not_disjoint_iff] at hnotdisj
    obtain ⟨y, hyerase, hycov⟩ := hnotdisj
    have hycov' : y ∉ coveredVertices (isolatedMarkedEdges H mark') := by
      intro hy
      exact Finset.disjoint_left.mp hdata.2.2 hyerase hy
    have hychange : y ∈ coveredVertices (isolatedMarkedEdges H mark) ∆
        coveredVertices (isolatedMarkedEdges H mark') :=
      Finset.mem_symmDiff.mpr (Or.inl ⟨hycov, hycov'⟩)
    have hybig := coveredVertices_symmDiff_subset_covered_symmDiff
      (isolatedMarkedEdges H mark) (isolatedMarkedEdges H mark') hychange
    obtain ⟨g, hgchange, hyg⟩ := mem_coveredVertices.mp hybig
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hgchange, Finset.mem_filter.mpr ⟨hdata.1, hdata.2.1, ?_⟩⟩
    exact Finset.not_disjoint_iff.mpr ⟨y, hyerase, hyg⟩

theorem card_potentialEdges_symmDiff_le_sum_changedInfluences
    {H : Hypergraph V} {mark mark' : EdgeMarking H} (x : V) :
    (potentialResidualEdges H mark x ∆
      potentialResidualEdges H mark' x).card ≤
      ∑ g ∈ isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark',
        rootInfluenceWeight H x g := by
  calc
    (potentialResidualEdges H mark x ∆
        potentialResidualEdges H mark' x).card
        ≤ ((isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark').biUnion
            (rootInfluenceEdges H x)).card :=
      Finset.card_le_card (potentialEdges_symmDiff_subset_changedInfluences x)
    _ ≤ ∑ g ∈ isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark',
          (rootInfluenceEdges H x g).card := Finset.card_biUnion_le
    _ = ∑ g ∈ isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark',
          rootInfluenceWeight H x g := by rfl

/-- Marked neighbors of one coordinate, excluding that coordinate itself. -/
def markedEdgeNeighbors (H : Hypergraph V) (mark : EdgeMarking H)
    (a : {e // e ∈ H}) : Hypergraph V :=
  (markedEdges H mark).filter fun g => g ≠ a.1 ∧ ¬Disjoint g a.1

/-- Outcome-dependent resampling budget for the root-degree potential.  The
first term pays for the distinguished coordinate itself.  The second pays
for marked neighbors whose isolated status can change when that coordinate
is resampled. -/
def rootResamplingBudget (H : Hypergraph V) (mark : EdgeMarking H)
    (x : V) (a : {e // e ∈ H}) : ℕ :=
  rootInfluenceWeight H x a.1 +
    ∑ g ∈ markedEdgeNeighbors H mark a, rootInfluenceWeight H x g

theorem changed_isolated_subset_insert_markedNeighbors
    {H : Hypergraph V} {a : {e // e ∈ H}}
    {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark') :
    isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark' ⊆
      insert a.1 (markedEdgeNeighbors H mark a) := by
  intro g hg
  rw [Finset.mem_symmDiff] at hg
  rcases hg with ⟨hgM, hgM'⟩ | ⟨hgM', hgM⟩
  · by_cases hga : g = a.1
    · exact Finset.mem_insert.mpr (Or.inl hga)
    · have hinter :=
        (isolatedMarkedEdges_lost_meets_coordinate hagree hgM hgM').resolve_left hga
      exact Finset.mem_insert.mpr (Or.inr <|
        Finset.mem_filter.mpr
          ⟨(mem_isolatedMarkedEdges.mp hgM).1, hga, hinter⟩)
  · by_cases hga : g = a.1
    · exact Finset.mem_insert.mpr (Or.inl hga)
    · have hinter :=
        (isolatedMarkedEdges_lost_meets_coordinate hagree.symm hgM' hgM).resolve_left hga
      have hgH := (isolatedMarkedEdges_isMatching H mark').1 hgM'
      have hgmarked : g ∈ markedEdges H mark :=
        (mem_markedEdges_iff_of_agreeOff hagree hgH hga).mpr
          (mem_isolatedMarkedEdges.mp hgM').1
      exact Finset.mem_insert.mpr (Or.inr <|
        Finset.mem_filter.mpr ⟨hgmarked, hga, hinter⟩)

/-- Outcome-dependent resampling bound used in the stopped martingale: the
change is charged to the toggled edge and its marked neighbors. -/
theorem card_potentialEdges_symmDiff_le_resamplingBound
    {H : Hypergraph V} {a : {e // e ∈ H}}
    {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark') (x : V) :
    (potentialResidualEdges H mark x ∆
      potentialResidualEdges H mark' x).card ≤
      rootInfluenceWeight H x a.1 +
        ∑ g ∈ markedEdgeNeighbors H mark a, rootInfluenceWeight H x g := by
  calc
    (potentialResidualEdges H mark x ∆
        potentialResidualEdges H mark' x).card
        ≤ ∑ g ∈ isolatedMarkedEdges H mark ∆ isolatedMarkedEdges H mark',
            rootInfluenceWeight H x g :=
      card_potentialEdges_symmDiff_le_sum_changedInfluences x
    _ ≤ ∑ g ∈ insert a.1 (markedEdgeNeighbors H mark a),
            rootInfluenceWeight H x g := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (changed_isolated_subset_insert_markedNeighbors hagree)
      intro g hg hnot
      omega
    _ = rootInfluenceWeight H x a.1 +
          ∑ g ∈ markedEdgeNeighbors H mark a, rootInfluenceWeight H x g := by
      rw [Finset.sum_insert]
      simp [markedEdgeNeighbors]

/-- Cardinality is 1-Lipschitz for symmetric difference, in the real-valued
form consumed by martingale increments. -/
theorem abs_card_sub_card_le_card_symmDiff {A B : Finset V} :
    |(A.card : ℝ) - (B.card : ℝ)| ≤ ((A ∆ B).card : ℝ) := by
  have hAB : A.card ≤ (A ∆ B).card + B.card := by
    calc
      A.card ≤ (A \ B).card + B.card := Finset.card_le_card_sdiff_add_card
      _ ≤ (A ∆ B).card + B.card := by
        exact Nat.add_le_add_right
          (Finset.card_le_card
            (Finset.symmDiff_subset_sdiff (s := A) (t := B))) B.card
  have hBA : B.card ≤ (A ∆ B).card + A.card := by
    calc
      B.card ≤ (B \ A).card + A.card := Finset.card_le_card_sdiff_add_card
      _ ≤ (A ∆ B).card + A.card := by
        exact Nat.add_le_add_right
          (Finset.card_le_card
            (Finset.symmDiff_subset_sdiff' (s := A) (t := B))) A.card
  have hABr : (A.card : ℝ) ≤ ((A ∆ B).card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hAB
  have hBAr : (B.card : ℝ) ≤ ((A ∆ B).card : ℝ) + (A.card : ℝ) := by
    exact_mod_cast hBA
  rw [abs_le]
  constructor <;> linarith

/-- Sharp outcome-dependent oscillation of the real root-degree potential. -/
theorem abs_potentialResidualDegree_sub_le_rootResamplingBudget
    {H : Hypergraph V} {a : {e // e ∈ H}}
    {mark mark' : EdgeMarking H}
    (hagree : MarkingsAgreeOff a mark mark') (x : V) :
    |(potentialResidualDegree H mark x : ℝ) -
      (potentialResidualDegree H mark' x : ℝ)| ≤
        (rootResamplingBudget H mark x a : ℝ) := by
  apply (abs_card_sub_card_le_card_symmDiff
    (A := potentialResidualEdges H mark x)
    (B := potentialResidualEdges H mark' x)).trans
  exact_mod_cast card_potentialEdges_symmDiff_le_resamplingBound hagree x

/-- Marked neighbors are a subfamily of the ordinary edge neighborhood. -/
theorem markedEdgeNeighbors_subset_edgeNeighborhood
    (H : Hypergraph V) (mark : EdgeMarking H) (a : {e // e ∈ H}) :
    markedEdgeNeighbors H mark a ⊆ edgeNeighborhood H a.1 := by
  intro g hg
  have hdata := Finset.mem_filter.mp hg
  exact mem_edgeNeighborhood.mpr
    ⟨(mem_markedEdges.mp hdata.1).choose, by
      intro h
      exact hdata.2.2 h.symm⟩

theorem card_markedEdgeNeighbors_le
    {H : Hypergraph V} (hH : IsUniform H 8) {D : ℕ}
    (hmax : MaxDegreeLE H D) (mark : EdgeMarking H)
    (a : {e // e ∈ H}) :
    (markedEdgeNeighbors H mark a).card ≤ 8 * D := by
  exact (Finset.card_le_card
    (markedEdgeNeighbors_subset_edgeNeighborhood H mark a)).trans
      (card_edgeNeighborhood_le_mul (hH a.1 a.2) hmax)

theorem rootInfluenceWeight_le_card_mul_codegree
    {H : Hypergraph V} {L : ℕ} (hcodeg : MaxCodegreeLE H 2 L)
    (x : V) (g : Finset V) :
    rootInfluenceWeight H x g ≤ g.card * L := by
  let links : V → Hypergraph V := fun y => H.filter fun e => {x, y} ⊆ e
  have hsub : rootInfluenceEdges H x g ⊆
      (g.erase x).biUnion links := by
    intro e he
    have heH := (Finset.mem_filter.mp he).1
    have hxe := (Finset.mem_filter.mp he).2.1
    have hinter := (Finset.mem_filter.mp he).2.2
    rw [Finset.not_disjoint_iff] at hinter
    obtain ⟨y, hyerase, hyg⟩ := hinter
    have hyx := (Finset.mem_erase.mp hyerase).1
    apply Finset.mem_biUnion.mpr
    refine ⟨y, Finset.mem_erase.mpr ⟨hyx, hyg⟩,
      Finset.mem_filter.mpr ⟨heH, ?_⟩⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxe, (Finset.mem_erase.mp hyerase).2⟩
  calc
    rootInfluenceWeight H x g
        ≤ ((g.erase x).biUnion links).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ g.erase x, (links y).card := Finset.card_biUnion_le
    _ = ∑ y ∈ g.erase x, codegree H {x, y} := by rfl
    _ ≤ ∑ _y ∈ g.erase x, L := by
      apply Finset.sum_le_sum
      intro y hy
      apply hcodeg {x, y}
      have hyx := (Finset.mem_erase.mp hy).1
      simp [hyx.symm]
    _ = (g.erase x).card * L := by simp
    _ ≤ g.card * L := Nat.mul_le_mul_right L Finset.card_erase_le

theorem rootInfluenceWeight_le_eight_mul
    {H : Hypergraph V} (hH : IsUniform H 8) {L : ℕ}
    (hcodeg : MaxCodegreeLE H 2 L) (x : V) {g : Finset V} (hg : g ∈ H) :
    rootInfluenceWeight H x g ≤ 8 * L := by
  simpa [hH g hg] using rootInfluenceWeight_le_card_mul_codegree hcodeg x g

/-- On a guarded outcome it is enough to guard the number of marked
neighbors: every individual influence weight is at most `8 L`. -/
theorem rootResamplingBudget_le_markedNeighborCount
    {H : Hypergraph V} (hH : IsUniform H 8) {L : ℕ}
    (hcodeg : MaxCodegreeLE H 2 L) (mark : EdgeMarking H)
    (x : V) (a : {e // e ∈ H}) :
    rootResamplingBudget H mark x a ≤
      8 * L * (1 + (markedEdgeNeighbors H mark a).card) := by
  unfold rootResamplingBudget
  have ha := rootInfluenceWeight_le_eight_mul hH hcodeg x a.2
  have hsum :
      (∑ g ∈ markedEdgeNeighbors H mark a, rootInfluenceWeight H x g) ≤
        (markedEdgeNeighbors H mark a).card * (8 * L) := by
    calc
      (∑ g ∈ markedEdgeNeighbors H mark a, rootInfluenceWeight H x g)
          ≤ ∑ _g ∈ markedEdgeNeighbors H mark a, 8 * L := by
            apply Finset.sum_le_sum
            intro g hg
            have hgH := (mem_markedEdges.mp (Finset.mem_filter.mp hg).1).choose
            exact rootInfluenceWeight_le_eight_mul hH hcodeg x hgH
      _ = (markedEdgeNeighbors H mark a).card * (8 * L) := by simp
  calc
    rootInfluenceWeight H x a.1 +
          ∑ g ∈ markedEdgeNeighbors H mark a, rootInfluenceWeight H x g
        ≤ 8 * L + (markedEdgeNeighbors H mark a).card * (8 * L) :=
      Nat.add_le_add ha hsum
    _ = 8 * L * (1 + (markedEdgeNeighbors H mark a).card) := by ring

/-- Deterministically, a coordinate has at most `8D` marked neighbors.  This
coarse corollary is useful outside the stopped process; the stopped process
uses the much smaller guarded count. -/
theorem rootResamplingBudget_le_degreeScale
    {H : Hypergraph V} (hH : IsUniform H 8) {D L : ℕ}
    (hmax : MaxDegreeLE H D) (hcodeg : MaxCodegreeLE H 2 L)
    (mark : EdgeMarking H) (x : V) (a : {e // e ∈ H}) :
    rootResamplingBudget H mark x a ≤ 8 * L * (1 + 8 * D) := by
  exact (rootResamplingBudget_le_markedNeighborCount hH hcodeg mark x a).trans
    (Nat.mul_le_mul_left (8 * L)
      (Nat.add_le_add_left (card_markedEdgeNeighbors_le hH hmax mark a) 1))

/-! ### A first product-space concentration theorem -/

/-- A single coordinate has Bernoulli mean `q` under the finite product mass.
This elementary marginal identity is used to center marked-neighbor guards. -/
theorem weightedMean_bit_true (n : ℕ) (q : ℝ) (i : Fin n) :
    BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
      (fun bits : Fin n → Bool => if bits i then 1 else 0) = q := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [BernoulliFreedman.weightedMean_succ]
          have hsection :
              BernoulliFreedman.sectionAverage
                (BernoulliFreedman.weight q)
                (fun bits : Fin (n + 1) → Bool =>
                  if bits 0 then (1 : ℝ) else 0) = fun _ => q := by
            funext y
            simp [BernoulliFreedman.sectionAverage,
              BernoulliFreedman.weight, BernoulliFreedman.bernoulliWeight]
          rw [hsection]
          simp only [BernoulliFreedman.weightedMean, Finset.sum_const_zero]
          rw [← Finset.sum_mul,
            BernoulliFreedman.sum_productMass_eq_one]
          · simp
          · exact fun i => BernoulliFreedman.weight_sum_one q i.succ
      | succ i =>
          rw [BernoulliFreedman.weightedMean_succ]
          have hsection :
              BernoulliFreedman.sectionAverage
                (BernoulliFreedman.weight q)
                (fun bits : Fin (n + 1) → Bool =>
                  if bits i.succ then (1 : ℝ) else 0) =
                fun bits : Fin n → Bool => if bits i then 1 else 0 := by
            funext y
            simp [BernoulliFreedman.sectionAverage,
              BernoulliFreedman.weight, BernoulliFreedman.bernoulliWeight]
          rw [hsection]
          have htail :
              (fun (j : Fin n) (z : Bool) =>
                BernoulliFreedman.weight q j.succ z) =
                BernoulliFreedman.weight q := by
            funext j z
            simp [BernoulliFreedman.weight,
              BernoulliFreedman.bernoulliWeight]
          rw [htail]
          exact ih i

/-- Whether the edge at coordinate `i` is a proper neighbor of `a`. -/
def isNeighborCoordinate (H : Hypergraph V) (a : {e // e ∈ H})
    (i : Fin H.card) : Prop :=
  let e := (edgeEquivFin H).symm i
  e.1 ≠ a.1 ∧ ¬Disjoint e.1 a.1

/-- The finite set of proper edge-neighbor coordinates. -/
noncomputable def neighborCoordinates (H : Hypergraph V)
    (a : {e // e ∈ H}) : Finset (Fin H.card) := by
  classical
  exact Finset.univ.filter (isNeighborCoordinate H a)

/-- The `0`-`1` real weight of a proper neighbor coordinate. -/
noncomputable def neighborCoordinateWeight (H : Hypergraph V)
    (a : {e // e ∈ H}) (i : Fin H.card) : ℝ := by
  classical
  exact if isNeighborCoordinate H a i then 1 else 0

theorem sum_neighborCoordinateWeight_eq_card (H : Hypergraph V)
    (a : {e // e ∈ H}) :
    ∑ i, neighborCoordinateWeight H a i = (neighborCoordinates H a).card := by
  classical
  simp [neighborCoordinateWeight, neighborCoordinates]

/-- Real-valued number of marked proper neighbors, written as a coordinate
sum so its expectation and coordinate oscillations are transparent. -/
noncomputable def markedNeighborCountBits (H : Hypergraph V)
    (a : {e // e ∈ H}) (bits : Fin H.card → Bool) : ℝ := by
  exact ∑ i, neighborCoordinateWeight H a i *
    (if bits i then (1 : ℝ) else 0)

/-- Coordinates which are both proper neighbors and marked. -/
noncomputable def markedNeighborCoordinates (H : Hypergraph V)
    (a : {e // e ∈ H}) (bits : Fin H.card → Bool) :
    Finset (Fin H.card) := by
  classical
  exact (neighborCoordinates H a).filter fun i => bits i = true

theorem markedNeighborCountBits_eq_card (H : Hypergraph V)
    (a : {e // e ∈ H}) (bits : Fin H.card → Bool) :
    markedNeighborCountBits H a bits =
      (markedNeighborCoordinates H a bits).card := by
  classical
  simp only [markedNeighborCountBits, markedNeighborCoordinates,
    neighborCoordinates, neighborCoordinateWeight, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hneighbor : isNeighborCoordinate H a i <;>
    cases hbit : bits i <;> simp [hneighbor, hbit]

/-- The canonical edge enumeration identifies the marked-neighbor coordinate
set with `markedEdgeNeighbors`. -/
noncomputable def markedNeighborCoordinatesEquiv (H : Hypergraph V)
    (a : {e // e ∈ H}) (bits : Fin H.card → Bool) :
    {i // i ∈ markedNeighborCoordinates H a bits} ≃
      {g // g ∈ markedEdgeNeighbors H (markingOfBits H bits) a} := by
  classical
  let toEdge : {i // i ∈ markedNeighborCoordinates H a bits} →
      {g // g ∈ markedEdgeNeighbors H (markingOfBits H bits) a} := fun i => by
    let e : {g // g ∈ H} := (edgeEquivFin H).symm i.1
    have hi := (Finset.mem_filter.mp i.2)
    have hneighbor : isNeighborCoordinate H a i.1 := by
      simpa [neighborCoordinates] using hi.1
    refine ⟨e.1, Finset.mem_filter.mpr ⟨?_, hneighbor.1, hneighbor.2⟩⟩
    exact mem_markedEdges.mpr ⟨e.2, by
      simpa [markingOfBits, e] using hi.2⟩
  let toCoordinate :
      {g // g ∈ markedEdgeNeighbors H (markingOfBits H bits) a} →
        {i // i ∈ markedNeighborCoordinates H a bits} := fun g => by
    have hgdata := Finset.mem_filter.mp g.2
    let hgH : g.1 ∈ H := (mem_markedEdges.mp hgdata.1).choose
    have hgmark : markingOfBits H bits ⟨g.1, hgH⟩ = true :=
      (mem_markedEdges.mp hgdata.1).choose_spec
    let eg : {e // e ∈ H} := ⟨g.1, hgH⟩
    refine ⟨edgeEquivFin H eg, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · simp only [neighborCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [isNeighborCoordinate, eg] using hgdata.2
    · simpa [markingOfBits, eg] using hgmark
  exact
    { toFun := toEdge
      invFun := toCoordinate
      left_inv := by
        intro i
        apply Subtype.ext
        simp [toEdge, toCoordinate]
      right_inv := by
        intro g
        apply Subtype.ext
        simp [toEdge, toCoordinate] }

theorem card_markedEdgeNeighbors_eq_markedNeighborCoordinates
    (H : Hypergraph V) (a : {e // e ∈ H}) (bits : Fin H.card → Bool) :
    (markedEdgeNeighbors H (markingOfBits H bits) a).card =
      (markedNeighborCoordinates H a bits).card := by
  simpa using Fintype.card_congr (markedNeighborCoordinatesEquiv H a bits).symm

theorem rootResamplingBudget_le_markedNeighborCountBits
    {H : Hypergraph V} (hH : IsUniform H 8) {L : ℕ}
    (hcodeg : MaxCodegreeLE H 2 L) (bits : Fin H.card → Bool)
    (x : V) (a : {e // e ∈ H}) :
    (rootResamplingBudget H (markingOfBits H bits) x a : ℝ) ≤
      8 * L * (1 + markedNeighborCountBits H a bits) := by
  have hbudget := rootResamplingBudget_le_markedNeighborCount
    hH hcodeg (markingOfBits H bits) x a
  rw [markedNeighborCountBits_eq_card,
    ← card_markedEdgeNeighbors_eq_markedNeighborCoordinates] 
  exact_mod_cast hbudget

theorem weightedMean_markedNeighborCountBits (H : Hypergraph V)
    (a : {e // e ∈ H}) (q : ℝ) :
    BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
        (markedNeighborCountBits H a) =
      q * (neighborCoordinates H a).card := by
  classical
  have hlinear :
      BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
          (markedNeighborCountBits H a) =
        ∑ i : Fin H.card,
          BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
            (fun bits => neighborCoordinateWeight H a i *
              (if bits i then (1 : ℝ) else 0)) := by
    simp only [BernoulliFreedman.weightedMean, markedNeighborCountBits,
      Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hlinear]
  calc
    ∑ i : Fin H.card,
        BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
          (fun bits => neighborCoordinateWeight H a i *
            (if bits i then (1 : ℝ) else 0))
        = ∑ i : Fin H.card, neighborCoordinateWeight H a i * q := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
                (fun bits => neighborCoordinateWeight H a i *
                  (if bits i then (1 : ℝ) else 0))
                = neighborCoordinateWeight H a i *
                    BernoulliFreedman.weightedMean
                      (BernoulliFreedman.weight q)
                      (fun bits => if bits i then (1 : ℝ) else 0) := by
                  simp only [BernoulliFreedman.weightedMean, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro bits hbits
                  ring
            _ = neighborCoordinateWeight H a i * q := by
              rw [weightedMean_bit_true H.card q i]
    _ = q * (neighborCoordinates H a).card := by
      rw [← Finset.sum_mul, sum_neighborCoordinateWeight_eq_card]
      ring

theorem markedNeighborCountBits_coordinateOscillation
    (H : Hypergraph V) (a : {e // e ∈ H}) :
    ∀ i (bits bits' : Fin H.card → Bool),
      (∀ j, j ≠ i → bits j = bits' j) →
      |markedNeighborCountBits H a bits -
        markedNeighborCountBits H a bits'| ≤
          neighborCoordinateWeight H a i := by
  classical
  intro i bits bits' hbits
  unfold markedNeighborCountBits
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j, (neighborCoordinateWeight H a j *
          (if bits j then (1 : ℝ) else 0) -
        neighborCoordinateWeight H a j *
          (if bits' j then (1 : ℝ) else 0))|
        = |(neighborCoordinateWeight H a i *
              (if bits i then (1 : ℝ) else 0) -
            neighborCoordinateWeight H a i *
              (if bits' i then (1 : ℝ) else 0))| := by
          rw [Finset.sum_eq_single i]
          · intro j hj hji
            rw [hbits j hji]
            simp
          · simp
    _ ≤ neighborCoordinateWeight H a i := by
      by_cases hia : isNeighborCoordinate H a i <;>
        simp [neighborCoordinateWeight, hia] <;>
          cases bits i <;> cases bits' i <;> norm_num

theorem card_neighborCoordinates_le_edgeNeighborhood
    (H : Hypergraph V) (a : {e // e ∈ H}) :
    (neighborCoordinates H a).card ≤ (edgeNeighborhood H a.1).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun i : Fin H.card => ((edgeEquivFin H).symm i).1) ?_ ?_
  · intro i hi
    have hneighbor : isNeighborCoordinate H a i := by
      simpa [neighborCoordinates] using hi
    exact mem_edgeNeighborhood.mpr
      ⟨((edgeEquivFin H).symm i).2, by
        intro hd
        exact hneighbor.2 hd.symm⟩
  · intro i hi j hj hij
    apply (edgeEquivFin H).symm.injective
    exact Subtype.ext hij

theorem card_neighborCoordinates_le
    {H : Hypergraph V} (hH : IsUniform H 8) {D : ℕ}
    (hmax : MaxDegreeLE H D) (a : {e // e ∈ H}) :
    (neighborCoordinates H a).card ≤ 8 * D := by
  exact (card_neighborCoordinates_le_edgeNeighborhood H a).trans
    (card_edgeNeighborhood_le_mul (hH a.1 a.2) hmax)

/-- Exponential guard tail for the number of marked neighbors of one edge.
When the nibble bias is `q = p/D`, its variance proxy is at most `8p`,
independently of the number of vertices in the hypergraph. -/
theorem markedNeighborCountBits_upperTail
    (H : Hypergraph V) (a : {e // e ∈ H}) {q t : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t)
    (hden : 0 < q * (1 - q) *
        ∑ i : Fin H.card,
          (neighborCoordinateWeight H a i) ^ 2 + t) :
    BernoulliFreedman.eventMass (BernoulliFreedman.weight q)
        {bits | q * (neighborCoordinates H a).card + t ≤
          markedNeighborCountBits H a bits} ≤
      Real.exp (-(t ^ 2) /
        (4 * (q * (1 - q) *
          ∑ i : Fin H.card,
            (neighborCoordinateWeight H a i) ^ 2 + t))) := by
  have htail := BernoulliFreedman.upperTail H.card q
    (markedNeighborCountBits H a)
    (neighborCoordinateWeight H a)
    1 t hq0 hq1
    (fun i => by
      by_cases hi : isNeighborCoordinate H a i <;>
        simp [neighborCoordinateWeight, hi])
    (markedNeighborCountBits_coordinateOscillation H a)
    (by norm_num)
    (fun i => by
      by_cases hi : isNeighborCoordinate H a i <;>
        simp [neighborCoordinateWeight, hi])
    ht (by simpa using hden)
  simpa [weightedMean_markedNeighborCountBits H a q] using htail

/-- The root-degree potential as a real random variable on the canonical
Boolean product space of current edges. -/
noncomputable def rootPotentialBits (H : Hypergraph V) (x : V) :
    (Fin H.card → Bool) → ℝ := fun bits =>
  (potentialResidualDegree H (markingOfBits H bits) x : ℝ)

/-- Boolean vectors which agree off coordinate `i` induce edge markings which
agree off the edge enumerated by `i`. -/
theorem markingsAgreeOff_markingOfBits
    (H : Hypergraph V) {bits bits' : Fin H.card → Bool} {i : Fin H.card}
    (hbits : ∀ j, j ≠ i → bits j = bits' j) :
    MarkingsAgreeOff ((edgeEquivFin H).symm i)
      (markingOfBits H bits) (markingOfBits H bits') := by
  intro a hai
  apply hbits
  intro hcoord
  apply hai
  apply (edgeEquivFin H).injective
  simpa using hcoord

/-- Unstopped bounded differences for the root potential.  This estimate is
deliberately retained as a sound coarse fallback.  The sequential nibble uses
`rootResamplingBudget_le_markedNeighborCount` instead, after stopping at a
small marked-neighbor guard. -/
theorem rootPotentialBits_coordinateOscillation
    {H : Hypergraph V} (hH : IsUniform H 8) {D L : ℕ}
    (hmax : MaxDegreeLE H D) (hcodeg : MaxCodegreeLE H 2 L) (x : V) :
    ∀ i (bits bits' : Fin H.card → Bool),
      (∀ j, j ≠ i → bits j = bits' j) →
      |rootPotentialBits H x bits - rootPotentialBits H x bits'| ≤
        (8 * L * (1 + 8 * D) : ℕ) := by
  intro i bits bits' hbits
  let a : {e // e ∈ H} := (edgeEquivFin H).symm i
  have hagree : MarkingsAgreeOff a
      (markingOfBits H bits) (markingOfBits H bits') :=
    markingsAgreeOff_markingOfBits H hbits
  have hsharp := abs_potentialResidualDegree_sub_le_rootResamplingBudget
    hagree x
  have hcoarse := rootResamplingBudget_le_degreeScale hH hmax hcodeg
    (markingOfBits H bits) x a
  exact hsharp.trans (by exact_mod_cast hcoarse)

/-- On the local neighbor-count guard, changing one edge coordinate changes
the root potential by at most `8 L (1+K)`.  This is the increment cap used by
the stopped Doob martingale. -/
theorem rootPotentialBits_coordinateOscillation_of_neighborGuard
    {H : Hypergraph V} (hH : IsUniform H 8) {L : ℕ}
    (hcodeg : MaxCodegreeLE H 2 L) (x : V) (i : Fin H.card)
    (bits bits' : Fin H.card → Bool)
    (hbits : ∀ j, j ≠ i → bits j = bits' j) {K : ℝ}
    (hguard : markedNeighborCountBits H ((edgeEquivFin H).symm i) bits ≤ K) :
    |rootPotentialBits H x bits - rootPotentialBits H x bits'| ≤
      8 * L * (1 + K) := by
  let a : {e // e ∈ H} := (edgeEquivFin H).symm i
  have hagree : MarkingsAgreeOff a
      (markingOfBits H bits) (markingOfBits H bits') :=
    markingsAgreeOff_markingOfBits H hbits
  have hsharp := abs_potentialResidualDegree_sub_le_rootResamplingBudget
    hagree x
  have hbudget := rootResamplingBudget_le_markedNeighborCountBits
    hH hcodeg bits x a
  exact hsharp.trans (hbudget.trans <| by
    have hnonneg : (0 : ℝ) ≤ 8 * L := by positivity
    gcongr)

/-- A completely discharged (but coarse) one-round upper tail under
independent edge marks of bias `q`.  Its role is to validate the complete
finite-product probability interface; the guarded theorem improves the
variance and increment scales using the outcome-dependent budget above. -/
theorem rootPotentialBits_upperTail_coarse
    {H : Hypergraph V} (hH : IsUniform H 8) {D L : ℕ}
    (hmax : MaxDegreeLE H D) (hcodeg : MaxCodegreeLE H 2 L)
    (x : V) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t)
    (hden : 0 < q * (1 - q) *
        ∑ _i : Fin H.card, ((8 * L * (1 + 8 * D) : ℕ) : ℝ) ^ 2 +
          ((8 * L * (1 + 8 * D) : ℕ) : ℝ) * t) :
    BernoulliFreedman.eventMass (BernoulliFreedman.weight q)
        {bits | BernoulliFreedman.weightedMean
            (BernoulliFreedman.weight q) (rootPotentialBits H x) + t ≤
          rootPotentialBits H x bits} ≤
      Real.exp (-(t ^ 2) /
        (4 * (q * (1 - q) *
          ∑ _i : Fin H.card, ((8 * L * (1 + 8 * D) : ℕ) : ℝ) ^ 2 +
            ((8 * L * (1 + 8 * D) : ℕ) : ℝ) * t))) := by
  let C : ℝ := ((8 * L * (1 + 8 * D) : ℕ) : ℝ)
  apply BernoulliFreedman.upperTail H.card q (rootPotentialBits H x)
    (fun _ => C) C t hq0 hq1
  · intro i
    dsimp [C]
    positivity
  · intro i bits bits' hbits
    exact rootPotentialBits_coordinateOscillation hH hmax hcodeg x
      i bits bits' hbits
  · dsimp [C]
    positivity
  · intro i
    exact le_rfl
  · exact ht
  · simpa [C] using hden

/-- Double-count the pairs `(e,g)` in which `e` is at the root and `g`
meets a non-root vertex of `e`. -/
theorem sum_rootInfluenceWeight_eq (H : Hypergraph V) (x : V) :
    ∑ g ∈ H, rootInfluenceWeight H x g =
      ∑ e ∈ H.filter (fun e => x ∈ e),
        (H.filter fun g => ¬Disjoint (e.erase x) g).card := by
  simp only [rootInfluenceWeight, rootInfluenceEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hxe : x ∈ e
  · simp [hxe, Finset.not_disjoint_iff]
  · simp [hxe]

/-- Under maximum degree `D`, the total root influence is at most
`7 D d_H(x)` in an 8-uniform host. -/
theorem sum_rootInfluenceWeight_le
    {H : Hypergraph V} (hH : IsUniform H 8) {D : ℕ}
    (hmax : MaxDegreeLE H D) (x : V) :
    ∑ g ∈ H, rootInfluenceWeight H x g ≤ 7 * D * degree H x := by
  rw [sum_rootInfluenceWeight_eq]
  calc
    ∑ e ∈ H.filter (fun e => x ∈ e),
        (H.filter fun g => ¬Disjoint (e.erase x) g).card
        ≤ ∑ _e ∈ H.filter (fun e => x ∈ e), 7 * D := by
          apply Finset.sum_le_sum
          intro e he
          have heH := (Finset.mem_filter.mp he).1
          have hxe := (Finset.mem_filter.mp he).2
          have hsub : H.filter (fun g => ¬Disjoint (e.erase x) g) ⊆
              (e.erase x).biUnion (fun y => H.filter fun g => y ∈ g) := by
            intro g hg
            have hgH := (Finset.mem_filter.mp hg).1
            have hinter := (Finset.mem_filter.mp hg).2
            rw [Finset.not_disjoint_iff] at hinter
            obtain ⟨y, hyerase, hyg⟩ := hinter
            exact Finset.mem_biUnion.mpr
              ⟨y, hyerase, Finset.mem_filter.mpr ⟨hgH, hyg⟩⟩
          calc
            (H.filter fun g => ¬Disjoint (e.erase x) g).card
                ≤ ((e.erase x).biUnion
                    (fun y => H.filter fun g => y ∈ g)).card :=
              Finset.card_le_card hsub
            _ ≤ ∑ y ∈ e.erase x, (H.filter fun g => y ∈ g).card :=
              Finset.card_biUnion_le
            _ = ∑ y ∈ e.erase x, degree H y := by rfl
            _ ≤ ∑ _y ∈ e.erase x, D := by
              apply Finset.sum_le_sum
              intro y hy
              exact hmax y
            _ = (e.erase x).card * D := by simp
            _ = 7 * D := by
              rw [Finset.card_erase_of_mem hxe, hH e heH]
    _ = (H.filter fun e => x ∈ e).card * (7 * D) := by simp
    _ = degree H x * (7 * D) := rfl
    _ = 7 * D * degree H x := by ring

/-! ### Aggregate influence on the Bernoulli product space -/

/-- Total influence weight of marked edges, in canonical coordinates. -/
noncomputable def markedRootInfluenceBits (H : Hypergraph V) (x : V)
    (bits : Fin H.card → Bool) : ℝ :=
  ∑ i, (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) *
    (if bits i then 1 else 0)

theorem sum_rootInfluenceWeight_coordinates_eq (H : Hypergraph V) (x : V) :
    ∑ i : Fin H.card,
        rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 =
      ∑ g ∈ H, rootInfluenceWeight H x g := by
  classical
  calc
    (∑ i : Fin H.card,
        rootInfluenceWeight H x ((edgeEquivFin H).symm i).1) =
        ∑ a : {e // e ∈ H}, rootInfluenceWeight H x a.1 := by
      exact (edgeEquivFin H).symm.sum_comp
        (fun a : {e // e ∈ H} => rootInfluenceWeight H x a.1)
    _ = ∑ g ∈ H, rootInfluenceWeight H x g := by
      exact Finset.sum_attach H (fun g => rootInfluenceWeight H x g)

/-- Exact expectation of the marked total influence.  At nibble bias
`q=p/D`, the deterministic double-counting lemma above makes this `O(pD)`
for a root of degree `O(D)`. -/
theorem weightedMean_markedRootInfluenceBits
    (H : Hypergraph V) (x : V) (q : ℝ) :
    BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
        (markedRootInfluenceBits H x) =
      q * ∑ g ∈ H, rootInfluenceWeight H x g := by
  classical
  have hlinear :
      BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
          (markedRootInfluenceBits H x) =
        ∑ i : Fin H.card,
          BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
            (fun bits =>
              (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) *
                (if bits i then 1 else 0)) := by
    simp only [BernoulliFreedman.weightedMean, markedRootInfluenceBits,
      Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hlinear]
  calc
    (∑ i : Fin H.card,
        BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
          (fun bits =>
            (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) *
              (if bits i then 1 else 0))) =
        ∑ i : Fin H.card,
          (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) * q := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
            (fun bits =>
              (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) *
                (if bits i then 1 else 0)) =
            (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) *
              BernoulliFreedman.weightedMean (BernoulliFreedman.weight q)
                (fun bits => if bits i then (1 : ℝ) else 0) := by
          simp only [BernoulliFreedman.weightedMean, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro bits hbits
          ring
        _ = (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ) * q := by
          rw [weightedMean_bit_true H.card q i]
    _ = q * ∑ g ∈ H, rootInfluenceWeight H x g := by
      rw [← Finset.sum_mul]
      have hcast :
          (∑ i : Fin H.card,
              (rootInfluenceWeight H x ((edgeEquivFin H).symm i).1 : ℝ)) =
            ∑ g ∈ H, (rootInfluenceWeight H x g : ℝ) := by
        exact_mod_cast sum_rootInfluenceWeight_coordinates_eq H x
      rw [hcast]
      rw [Nat.cast_sum]
      ring

theorem sum_subtype_if_not_disjoint (H : Hypergraph V) (g : Finset V)
    (c : ℕ) :
    ∑ a : {e // e ∈ H}, (if ¬ Disjoint g a.1 then c else 0) =
      (edgeNeighborhood H g).card * c := by
  classical
  change (Finset.univ : Finset {e // e ∈ H}).sum
    (fun a => if ¬ Disjoint g a.1 then c else 0) = _
  rw [← Finset.attach_eq_univ, Finset.sum_attach H]
  simp [edgeNeighborhood, mul_comm]

/-- Pointwise aggregate resampling budget.  The marked-neighbor contribution
is charged in the opposite order: a marked edge `g` is charged once for each
host edge meeting it, at most `8D` times. -/
theorem sum_rootResamplingBudget_le
    {H : Hypergraph V} (hH : IsUniform H 8) {D : ℕ}
    (hmax : MaxDegreeLE H D) (mark : EdgeMarking H) (x : V) :
    ∑ a : {e // e ∈ H}, rootResamplingBudget H mark x a ≤
      (∑ g ∈ H, rootInfluenceWeight H x g) +
        8 * D *
          (∑ g ∈ markedEdges H mark, rootInfluenceWeight H x g) := by
  classical
  simp only [rootResamplingBudget, Finset.sum_add_distrib]
  apply Nat.add_le_add
  · exact le_of_eq (Finset.sum_attach H (fun g => rootInfluenceWeight H x g))
  · calc
      (∑ a : {e // e ∈ H},
          ∑ g ∈ markedEdgeNeighbors H mark a,
            rootInfluenceWeight H x g) =
          ∑ a : {e // e ∈ H},
            ∑ g ∈ markedEdges H mark,
              if g ≠ a.1 ∧ ¬Disjoint g a.1 then
                rootInfluenceWeight H x g else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            simp only [markedEdgeNeighbors, Finset.sum_filter]
      _ = ∑ g ∈ markedEdges H mark,
            ∑ a : {e // e ∈ H},
              if g ≠ a.1 ∧ ¬Disjoint g a.1 then
                rootInfluenceWeight H x g else 0 := by
          rw [Finset.sum_comm]
      _ ≤ ∑ g ∈ markedEdges H mark,
            8 * D * rootInfluenceWeight H x g := by
          apply Finset.sum_le_sum
          intro g hg
          have hgH := (mem_markedEdges.mp hg).choose
          calc
            (∑ a : {e // e ∈ H},
                if g ≠ a.1 ∧ ¬Disjoint g a.1 then
                  rootInfluenceWeight H x g else 0) ≤
                ∑ a : {e // e ∈ H},
                  if ¬Disjoint g a.1 then
                    rootInfluenceWeight H x g else 0 := by
                  apply Finset.sum_le_sum
                  intro a ha
                  by_cases hinter : ¬ Disjoint g a.1
                  · by_cases hga : g = a.1 <;> simp [hinter, hga]
                  · simp [hinter]
            _ = (edgeNeighborhood H g).card * rootInfluenceWeight H x g :=
              sum_subtype_if_not_disjoint H g _
            _ ≤ (8 * D) * rootInfluenceWeight H x g :=
              Nat.mul_le_mul_right _
                (card_edgeNeighborhood_le_mul (hH g hgH) hmax)
      _ = 8 * D *
            (∑ g ∈ markedEdges H mark, rootInfluenceWeight H x g) := by
          rw [Finset.mul_sum]

/-! ### Iterating guarded rounds -/

/-- A global mark vector restricts to the edges of every residual host.  This
keeps all rounds on one fixed finite outcome type while the residual edge set
changes. -/
abbrev GlobalEdgeMarking (V : Type*) := Finset V → Bool

def restrictGlobalMarking (H : Hypergraph V) (mark : GlobalEdgeMarking V) :
    EdgeMarking H := fun e => mark e.1

/-- Extend a marking of the current residual host to the fixed global edge
coordinate type.  Values away from the current host are irrelevant. -/
noncomputable def globalizeMarking (H : Hypergraph V) (mark : EdgeMarking H) :
    GlobalEdgeMarking V := fun e =>
  if he : e ∈ H then mark ⟨e, he⟩ else false

@[simp] theorem restrictGlobalMarking_globalizeMarking
    (H : Hypergraph V) (mark : EdgeMarking H) :
    restrictGlobalMarking H (globalizeMarking H mark) = mark := by
  funext e
  simp [restrictGlobalMarking, globalizeMarking]

/-- Residual host after processing a finite list of rounds.  The tail is
processed first, matching `runGreedy` in `ConflictFreeMatching.lean`. -/
def runNibbleResidual (H : Hypergraph V) :
    List (GlobalEdgeMarking V) → Hypergraph V
  | [] => H
  | mark :: marks =>
      let R := runNibbleResidual H marks
      nibbleResidual R (restrictGlobalMarking R mark)

/-- Union of all isolated marked edges accepted along the run. -/
def runNibbleMatching (H : Hypergraph V) :
    List (GlobalEdgeMarking V) → Hypergraph V
  | [] => ∅
  | mark :: marks =>
      let R := runNibbleResidual H marks
      isolatedMarkedEdges R (restrictGlobalMarking R mark) ∪
        runNibbleMatching H marks

@[simp] theorem runNibbleResidual_nil (H : Hypergraph V) :
    runNibbleResidual H [] = H := rfl

@[simp] theorem runNibbleMatching_nil (H : Hypergraph V) :
    runNibbleMatching H [] = ∅ := rfl

@[simp] theorem coveredVertices_union (M N : Hypergraph V) :
    coveredVertices (M ∪ N) = coveredVertices M ∪ coveredVertices N := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_coveredVertices.mp hv
    rw [Finset.mem_union] at he
    rcases he with heM | heN
    · exact Finset.mem_union_left _ (mem_coveredVertices.mpr ⟨e, heM, hve⟩)
    · exact Finset.mem_union_right _ (mem_coveredVertices.mpr ⟨e, heN, hve⟩)
  · intro hv
    rw [Finset.mem_union] at hv
    rcases hv with hvM | hvN
    · obtain ⟨e, heM, hve⟩ := mem_coveredVertices.mp hvM
      exact mem_coveredVertices.mpr ⟨e, Finset.mem_union_left _ heM, hve⟩
    · obtain ⟨e, heN, hve⟩ := mem_coveredVertices.mp hvN
      exact mem_coveredVertices.mpr ⟨e, Finset.mem_union_right _ heN, hve⟩

theorem deleteVertices_deleteVertices (H : Hypergraph V) (S T : Finset V) :
    deleteVertices (deleteVertices H S) T = deleteVertices H (S ∪ T) := by
  ext e
  simp only [mem_deleteVertices, Finset.disjoint_union_right]
  aesop

theorem isMatching_union_of_cross_disjoint {H M N : Hypergraph V}
    (hM : IsMatching H M) (hN : IsMatching H N)
    (hcross : ∀ e ∈ M, ∀ f ∈ N, Disjoint e f) :
    IsMatching H (M ∪ N) := by
  refine ⟨Finset.union_subset hM.1 hN.1, ?_⟩
  intro e he f hf hef
  rw [Finset.mem_union] at he hf
  rcases he with heM | heN <;> rcases hf with hfM | hfN
  · exact hM.2 heM hfM hef
  · exact hcross e heM f hfN
  · exact (hcross f hfM e heN).symm
  · exact hN.2 heN hfN hef

theorem runNibbleResidual_eq_delete (H : Hypergraph V)
    (marks : List (GlobalEdgeMarking V)) :
    runNibbleResidual H marks =
      deleteVertices H (coveredVertices (runNibbleMatching H marks)) := by
  induction marks with
  | nil =>
      ext e
      simp [deleteVertices, coveredVertices]
  | cons mark marks ih =>
      rw [runNibbleResidual, runNibbleMatching, coveredVertices_union]
      change deleteVertices (runNibbleResidual H marks)
          (coveredVertices
            (isolatedMarkedEdges (runNibbleResidual H marks)
              (restrictGlobalMarking (runNibbleResidual H marks) mark))) = _
      rw [ih, deleteVertices_deleteVertices]
      congr 1
      exact Finset.union_comm _ _

theorem runNibbleResidual_subset_host (H : Hypergraph V)
    (marks : List (GlobalEdgeMarking V)) :
    runNibbleResidual H marks ⊆ H := by
  rw [runNibbleResidual_eq_delete]
  exact Finset.filter_subset _ _

theorem runNibbleMatching_isMatching (H : Hypergraph V)
    (marks : List (GlobalEdgeMarking V)) :
    IsMatching H (runNibbleMatching H marks) := by
  induction marks with
  | nil => exact isMatching_empty H
  | cons mark marks ih =>
      let R := runNibbleResidual H marks
      let current := isolatedMarkedEdges R (restrictGlobalMarking R mark)
      have hcurrentR : IsMatching R current :=
        isolatedMarkedEdges_isMatching R (restrictGlobalMarking R mark)
      have hcurrentH : IsMatching H current :=
        ⟨hcurrentR.1.trans (runNibbleResidual_subset_host H marks), hcurrentR.2⟩
      rw [runNibbleMatching]
      apply isMatching_union_of_cross_disjoint hcurrentH ih
      intro e he f hf
      have heR := hcurrentR.1 he
      change e ∈ runNibbleResidual H marks at heR
      rw [runNibbleResidual_eq_delete] at heR
      have hedisj := (mem_deleteVertices.mp heR).2
      exact Finset.disjoint_of_subset_right (edge_subset_coveredVertices hf) hedisj

theorem runNibbleResidual_maxCodegreeLE {H : Hypergraph V} {j L : ℕ}
    (hcodeg : MaxCodegreeLE H j L) (marks : List (GlobalEdgeMarking V)) :
    MaxCodegreeLE (runNibbleResidual H marks) j L := by
  intro s hs
  exact (codegree_mono_hypergraph (runNibbleResidual_subset_host H marks) s).trans
    (hcodeg s hs)

theorem runNibbleMatching_card_covered {H : Hypergraph V}
    (hH : IsUniform H 8) (marks : List (GlobalEdgeMarking V)) :
    (coveredVertices (runNibbleMatching H marks)).card =
      8 * (runNibbleMatching H marks).card := by
  rw [card_coveredVertices_of_uniform_matching hH
    (runNibbleMatching_isMatching H marks)]
  omega

/-- Ground-set vertices not yet covered by the accumulated matching. -/
def runNibbleUncovered (H : Hypergraph V)
    (marks : List (GlobalEdgeMarking V)) : Finset V :=
  Finset.univ \ coveredVertices (runNibbleMatching H marks)

theorem coveredVertices_subset_univ (M : Hypergraph V) :
    coveredVertices M ⊆ (Finset.univ : Finset V) := by
  exact Finset.subset_univ _

/-- The covered and uncovered ground-set vertices partition the finite type. -/
theorem runNibble_covered_add_uncovered (H : Hypergraph V)
    (marks : List (GlobalEdgeMarking V)) :
    (coveredVertices (runNibbleMatching H marks)).card +
      (runNibbleUncovered H marks).card = Fintype.card V := by
  rw [add_comm]
  exact Finset.card_sdiff_add_card_eq_card
    (coveredVertices_subset_univ (runNibbleMatching H marks))

/-- Exact size bookkeeping for an 8-uniform nibble run. -/
theorem runNibble_matching_eight_mul_add_uncovered {H : Hypergraph V}
    (hH : IsUniform H 8) (marks : List (GlobalEdgeMarking V)) :
    8 * (runNibbleMatching H marks).card +
      (runNibbleUncovered H marks).card = Fintype.card V := by
  rw [← runNibbleMatching_card_covered hH marks]
  exact runNibble_covered_add_uncovered H marks

theorem runNibble_matching_nearPerfect_of_uncovered_le {H : Hypergraph V}
    (hH : IsUniform H 8) (marks : List (GlobalEdgeMarking V)) {u : ℕ}
    (huncovered : (runNibbleUncovered H marks).card ≤ u) :
    Fintype.card V ≤ 8 * (runNibbleMatching H marks).card + u := by
  rw [← runNibble_matching_eight_mul_add_uncovered hH marks]
  exact Nat.add_le_add_left huncovered _

end NibbleRound

/-! ## Extracting a good outcome from a finite Freedman estimate -/

namespace Pippenger

open Freedman

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]

/-- If a finite event has mass strictly below the total mass, some outcome
outside the event has positive mass. -/
theorem exists_pos_mass_not_mem
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    {A : Finset Ω} (hA : eventMass p A < 1) :
    ∃ ω, 0 < p ω ∧ ω ∉ A := by
  by_contra hnot
  push Not at hnot
  have hzero : ∀ ω ∉ A, p ω = 0 := by
    intro ω hω
    apply le_antisymm
    · exact le_of_not_gt (fun hpω => hω (hnot ω hpω))
    · exact hp ω
  have hsplit : (∑ ω, p ω) = eventMass p A := by
    rw [← Finset.sum_subset (Finset.subset_univ A)]
    · rfl
    · intro ω hωuniv hωA
      exact hzero ω hωA
  rw [hp_one] at hsplit
  linarith

/-- A denominator-form Freedman bound strictly below one produces a concrete
positive-mass trajectory below the upper tail threshold.  This theorem is
the finite outcome-extraction step used by a random nibble after the
conditional moment estimates have been verified. -/
theorem exists_outcome_partialSum_lt_of_freedman
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    {info : ℕ → Ω → ι} (hfil : IsFiltration info)
    {d : ℕ → Ω → ℝ} (hadapted : ∀ k, KnownAt info (k + 1) (d k))
    {v : ℕ → ℝ} (hmom : ConditionalMomentBounds p info d v)
    {R t V : ℝ} (hR0 : 0 ≤ R) (ht : 0 ≤ t) (hV0 : 0 ≤ V)
    (hden : 0 < V + R * t)
    (hR : ∀ k ω, |d k ω| ≤ R) {n : ℕ}
    (hV : ∑ k ∈ Finset.range n, v k ≤ V)
    (hexp : Real.exp (-(t ^ 2) / (4 * (V + R * t))) < 1) :
    ∃ ω, 0 < p ω ∧ partialSum d n ω < t := by
  let A : Finset Ω := Finset.univ.filter fun ω => t ≤ partialSum d n ω
  have hmass : eventMass p A < 1 := by
    refine lt_of_le_of_lt ?_ hexp
    exact freedman hp hp_one hfil hadapted hmom hR0 ht hV0 hden hR hV
  obtain ⟨ω, hpω, hωA⟩ := exists_pos_mass_not_mem hp hp_one hmass
  refine ⟨ω, hpω, ?_⟩
  simpa [A] using hωA

end Pippenger

end Erdos136

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos752.Erdos752AssemblyAlt
import ErdosProblems.Erdos752.Erdos752BFS
import ErdosProblems.Erdos752.Erdos752Branch
import ErdosProblems.Erdos752.Erdos752Parent
import ErdosProblems.Erdos752.Erdos752PathSide

/-!
# Closing a path in two breadth-first layers

This file proves the path-assembly lemma used for Erdős Problem 752.  A
long path in two consecutive breadth-first layers has many vertices in the
lower layer.  Coherent breadth-first parent paths split those vertices into
two branches below their last common ancestor.  Closing path prefixes through
the parent tree gives distinct cycle lengths, with an explicit factor `8`.
-/

open Function Set SimpleGraph

namespace Erdos752

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- The two-layer slice is a subgraph of the ambient graph. -/
private lemma bfsPair_le (G : SimpleGraph V) (root : V) (i : ℕ) :
    bfsPair G root i ≤ G := by
  exact SimpleGraph.between_le

/-- A nontrivial walk in a two-layer slice only uses vertices in its two
defining layers. -/
private lemma mem_lower_or_upper_of_mem_bfsPair_walk
    {G : SimpleGraph V} {root x y v : V} {i : ℕ}
    (p : (bfsPair G root i).Walk x y) (hp : 0 < p.length)
    (hv : v ∈ p.support) :
    G.dist root v = i ∨ G.dist root v = i + 1 := by
  have hn : ¬p.Nil := by simpa [Walk.not_nil_iff_lt_length] using hp
  have hsupp : v ∈ (bfsPair G root i).support :=
    SimpleGraph.mem_support_of_mem_walk_support p hn hv
  simpa only [mem_bfsLayer, Set.mem_union] using bfsPair_support_subset hsupp

/-- Every vertex of a nontrivial two-level path has ambient breadth-first
depth at least the lower-layer index. -/
private lemma lower_le_dist_of_mem_bfsPair_walk
    {G : SimpleGraph V} {root x y v : V} {i : ℕ}
    (p : (bfsPair G root i).Walk x y) (hp : 0 < p.length)
    (hv : v ∈ p.support) : i ≤ G.dist root v := by
  rcases mem_lower_or_upper_of_mem_bfsPair_walk p hp hv with h | h <;> omega

/--
A simple path of length at least four in two consecutive BFS layers gives a
finset of cycle lengths in the ambient connected graph.  The numerical loss
is exactly the factor eight used in the distinct-length proof.

The lower bound four is sharp for this purely path-local statement: a
length-two upper--lower--upper path may occur in a tree.  In the application
the DFS path has length at least `2 * m` with `m ≥ 2`.
-/
theorem exists_cycle_lengths_of_bfsPair_path [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (root : V) (i : ℕ)
    {x y : V} (p : (bfsPair G root i).Walk x y)
    (hp : p.IsPath) (hlen : 4 ≤ p.length) :
    ∃ L : Finset ℕ, p.length ≤ 8 * L.card ∧
      ∀ l ∈ L, ∃ v : V, ∃ c : G.Walk v v,
        c.IsCycle ∧ c.length = l := by
  classical
  let H := bfsPair G root i
  let S : Finset V := pathSideVertices p (bfsLayer G root i)
  have hbi : H.IsBipartiteWith (bfsLayer G root i)
      (bfsLayer G root (i + 1)) := by
    exact SimpleGraph.between_isBipartiteWith (bfsLayer_disjoint (by omega))
  have hpS : p.length ≤ 2 * S.card := by
    exact length_le_twice_card_pathSideVertices hbi p hp
  have hScard : 2 ≤ S.card := by omega
  have hSmem_support : ∀ s ∈ S, s ∈ p.support := by
    intro s hs
    exact List.mem_toFinset.mp (Finset.mem_filter.mp hs).1
  have hSdist : ∀ s ∈ S, G.dist root s = i := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2
  obtain ⟨j, hji, _z, A, B, a, haA, _hAne, hAS, hBdef, _hAhalf,
      hSB, hdetourB⟩ :=
    exists_bfs_branch_uniform_detours hconn root S hScard i hSdist
  have haS : a ∈ S := hAS haA
  have haSupport : a ∈ p.support := hSmem_support a haS
  have hBsupport : ∀ b ∈ B, b ∈ p.support := by
    intro b hb
    apply hSmem_support b
    rw [hBdef] at hb
    exact (Finset.mem_sdiff.mp hb).1
  obtain ⟨endpoint, qH, B₀, _hend, hqHPath, hqHSupport, hB₀B,
      hB₀q, hBB₀⟩ :=
    exists_endpoint_side_subpath p hp haSupport B hBsupport
  let q : G.Walk a endpoint := qH.mapLe (bfsPair_le G root i)
  have hqPath : q.IsPath := by
    exact hqHPath.mapLe (bfsPair_le G root i)
  have hB₀q' : ∀ b ∈ B₀, b ∈ q.support := by
    intro b hb
    simpa [q] using hB₀q b hb
  have hqLevel : ∀ v ∈ q.support, i ≤ G.dist root v := by
    intro v hv
    have hvH : v ∈ qH.support := by simpa [q] using hv
    exact lower_le_dist_of_mem_bfsPair_walk p (by omega)
      (hqHSupport v hvH)
  have hdetour : ∀ b : ↑B₀, ∃ qb : G.Walk a b.1,
      qb.IsPath ∧ qb.length = 2 * (i - j) ∧
        ∀ v ∈ qb.support, v ≠ a → v ≠ b.1 → G.dist root v < i := by
    intro b
    have hbB : b.1 ∈ B := hB₀B b.2
    exact hdetourB b.1 hbB
  let detour : ∀ b : ↑B₀, G.Walk a b.1 :=
    fun b ↦ Classical.choose (hdetour b)
  have hdetourPath : ∀ b, (detour b).IsPath := by
    intro b
    exact (Classical.choose_spec (hdetour b)).1
  have hdetourLength : ∀ b, (detour b).length = 2 * (i - j) := by
    intro b
    exact (Classical.choose_spec (hdetour b)).2.1
  have hdetourBelow : ∀ b v, v ∈ (detour b).support →
      v ≠ a → v ≠ b.1 → G.dist root v < i := by
    intro b v hv hva hvb
    exact (Classical.choose_spec (hdetour b)).2.2 v hv hva hvb
  have hdetourLong : 1 < 2 * (i - j) := by omega
  obtain ⟨L, hLcard, hLcycles⟩ :=
    exists_distinct_cycle_lengths_of_uniform_detours q hqPath B₀ hB₀q'
      hqLevel detour hdetourPath hdetourLength hdetourLong hdetourBelow
  refine ⟨L, ?_, hLcycles⟩
  calc
    p.length ≤ 2 * S.card := hpS
    _ ≤ 2 * (2 * B.card) := Nat.mul_le_mul_left 2 hSB
    _ ≤ 2 * (2 * (2 * B₀.card)) := by
      gcongr
    _ = 8 * L.card := by omega

/-- The same assembly theorem for a path lying in any subgraph of the
two-level slice. -/
theorem exists_cycle_lengths_of_path_in_subgraph_bfsPair [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (root : V) (i : ℕ)
    {K : SimpleGraph V} (hK : K ≤ bfsPair G root i)
    {x y : V} (p : K.Walk x y) (hp : p.IsPath) (hlen : 4 ≤ p.length) :
    ∃ L : Finset ℕ, p.length ≤ 8 * L.card ∧
      ∀ l ∈ L, ∃ v : V, ∃ c : G.Walk v v,
        c.IsCycle ∧ c.length = l := by
  let p' : (bfsPair G root i).Walk x y := p.mapLe hK
  have hp' : p'.IsPath := hp.mapLe hK
  have hlen' : 4 ≤ p'.length := by simpa [p'] using hlen
  obtain ⟨L, hL, hcycles⟩ :=
    exists_cycle_lengths_of_bfsPair_path G hconn root i p' hp' hlen'
  refine ⟨L, ?_, hcycles⟩
  simpa [p'] using hL

/-- Version used by the minimum-degree core: the path lives in the graph
induced by a slice subgraph on its support. -/
theorem exists_cycle_lengths_of_induce_support_path [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (root : V) (i : ℕ)
    {K : SimpleGraph V} (hK : K ≤ bfsPair G root i)
    {x y : K.support} (p : (K.induce K.support).Walk x y)
    (hp : p.IsPath) (hlen : 4 ≤ p.length) :
    ∃ L : Finset ℕ, p.length ≤ 8 * L.card ∧
      ∀ l ∈ L, ∃ v : V, ∃ c : G.Walk v v,
        c.IsCycle ∧ c.length = l := by
  let inclusion : K.induce K.support →g K :=
    (SimpleGraph.Embedding.induce (G := K) K.support).toHom
  let pK := p.map inclusion
  have hpK : pK.IsPath := hp.map Subtype.val_injective
  have hpKlen : pK.length = p.length := by
    dsimp only [pK]
    exact p.length_map inclusion
  have hlenK : 4 ≤ pK.length := by omega
  obtain ⟨L, hL, hcycles⟩ :=
    exists_cycle_lengths_of_path_in_subgraph_bfsPair G hconn root i hK
      pK hpK hlenK
  refine ⟨L, ?_, hcycles⟩
  omega

end

end Erdos752

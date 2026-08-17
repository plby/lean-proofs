/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Path-side counting for Erdős Problem 752

This file contains two elementary facts about a simple path used in the
cycle-length assembly argument.

* A path in a graph bipartite between `s` and `t` has at least half as many
  vertices in either side as it has edges.
* If a vertex `a` splits a path into its two endpoint-side subpaths, then one
  of those subpaths contains at least half of any prescribed finite set of
  vertices on the path.

The second statement returns the actual endpoint, subpath, and retained
finset, so no choice or cardinality bookkeeping remains for its callers.
-/

open Function Set SimpleGraph

namespace Erdos752

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- The distinct vertices of a walk which lie in a prescribed side. -/
def pathSideVertices {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (s : Set V) : Finset V :=
  p.support.toFinset.filter (fun v ↦ v ∈ s)

/--
The simultaneous inductive estimate behind `length_le_twice_card_pathSideVertices`.
If a walk starts in the left side, its number of vertices (edges plus one)
is at most twice its number of left-side vertices.  If it starts in the
right side, its number of edges is at most twice that number.
-/
private lemma path_length_countP_bounds {G : SimpleGraph V} {s t : Set V}
    (hbi : G.IsBipartiteWith s t) {x y : V} (p : G.Walk x y) :
    (x ∈ s → p.length + 1 ≤ 2 * p.support.countP (fun v ↦ v ∈ s)) ∧
      (x ∈ t → p.length ≤ 2 * p.support.countP (fun v ↦ v ∈ s)) := by
  induction p with
  | nil =>
      constructor
      · intro hx
        simp [hx]
      · intro _hx
        simp
  | @cons x z y hxz p ih =>
      constructor
      · intro hxs
        have hzt : z ∈ t := hbi.mem_of_mem_adj hxs hxz
        have htail := ih.2 hzt
        simp only [Walk.length_cons, Walk.support_cons, List.countP_cons]
        simp [hxs]
        omega
      · intro hxt
        have hzs : z ∈ s := hbi.mem_of_mem_adj' hxt hxz.symm
        have htail := ih.1 hzs
        have hnot : x ∉ s := Set.disjoint_right.mp hbi.disjoint hxt
        simp only [Walk.length_cons, Walk.support_cons, List.countP_cons]
        simp [hnot]
        omega

/--
If `p` is a simple path in a graph whose edges run between `s` and `t`, then
the number of edges of `p` is at most twice the number of its vertices in
`s`.  The statement is valid for either endpoint parity, including the
degenerate path of length zero.
-/
theorem length_le_twice_card_pathSideVertices {G : SimpleGraph V}
    {s t : Set V} (hbi : G.IsBipartiteWith s t) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) :
    p.length ≤ 2 * (pathSideVertices p s).card := by
  classical
  have hcount : (pathSideVertices p s).card =
      p.support.countP (fun v ↦ v ∈ s) := by
    exact hp.support_nodup.card_eq_countP
  rw [hcount]
  cases p with
  | nil => simp
  | @cons x z y hxz p =>
      rcases hbi.mem_of_adj hxz with hxs | hxt
      · exact (path_length_countP_bounds hbi (.cons hxz p)).1 hxs.1 |>.trans' (by omega)
      · exact (path_length_countP_bounds hbi (.cons hxz p)).2 hxt.1

/-- The vertices of `B` which occur on a given walk. -/
private def verticesOnWalk {G : SimpleGraph V} {x y : V}
    (B : Finset V) (p : G.Walk x y) : Finset V :=
  B.filter (fun v ↦ v ∈ p.support)

/-- Every vertex on a walk lies on one of the two pieces obtained by cutting at `a`. -/
private lemma mem_takeUntil_or_dropUntil {G : SimpleGraph V} {x y a v : V}
    (p : G.Walk x y) (ha : a ∈ p.support) (hv : v ∈ p.support) :
    v ∈ (p.takeUntil a ha).support ∨ v ∈ (p.dropUntil a ha).support := by
  have hv' : v ∈ ((p.takeUntil a ha).append (p.dropUntil a ha)).support := by
    simpa only [p.take_spec ha] using hv
  simpa only [Walk.mem_support_append_iff] using hv'

/-- The prescribed vertices are covered by the two endpoint-side pieces. -/
private lemma card_le_endpoint_pieces {G : SimpleGraph V} {x y a : V}
    (p : G.Walk x y) (ha : a ∈ p.support) (B : Finset V)
    (hB : ∀ b ∈ B, b ∈ p.support) :
    B.card ≤ (verticesOnWalk B (p.takeUntil a ha).reverse).card +
      (verticesOnWalk B (p.dropUntil a ha)).card := by
  classical
  let B₀ := verticesOnWalk B (p.takeUntil a ha).reverse
  let B₁ := verticesOnWalk B (p.dropUntil a ha)
  have hsubset : B ⊆ B₀ ∪ B₁ := by
    intro b hb
    have hbpieces := mem_takeUntil_or_dropUntil p ha (hB b hb)
    rcases hbpieces with hb₀ | hb₁
    · apply Finset.mem_union_left B₁
      simp only [B₀, verticesOnWalk, Finset.mem_filter, hb, true_and]
      simpa [Walk.support_reverse] using hb₀
    · apply Finset.mem_union_right B₀
      simpa only [B₁, verticesOnWalk, Finset.mem_filter, hb, true_and]
  calc
    B.card ≤ (B₀ ∪ B₁).card := Finset.card_le_card hsubset
    _ ≤ B₀.card + B₁.card := Finset.card_union_le _ _

/--
Cut a simple path `p` at a vertex `a`.  For every finite set `B` of vertices
on `p`, one of the two subpaths from `a` to an endpoint contains a subset
`B₀ ⊆ B` of at least half the vertices of `B`.

The witness `q` is literally either the reversal of the prefix ending at
`a`, or the suffix starting at `a`; hence it is a simple path, has an endpoint
of `p` as its far endpoint, and has support contained in that of `p`.
-/
theorem exists_endpoint_side_subpath {G : SimpleGraph V} {x y a : V}
    (p : G.Walk x y) (hp : p.IsPath) (ha : a ∈ p.support)
    (B : Finset V) (hB : ∀ b ∈ B, b ∈ p.support) :
    ∃ (z : V) (q : G.Walk a z) (B₀ : Finset V),
      (z = x ∨ z = y) ∧ q.IsPath ∧
      (∀ v ∈ q.support, v ∈ p.support) ∧
      B₀ ⊆ B ∧ (∀ b ∈ B₀, b ∈ q.support) ∧
      B.card ≤ 2 * B₀.card := by
  classical
  let q₀ : G.Walk a x := (p.takeUntil a ha).reverse
  let q₁ : G.Walk a y := p.dropUntil a ha
  let B₀ := verticesOnWalk B q₀
  let B₁ := verticesOnWalk B q₁
  have hcard : B.card ≤ B₀.card + B₁.card := by
    simpa only [q₀, q₁, B₀, B₁] using
      card_le_endpoint_pieces p ha B hB
  by_cases hlarge : B₁.card ≤ B₀.card
  · refine ⟨x, q₀, B₀, Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hp.takeUntil ha).reverse
    · intro v hv
      apply p.support_takeUntil_subset_support ha
      simpa [q₀, Walk.support_reverse] using hv
    · intro b hb
      exact (Finset.mem_filter.mp hb).1
    · intro b hb
      exact (Finset.mem_filter.mp hb).2
    · omega
  · have hlarge' : B₀.card ≤ B₁.card := by omega
    refine ⟨y, q₁, B₁, Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact hp.dropUntil ha
    · intro v hv
      exact p.support_dropUntil_subset_support ha hv
    · intro b hb
      exact (Finset.mem_filter.mp hb).1
    · intro b hb
      exact (Finset.mem_filter.mp hb).2
    · omega

end

end Erdos752

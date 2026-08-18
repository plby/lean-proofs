/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueLevels
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# A canonical parent presentation of a finite BFS tree

For the ordered-level lemma we only need a parent map which decreases graph
distance from a fixed root by exactly one.  This file constructs such a map
from shortest paths and records its iteration laws.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

theorem exists_bfs_parent
    {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    (x v : V) (hv : 0 < G.dist x v) :
    ∃ u : V, G.Adj u v ∧ G.dist x u + 1 = G.dist x v := by
  obtain ⟨p, -, hp⟩ := hconn.exists_path_of_dist x v
  have hpnon : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp]
    exact hv
  let u := p.penultimate
  have huv : G.Adj u v := p.adj_penultimate hpnon
  refine ⟨u, huv, ?_⟩
  have hdrop : G.dist x u ≤ G.dist x v - 1 := by
    calc
      G.dist x u ≤ p.dropLast.length := SimpleGraph.dist_le p.dropLast
      _ = p.length - 1 := p.length_dropLast
      _ = G.dist x v - 1 := by rw [hp]
  have hlower : G.dist x v ≤ G.dist x u + 1 := by
    have htri := huv.reachable.dist_triangle_right x
    have huvDist : G.dist u v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr huv
    simpa [huvDist] using htri
  omega

/-- A breadth-first parent map rooted at `root`. -/
structure BFSTree {V : Type*} (G : SimpleGraph V) (root : V) where
  parent : V → V
  parent_of_dist_zero : ∀ v, G.dist root v = 0 → parent v = v
  adj_parent : ∀ v, 0 < G.dist root v → G.Adj (parent v) v
  dist_parent : ∀ v, 0 < G.dist root v →
    G.dist root (parent v) + 1 = G.dist root v

/-- Every connected graph admits a BFS parent map from any root. -/
def BFSTree.ofConnected {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (root : V) : BFSTree G root where
  parent v := if hv : 0 < G.dist root v then
    Classical.choose (exists_bfs_parent hconn root v hv) else v
  parent_of_dist_zero v hv := by
    simp [hv]
  adj_parent v hv := by
    simp only [dif_pos hv]
    exact (Classical.choose_spec (exists_bfs_parent hconn root v hv)).1
  dist_parent v hv := by
    simp only [dif_pos hv]
    exact (Classical.choose_spec (exists_bfs_parent hconn root v hv)).2

namespace BFSTree

variable {V : Type*} {G : SimpleGraph V} {root : V}

/-- The `r`th ancestor under the parent map. -/
def ancestor (T : BFSTree G root) (r : ℕ) (v : V) : V :=
  T.parent^[r] v

@[simp] theorem ancestor_zero (T : BFSTree G root) (v : V) :
    T.ancestor 0 v = v := rfl

@[simp] theorem ancestor_succ (T : BFSTree G root) (r : ℕ) (v : V) :
  T.ancestor (r + 1) v = T.parent (T.ancestor r v) := by
  simp [ancestor, Function.iterate_succ_apply']

theorem parent_ancestor (T : BFSTree G root) (r : ℕ) (v : V) :
    T.parent (T.ancestor r v) = T.ancestor r (T.parent v) := by
  rw [← T.ancestor_succ r v]
  simp [ancestor, Function.iterate_succ_apply]

theorem ancestor_succ_parent (T : BFSTree G root) (r : ℕ) (v : V) :
    T.ancestor (r + 1) v = T.ancestor r (T.parent v) := by
  simp [ancestor, Function.iterate_succ_apply]

/-- Before the root is reached, every parent iteration decreases distance
by exactly one. -/
theorem dist_ancestor_add
    (T : BFSTree G root) (v : V) :
    ∀ r : ℕ, r ≤ G.dist root v →
      G.dist root (T.ancestor r v) + r = G.dist root v := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ih =>
      have hrle : r ≤ G.dist root v := by omega
      have hih := ih hrle
      have hpos : 0 < G.dist root (T.ancestor r v) := by omega
      rw [ancestor_succ]
      have hp := T.dist_parent (T.ancestor r v) hpos
      omega

theorem dist_ancestor
    (T : BFSTree G root) (v : V) {r : ℕ}
    (hr : r ≤ G.dist root v) :
    G.dist root (T.ancestor r v) = G.dist root v - r := by
  have := T.dist_ancestor_add v r hr
  omega

/-- At its distance from the root, the ancestor chain reaches the root. -/
theorem ancestor_dist_eq_root
    (T : BFSTree G root) (hconn : G.Connected) (v : V) :
    T.ancestor (G.dist root v) v = root := by
  have := T.dist_ancestor v (r := G.dist root v) le_rfl
  exact ((hconn.dist_eq_zero_iff).mp (by simpa using this)).symm

/-- Consecutive ancestors are adjacent until the root is reached. -/
theorem adj_ancestor_succ
    (T : BFSTree G root) (v : V) {r : ℕ}
    (hr : r < G.dist root v) :
    G.Adj (T.ancestor (r + 1) v) (T.ancestor r v) := by
  rw [ancestor_succ]
  apply T.adj_parent
  have hd := T.dist_ancestor v (Nat.le_of_lt hr)
  omega

/-- Once two ancestor chains meet, all later ancestors agree. -/
theorem ancestor_add_eq_of_ancestor_eq
    (T : BFSTree G root) {u v : V} {r : ℕ}
    (h : T.ancestor r u = T.ancestor r v) (s : ℕ) :
    T.ancestor (r + s) u = T.ancestor (r + s) v := by
  rw [Nat.add_comm]
  simp only [ancestor, Function.iterate_add_apply]
  change T.parent^[s] (T.ancestor r u) =
    T.parent^[s] (T.ancestor r v)
  rw [h]

end BFSTree

end Erdos570

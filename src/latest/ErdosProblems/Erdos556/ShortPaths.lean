import ErdosProblems.Erdos556.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Short paths in graphs of large minimum degree

The open neighbourhoods at every third position on a shortest path are
disjoint. Counting these neighbourhoods gives the diameter estimate used
when constructing connecting reservoirs.
-/

namespace Erdos556

open SimpleGraph

theorem dist_getVert_of_shortest {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hsub := ((p.take j).isSubwalk_drop i).trans (p.isSubwalk_take j)
  have h := length_eq_dist_of_subwalk hp hsub
  simpa only [Walk.drop_length, Walk.take_length, Walk.take_getVert,
    inf_eq_left.mpr hj, inf_eq_right.mpr hij] using h.symm

theorem no_common_neighbor_of_shortest_gap {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j : ℕ} (hij : i + 3 ≤ j) (hj : j ≤ p.length) (z : V) :
    ¬ (G.Adj (p.getVert i) z ∧ G.Adj (p.getVert j) z) := by
  rintro ⟨hi, hjz⟩
  have hdist := G.dist_le (Walk.cons hi (Walk.cons hjz.symm Walk.nil))
  rw [dist_getVert_of_shortest p hp (by omega) hj] at hdist
  simp only [Walk.length_cons, Walk.length_nil] at hdist
  omega

/-- A shortest path meets pairwise disjoint open neighbourhoods at positions
`0, 3, 6, ...`. -/
theorem shortest_path_neighborhood_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (d : ℕ) (hdeg : ∀ w, d ≤ G.degree w) :
    (p.length / 3 + 1) * d ≤ Fintype.card V := by
  classical
  let I := Fin (p.length / 3 + 1)
  let W (i : I) := G.neighborSet (p.getVert (3 * i.val))
  let f : (Σ i : I, W i) → V := fun x => x.2.val
  have hindex (i : I) : 3 * i.val ≤ p.length := by
    have hi := i.isLt
    omega
  have hinj : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hij : i = j := by
      by_contra hne
      have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hij | hji
      · apply no_common_neighbor_of_shortest_gap p hp
          (i := 3 * i.val) (j := 3 * j.val) (by omega) (hindex j) x.val
        refine ⟨x.property, ?_⟩
        have heq : x.val = y.val := hxy
        rw [heq]
        exact y.property
      · apply no_common_neighbor_of_shortest_gap p hp
          (i := 3 * j.val) (j := 3 * i.val) (by omega) (hindex i) y.val
        refine ⟨y.property, ?_⟩
        have heq : x.val = y.val := hxy
        rw [← heq]
        exact x.property
    subst j
    have heq : x = y := Subtype.ext hxy
    subst y
    rfl
  have hc := Fintype.card_le_of_injective f hinj
  have hsum : (p.length / 3 + 1) * d ≤ Fintype.card (Σ i : I, W i) := by
    rw [Fintype.card_sigma]
    calc
      (p.length / 3 + 1) * d = ∑ _i : I, d := by simp [I]
      _ ≤ ∑ i : I, Fintype.card (W i) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [W, card_neighborSet_eq_degree] using hdeg (p.getVert (3 * i.val))
  exact hsum.trans hc

/-- A division-free diameter bound, suitable for later real-valued estimates. -/
theorem exists_short_path_of_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ w, d ≤ G.degree w) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ d * p.length < 3 * Fintype.card V := by
  obtain ⟨p, hp, hdist⟩ := hconn.exists_path_of_dist u v
  refine ⟨p, hp, ?_⟩
  have hc := shortest_path_neighborhood_count G p hdist d hdeg
  have hlen : p.length < 3 * (p.length / 3 + 1) := by omega
  nlinarith

#print axioms exists_short_path_of_min_degree

end Erdos556

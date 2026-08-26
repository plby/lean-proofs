import ErdosProblems.Erdos73.GraphPaths

/-! A simple path cannot enter a region through a cutset that is a clique in that path. -/

namespace Erdos73Infrastructure.SimpleGraph.GraphPath

open _root_.SimpleGraph Finset

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

theorem indices_consecutive_of_edge (P : GraphPath G) {i j : ℕ}
    (hi : i ≤ P.walk.length) (hj : j ≤ P.walk.length)
    (he : s(P.walk.getVert i, P.walk.getVert j) ∈ P.edgeSet) : i + 1 = j ∨ j + 1 = i := by
  have ha := Walk.adj_toSubgraph_iff_mem_edges.mpr (List.mem_toFinset.mp he)
  obtain ⟨r, hr, hrl⟩ := P.walk.toSubgraph_adj_iff.mp ha
  rcases Sym2.eq_iff.mp hr with ⟨hri, hrj⟩ | ⟨hrj, hri⟩
  · have hi' := P.isPath.getVert_injOn (show r ≤ P.walk.length by omega) hi hri
    have hj' := P.isPath.getVert_injOn (show r + 1 ≤ P.walk.length by omega) hj hrj
    omega
  · have hj' := P.isPath.getVert_injOn (show r ≤ P.walk.length by omega) hj hrj
    have hi' := P.isPath.getVert_injOn (show r + 1 ≤ P.walk.length by omega) hi hri
    omega

theorem disjoint_region_of_pathClique_cut (P : GraphPath G) (S C : Finset V)
    (hs : P.source ∉ S) (ht : P.target ∉ S)
    (hcut : ∀ x ∈ P.vertexSet, x ∈ S → ∀ y ∈ P.vertexSet,
      y ∉ S → G.Adj x y → y ∈ C)
    (hclique : ∀ a ∈ C, a ∈ P.vertexSet → ∀ b ∈ C, b ∈ P.vertexSet →
      a ≠ b → s(a, b) ∈ P.edgeSet) : Disjoint P.vertexSet S := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvP hvS
  obtain ⟨r, hr, hrl⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hvP)
  let T := (Finset.range (P.walk.length + 1)).filter (fun i => P.walk.getVert i ∈ S)
  have hT (i : ℕ) : i ∈ T ↔ i ≤ P.walk.length ∧ P.walk.getVert i ∈ S := by
    simp only [T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hne : T.Nonempty := ⟨r, (hT r).mpr ⟨hrl, hr ▸ hvS⟩⟩
  obtain ⟨i, hiT, hmin⟩ := T.exists_min_image id hne
  obtain ⟨j, hjT, hmax⟩ := T.exists_max_image id hne
  have hi := (hT i).mp hiT
  have hj := (hT j).mp hjT
  have hij : i ≤ j := hmin j hjT
  have hi0 : 0 < i := by
    by_contra h
    have he : i = 0 := by omega
    exact hs (by simpa only [he, Walk.getVert_zero] using hi.2)
  have hjl : j < P.walk.length := by
    by_contra h
    have he : j = P.walk.length := by omega
    exact ht (by simpa only [he, Walk.getVert_length] using hj.2)
  have hprev : P.walk.getVert (i - 1) ∉ S := by
    intro hh
    have hm := hmin (i - 1) ((hT (i - 1)).mpr ⟨by omega, hh⟩)
    change i ≤ i - 1 at hm
    omega
  have hnext : P.walk.getVert (j + 1) ∉ S := by
    intro hh
    have hm := hmax (j + 1) ((hT (j + 1)).mpr ⟨by omega, hh⟩)
    change j + 1 ≤ j at hm
    omega
  have hmem (n : ℕ) : P.walk.getVert n ∈ P.vertexSet :=
    List.mem_toFinset.mpr (P.walk.getVert_mem_support n)
  have hprevAdj : G.Adj (P.walk.getVert i) (P.walk.getVert (i - 1)) := by
    have hh := (P.walk.toSubgraph.adj_sub
      (P.walk.toSubgraph_adj_getVert (show i - 1 < P.walk.length by omega))).symm
    simpa only [Nat.sub_add_cancel hi0] using hh
  have hnextAdj : G.Adj (P.walk.getVert j) (P.walk.getVert (j + 1)) :=
    P.walk.toSubgraph.adj_sub (P.walk.toSubgraph_adj_getVert hjl)
  have hprevC := hcut _ (hmem i) hi.2 _ (hmem (i - 1)) hprev hprevAdj
  have hnextC := hcut _ (hmem j) hj.2 _ (hmem (j + 1)) hnext hnextAdj
  have hneq : P.walk.getVert (i - 1) ≠ P.walk.getVert (j + 1) := by
    intro he
    have hh := P.isPath.getVert_injOn (show i - 1 ≤ P.walk.length by omega)
      (show j + 1 ≤ P.walk.length by omega) he
    omega
  have hedge := hclique _ hprevC (hmem (i - 1)) _ hnextC (hmem (j + 1)) hneq
  have hh := P.indices_consecutive_of_edge (by omega : i - 1 ≤ P.walk.length)
    (by omega : j + 1 ≤ P.walk.length) hedge
  omega

end Erdos73Infrastructure.SimpleGraph.GraphPath

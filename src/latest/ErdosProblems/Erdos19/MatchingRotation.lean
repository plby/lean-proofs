import ErdosProblems.Erdos19.GraphMatching

/-! # Moving an unmatched vertex without changing matching size -/

namespace Erdos19

open _root_.SimpleGraph

theorem exists_matching_rotation_with_edge_control {V : Type*} [Fintype V]
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    {u v w : V} (hu : u ∉ M.verts) (hvw : M.Adj v w) (huv : G.Adj u v) :
    ∃ N : G.Subgraph, N.IsMatching ∧
      N.verts = insert u (M.verts \ {w}) ∧ N.edgeSet.ncard = M.edgeSet.ncard ∧
      N.edgeSet ⊆ M.edgeSet ∪ {s(u, v)} ∧
      (∀ x y, M.Adj x y → x ≠ v → x ≠ w → y ≠ v → y ≠ w → N.Adj x y) := by
  classical
  let R := M.deleteVerts {v, w}
  let P := G.subgraphOfAdj huv
  have hR : R.IsMatching := matching_delete_endpoints M hM hvw
  have hP : P.IsMatching := Subgraph.IsMatching.subgraphOfAdj huv
  have hPv : P.verts = {u, v} := by simp [P]
  have hRP : Disjoint R.support P.support := by
    rw [hR.support_eq_verts, hP.support_eq_verts, hPv, Set.disjoint_left]
    intro x hx hxP
    change x ∈ M.verts ∧ x ∉ ({v, w} : Set V) at hx
    rcases hxP with (rfl | rfl)
    · exact hu hx.1
    · exact hx.2 (Or.inl rfl)
  let N := R ⊔ P
  have hN : N.IsMatching := hR.sup hP hRP
  have hverts : N.verts = insert u (M.verts \ {w}) := by
    ext x
    change (x ∈ M.verts ∧ x ∉ ({v, w} : Set V)) ∨ x ∈ P.verts ↔ _
    rw [hPv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_sdiff, not_or]
    constructor
    · rintro (hx | hx)
      · exact Or.inr ⟨hx.1, hx.2.2⟩
      · rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨hvw.fst_mem, hvw.ne⟩
    · rintro (rfl | hx)
      · exact Or.inr (Or.inl rfl)
      · by_cases hxv : x = v
        · exact Or.inr (Or.inr hxv)
        · exact Or.inl ⟨hx.1, hxv, hx.2⟩
  have hcard : N.verts.ncard = M.verts.ncard := by
    rw [hverts, Set.ncard_insert_of_notMem (fun hx ↦ hu hx.1),
      Set.ncard_sdiff (Set.singleton_subset_iff.mpr hvw.snd_mem), Set.ncard_singleton]
    have hpos := (Set.ncard_pos (Set.toFinite M.verts)).mpr
      (show M.verts.Nonempty from ⟨w, hvw.snd_mem⟩)
    omega
  refine ⟨N, hN, hverts, ?_, ?_, ?_⟩
  · rw [matching_verts_ncard_generic N hN, matching_verts_ncard_generic M hM] at hcard
    omega
  · have hRedge : R.edgeSet ⊆ M.edgeSet :=
      Subgraph.edgeSet_mono (show R ≤ M from Subgraph.deleteVerts_le)
    have hPedge : P.edgeSet = {s(u, v)} := by simp [P]
    change (R ⊔ P).edgeSet ⊆ _
    rw [Subgraph.edgeSet_sup, hPedge]
    exact Set.union_subset_union_left _ hRedge
  · intro x y hxy hxv hxw hyv hyw
    change R.Adj x y ∨ P.Adj x y
    left
    exact Subgraph.deleteVerts_adj.mpr
      ⟨hxy.fst_mem, fun h ↦ h.elim hxv hxw,
        hxy.snd_mem, fun h ↦ h.elim hyv hyw, hxy⟩

theorem exists_matching_rotation {V : Type*} [Fintype V]
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    {u v w : V} (hu : u ∉ M.verts) (hvw : M.Adj v w) (huv : G.Adj u v) :
    ∃ N : G.Subgraph, N.IsMatching ∧
      N.verts = insert u (M.verts \ {w}) ∧ N.edgeSet.ncard = M.edgeSet.ncard := by
  obtain ⟨N, hN, hNv, hNc, _, _⟩ := exists_matching_rotation_with_edge_control M hM hu hvw huv
  exact ⟨N, hN, hNv, hNc⟩

theorem exists_matching_maximizing_edges_and_coverage {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (U : Set V) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      (∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      (∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard = M.edgeSet.ncard →
        (N.verts ∩ U).ncard ≤ (M.verts ∩ U).ncard) := by
  classical
  let score (N : G.Subgraph) :=
    (Fintype.card V + 1) * N.edgeSet.ncard + (N.verts ∩ U).ncard
  obtain ⟨M, hM, hscore⟩ := exists_matching_maximizing G score
  have hcover : (M.verts ∩ U).ncard ≤ Fintype.card V := by
    have hs := Set.ncard_le_ncard (Set.subset_univ (M.verts ∩ U))
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hs
  refine ⟨M, hM, ?_, ?_⟩
  · intro N hN
    have hs := hscore N hN
    dsimp only [score] at hs
    by_contra hlarge
    have hm : M.edgeSet.ncard + 1 ≤ N.edgeSet.ncard := by omega
    have hp := Nat.mul_le_mul_left (Fintype.card V + 1) hm
    nlinarith only [hp, hs, hcover]
  · intro N hN hcard
    have hs := hscore N hN
    dsimp only [score] at hs
    rw [hcard] at hs
    omega

#print axioms exists_matching_rotation
#print axioms exists_matching_maximizing_edges_and_coverage

end Erdos19

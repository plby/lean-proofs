import ErdosProblems.Erdos19.MatchingDeletion

/-! # Exact degree accounting for packed matchings and a reservoir -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem neighbor_ncard_sup_of_disjoint (G H : _root_.SimpleGraph V)
    (hdis : Disjoint G H) (v : V) :
    ((G ⊔ H).neighborSet v).ncard = (G.neighborSet v).ncard + (H.neighborSet v).ncard := by
  rw [neighborSet_sup]
  exact Set.ncard_union_eq (disjoint_neighborSet.mpr hdis v)

theorem base_reservoir_used_degree_identity (G R U : _root_.SimpleGraph V)
    (hRG : R ≤ G) (hUG : U ≤ G) (v : V) :
    ((G \ (R ⊔ U)).neighborSet v).ncard + (R.neighborSet v).ncard +
        (U.neighborSet v).ncard =
      (G.neighborSet v).ncard + ((R ⊓ U).neighborSet v).ncard := by
  rw [neighborSet_sdiff, neighborSet_sup, neighborSet_inf]
  have hsub : R.neighborSet v ∪ U.neighborSet v ⊆ G.neighborSet v := by
    intro w hw
    exact hw.elim (fun h ↦ hRG h) (fun h ↦ hUG h)
  have hcard := Set.ncard_union_add_ncard_inter (R.neighborSet v) (U.neighborSet v)
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_sdiff hsub]
  omega

theorem matching_neighbor_ncard (G : _root_.SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) (v : V) :
    (M.spanningCoe.neighborSet v).ncard = if v ∈ M.verts then 1 else 0 := by
  classical
  by_cases hv : v ∈ M.verts
  · rw [if_pos hv]
    have hsmall : (M.spanningCoe.neighborSet v).ncard ≤ 1 := by
      apply Set.ncard_le_one_iff_subsingleton.mpr
      intro x hx y hy
      exact hM.eq_of_adj_left hx hy
    obtain ⟨w, hw, _⟩ := hM hv
    have hpos : 0 < (M.spanningCoe.neighborSet v).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨w, hw⟩
    omega
  · rw [if_neg hv]
    have hempty : M.spanningCoe.neighborSet v = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hv (show M.Adj v w from hw).fst_mem
    rw [hempty, Set.ncard_empty]

theorem reservoir_load_sup_matching (U R : _root_.SimpleGraph V)
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hdis : Disjoint U M.spanningCoe) (v : V) :
    (((U ⊔ M.spanningCoe) ⊓ R).neighborSet v).ncard =
      ((U ⊓ R).neighborSet v).ncard + ((M.spanningCoe ⊓ R).neighborSet v).ncard := by
  rw [inf_sup_right]
  exact neighbor_ncard_sup_of_disjoint _ _ (hdis.mono inf_le_left inf_le_left) v

theorem matching_reservoir_increment_le_one (R : _root_.SimpleGraph V)
    {G : _root_.SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) (v : V) :
    ((M.spanningCoe ⊓ R).neighborSet v).ncard ≤ 1 := by
  have hsub : (M.spanningCoe ⊓ R).neighborSet v ⊆ M.spanningCoe.neighborSet v :=
    fun _ h ↦ h.1
  apply (Set.ncard_le_ncard hsub).trans
  rw [matching_neighbor_ncard G M hM]
  split_ifs <;> omega

#print axioms base_reservoir_used_degree_identity
#print axioms reservoir_load_sup_matching

end Erdos19

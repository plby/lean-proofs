import ErdosProblems.Erdos19.MatchingRotation
import ErdosProblems.Erdos19.NearPerfectMatching

/-! # A maximum matching that covers a prescribed small set -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_maximum_matching_covering {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (U : Set V)
    (hdegree : ∀ u ∈ U, U.ncard ≤ (G.neighborSet u).ncard) :
    ∃ M : G.Subgraph, M.IsMatching ∧ U ⊆ M.verts ∧
      ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  obtain ⟨M, hM, hmax, hcover⟩ := exists_matching_maximizing_edges_and_coverage G U
  refine ⟨M, hM, ?_, hmax⟩
  intro u hu
  by_contra huM
  have hmates : ∀ v : G.neighborSet u, ∃ w, w ∈ U ∧ M.Adj v.1 w := by
    intro v
    have hvM : v.1 ∈ M.verts := by
      by_contra hv
      exact (maximum_matching_unmatched_pairwise_not_adj M hM hmax
        huM hv v.2.ne) v.2
    obtain ⟨w, hvw, _⟩ := hM hvM
    refine ⟨w, ?_, hvw⟩
    by_contra hwU
    obtain ⟨N, hN, hNv, hNc⟩ := exists_matching_rotation M hM huM hvw v.2
    have hsub : insert u (M.verts ∩ U) ⊆ N.verts ∩ U := by
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨by rw [hNv]; exact Or.inl rfl, hu⟩
      · refine ⟨?_, hx.2⟩
        rw [hNv]
        exact Or.inr ⟨hx.1, fun hxw ↦ hwU (hxw ▸ hx.2)⟩
    have hcard := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem (fun hx ↦ huM hx.1)] at hcard
    have hmaxcover := hcover N hN hNc
    omega
  choose mate hmateU hmateAdj using hmates
  let f : G.neighborSet u → (U \ {u} : Set V) := fun v ↦
    ⟨mate v, hmateU v, fun h ↦ huM (h ▸ (hmateAdj v).snd_mem)⟩
  have hinj : Function.Injective f := by
    intro v w h
    have hsame : mate v = mate w := congrArg Subtype.val h
    have hvw : M.Adj v.1 (mate w) := by rw [← hsame]; exact hmateAdj v
    exact Subtype.ext (hM.eq_of_adj_right hvw (hmateAdj w))
  let _ : Fintype (G.neighborSet u) := Fintype.ofFinite _
  let _ : Fintype (U \ {u} : Set V) := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Set.fintypeCard_eq_ncard] at hcard
  rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hu), Set.ncard_singleton] at hcard
  have hpos := (Set.ncard_pos (Set.toFinite U)).mpr (show U.Nonempty from ⟨u, hu⟩)
  have hdeg := hdegree u hu
  omega

/-- The exceptional vertices can all be covered without losing the
near-perfect matching bound supplied by Vizing's theorem. -/
theorem exists_matching_covering_with_degree_bound {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (U : Set V)
    (hU : ∀ u ∈ U, U.ncard ≤ (G.neighborSet u).ncard)
    (d D : ℕ) (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ D) :
    ∃ M : G.Subgraph, M.IsMatching ∧ U ⊆ M.verts ∧
      M.vertsᶜ.ncard * (D + 1) ≤ Fintype.card V * (D + 1 - d) := by
  classical
  obtain ⟨M, hM, hMU, hMmax⟩ := exists_maximum_matching_covering G U hU
  obtain ⟨N, hN, _, hNbound⟩ := exists_maximum_matching_few_uncovered_of_degrees G d D hmin hmax
  have hMcard := hMmax N hN
  have hverts : N.verts.ncard ≤ M.verts.ncard := by
    rw [matching_verts_ncard_generic N hN, matching_verts_ncard_generic M hM]
    exact Nat.mul_le_mul_left 2 hMcard
  have hcompl : M.vertsᶜ.ncard ≤ N.vertsᶜ.ncard := by
    rw [Set.ncard_compl, Set.ncard_compl]
    exact Nat.sub_le_sub_left hverts _
  exact ⟨M, hM, hMU, (Nat.mul_le_mul_right _ hcompl).trans hNbound⟩

#print axioms exists_maximum_matching_covering
#print axioms exists_matching_covering_with_degree_bound

end Erdos19

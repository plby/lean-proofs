/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.AlmostBipartite

/-!
# Deleting transferred vertices from a sampled internal matching

This file isolates the finite matching-deletion bridge used in the
almost-bipartite counting argument for Erdős Problem 622.
-/

open scoped SimpleGraph

namespace Erdos622

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `F` incident with at least one vertex of `T`. -/
private noncomputable def matchingEdgesAt
    (F : SimpleGraph V) (T : Finset V) : Finset (Sym2 V) :=
  T.biUnion fun v ↦ F.incidenceFinset v

private lemma mem_matchingEdgesAt_iff (F : SimpleGraph V) (T : Finset V)
    (e : Sym2 V) :
    e ∈ matchingEdgesAt F T ↔ ∃ v ∈ T, e ∈ F.incidenceFinset v := by
  simp [matchingEdgesAt]

private lemma card_matchingEdgesAt_le
    {F : SimpleGraph V} (T : Finset V) (hdegree : ∀ v, F.degree v ≤ 1) :
    (matchingEdgesAt F T).card ≤ T.card := by
  calc
    (matchingEdgesAt F T).card ≤ ∑ v ∈ T, (F.incidenceFinset v).card := by
      exact Finset.card_biUnion_le
    _ = ∑ v ∈ T, F.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      exact F.card_incidenceFinset_eq_degree v
    _ ≤ ∑ _v ∈ T, 1 := by
      exact Finset.sum_le_sum fun v _ ↦ hdegree v
    _ = T.card := by simp

/-- Delete every matching edge incident with `T`.  At most `|T|` edges are
lost, and the remaining support avoids `T`. -/
theorem exists_submatchingGraph_avoiding_finset
    {F : SimpleGraph V} (T : Finset V)
    (hdegree : ∀ v, F.degree v ≤ 1) :
    ∃ H : SimpleGraph V,
      H ≤ F ∧
      (∀ v, H.degree v ≤ 1) ∧
      H.support ⊆ (T : Set V)ᶜ ∧
      F.edgeFinset.card ≤ H.edgeFinset.card + T.card := by
  let D := matchingEdgesAt F T
  let H := F.deleteEdges (D : Set (Sym2 V))
  let : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
  refine ⟨H, SimpleGraph.deleteEdges_le _, ?_, ?_, ?_⟩
  · intro v
    have hN : H.neighborSet v ⊆ F.neighborSet v := by
      intro w hvw
      exact (SimpleGraph.deleteEdges_le _) hvw
    have hcardle := Set.ncard_le_ncard hN
    have hleft : (H.neighborSet v).ncard = H.degree v := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hright : (F.neighborSet v).ncard = F.degree v := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [hleft, hright] at hcardle
    exact hcardle.trans (hdegree v)
  · intro v hv hvT
    obtain ⟨w, hvw⟩ := hv
    have hvwF : F.Adj v w := (SimpleGraph.deleteEdges_le _) hvw
    have hedgeF : s(v, w) ∈ F.incidenceFinset v := by
      simp [hvwF]
    have hedgeD : s(v, w) ∈ D := by
      exact (mem_matchingEdgesAt_iff F T _).2 ⟨v, hvT, hedgeF⟩
    exact (SimpleGraph.deleteEdges_adj.mp hvw).2 hedgeD
  · have hDsub : D ⊆ F.edgeFinset := by
      intro e he
      obtain ⟨v, _hvT, hev⟩ := (mem_matchingEdgesAt_iff F T e).1 he
      exact F.incidenceFinset_subset v hev
    have hcardD : D.card ≤ T.card := card_matchingEdgesAt_le T hdegree
    have hedge : H.edgeFinset = F.edgeFinset \ D := by
      simp [H, D, SimpleGraph.edgeFinset_deleteEdges]
    have hcardEq : F.edgeFinset.card = H.edgeFinset.card + D.card := by
      rw [hedge, Finset.card_sdiff_add_card_eq_card hDsub]
    calc
      F.edgeFinset.card = H.edgeFinset.card + D.card := hcardEq
      _ ≤ H.edgeFinset.card + T.card := Nat.add_le_add_left hcardD _

/-- If a matching was found in the old-plus-transferred part `B ∪ T`, then
deleting all matching edges incident with `T` leaves the requested number of
edges supported on the original part `B`. -/
theorem RandomCover.HasMatchingAtLeast.induce_internalGraph_union_delete
    {G : SimpleGraph V} {B T B0 S : Finset V} {m : ℕ} {q : ℝ}
    (hB0 : B0 = B ∪ T) (_hBT : Disjoint B T)
    (h : RandomCover.HasMatchingAtLeast (internalGraph G B0) S q)
    (hmq : ((m + (S ∩ T).card : ℕ) : ℝ) ≤ q) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B) m := by
  obtain ⟨M, hMmatching, hMsupport, hMcard⟩ := h
  let F : SimpleGraph V := M.spanningCoe
  have hFdegree : ∀ v, F.degree v ≤ 1 := by
    intro v
    change M.spanningCoe.degree v ≤ 1
    rw [M.degree_spanningCoe]
    by_cases hv : v ∈ M.verts
    · rw [(SimpleGraph.Subgraph.isMatching_iff_forall_degree.mp hMmatching) v hv]
    · rw [M.degree_of_notMem_verts hv]
      omega
  have hFcard : q ≤ (F.edgeFinset.card : ℝ) := by
    have hverts : M.verts.toFinset.card = 2 * F.edgeFinset.card := by
      rw [← F.sum_degrees_eq_twice_card_edges]
      have hdeg (v : V) :
          M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
        rw [M.degree_spanningCoe]
        split_ifs with hv
        · exact (SimpleGraph.Subgraph.isMatching_iff_forall_degree.mp hMmatching) v hv
        · exact M.degree_of_notMem_verts hv
      change M.verts.toFinset.card = ∑ v, M.spanningCoe.degree v
      simp_rw [hdeg]
      simp
    rw [hverts] at hMcard
    norm_num at hMcard ⊢
    linarith
  obtain ⟨H, hHF, hHdegree, hHavoid, hloss⟩ :=
    exists_submatchingGraph_avoiding_finset (F := F) (S ∩ T) hFdegree
  have hmH : m ≤ H.edgeFinset.card := by
    have hlossReal : (F.edgeFinset.card : ℝ) ≤
        H.edgeFinset.card + (S ∩ T).card := by
      exact_mod_cast hloss
    norm_num only [Nat.cast_add] at hmq hlossReal
    have hmReal : (m : ℝ) ≤ H.edgeFinset.card := by linarith
    exact_mod_cast hmReal
  have hHG : H ≤ G := by
    exact hHF.trans (M.spanningCoe_le.trans (internalGraph_le G B0))
  have hHsupportS : H.support ⊆ (S : Set V) := by
    intro v hv
    obtain ⟨w, hvw⟩ := hv
    exact hMsupport (M.edge_vert (hHF hvw))
  have hHsupportB : H.support ⊆ (B : Set V) := by
    intro v hv
    obtain ⟨w, hvw⟩ := hv
    have hvB0 : v ∈ B0 :=
      (internalGraph_adj G B0 v w).mp
        (M.spanningCoe_le (hHF hvw)) |>.1
    rw [hB0] at hvB0
    rcases Finset.mem_union.mp hvB0 with hvB | hvT
    · exact hvB
    · exact False.elim ((hHavoid ⟨w, hvw⟩) (by
        exact Finset.mem_inter.mpr ⟨hHsupportS ⟨w, hvw⟩, hvT⟩))
  have hforest : ContainsLinearForestWith G (B ∩ S) m := by
    refine ContainsLinearForestWith.of_degree_le_one hHG hHdegree ?_ hmH
    intro v hv
    exact Finset.mem_inter.mpr ⟨hHsupportB hv, hHsupportS hv⟩
  have hinduced := hforest.induce Finset.inter_subset_right
  have hpart : restrictedPart S (B ∩ S) = restrictedPart S B := by
    ext v
    simp only [mem_restrictedPart, Finset.mem_inter]
    exact and_iff_left v.property
  simpa only [hpart] using hinduced

end Erdos622

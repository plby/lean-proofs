import ErdosProblems.Erdos73.TwoConnectedPaths
import ErdosProblems.Erdos73.ParityTailExtension
import ErdosProblems.Erdos73.OddPathRegion

/-! Two-connected balanced networks extend external parity-breaking paths. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exists_two_tails_in_support (D T : Finset V) (a b : V)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hTD : T ⊆ D) (hT : 2 ≤ T.card)
    (hconn : ∀ X : Finset (D : Set V), X.card < 2 →
      ((G.induce (D : Set V)).induce (X : Set (D : Set V))ᶜ).Preconnected) :
    ∃ P Q : GraphPath G, P.source = a ∧ Q.source = b ∧
      P.target ∈ T ∧ Q.target ∈ T ∧ P.vertexSet ⊆ D ∧ Q.vertexSet ⊆ D ∧
      Disjoint P.vertexSet Q.vertexSet := by
  let a' : (D : Set V) := ⟨a, ha⟩
  let b' : (D : Set V) := ⟨b, hb⟩
  have hne : a' ≠ b' := fun hh => hab (congrArg Subtype.val hh)
  have hp := two_paths_of_delete_preconnected hconn {a', b'} (regionTerminals T D)
    (by simp [hne]) (by simpa only [regionTerminals_card hTD] using hT)
  obtain ⟨P, Q, hP, hQ, hPs, hQs, hPQ⟩ := two_clean_tails_of_pair_packing a' b' hne _ hp
  let f := (Embedding.induce (D : Set V) : G.induce (D : Set V) ↪g G).toCopy
  refine ⟨P.mapCopy f, Q.mapCopy f, congrArg Subtype.val hPs, congrArg Subtype.val hQs,
    (mem_regionTerminals _ _ _).mp hP.target_mem,
    (mem_regionTerminals _ _ _).mp hQ.target_mem, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, _, rfl⟩ := (P.mem_mapCopy_vertexSet f v).mp hv
    exact w.property
  · intro v hv
    obtain ⟨w, _, rfl⟩ := (Q.mem_mapCopy_vertexSet f v).mp hv
    exact w.property
  · apply Finset.disjoint_left.mpr
    intro v hvP hvQ
    obtain ⟨x, hx, hxv⟩ := (P.mem_mapCopy_vertexSet f v).mp hvP
    obtain ⟨y, hy, hyv⟩ := (Q.mem_mapCopy_vertexSet f v).mp hvQ
    have he : x = y := f.injective (hxv.trans hyv.symm)
    exact Finset.disjoint_left.mp hPQ hx (he ▸ hy)

theorem exists_parityBreaking_network_extension {R D T : Finset V}
    (c : BipartiteColoringOn G R) (U : GraphPath G)
    (hU : IsParityBreakingPath c.color R U) (hDR : D ⊆ R)
    (hs : U.source ∈ D) (ht : U.target ∈ D) (hTD : T ⊆ D) (hT : 2 ≤ T.card)
    (hconn : ∀ X : Finset (D : Set V), X.card < 2 →
      ((G.induce (D : Set V)).induce (X : Set (D : Set V))ᶜ).Preconnected) :
    ∃ B : GraphPath G, IsParityBreakingPath c.color T B ∧
      B.vertexSet ⊆ D ∪ U.vertexSet := by
  obtain ⟨P, Q, hPs, hQs, hPt, hQt, hPD, hQD, hPQ⟩ :=
    exists_two_tails_in_support D T U.source U.target hs ht hU.breaking.source_ne_target hTD hT hconn
  obtain ⟨B, hB, hsub⟩ := exists_parityBreaking_extension_supported c U P Q hU hPQ
    (hPD.trans hDR) (hQD.trans hDR) hPs hQs hPt hQt
  refine ⟨B, hB, hsub.trans ?_⟩
  exact union_subset (union_subset_union hPD subset_rfl) (hQD.trans subset_union_left)

end
end Erdos73

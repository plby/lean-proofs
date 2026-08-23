import ErdosProblems.Erdos1105.EvenNoncliqueCore

namespace Erdos1105

open SimpleGraph Finset

/-- The two possible low-core configurations for the six-vertex path:
a two-vertex cover, or a root with no three-edge path starting there. -/
theorem path_six_nonclique_cover_or_root {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Preconnected) (hfree : ¬pathGraph 6 ⊑ G)
    (hmax : ∀ J : SimpleGraph (Option V), graphCone G ≤ J → NoLongCycle J 7 →
      J = graphCone G)
    (hnot : ¬(graphCone G).IsClique (vertexCore (graphCone G) 2 : Set (Option V))) :
    (∃ A : Finset V, A.card = 2 ∧ ∀ x y, G.Adj x y → x ∈ A ∨ y ∈ A) ∨
      ∃ u, ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2 := by
  classical
  have hG : NoLongCycle (graphCone G) (2 * 2 + 3) :=
    no_long_cycle_cone_of_path_free G (by omega) hfree
  have hu := graphCone_universal G
  have hconn' := graphCone_delete_preconnected G hconn
  obtain ⟨x, y, p, hp, hlong⟩ := exists_longest_core_path_of_not_clique _ hG hmax hnot
  have htwo
      (hA : startNeighborIndices p = insert (p.length - 2 - 1) (range 2))
      (hB : endNeighborIndices p = insert 2 (Ico (p.length - 2) p.length)) :
      ∃ u, ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2 := by
    obtain ⟨S, v, hS, huS, hv, hvS, hc, hclosed⟩ := low_core_two_attachment_pendant hG
      hu hconn' p hp (by omega) (by omega) hA hB
    obtain ⟨T, w, hT, hw, hclique, hclosed⟩ := cone_pendant_clique G hS huS hv hvS hc hclosed
    exact ⟨w, rooted_path_bound_of_pendant_clique G (by omega) hT hw hclique hclosed hfree⟩
  by_cases hlen : p.length = 6
  · obtain ⟨a, ha, had, hB, hbefore, hafter, hmiddle⟩ :=
      short_low_core_complete_pattern hG hu hconn' p hp hlen
    by_cases ha2 : a = 2
    · subst a
      have hB' : endNeighborIndices p = insert 2 (Ico (p.length - 2) p.length) := by
        simpa only [show 2 + 1 - 2 = 1 by omega, range_one, image_singleton,
          Nat.mul_zero, Nat.add_zero, singleton_union] using hB
      exact Or.inr (htwo (short_two_attachment_start_pattern hG hu hconn' p hp hlen hB') hB')
    · have ha1 : a = 1 := by omega
      have hAlt := short_core_alternating_ends hG hu hconn' p hp hlen ha had hbefore hafter hmiddle
      have hshape := short_core_edge_shape hG hu hconn' p hp hlen ha (by omega) hbefore hafter hmiddle
      have hAcard := pathInitialBlock_card p hp.isPath (a := a) (by omega)
      have hBcard := pathFinalBlock_card p hp.isPath (a := a) (by omega)
      have hCcard := pathAttachments_card hAlt
      have hcover : ∀ v w, (graphCone G).Adj v w →
          v ∈ pathAttachments p 2 a ∨ w ∈ pathAttachments p 2 a := by
        intro v w hvw
        rcases hshape v w hvw with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hvw.ne ((card_le_one_iff.mp (by omega : (pathInitialBlock p a).card ≤ 1)) h.1 h.2)).elim
        · exact (hvw.ne ((card_le_one_iff.mp (by omega : (pathFinalBlock p a).card ≤ 1)) h.1 h.2)).elim
      obtain ⟨i, hi, hiu⟩ := short_core_universal_attachment hG hu p hp.isPath hlen ha had
        hbefore hafter hmiddle
      have hNone : none ∈ pathAttachments p 2 a := mem_image.mpr ⟨i, mem_range.mpr hi, hiu⟩
      obtain ⟨A, hA, hcover⟩ := cone_cover_remove_none G _ hNone hcover
      exact Or.inl ⟨A, by omega, hcover⟩
  · obtain ⟨hA, hB⟩ := long_low_core_neighbor_pattern hG hu hconn' p hp (by omega)
    exact Or.inr (htwo hA hB)

end Erdos1105

#print axioms Erdos1105.path_six_nonclique_cover_or_root

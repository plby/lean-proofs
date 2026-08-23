import ErdosProblems.Erdos1105.ShortCoreShape
import ErdosProblems.Erdos1105.LowCorePathReduction
import ErdosProblems.Erdos1105.TwoCliqueJoinCount

namespace Erdos1105

open SimpleGraph Finset

lemma cone_cover_remove_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Finset (Option V)) (hNone : none ∈ C)
    (hcover : ∀ x y, (graphCone G).Adj x y → x ∈ C ∨ y ∈ C) :
    ∃ S : Finset V, S.card + 1 = C.card ∧ ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S := by
  classical
  let S := univ.filter fun v ↦ some v ∈ C
  have himage : S.image some = C.erase none := by
    ext v
    cases v <;> simp [S]
  have hcard : S.card + 1 = C.card := by
    have h := congrArg Finset.card himage
    rw [card_image_of_injective _ (Option.some_injective V), card_erase_of_mem hNone] at h
    have hpos := card_pos.mpr ⟨none, hNone⟩
    omega
  refine ⟨S, hcard, ?_⟩
  intro x y hxy
  have h := hcover (some x) (some y) hxy
  simpa only [S, mem_filter, mem_univ, true_and] using h

/-- For even paths of order at least eight, a non-clique low core yields
either the required edge bound or a vertex cover of the size already
handled by the rainbow split-graph argument. -/
theorem even_nonclique_core_bound_or_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V) (hconn : G.Preconnected)
    (hfree : ¬pathGraph (2 * d + 2) ⊑ G)
    (hmax : ∀ J : SimpleGraph (Option V), graphCone G ≤ J → NoLongCycle J (2 * d + 3) →
      J = graphCone G)
    (hnot : ¬(graphCone G).IsClique (vertexCore (graphCone G) d : Set (Option V))) :
    G.edgeFinset.card ≤ pathFormula (Fintype.card V) (2 * d + 2) ∨
      ∃ C : Finset V, C.card = d ∧ ∀ x y, G.Adj x y → x ∈ C ∨ y ∈ C := by
  classical
  by_cases hlow : G.edgeFinset.card ≤ pathFormula (Fintype.card V) (2 * d + 2)
  · exact Or.inl hlow
  have hhigh : pathFormula (Fintype.card V) (2 * d + 2) < G.edgeFinset.card := by omega
  have hG : NoLongCycle (graphCone G) (2 * d + 3) :=
    no_long_cycle_cone_of_path_free G (by omega) hfree
  have hu := graphCone_universal G
  have hconn' := graphCone_delete_preconnected G hconn
  obtain ⟨x, y, p, hp, hlen, a, ha, had, _, hbefore, hafter, hmiddle⟩ :=
    even_high_nonclique_core_short_pattern G hd hn hconn hfree hmax hnot hhigh
  have hAlt := short_core_alternating_ends hG hu hconn' p hp hlen ha had.le hbefore hafter hmiddle
  have hshape := short_core_edge_shape hG hu hconn' p hp hlen ha had hbefore hafter hmiddle
  have hA := pathInitialBlock_card p hp.isPath (a := a) (by omega)
  have hB := pathFinalBlock_card p hp.isPath (a := a) (by omega)
  have hC := pathAttachments_card hAlt
  by_cases ha1 : a = 1
  · have hcover : ∀ v w, (graphCone G).Adj v w →
        v ∈ pathAttachments p d a ∨ w ∈ pathAttachments p d a := by
      intro v w hvw
      rcases hshape v w hvw with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hvw.ne ((card_le_one_iff.mp (by omega : (pathInitialBlock p a).card ≤ 1)) h.1 h.2)).elim
      · exact (hvw.ne ((card_le_one_iff.mp (by omega : (pathFinalBlock p a).card ≤ 1)) h.1 h.2)).elim
    obtain ⟨i, hi, hiu⟩ := short_core_universal_attachment hG hu p hp.isPath hlen ha had.le
      hbefore hafter hmiddle
    have hNone : none ∈ pathAttachments p d a := mem_image.mpr ⟨i, mem_range.mpr hi, hiu⟩
    obtain ⟨C, hcard, hcover⟩ := cone_cover_remove_none G _ hNone hcover
    exact Or.inr ⟨C, by omega, hcover⟩
  · have hcount := two_clique_join_edge_bound (graphCone G)
      (pathInitialBlock p a) (pathFinalBlock p a) (pathAttachments p d a) hshape
    rw [hA, hB, hC, graphCone_card_edges G, Fintype.card_option] at hcount
    have hb := two_clique_join_cone_count (Fintype.card V) d a G.edgeFinset.card had.le hn hcount
    exact Or.inl (two_clique_join_count_le_even_formula _ _ _ _ (by omega) had hn hb)

end Erdos1105

#print axioms Erdos1105.even_nonclique_core_bound_or_cover

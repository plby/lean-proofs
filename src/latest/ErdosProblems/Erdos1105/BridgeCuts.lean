import ErdosProblems.Erdos1105.ColorRepresentative

namespace Erdos1105

open SimpleGraph

theorem bridge_on_trail_separates_endpoints {V : Type*} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail) {e : Sym2 V}
    (he : G.IsBridge e) (hep : e ∈ p.edges) : ¬(G.deleteEdges {e}).Reachable a b := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    intro hab
    by_cases hay : (G.deleteEdges {s(x, y)}).Reachable a y
    · have hax : ¬(G.deleteEdges {s(x, y)}).Reachable a x :=
        fun hax ↦ (isBridge_iff.mp he) (hax.symm.trans hay)
      have hbx : ¬(G.deleteEdges {s(x, y)}).Reachable b x := fun hbx ↦ hax (hab.trans hbx)
      have hnot := hp.not_mem_edges_of_not_reachable
        (x := y) (y := x) (by simpa only [Sym2.eq_swap] using hax)
        (by simpa only [Sym2.eq_swap] using hbx)
      exact hnot (by simpa only [Sym2.eq_swap] using hep)
    · have hby : ¬(G.deleteEdges {s(x, y)}).Reachable b y := fun hby ↦ hay (hab.trans hby)
      exact hp.not_mem_edges_of_not_reachable hay hby hep

theorem exists_separating_bridge_of_deleted_bridges {V : Type*} {G : SimpleGraph V}
    (hconn : G.Preconnected) {X : Set (Sym2 V)} (hX : ∀ e ∈ X, G.IsBridge e)
    {a b : V} (hab : ¬(G.deleteEdges X).Reachable a b) :
    ∃ e ∈ X, ¬(G.deleteEdges {e}).Reachable a b := by
  obtain ⟨p, hp⟩ := (hconn a b).exists_isPath
  obtain ⟨e, heX, hep⟩ := p.exists_mem_edges_of_not_reachable_deleteEdges hab
  exact ⟨e, heX, bridge_on_trail_separates_endpoints p hp.isTrail (hX e heX) hep⟩

end Erdos1105

#print axioms Erdos1105.exists_separating_bridge_of_deleted_bridges

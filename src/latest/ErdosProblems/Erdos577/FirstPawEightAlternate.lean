import ErdosProblems.Erdos577.FirstPawEightTransport
import ErdosProblems.Erdos577.PawTerminalExchange

/-! The pattern (8) involution preserves both block scores and retains every outside block. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma feasible_swapped_score {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q) :
    edgeCount G (swappedLocal p q hd h).block = edgeCount G b := by
  let l := (swappedLocal p q hd h).withSupport
    (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  have hmax : edgeCount G (swappedLocal p q hd h).block ≤ edgeCount G b := hc.local_edges_le hb l
  have hlow := swapped_score_lower p q hd h
  rw [Unattached.oldEdges_diagonal] at hlow
  exact le_antisymm hmax ((congrArg (edgeCount G) hq).symm.trans_le hlow)

theorem exists_alternate {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = p.vertices 3 ∧
      (swappedPaw p q hd h).support = d.remainder ∧
      (swappedQuad p q hd h).support ∈ d.blocks ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  let l := (swappedLocal p q hd h).withSupport
    (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let d := c.replaceBlock b hb l
  have hscore : edgeCount G l.block = edgeCount G b := feasible_swapped_score hc p hp hb q hq hd h
  have hs := c.replaceBlock_scores_eq hb l hscore
  have ht : d.terminal = p.vertices 3 := by
    change (swappedLocal p q hd h).terminal = _
    exact swapped_local_terminal p q hd h
  have hp' : (swappedPaw p q hd h).support = d.remainder := by
    change (swappedPaw p q hd h).support = (swappedLocal p q hd h).remainder
    exact swapped_paw_support p q hd h
  have hq' : (swappedQuad p q hd h).support ∈ d.blocks := by
    change (swappedQuad p q hd h).support ∈ c.blocks.erase b ∪ {(swappedLocal p q hd h).block}
    rw [swapped_quad_support]
    exact mem_union_right _ (mem_singleton_self _)
  exact ⟨d, hc.replaceBlock_feasible hb l hscore, ht, hp', hq', hs.1, hs.2,
    fun a ha hab ↦ mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)⟩

theorem exists_terminal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q) (second : Bool) :
    ∃ d : TriangleChain G, d.Feasible ∧
      d.terminal = PawEncoding.labeling p q hd (if second then 3 else 0) ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  cases second
  · exact ⟨c.presentPaw p hp, hc.presentPaw_feasible p hp, rfl, fun _ ha _ ↦ ha⟩
  · obtain ⟨d, hdf, hdt, _, _, _, _, hkeep⟩ := exists_alternate hc p hp hb q hq hd h
    exact ⟨d, hdf, hdt, hkeep⟩

end Erdos577.FirstPawEight

import ErdosProblems.Erdos577.FirstPawSevenModel
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.PawTerminalExchange

/-! An actual alternate paw exposes the second feasible terminal without changing either score. -/

namespace Erdos577.FirstPawSeven

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def swappedPaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern7 p q) : Paw G := alternatePaw.image (coreCopy p q hd h)

lemma original_leaf_not_swapped (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q) :
    p.leaf ∉ (swappedPaw p q hd h).support := by
  intro hx
  change p.leaf ∈ (alternatePaw.image (coreCopy p q hd h)).support at hx
  rw [Paw.image_support] at hx
  obtain ⟨i, hi, he⟩ := mem_image.mp hx
  have he0 : coreCopy p q hd h i = coreCopy p q hd h 0 := he
  have hi0 : i = 0 := (coreCopy p q hd h).injective he0
  exact original_leaf_not_alternate (hi0 ▸ hi)

variable [Fintype V]

theorem exists_alternate {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q 3 ∧
      (swappedPaw p q hd h).support = d.remainder ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  let f := coreCopy p q hd h
  let l := (alternateLocal.image f).withSupport
    ((coreCopy_image p q hd h).trans (show p.support ∪ q.support = c.remainder ∪ b by
      rw [hp, hq]))
  let d := c.replaceBlock b hb l
  have hlow : 5 ≤ edgeCount G l.block := by
    have hh := alternateLocal.image_edgeCount_le f
    rw [alternate_score] at hh
    exact hh
  have hold : edgeCount G b = 5 := by rw [← hq]; exact old_score p q h
  have hscore : edgeCount G l.block = edgeCount G b :=
    le_antisymm (hc.local_edges_le hb l) (hold ▸ hlow)
  refine ⟨d, hc.replaceBlock_feasible hb l hscore, rfl, ?_, ?_⟩
  · change (alternatePaw.image f).support = l.remainder
    rw [Paw.image_support, Paw.support_eq, image_insert]
    rfl
  · intro a ha hab
    exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

theorem exists_terminal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q) (second : Bool) :
    ∃ d : TriangleChain G, d.Feasible ∧
      d.terminal = PawEncoding.labeling p q hd (if second then 7 else 0) ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  cases second
  · exact ⟨c.presentPaw p hp, hc.presentPaw_feasible p hp, rfl, fun _ ha _ ↦ ha⟩
  · obtain ⟨d, hdf, hdt, _, hkeep⟩ := exists_alternate hc p hp hb q hq hd h
    exact ⟨d, hdf, hdt, hkeep⟩

end Erdos577.FirstPawSeven

import ErdosProblems.Erdos577.FirstPawSixTerminalModel
import ErdosProblems.Erdos577.LocalChainSupport

/-! Both alternate paw presentations preserve feasibility and all further blocks. -/

namespace Erdos577.FirstPawSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def alternatePaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q) (tag : Fin 3)
    (hrows : PawBlock.ExactRows p q (caseRows (TerminalModel.index tag))) (second : Bool) : Paw G :=
  (TerminalModel.paw tag second).image (CaseModel.copy p q hd hdiag.1 _ hrows)

lemma other_terminal_not_alternate (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (tag : Fin 3)
    (hrows : PawBlock.ExactRows p q (caseRows (TerminalModel.index tag))) (second : Bool) :
    PawEncoding.labeling p q hd (if second then 7 else 3) ∉
      (alternatePaw p q hd hdiag tag hrows second).support := by
  intro hx
  change _ ∈ ((TerminalModel.paw tag second).image (CaseModel.copy p q hd hdiag.1 _ hrows)).support
    at hx
  rw [Paw.image_support] at hx
  obtain ⟨i, hi, he⟩ := mem_image.mp hx
  have hi' : i = (if second then 7 else 3) := (CaseModel.copy p q hd hdiag.1 _ hrows).injective he
  exact TerminalModel.other_terminal_not_mem tag second (hi' ▸ hi)

variable [Fintype V]

theorem exists_alternate {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (tag : Fin 3)
    (hrows : PawBlock.ExactRows p q (caseRows (TerminalModel.index tag))) (second : Bool) :
    ∃ d : TriangleChain G, d.Feasible ∧
      d.terminal = PawEncoding.labeling p q hd (if second then 3 else 7) ∧
      (alternatePaw p q hd hdiag tag hrows second).support = d.remainder ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  let f := CaseModel.copy p q hd hdiag.1 _ hrows
  let l := ((TerminalModel.chain tag second).image f).withSupport
    ((CaseModel.copy_image p q hd hdiag.1 _ hrows).trans
      (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq]))
  let d := c.replaceBlock b hb l
  have hlow : 5 ≤ edgeCount G l.block := by
    have hh := (TerminalModel.chain tag second).image_edgeCount_le f
    rw [TerminalModel.block_score] at hh
    exact hh
  have hold : edgeCount G b = 5 := by
    rw [← hq, q.edgeCount_eq, if_pos hdiag.1, if_neg hdiag.2]
  have hscore : edgeCount G l.block = edgeCount G b :=
    le_antisymm (hc.local_edges_le hb l) (hold ▸ hlow)
  refine ⟨d, hc.replaceBlock_feasible hb l hscore, ?_, ?_, ?_⟩
  · cases second <;> rfl
  · change ((TerminalModel.paw tag second).image f).support = l.remainder
    rw [Paw.image_support, Paw.support_eq, image_insert]
    rfl
  · intro a ha hab
    exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

end Erdos577.FirstPawSix

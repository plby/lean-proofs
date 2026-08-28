import ErdosProblems.Erdos577.WeightedThirteenModel
import ErdosProblems.Erdos577.TerminalReplacements
import ErdosProblems.Erdos577.LocalChainSupport

/-! A chordless first block exposes either low vertex as a feasible terminal. -/

namespace Erdos577.WeightedThirteen

open Finset

def lowIndex (second : Bool) : Fin 4 := if second then 3 else 1

def ownIndex (second : Bool) : Fin 4 := if second then 2 else 3

def lowLocal (second : Bool) : LocalChain graph univ where
  terminal := if second then 7 else 5
  triangle := if second then {6, 3, 5} else {6, 2, 7}
  block := if second then {0, 4, 2, 1} else {0, 4, 3, 1}
  triangle_clique := by cases second <;> decide +kernel
  terminal_not_mem := by cases second <;> decide +kernel
  quad := QuadOn.of_degreeIn (by cases second <;> decide +kernel)
    (by cases second <;> decide +kernel)
  disjoint := by cases second <;> decide +kernel
  cover := by cases second <;> decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_chordless_low_terminal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (hdiag : ¬G.Adj (q 0) (q 2)) (second : Bool) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q (lowIndex second) ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  let l := ((lowLocal second).image (coreCopy p q hd h)).withSupport
    (show univ.image (coreCopy p q hd h) = c.remainder ∪ b by rw [coreCopy_image, hp, hq])
  have hb4 : edgeCount G b = 4 := by
    rw [← hq, q.edgeCount_eq, if_neg hdiag, if_neg h.1]
  have hlo := l.quad.four_le_edgeCount
  have hhi := hc.local_edges_le hb l
  have heq : edgeCount G l.block = edgeCount G b := by omega
  let d := c.replaceBlock b hb l
  refine ⟨d, hc.replaceBlock_feasible hb l heq, ?_, ?_⟩
  · cases second <;> rfl
  · intro a ha hab
    exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

theorem chordless_low_universal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (hdiag : ¬G.Adj (q 0) (q 2)) (second : Bool)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (h3 : 3 ≤ degreeIn G (q (lowIndex second)) a) (u : V) (hu : u ∈ a) :
    QuadOn G (insert (q (lowIndex second)) (a.erase u)) := by
  obtain ⟨d, hdF, hdx, hkeep⟩ := exists_chordless_low_terminal hc p hp hb q hq hd h hdiag second
  rw [← hdx] at h3 ⊢
  exact hdF.terminal_universal_replace (hkeep a ha hab) h3 hu

theorem diagonal_of_nonuniversal_low {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (second : Bool) {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (h3 : 3 ≤ degreeIn G (q (lowIndex second)) a)
    (hnot : ¬∀ u ∈ a, QuadOn G (insert (q (lowIndex second)) (a.erase u))) :
    G.Adj (q 0) (q 2) := by
  by_contra hdiag
  exact hnot (chordless_low_universal hc p hp hb q hq hd h hdiag second ha hab h3)

end Erdos577.WeightedThirteen

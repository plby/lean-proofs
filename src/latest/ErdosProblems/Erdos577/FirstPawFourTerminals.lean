import ErdosProblems.Erdos577.FirstPawFourModel
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.QuadDegrees
import ErdosProblems.Erdos577.QuadScores

/-! Either low vertex of a diamond in pattern (4) can be exposed as a feasible terminal. -/

namespace Erdos577.FirstPawFour

open Finset

namespace TerminalTable

def terminal (second : Bool) : Fin 8 := if second then 7 else 5

def otherLow (second : Bool) : Fin 8 := if second then 5 else 7

def triangle (miss : Fin 10) : Finset (Fin 8) :=
  if miss = 0 then {4, 2, 3} else if miss = 1 then {6, 2, 3} else {1, 2, 3}

def block (miss : Fin 10) (second : Bool) : Finset (Fin 8) :=
  if miss = 0 then {0, 1, otherLow second, 6}
  else if miss = 1 then {0, 1, otherLow second, 4} else {0, 4, otherLow second, 6}

def chain (miss : Fin 10) (second : Bool) : LocalChain (graph miss) univ where
  terminal := terminal second
  triangle := triangle miss
  block := block miss second
  triangle_clique := by fin_cases miss <;> decide +kernel
  terminal_not_mem := by fin_cases miss <;> cases second <;> decide +kernel
  quad := by
    apply QuadOn.of_degreeIn
    · fin_cases miss <;> cases second <;> decide +kernel
    · fin_cases miss <;> cases second <;> decide +kernel
  disjoint := by fin_cases miss <;> cases second <;> decide +kernel
  cover := by fin_cases miss <;> cases second <;> decide +kernel

lemma block_score (miss : Fin 10) (second : Bool) :
    edgeCount (graph miss) (chain miss second).block = 5 := by
  fin_cases miss <;> cases second <;> decide +kernel

end TerminalTable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_diamond_low_terminal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) (hdiag : ¬G.Adj (q 1) (q 3))
    (second : Bool) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q (if second then 3 else 1) ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  obtain ⟨miss, hrows⟩ := exists_lower_rows p q h hheavy
  let f := copy p q hd h.1 miss hrows
  let l := ((TerminalTable.chain miss second).image f).withSupport
    ((copy_image p q hd h.1 miss hrows).trans (show p.support ∪ q.support = c.remainder ∪ b by
      rw [hp, hq]))
  have hscore : edgeCount G b = 5 := by
    rw [← hq, q.edgeCount_eq, if_pos h.1, if_neg hdiag]
  have hlow : 5 ≤ edgeCount G l.block := by
    have he := (TerminalTable.chain miss second).image_edgeCount_le f
    rw [TerminalTable.block_score] at he
    exact he
  have he : edgeCount G l.block = edgeCount G b :=
    le_antisymm (hc.local_edges_le hb l) (hscore ▸ hlow)
  refine ⟨c.replaceBlock b hb l, hc.replaceBlock_feasible hb l he, ?_, ?_⟩
  · cases second <;> rfl
  · intro a ha hab
    exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

end Erdos577.FirstPawFour

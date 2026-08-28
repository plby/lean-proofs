import ErdosProblems.Erdos577.FirstPawSevenModel
import ErdosProblems.Erdos577.LocalPathPartition

/-! Six literal insertion tests for pattern (7), covering both terminal choices. -/

namespace Erdos577.FirstPawSeven

open Finset

namespace FactorTable

def terminal : Fin 6 → Fin 8 := ![0, 0, 0, 7, 7, 7]

def triple : Fin 6 → Fin 3 → Fin 8 :=
  ![![7, 6, 2], ![7, 6, 5], ![5, 1, 2], ![0, 4, 5], ![0, 1, 2], ![5, 6, 2]]

def block : Fin 6 → Finset (Fin 8) :=
  ![{1, 3, 4, 5}, {1, 2, 3, 4}, {3, 4, 7, 6}, {1, 2, 3, 6}, {3, 4, 5, 6}, {0, 1, 3, 4}]

def partition (tag : Fin 6) : LocalPathPartition graph univ where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

lemma endpoint_coverage (u v w : Fin 8) (hu : u ∈ terminalSet)
    (hv : v ∈ weightSet.erase u) (hw : w ∈ weightSet.erase u) (hvw : v ≠ w) :
    ∃ tag : Fin 6, terminal tag = u ∧
      ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
  have hall : ∀ u v w : Fin 8, u ∈ terminalSet → v ∈ weightSet.erase u →
      w ∈ weightSet.erase u → v ≠ w → ∃ tag : Fin 6, terminal tag = u ∧
        ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
    decide +kernel
  exact hall u v w hu hv hw hvw

end FactorTable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 6) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := ((FactorTable.partition tag).image (coreCopy p q hd h)).withSupport
    ((coreCopy_image p q hd h).trans (show p.support ∪ q.support = c.remainder ∪ b by
      rw [hp, hq]))
  exact c.no_common_replacement hcard hn hb ha hab d

end Erdos577.FirstPawSeven

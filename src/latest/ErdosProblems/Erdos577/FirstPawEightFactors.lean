import ErdosProblems.Erdos577.FirstPawEightModel
import ErdosProblems.Erdos577.LocalPathPartition

/-! Twelve literal insertion paths cover every pair of the other three distinguished rows. -/

namespace Erdos577.FirstPawEight

open Finset

namespace FactorTable

def terminal : Fin 12 → Fin 8 := ![0, 0, 0, 3, 3, 3, 5, 5, 5, 7, 7, 7]

def triple : Fin 12 → Fin 3 → Fin 8 :=
  ![![3, 2, 5], ![3, 2, 7], ![5, 4, 7], ![0, 4, 5], ![0, 4, 7], ![5, 2, 7],
    ![0, 1, 3], ![0, 4, 7], ![3, 2, 7], ![0, 1, 3], ![0, 4, 5], ![3, 2, 5]]

def block : Fin 12 → Finset (Fin 8) :=
  ![{1, 4, 6, 7}, {1, 4, 5, 6}, {1, 3, 2, 6}, {1, 2, 6, 7}, {1, 2, 5, 6}, {1, 0, 4, 6},
    {2, 4, 6, 7}, {1, 3, 2, 6}, {0, 1, 6, 4}, {2, 4, 5, 6}, {1, 3, 2, 6}, {0, 1, 6, 4}]

def partition (diagonal : Fin 4) (hd : diagonal = 1 ∨ diagonal = 3) (tag : Fin 12) :
    LocalPathPartition (graph diagonal) univ where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by rcases hd with rfl | rfl <;> fin_cases tag <;> decide +kernel
  edge12 := by rcases hd with rfl | rfl <;> fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by rcases hd with rfl | rfl <;> fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

lemma endpoint_coverage (u v w : Fin 8) (hu : u ∈ weightSet)
    (hv : v ∈ weightSet.erase u) (hw : w ∈ weightSet.erase u) (hvw : v ≠ w) :
    ∃ tag : Fin 12, terminal tag = u ∧
      ((triple tag 0 = v ∧ triple tag 2 = w) ∨ (triple tag 0 = w ∧ triple tag 2 = v)) := by
  have hall : ∀ u v w : Fin 8, u ∈ weightSet → v ∈ weightSet.erase u →
      w ∈ weightSet.erase u → v ≠ w → ∃ tag : Fin 12, terminal tag = u ∧
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
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 12) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := ((FactorTable.partition (Unattached.diagonal q) (diagonal_cases q h.1) tag).image
    (coreCopy p q hd h)).withSupport
      ((coreCopy_image p q hd h).trans (show p.support ∪ q.support = c.remainder ∪ b by
        rw [hp, hq]))
  exact c.no_common_replacement hcard hn hb ha hab d

end Erdos577.FirstPawEight

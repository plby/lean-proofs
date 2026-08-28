import ErdosProblems.Erdos577.WeightedFifteenModel
import ErdosProblems.Erdos577.LocalPathPartition

/-! Ten explicit common-replacement prohibitions in the positive core of pattern (15). -/

namespace Erdos577.WeightedFifteen

open Finset

namespace FactorTable

def terminal : Fin 10 → Fin 8 := ![0, 1, 3, 3, 5, 4, 0, 5, 0, 0]

def triple : Fin 10 → Fin 3 → Fin 8 :=
  ![![1, 2, 3], ![0, 4, 5], ![5, 6, 7], ![4, 0, 1], ![3, 6, 7],
    ![0, 1, 3], ![1, 2, 7], ![1, 0, 4], ![4, 6, 7], ![1, 3, 5]]

def block : Fin 10 → Finset (Fin 8) :=
  ![{4, 5, 6, 7}, {2, 3, 6, 7}, {0, 1, 2, 4}, {2, 5, 6, 7}, {0, 1, 2, 4},
    {2, 5, 6, 7}, {3, 5, 4, 6}, {2, 3, 6, 7}, {1, 2, 5, 3}, {2, 4, 7, 6}]

def partition (tag : Fin 10) : LocalPathPartition graph univ where
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

end FactorTable

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def localPathPartition (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (tag : Fin 10) :
    LocalPathPartition G (p.support ∪ q.support) :=
  ((FactorTable.partition tag).image (coreCopy p q hd h)).withSupport (coreCopy_image p q hd h)

variable [Fintype V]

omit [DecidableRel G.Adj] in
lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 10) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := (localPathPartition p q hd h tag).withSupport
    (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  exact c.no_common_replacement hcard hn hb ha hab d

end Erdos577.WeightedFifteen

import ErdosProblems.Erdos577.WeightedThirteenModel
import ErdosProblems.Erdos577.LocalPathPartition

/-! Eight explicit local path partitions for the forced block of pattern (13). -/

namespace Erdos577.WeightedThirteen

open Finset

namespace FactorTable

def terminal : Fin 8 → Fin 8 := ![0, 1, 3, 7, 3, 7, 5, 5]

def triple : Fin 8 → Fin 3 → Fin 8 :=
  ![![1, 2, 3], ![0, 4, 5], ![5, 6, 7], ![0, 1, 3],
    ![0, 1, 2], ![5, 6, 3], ![7, 6, 2], ![7, 6, 3]]

def block : Fin 8 → Finset (Fin 8) :=
  ![{4, 5, 6, 7}, {2, 3, 6, 7}, {0, 1, 2, 4}, {2, 4, 5, 6},
    {4, 5, 6, 7}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}]

def partition (tag : Fin 8) : LocalPathPartition graph univ where
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
    (h : WeightedPawBlock.Pattern13 p q) (tag : Fin 8) :
    LocalPathPartition G (p.support ∪ q.support) :=
  ((FactorTable.partition tag).image (coreCopy p q hd h)).withSupport (coreCopy_image p q hd h)

variable [Fintype V]

omit [DecidableRel G.Adj] in
lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 8) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := (localPathPartition p q hd h tag).withSupport
    (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  exact c.no_common_replacement hcard hn hb ha hab d

end Erdos577.WeightedThirteen

import ErdosProblems.Erdos577.WeightedFifteenDenseModel

/-! Explicit terminal exposures and all fourteen path rows in the dense configuration. -/

namespace Erdos577.WeightedFifteen.DenseModel

open Finset

def terminal (second : Bool) : Fin 12 := if second then 7 else 8

def terminalTriangle (second : Bool) : Finset (Fin 12) :=
  if second then {0, 4, 8} else {1, 2, 3}

def terminalBlock (second complete : Bool) : Finset (Fin 12) :=
  if second then (if complete then {2, 3, 5, 6} else {1, 9, 11, 10})
  else (if complete then {0, 9, 10, 11} else {4, 5, 6, 7})

lemma terminal_triangle_clique (second : Bool) : graph.IsNClique 3 (terminalTriangle second) := by
  cases second <;> decide +kernel

lemma terminal_not_mem (second : Bool) : terminal second ∉ terminalTriangle second := by
  cases second <;> decide +kernel

lemma terminal_blocks_disjoint (second : Bool) :
    Disjoint (terminalBlock second false) (terminalBlock second true) := by
  cases second <;> decide +kernel

lemma terminal_remainder (second : Bool) :
    univ \ (terminalBlock second false ∪ terminalBlock second true) =
      insert (terminal second) (terminalTriangle second) := by
  cases second <;> decide +kernel

lemma terminal_block_quad (second complete : Bool) : QuadOn graph (terminalBlock second complete) :=
  QuadOn.of_degreeIn (by cases second <;> cases complete <;> decide +kernel)
    (by cases second <;> cases complete <;> decide +kernel)

lemma terminal_block_score (second complete : Bool) :
    edgeCount graph (terminalBlock second complete) = if complete then 6 else 5 := by
  cases second <;> cases complete <;> decide +kernel

lemma terminal_block_adj (second complete : Bool) :
    ∀ i ∈ terminalBlock second complete, ∀ j ∈ terminalBlock second complete,
      upperGraph.Adj i j ↔ graph.Adj i j := by
  cases second <;> cases complete <;> decide +kernel

namespace FinalTable

def triple (second : Bool) : Fin 7 → Fin 3 → Fin 12 :=
  if second then
    ![![0, 1, 3], ![0, 4, 5], ![0, 8, 1], ![0, 4, 8],
      ![1, 0, 8], ![3, 6, 5], ![3, 1, 8]]
  else
    ![![0, 1, 3], ![0, 4, 5], ![0, 4, 7], ![1, 2, 3],
      ![1, 2, 7], ![1, 3, 5], ![5, 4, 7]]

def firstBlock (second : Bool) : Fin 7 → Finset (Fin 12) :=
  if second then
    ![{2, 4, 5, 6}, {1, 2, 6, 3}, {2, 3, 5, 6}, {1, 9, 11, 10},
      {2, 3, 5, 6}, {0, 1, 2, 4}, {0, 9, 10, 11}]
  else
    ![{2, 5, 6, 7}, {1, 9, 11, 10}, {1, 9, 11, 10}, {0, 9, 10, 11},
      {0, 9, 10, 11}, {0, 9, 10, 11}, {0, 9, 10, 11}]

def secondBlock (second : Bool) : Fin 7 → Finset (Fin 12) :=
  if second then
    ![{8, 9, 10, 11}, {8, 9, 10, 11}, {4, 9, 11, 10}, {2, 3, 5, 6},
      {4, 9, 11, 10}, {8, 9, 10, 11}, {2, 4, 5, 6}]
  else
    ![{4, 9, 11, 10}, {2, 3, 6, 7}, {2, 3, 5, 6}, {4, 5, 6, 7},
      {3, 5, 4, 6}, {2, 4, 6, 7}, {1, 2, 6, 3}]

def partition (second : Bool) (tag : Fin 7) :
    LocalPathPartition graph (univ \ secondBlock second tag) where
  terminal := terminal second
  triple := ⟨triple second tag, by cases second <;> fin_cases tag <;> decide +kernel⟩
  edge01 := by cases second <;> fin_cases tag <;> decide +kernel
  edge12 := by cases second <;> fin_cases tag <;> decide +kernel
  terminal_not_mem := by cases second <;> fin_cases tag <;> decide +kernel
  block := firstBlock second tag
  quad := QuadOn.of_degreeIn (by cases second <;> fin_cases tag <;> decide +kernel)
    (by cases second <;> fin_cases tag <;> decide +kernel)
  disjoint := by cases second <;> fin_cases tag <;> decide +kernel
  cover := by cases second <;> fin_cases tag <;> decide +kernel

lemma second_quad (second : Bool) (tag : Fin 7) : QuadOn graph (secondBlock second tag) :=
  QuadOn.of_degreeIn (by cases second <;> fin_cases tag <;> decide +kernel)
    (by cases second <;> fin_cases tag <;> decide +kernel)

def triples (second : Bool) : Fin 10 → Finset (Fin 12) :=
  let z : Fin 12 := if second then 8 else 7
  ![{0, 1, 3}, {0, 1, 5}, {0, 1, z}, {0, 3, 5}, {0, 3, z},
    {0, 5, z}, {1, 3, 5}, {1, 3, z}, {1, 5, z}, {3, 5, z}]

lemma triples_cover (second : Bool) :
    (sixSet.erase (terminal second)).powersetCard 3 = univ.image (triples second) := by
  cases second <;> decide +kernel

lemma triple_endpoints (second : Bool) (i : Fin 10) :
    ∃ tag : Fin 7, triple second tag 0 ∈ triples second i ∧
      triple second tag 2 ∈ triples second i := by
  cases second <;> fin_cases i <;> decide +kernel

lemma endpoint_coverage (second : Bool) :
    ∀ s ∈ ((sixSet.erase (terminal second)).powersetCard 3),
      ∃ tag : Fin 7, triple second tag 0 ∈ s ∧ triple second tag 2 ∈ s := by
  intro s hs
  rw [triples_cover] at hs
  obtain ⟨i, _, rfl⟩ := mem_image.mp hs
  exact triple_endpoints second i

end FinalTable

end Erdos577.WeightedFifteen.DenseModel

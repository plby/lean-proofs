import ErdosProblems.Erdos577.FirstPawFourModel

/-! All180 explicit complementary path witnesses in the ten pattern (4) cores. -/

namespace Erdos577.FirstPawFour.PairTable

open Finset

def terminalSet : Finset (Fin 8) := {0, 5, 7}

def vertexSet : Finset (Fin 8) := {0, 2, 3, 5, 7}

def terminal : Fin 18 → Fin 8 :=
  ![0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7]

def endpoint0 : Fin 18 → Fin 8 :=
  ![2, 2, 2, 3, 3, 5, 0, 0, 0, 2, 2, 3, 0, 0, 0, 2, 2, 3]

def endpoint2 : Fin 18 → Fin 8 :=
  ![3, 5, 7, 5, 7, 7, 2, 3, 7, 3, 7, 7, 2, 3, 5, 3, 5, 5]

def middle : Fin 10 → Fin 18 → Fin 8 :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 1, 4, 4, 4],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 1, 1, 1, 6, 6, 6],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 4, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 4, 1, 4, 4, 1, 1, 4, 1, 4, 4, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4],
    ![1, 1, 1, 6, 6, 1, 1, 6, 1, 1, 1, 6, 1, 6, 1, 1, 1, 6],
    ![1, 4, 4, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1],
    ![1, 6, 6, 1, 1, 1, 6, 1, 1, 1, 6, 1, 6, 1, 1, 1, 6, 1]]

def block : Fin 10 → Fin 18 → Finset (Fin 8) :=
  ![![{4, 5, 6, 7}, {3, 4, 7, 6}, {3, 4, 5, 6}, {2, 4, 7, 6},
      {2, 4, 5, 6}, {2, 3, 4, 6}, {3, 4, 7, 6}, {2, 4, 7, 6},
      {2, 3, 4, 6}, {0, 1, 7, 6}, {0, 1, 3, 6}, {0, 1, 2, 6},
      {3, 4, 5, 6}, {2, 4, 5, 6}, {2, 3, 4, 6}, {0, 1, 5, 6},
      {0, 1, 3, 6}, {0, 1, 2, 6}],
    ![{4, 5, 6, 7}, {3, 4, 7, 6}, {3, 4, 5, 6}, {2, 4, 7, 6},
      {2, 4, 5, 6}, {2, 3, 4, 6}, {3, 4, 7, 6}, {2, 4, 7, 6},
      {2, 3, 4, 6}, {0, 1, 7, 4}, {0, 1, 3, 4}, {0, 1, 2, 4},
      {3, 4, 5, 6}, {2, 4, 5, 6}, {2, 3, 4, 6}, {0, 1, 5, 4},
      {0, 1, 3, 4}, {0, 1, 2, 4}],
    ![{4, 5, 6, 7}, {3, 4, 7, 6}, {3, 4, 5, 6}, {2, 4, 7, 6},
      {2, 4, 5, 6}, {2, 3, 4, 6}, {3, 4, 7, 6}, {2, 4, 7, 6},
      {2, 3, 4, 6}, {0, 4, 7, 6}, {0, 4, 3, 6}, {0, 4, 2, 6},
      {3, 4, 5, 6}, {2, 4, 5, 6}, {2, 3, 4, 6}, {0, 4, 5, 6},
      {0, 4, 3, 6}, {0, 4, 2, 6}],
    ![{4, 5, 6, 7}, {1, 3, 6, 7}, {3, 4, 5, 6}, {1, 2, 6, 7},
      {2, 4, 5, 6}, {1, 2, 3, 6}, {3, 4, 7, 6}, {2, 4, 7, 6},
      {2, 3, 4, 6}, {0, 4, 7, 6}, {0, 4, 3, 6}, {0, 4, 2, 6},
      {3, 4, 5, 6}, {2, 4, 5, 6}, {1, 2, 3, 6}, {0, 4, 5, 6},
      {0, 1, 3, 6}, {0, 1, 2, 6}],
    ![{4, 5, 6, 7}, {3, 4, 7, 6}, {3, 4, 5, 6}, {2, 4, 7, 6},
      {2, 4, 5, 6}, {2, 3, 4, 6}, {3, 4, 7, 6}, {2, 4, 7, 6},
      {2, 3, 4, 6}, {0, 4, 7, 6}, {0, 4, 3, 6}, {0, 4, 2, 6},
      {3, 4, 5, 6}, {2, 4, 5, 6}, {2, 3, 4, 6}, {0, 4, 5, 6},
      {0, 4, 3, 6}, {0, 4, 2, 6}],
    ![{4, 5, 6, 7}, {3, 4, 7, 6}, {1, 3, 6, 5}, {2, 4, 7, 6},
      {1, 2, 6, 5}, {1, 2, 3, 6}, {3, 4, 7, 6}, {2, 4, 7, 6},
      {1, 2, 3, 6}, {0, 4, 7, 6}, {0, 1, 3, 6}, {0, 1, 2, 6},
      {3, 4, 5, 6}, {2, 4, 5, 6}, {2, 3, 4, 6}, {0, 4, 5, 6},
      {0, 4, 3, 6}, {0, 4, 2, 6}],
    ![{4, 5, 6, 7}, {3, 4, 7, 6}, {3, 4, 5, 6}, {1, 2, 6, 7},
      {1, 2, 6, 5}, {2, 3, 4, 6}, {3, 4, 7, 6}, {1, 2, 6, 7},
      {2, 3, 4, 6}, {0, 4, 7, 6}, {0, 4, 3, 6}, {0, 1, 2, 6},
      {3, 4, 5, 6}, {1, 2, 6, 5}, {2, 3, 4, 6}, {0, 4, 5, 6},
      {0, 4, 3, 6}, {0, 1, 2, 6}],
    ![{4, 5, 6, 7}, {3, 4, 7, 6}, {3, 4, 5, 6}, {1, 2, 4, 7},
      {1, 2, 4, 5}, {2, 3, 6, 4}, {3, 4, 7, 6}, {1, 2, 4, 7},
      {2, 3, 6, 4}, {0, 4, 7, 6}, {0, 4, 3, 6}, {0, 1, 2, 4},
      {3, 4, 5, 6}, {1, 2, 4, 5}, {2, 3, 6, 4}, {0, 4, 5, 6},
      {0, 4, 3, 6}, {0, 1, 2, 4}],
    ![{4, 5, 6, 7}, {1, 3, 6, 7}, {1, 3, 6, 5}, {2, 4, 7, 6},
      {2, 4, 5, 6}, {2, 3, 6, 4}, {1, 3, 6, 7}, {2, 4, 7, 6},
      {2, 3, 6, 4}, {0, 4, 7, 6}, {0, 1, 3, 6}, {0, 4, 2, 6},
      {1, 3, 6, 5}, {2, 4, 5, 6}, {2, 3, 6, 4}, {0, 4, 5, 6},
      {0, 1, 3, 6}, {0, 4, 2, 6}],
    ![{4, 5, 6, 7}, {1, 3, 4, 7}, {1, 3, 4, 5}, {2, 4, 7, 6},
      {2, 4, 5, 6}, {2, 3, 4, 6}, {1, 3, 4, 7}, {2, 4, 7, 6},
      {2, 3, 4, 6}, {0, 4, 7, 6}, {0, 1, 3, 4}, {0, 4, 2, 6},
      {1, 3, 4, 5}, {2, 4, 5, 6}, {2, 3, 4, 6}, {0, 4, 5, 6},
      {0, 1, 3, 4}, {0, 4, 2, 6}]]

def triple (miss : Fin 10) (tag : Fin 18) : Fin 3 → Fin 8 :=
  ![endpoint0 tag, middle miss tag, endpoint2 tag]

private def partition0 (tag : Fin 18) : LocalPathPartition (graph 0) univ where
  terminal := terminal tag
  triple := ⟨triple 0 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 0 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition1 (tag : Fin 18) : LocalPathPartition (graph 1) univ where
  terminal := terminal tag
  triple := ⟨triple 1 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 1 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition2 (tag : Fin 18) : LocalPathPartition (graph 2) univ where
  terminal := terminal tag
  triple := ⟨triple 2 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 2 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition3 (tag : Fin 18) : LocalPathPartition (graph 3) univ where
  terminal := terminal tag
  triple := ⟨triple 3 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 3 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition4 (tag : Fin 18) : LocalPathPartition (graph 4) univ where
  terminal := terminal tag
  triple := ⟨triple 4 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 4 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition5 (tag : Fin 18) : LocalPathPartition (graph 5) univ where
  terminal := terminal tag
  triple := ⟨triple 5 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 5 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition6 (tag : Fin 18) : LocalPathPartition (graph 6) univ where
  terminal := terminal tag
  triple := ⟨triple 6 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 6 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition7 (tag : Fin 18) : LocalPathPartition (graph 7) univ where
  terminal := terminal tag
  triple := ⟨triple 7 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 7 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition8 (tag : Fin 18) : LocalPathPartition (graph 8) univ where
  terminal := terminal tag
  triple := ⟨triple 8 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 8 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

private def partition9 (tag : Fin 18) : LocalPathPartition (graph 9) univ where
  terminal := terminal tag
  triple := ⟨triple 9 tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block 9 tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

def partition (miss : Fin 10) (tag : Fin 18) : LocalPathPartition (graph miss) univ :=
  match miss with
  | 0 => partition0 tag
  | 1 => partition1 tag
  | 2 => partition2 tag
  | 3 => partition3 tag
  | 4 => partition4 tag
  | 5 => partition5 tag
  | 6 => partition6 tag
  | 7 => partition7 tag
  | 8 => partition8 tag
  | 9 => partition9 tag

lemma partition_terminal (miss : Fin 10) (tag : Fin 18) :
    (partition miss tag).terminal = terminal tag := by fin_cases miss <;> rfl

lemma partition_triple (miss : Fin 10) (tag : Fin 18) (i : Fin 3) :
    (partition miss tag).triple i = triple miss tag i := by fin_cases miss <;> rfl

lemma endpoint_coverage (u v w : Fin 8) (hu : u ∈ terminalSet)
    (hv : v ∈ vertexSet.erase u) (hw : w ∈ vertexSet.erase u) (hvw : v ≠ w) :
    ∃ tag : Fin 18, terminal tag = u ∧
      ((endpoint0 tag = v ∧ endpoint2 tag = w) ∨
        (endpoint0 tag = w ∧ endpoint2 tag = v)) := by
  have hall : ∀ u ∈ terminalSet, ∀ v ∈ vertexSet.erase u, ∀ w ∈ vertexSet.erase u, v ≠ w →
      ∃ tag : Fin 18, terminal tag = u ∧
        ((endpoint0 tag = v ∧ endpoint2 tag = w) ∨
          (endpoint0 tag = w ∧ endpoint2 tag = v)) := by decide +kernel
  exact hall u hu v hv w hw hvw

end Erdos577.FirstPawFour.PairTable

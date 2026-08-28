import ErdosProblems.Erdos577.TripleCoreWitnessCycles

/-! The exact triangle, bridge, complement score and C-budget data for all forty-eight entries. -/

namespace Erdos577.TripleCorePatterns

open Finset

lemma triangle_clique (tag : Fin 12) (j : Fin 4) :
    (graph tag).IsNClique 3 (triple tag j) := by
  have hall : ∀ tag : Fin 12, ∀ j : Fin 4, (graph tag).IsNClique 3 (triple tag j) := by
    decide +kernel
  exact hall tag j

lemma u_data (tag : Fin 12) (j : Fin 4) (h : kind tag j = 0) :
    triple tag j ⊆ core \ {1, 2} ∧ (graph tag).Adj 1 (first tag j) := by
  have hall : ∀ tag : Fin 12, ∀ j : Fin 4, kind tag j = 0 →
      triple tag j ⊆ core \ {1, 2} ∧ (graph tag).Adj 1 (first tag j) := by
    decide +kernel
  exact hall tag j h

lemma v_data (tag : Fin 12) (j : Fin 4) (h : kind tag j = 1) :
    triple tag j ⊆ core \ {marked j, 2} ∧ (graph tag).Adj (marked j) (first tag j) := by
  have hall : ∀ tag : Fin 12, ∀ j : Fin 4, kind tag j = 1 →
      triple tag j ⊆ core \ {marked j, 2} ∧ (graph tag).Adj (marked j) (first tag j) := by
    decide +kernel
  exact hall tag j h

lemma c_data (tag : Fin 12) (j : Fin 4) (h : kind tag j = 2) :
    first tag j ∈ block ∧ second tag j ∈ block ∧
      marked j ∈ ({first tag j, second tag j} : Finset (Fin 8)) ∧
      contacts (graph tag) (triple tag j) core ≤ 17 := by
  have hall : ∀ tag : Fin 12, ∀ j : Fin 4, kind tag j = 2 →
      first tag j ∈ block ∧ second tag j ∈ block ∧
        marked j ∈ ({first tag j, second tag j} : Finset (Fin 8)) ∧
        contacts (graph tag) (triple tag j) core ≤ 17 := by
    decide +kernel
  exact hall tag j h

lemma complement_score (tag : Fin 12) (j : Fin 4) :
    edgeCount (graph tag) block ≤ edgeCount (graph tag) (target tag j 0) := by
  rw [old_score]
  fin_cases tag <;> fin_cases j <;> decide +kernel

end Erdos577.TripleCorePatterns

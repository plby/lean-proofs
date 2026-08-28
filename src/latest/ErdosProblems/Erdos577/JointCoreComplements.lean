import ErdosProblems.Erdos577.JointCoreModel

/-! Positive complementary quadrilaterals for every source core pattern. -/

namespace Erdos577.JointCore

open Finset

theorem distinguished_edges (tag : Fin 8) :
    (graph tag).Adj 1 6 ∧ (graph tag).Adj 1 7 ∧ (graph tag).Adj 6 7 := by
  have hf : ∀ tag : Fin 8,
      (graph tag).Adj 1 6 ∧ (graph tag).Adj 1 7 ∧ (graph tag).Adj 6 7 := by
    decide +kernel
  exact hf tag

theorem primary_edges (tag : Fin 8) : 5 ≤ edgeCount (graph tag) (core \ {1, 6, 7}) := by
  have hf : ∀ tag : Fin 8, 5 ≤ edgeCount (graph tag) (core \ {1, 6, 7}) := by
    decide +kernel
  exact hf tag

theorem primary_quad (tag : Fin 8) : QuadOn (graph tag) (core \ {1, 6, 7}) := by
  apply QuadOn.of_degreeIn (by decide +kernel)
  have hf : ∀ tag : Fin 8, ∀ v ∈ core \ {1, 6, 7},
      2 ≤ degreeIn (graph tag) v (core \ {1, 6, 7}) := by decide +kernel
  exact hf tag

theorem secondary_first (tag : Fin 8) : QuadOn (graph tag) (core \ {6, 1, 2}) := by
  apply QuadOn.of_degreeIn (by decide +kernel)
  have hf : ∀ tag : Fin 8, ∀ v ∈ core \ {6, 1, 2},
      2 ≤ degreeIn (graph tag) v (core \ {6, 1, 2}) := by decide +kernel
  exact hf tag

theorem secondary_second (tag : Fin 8) : QuadOn (graph tag) (core \ {7, 1, 2}) := by
  apply QuadOn.of_degreeIn (by decide +kernel)
  have hf : ∀ tag : Fin 8, ∀ v ∈ core \ {7, 1, 2},
      2 ≤ degreeIn (graph tag) v (core \ {7, 1, 2}) := by decide +kernel
  exact hf tag

theorem tertiary_quad (tag : Fin 8) : QuadOn (graph tag) (core \ {6, 7, 2}) := by
  apply QuadOn.of_degreeIn (by decide +kernel)
  have hf : ∀ tag : Fin 8, ∀ v ∈ core \ {6, 7, 2},
      2 ≤ degreeIn (graph tag) v (core \ {6, 7, 2}) := by decide +kernel
  exact hf tag

theorem third_replacement (tag : Fin 8) (u : Fin 8) (hu : u ∈ block) :
    QuadOn (graph tag) (insert 3 (block.erase u)) := by
  have hc : ∀ u : Fin 8, u ∈ block → (insert 3 (block.erase u)).card = 4 := by
    decide +kernel
  apply QuadOn.of_degreeIn (hc u hu)
  have hf : ∀ tag : Fin 8, ∀ u : Fin 8, u ∈ block →
      ∀ v ∈ insert 3 (block.erase u),
        2 ≤ degreeIn (graph tag) v (insert 3 (block.erase u)) := by decide +kernel
  exact hf tag u hu

end Erdos577.JointCore

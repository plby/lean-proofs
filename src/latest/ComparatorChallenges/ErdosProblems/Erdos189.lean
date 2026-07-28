import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Erdos189

noncomputable def Erdos189For :
    (EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) →
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Prop) →
    (EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) →
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ) → Prop := by
  sorry

theorem erdos_189 :
    Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
          line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
            line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction)
      (fun a b c _d ↦ dist a b * dist b c) ↔ False := by
  sorry

end Erdos189

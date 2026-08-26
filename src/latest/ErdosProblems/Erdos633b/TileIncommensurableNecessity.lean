import ErdosProblems.Erdos633b.CommensurabilityTransfer
import ErdosProblems.Erdos633b.IncommensurableNecessity

/-! The tile-based incommensurable classification follows from the proved
commensurability transfer. Every remaining counterexample would have
commensurable tile and outer angles. -/

namespace Erdos633b

namespace Triangle

theorem not_equilateral_of_injective_angles (T : Triangle)
    (h : Function.Injective T.angle) : ¬ ∀ i, T.angle i = Real.pi / 3 := by
  intro he
  have hi : (0 : Fin 3) = 1 := h ((he 0).trans (he 1).symm)
  exact (by decide : (0 : Fin 3) ≠ 1) hi

end Triangle

namespace Tiling

theorem tile_incommensurable_scalene_angle_classification {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hscalene : Function.Injective T.angle) :
    ReptilingAngles d.tile T ∨ SixAngleShapes d.tile T :=
  d.incommensurable_scalene_angle_classification
    (d.outer_incommensurable_of_tile (T.not_equilateral_of_injective_angles hscalene) hirr)
    hscalene

theorem incommensurable_tile_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi)) :
    EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · exact d.incommensurable_necessary hn
      (d.outer_incommensurable_of_tile (T.not_equilateral_of_injective_angles hscalene) hirr)
  · exact eightCases_of_not_injective_angles T hscalene

theorem rational_angles_of_counterexample {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    (∀ i, IsRational (d.tile.angle i / Real.pi)) ∧
      (∀ i, IsRational (T.angle i / Real.pi)) ∧
      Function.Injective T.angle ∧ ¬ ReptilingAngles d.tile T := by
  have ht : ∀ i, IsRational (d.tile.angle i / Real.pi) := by
    by_contra h
    exact hnot (d.incommensurable_tile_necessary hn h)
  refine ⟨ht, d.rational_angles_of_tile ht, ?_, ?_⟩
  · by_contra h
    exact hnot (eightCases_of_not_injective_angles T h)
  · intro h
    exact hnot (d.reptiling_necessary hn h)

end Tiling
end Erdos633b

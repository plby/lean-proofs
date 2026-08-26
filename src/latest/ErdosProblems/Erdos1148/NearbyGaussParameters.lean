import ErdosProblems.Erdos1148.GaussFrameCoordinates
import ErdosProblems.Erdos1148.GaussLiftBoxes

/-! # Bounded Gauss parameters for nearby matrix lifts -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_boundedGaussParameters_of_close {η : ℝ} (hη : η ≤ 1 / 2)
    (g h : SL(2, ℝ)) (hclose : EntryCloseOne η (g⁻¹ * h)) :
    ∃ p : BoundedGaussParameters, gaussParameterFrame g p = h := by
  obtain ⟨r, x, a, ha, hr, hx, hheight, heq⟩ := entryCloseOne_gauss_coordinates hη hclose
  have habs := abs_le.mp hheight
  let p : BoundedGaussParameters := ⟨(r, x, a), by
    exact ⟨by linarith, by linarith, by linarith [habs.1], by linarith [habs.2]⟩⟩
  refine ⟨p, ?_⟩
  change g * unstableHorocycle r * upperTriangularFrame x a _ = h
  calc
    _ = g * (g⁻¹ * h) := by rw [heq, mul_assoc]
    _ = h := by group

theorem exists_boundedGaussParameters_of_forward_tube {η δ : ℝ}
    (hη : η ≤ 1 / 2) (g h : SL(2, ℝ))
    (htube : EntryForwardBowenTube η δ (g⁻¹ * h)) :
    ∃ p : BoundedGaussParameters, gaussParameterFrame g p = h ∧
      |p.val.1| ≤ 2 * δ ∧ |p.val.2.1| ≤ 2 * η ∧ |p.val.2.2 - 1| ≤ η := by
  obtain ⟨r, x, a, ha, hr, hx, hheight, heq⟩ :=
    entryCloseOne_gauss_coordinates hη htube.1
  have habs := abs_le.mp hheight
  have hδ : 0 ≤ δ := (abs_nonneg _).trans htube.2
  have hentry : (g⁻¹ * h) 1 0 = r * a := by
    rw [heq, Matrix.SpecialLinearGroup.coe_mul]
    simp [unstableHorocycle, upperTriangularFrame, Matrix.mul_apply, Fin.sum_univ_two]
  have hrδ : |r| ≤ 2 * δ := by
    have hlower := htube.2
    rw [hentry, abs_mul, abs_of_pos ha] at hlower
    nlinarith [abs_nonneg r, habs.1]
  let p : BoundedGaussParameters := ⟨(r, x, a), by
    exact ⟨by linarith, by linarith, by linarith [habs.1], by linarith [habs.2]⟩⟩
  refine ⟨p, ?_, hrδ, hx, hheight⟩
  change g * unstableHorocycle r * upperTriangularFrame x a _ = h
  calc
    _ = g * (g⁻¹ * h) := by rw [heq, mul_assoc]
    _ = h := by group

end Erdos1148.DukeArithmetic

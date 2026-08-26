import ErdosProblems.Erdos633b.SixtyTranslations
import ErdosProblems.Erdos633b.EquilateralPartition

/-! Actual rigid rotations identify the three equilateral trapezoid regions. -/

namespace Erdos633b.Sixty

theorem point_of_coords (d : ℝ) (hd : 0 < d) (p : Plane) :
    point d ((frame d hd).coord 1 p) ((frame d hd).coord 2 p) = p := by
  rw [point_eq_latticeShift d hd]
  have h := (frame d hd).reconstruct p
  have h0 : (frame d hd).points 0 = 0 := point_zero d
  simpa only [h0, add_zero] using h

theorem rotation120_point (d : ℝ) (he : d ^ 2 = 3) (s t : ℝ) :
    rotation (-1 / 2) (d / 2) (by nlinarith) (point d s t) = point d (-s - t) s := by
  change rotationMap (-1 / 2) (d / 2) (point d s t) = _
  ext i
  fin_cases i
  · simp [rotationMap, point]
    linear_combination -(t / 4) * he
  · simp [rotationMap, point]
    ring

noncomputable def turn (d : ℝ) (he : d ^ 2 = 3) (q : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rotation (-1 / 2) (d / 2) (by nlinarith)).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ Plane (point d (3 * q) 0))

theorem turn_point (d : ℝ) (he : d ^ 2 = 3) (q s t : ℝ) :
    turn d he q (point d s t) = point d (3 * q - s - t) s := by
  change point d (3 * q) 0 + rotation (-1 / 2) (d / 2) (by nlinarith) (point d s t) = _
  rw [rotation120_point d he, ← point_add]
  congr 1 <;> ring

theorem turn_coords (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (q : ℝ) (p : Plane) :
    (frame d hd).coord 1 (turn d he q p) =
      3 * q - (frame d hd).coord 1 p - (frame d hd).coord 2 p ∧
      (frame d hd).coord 2 (turn d he q p) = (frame d hd).coord 1 p := by
  have hp : turn d he q p =
      point d (3 * q - (frame d hd).coord 1 p - (frame d hd).coord 2 p)
        ((frame d hd).coord 1 p) := by
    calc
      _ = turn d he q (point d ((frame d hd).coord 1 p) ((frame d hd).coord 2 p)) := by
        rw [point_of_coords d hd]
      _ = _ := turn_point d he q _ _
  rw [hp]
  exact frame_coords d hd _ _

theorem turn_image_first (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (q : ℝ) :
    turn d he q '' EquilateralPartition.region (frame d hd) q .first =
      EquilateralPartition.region (frame d hd) q .second := by
  ext p
  constructor
  · rintro ⟨v, ⟨hs, ht, hty, hsum⟩, rfl⟩
    change 0 ≤ (frame d hd).coord 2 (turn d he q v) ∧
      q ≤ (frame d hd).coord 1 (turn d he q v) ∧
      2 * q ≤ (frame d hd).coord 1 (turn d he q v) + (frame d hd).coord 2 (turn d he q v) ∧
      (frame d hd).coord 1 (turn d he q v) + (frame d hd).coord 2 (turn d he q v) ≤ 3 * q
    rw [(turn_coords d hd he q v).1, (turn_coords d hd he q v).2]
    exact ⟨hs, by linarith, by linarith, by linarith⟩
  · rintro ⟨ht, hs, hlo, hhi⟩
    refine ⟨(turn d he q).symm p, ?_, (turn d he q).apply_symm_apply p⟩
    have hh := turn_coords d hd he q ((turn d he q).symm p)
    rw [(turn d he q).apply_symm_apply p] at hh
    change 0 ≤ (frame d hd).coord 1 ((turn d he q).symm p) ∧
      0 ≤ (frame d hd).coord 2 ((turn d he q).symm p) ∧
      (frame d hd).coord 2 ((turn d he q).symm p) ≤ q ∧
      (frame d hd).coord 1 ((turn d he q).symm p) +
        (frame d hd).coord 2 ((turn d he q).symm p) ≤ 2 * q
    exact ⟨by linarith [hh.2], by linarith [hh.1, hh.2],
      by linarith [hh.1, hh.2], by linarith [hh.1, hh.2]⟩

theorem turn_image_second (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (q : ℝ) :
    turn d he q '' EquilateralPartition.region (frame d hd) q .second =
      EquilateralPartition.region (frame d hd) q .third := by
  ext p
  constructor
  · rintro ⟨v, ⟨ht, hs, hlo, hhi⟩, rfl⟩
    change 0 ≤ (frame d hd).coord 1 (turn d he q v) ∧
      (frame d hd).coord 1 (turn d he q v) ≤ q ∧
      q ≤ (frame d hd).coord 2 (turn d he q v) ∧
      (frame d hd).coord 1 (turn d he q v) + (frame d hd).coord 2 (turn d he q v) ≤ 3 * q
    rw [(turn_coords d hd he q v).1, (turn_coords d hd he q v).2]
    exact ⟨by linarith, by linarith, hs, by linarith⟩
  · rintro ⟨hs, hs1, ht, hsum⟩
    refine ⟨(turn d he q).symm p, ?_, (turn d he q).apply_symm_apply p⟩
    have hh := turn_coords d hd he q ((turn d he q).symm p)
    rw [(turn d he q).apply_symm_apply p] at hh
    change 0 ≤ (frame d hd).coord 2 ((turn d he q).symm p) ∧
      q ≤ (frame d hd).coord 1 ((turn d he q).symm p) ∧
      2 * q ≤ (frame d hd).coord 1 ((turn d he q).symm p) +
        (frame d hd).coord 2 ((turn d he q).symm p) ∧
      (frame d hd).coord 1 ((turn d he q).symm p) +
        (frame d hd).coord 2 ((turn d he q).symm p) ≤ 3 * q
    exact ⟨by linarith [hh.1, hh.2], by linarith [hh.2],
      by linarith [hh.1, hh.2], by linarith [hh.1, hh.2]⟩

end Erdos633b.Sixty

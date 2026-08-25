import StackExchange.Puzzling139335.AcuteCorner.Defs
import StackExchange.Puzzling139335.PlaneIsometries

namespace Puzzling139335.AcuteCorner

open Set

/-- Two vectors in the explicit forty-five-degree cone have determinant
bounded in absolute value by their scalar product. -/
theorem cone45_pair_bound {u v : Plane}
    (hu : u ∈ cone45) (hv : v ∈ cone45) :
    |det u v| ≤ dot u v := by
  change 0 ≤ u 1 ∧ u 1 ≤ u 0 at hu
  change 0 ≤ v 1 ∧ v 1 ≤ v 0 at hv
  have hu0 : 0 ≤ u 0 := le_trans hu.1 hu.2
  have hv0 : 0 ≤ v 0 := le_trans hv.1 hv.2
  apply abs_le.mpr
  dsimp [det, dot]
  constructor
  · nlinarith only [
      mul_le_mul_of_nonneg_right hu.2 hv0,
      mul_nonneg hu0 hv.1, mul_nonneg hu.1 hv.1]
  · nlinarith only [
      mul_le_mul_of_nonneg_left hv.2 hu0,
      mul_nonneg hu.1 hv0, mul_nonneg hu.1 hv.1]

/-- Affine Euclidean isometries preserve scalar products of displacements
and absolute determinants, including the orientation-reversing case. -/
theorem affine_pair_invariants
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b v : Plane) :
    dot (e a - e v) (e b - e v) = dot (a - v) (b - v) ∧
      |det (e a - e v) (e b - e v)| = |det (a - v) (b - v)| := by
  obtain ⟨c, s, hcs, he | he⟩ :=
    PlaneIsometries.affine_coordinate_classification e
  · have hdot :
        dot (e a - e v) (e b - e v) = (c ^ 2 + s ^ 2) * dot (a - v) (b - v) := by
      rw [he a, he b, he v]
      simp [dot, PlaneIsometries.directCoordinates]
      ring
    have hdet :
        det (e a - e v) (e b - e v) = (c ^ 2 + s ^ 2) * det (a - v) (b - v) := by
      rw [he a, he b, he v]
      simp [det, PlaneIsometries.directCoordinates]
      ring
    constructor
    · simpa [hcs] using hdot
    · rw [hdet, hcs, one_mul]
  · have hdot :
        dot (e a - e v) (e b - e v) = (c ^ 2 + s ^ 2) * dot (a - v) (b - v) := by
      rw [he a, he b, he v]
      simp [dot, PlaneIsometries.reversingCoordinates]
      ring
    have hdet :
        det (e a - e v) (e b - e v) = -(c ^ 2 + s ^ 2) * det (a - v) (b - v) := by
      rw [he a, he b, he v]
      simp [det, PlaneIsometries.reversingCoordinates]
      ring
    constructor
    · simpa [hcs] using hdot
    · rw [hdet, hcs]
      simp

/-- An affine isometry preserves the scalar product of two displacements. -/
theorem affine_dot_sub (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b v : Plane) :
    dot (e a - e v) (e b - e v) = dot (a - v) (b - v) :=
  (affine_pair_invariants e a b v).1

/-- An affine isometry preserves the absolute determinant of two displacements. -/
theorem affine_abs_det_sub (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b v : Plane) :
    |det (e a - e v) (e b - e v)| = |det (a - v) (b - v)| :=
  (affine_pair_invariants e a b v).2

/-- The determinant bound holds for actual points of any set with a
forty-five-degree supporting cone at the specified vertex. -/
theorem Supports45.pair_bound {P : Set Plane} {v a b : Plane}
    (h : Supports45 P v) (ha : a ∈ P) (hb : b ∈ P) :
    |det (a - v) (b - v)| ≤ dot (a - v) (b - v) := by
  obtain ⟨e, hev, hP⟩ := h
  have hcone := cone45_pair_bound (hP (mem_image_of_mem e ha))
    (hP (mem_image_of_mem e hb))
  have hdisplacements :
      |det (e a - e v) (e b - e v)| ≤ dot (e a - e v) (e b - e v) := by
    simpa [hev] using hcone
  rw [affine_abs_det_sub, affine_dot_sub] at hdisplacements
  exact hdisplacements

/-- Supporting-cone containment transports through a genuine affine
Euclidean isometry of the whole plane. -/
theorem Supports45.image {P : Set Plane} {v : Plane}
    (h : Supports45 P v) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    Supports45 (e '' P) (e v) := by
  obtain ⟨f, hfv, hP⟩ := h
  refine ⟨e.symm.trans f, ?_, ?_⟩
  · simpa using hfv
  · rintro y ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    simpa using hP (mem_image_of_mem f hp)

end Puzzling139335.AcuteCorner

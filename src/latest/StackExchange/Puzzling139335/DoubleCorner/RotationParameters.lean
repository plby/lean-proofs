import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity.Normalized

/-!
# Parameters of a rotation between two pieces at the origin

The source and image are actual subsets of the square.  Their nonempty
interiors force the cosine of an origin-fixing rotation to be positive.
If their interiors are disjoint, the sine cannot vanish.  Reversing the
congruence changes only the sign of the sine and exchanges the actual sets.
-/

open Set

namespace Puzzling139335.DoubleCorner

noncomputable section

open PlaneIsometries

/-- A normalized rotation fixes the origin. -/
theorem normalized_rotation_fixes_zero (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (he : ∀ p, e p = directCoordinates c s 0 p) : e 0 = 0 := by
  rw [he]
  apply plane_ext <;> simp [directCoordinates]

/-- A rotation fitting a set with nonempty interior and its image into
the positive square has strictly positive cosine. -/
theorem normalized_rotation_cos_pos (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (he : ∀ p, e p = directCoordinates c s 0 p)
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : 0 < c := by
  obtain ⟨p, hp⟩ := hint
  have hpS := SquareSymmetry.interior_unitSquare_coordinates (interior_mono hP hp)
  have hep : e p ∈ interior (e '' P) :=
    (mem_interior_image_affineIsometry e).mpr hp
  have hepS := SquareSymmetry.interior_unitSquare_coordinates (interior_mono heP hep)
  have hdot : p 0 * (e p) 0 + p 1 * (e p) 1 = c * ((p 0) ^ 2 + (p 1) ^ 2) := by
    rw [he p]
    simp only [directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    ring
  have hprod : 0 < c * ((p 0) ^ 2 + (p 1) ^ 2) := by
    rw [← hdot]
    exact add_pos (mul_pos hpS.1.1 hepS.1.1) (mul_pos hpS.2.1 hepS.2.1)
  exact pos_of_mul_pos_left hprod (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Disjoint interiors exclude the identity rotation.  Once square fit
has forced positive cosine, this is exactly the nonvanishing of sine. -/
theorem normalized_rotation_sin_ne_zero (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty)
    (hdis : Disjoint (interior P) (interior (e '' P))) : s ≠ 0 := by
  have hc := normalized_rotation_cos_pos e he hP heP hint
  intro hs
  have hc1 : c = 1 := by nlinarith
  have heid (p : Plane) : e p = p := by
    rw [he p, hc1, hs]
    apply plane_ext <;> simp [directCoordinates]
  obtain ⟨p, hp⟩ := hint
  have hep := (mem_interior_image_affineIsometry e).mpr hp
  rw [heid p] at hep
  exact Set.disjoint_left.mp hdis hp hep

/-- The complete elementary bounds for a nontrivial rotation fitting
two disjoint-interior copies in the normalized square. -/
theorem normalized_rotation_parameter_bounds (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty)
    (hdis : Disjoint (interior P) (interior (e '' P))) :
    0 < c ∧ c < 1 ∧ s ≠ 0 ∧ -1 < s ∧ s < 1 := by
  have hc := normalized_rotation_cos_pos e he hP heP hint
  have hs := normalized_rotation_sin_ne_zero e hcs he hP heP hint hdis
  have hs2 := sq_pos_of_ne_zero hs
  have hc2 := sq_pos_of_pos hc
  refine ⟨hc, ?_, hs, ?_, ?_⟩ <;> nlinarith

/-- Multiplying opposite rotation coordinate matrices cancels exactly. -/
theorem directCoordinates_neg_comp_self {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (p : Plane) :
    directCoordinates c (-s) 0 (directCoordinates c s 0 p) = p := by
  apply plane_ext
  · simp only [directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    calc
      c * (c * p 0 - s * p 1) - -s * (s * p 0 + c * p 1) =
          (c ^ 2 + s ^ 2) * p 0 := by ring
      _ = p 0 := by rw [hcs, one_mul]
  · simp only [directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    calc
      -s * (c * p 0 - s * p 1) + c * (s * p 0 + c * p 1) =
          (c ^ 2 + s ^ 2) * p 1 := by ring
      _ = p 1 := by rw [hcs, one_mul]

/-- The inverse of a normalized direct rotation has the same cosine and
the opposite sine. -/
theorem normalized_rotation_symm_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (he : ∀ p, e p = directCoordinates c s 0 p) (p : Plane) :
    e.symm p = directCoordinates c (-s) 0 p := by
  calc
    e.symm p = directCoordinates c (-s) 0 (directCoordinates c s 0 (e.symm p)) :=
      (directCoordinates_neg_comp_self hcs (e.symm p)).symm
    _ = directCoordinates c (-s) 0 p := by rw [← he, e.apply_symm_apply]

/-- Reversing the congruence exchanges the actual pieces and preserves
their nonempty interiors and disjointness. -/
theorem rotation_inverse_pair (e : Plane ≃ᵃⁱ[ℝ] Plane) {P : Set Plane}
    (hint : (interior P).Nonempty)
    (hdis : Disjoint (interior P) (interior (e '' P))) :
    e.symm '' (e '' P) = P ∧ (interior (e '' P)).Nonempty ∧
      Disjoint (interior (e '' P)) (interior (e.symm '' (e '' P))) := by
  have himage : e.symm '' (e '' P) = P := by rw [Set.image_image]; simp
  refine ⟨himage, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hint
    exact ⟨e p, (mem_interior_image_affineIsometry e).mpr hp⟩
  · simpa only [himage] using hdis.symm

end

end Puzzling139335.DoubleCorner

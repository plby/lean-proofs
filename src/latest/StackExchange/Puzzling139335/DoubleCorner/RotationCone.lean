import StackExchange.Puzzling139335.AcuteCorner.Cone
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Supporting cones forced by a rotation at a square corner

The assumptions here are coordinate formulas for a genuine affine isometry
and containment of the actual sets in the square. No boundary sector or
convex-hull identification is assumed.
-/

open Set

namespace Puzzling139335.DoubleCorner

noncomputable section

open AcuteCorner PlaneIsometries

/-- The interior of a coordinate half-plane is the strict half-plane. -/
theorem interior_coord_le (i j : Fin 2) (hij : i ≠ j) :
    interior {p : Plane | p i ≤ p j} = {p : Plane | p i < p j} := by
  let f : Plane →L[ℝ] ℝ := EuclideanSpace.proj i - EuclideanSpace.proj j
  have hsurj : Function.Surjective f := by
    intro r
    refine ⟨EuclideanSpace.single i r, ?_⟩
    simp [f, hij.symm]
  have heq : {p : Plane | p i ≤ p j} = f ⁻¹' Iic 0 := by
    ext p
    simp [f]
  rw [heq, f.interior_preimage hsurj]
  ext p
  simp [f]

/-- A set on either side of the diagonal cannot contain a neighborhood of
any point of that diagonal. -/
theorem not_mem_interior_of_diagonal_support {P : Set Plane} {p : Plane}
    (hp : p 0 = p 1)
    (hP : (∀ q ∈ P, q 0 ≤ q 1) ∨ (∀ q ∈ P, q 1 ≤ q 0)) :
    p ∉ interior P := by
  intro hpP
  rcases hP with hP | hP
  · have hmem := interior_mono (show P ⊆ {q : Plane | q 0 ≤ q 1} from hP) hpP
    rw [interior_coord_le 0 1 (by decide)] at hmem
    exact (ne_of_lt hmem) hp
  · have hmem := interior_mono (show P ⊆ {q : Plane | q 1 ≤ q 0} from hP) hpP
    rw [interior_coord_le 1 0 (by decide)] at hmem
    exact (ne_of_lt hmem) hp.symm

theorem squareCenter_not_mem_interior_of_diagonal_support {P : Set Plane}
    (hP : (∀ q ∈ P, q 0 ≤ q 1) ∨ (∀ q ∈ P, q 1 ≤ q 0)) :
    squareCenter ∉ interior P :=
  not_mem_interior_of_diagonal_support rfl hP

private theorem supports45_of_subset_cone {P : Set Plane} (hP : P ⊆ cone45) :
    Supports45 P 0 := by
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, rfl, ?_⟩
  simpa using hP

private theorem supports45_of_upper_cone {P : Set Plane}
    (hP : ∀ p ∈ P, 0 ≤ p 0 ∧ p 0 ≤ p 1) : Supports45 P 0 := by
  refine ⟨ReflectionSeparation.diagonal, ?_, ?_⟩
  · apply plane_ext <;> simp
  · rintro p ⟨q, hq, rfl⟩
    simpa [cone45] using hP q hq

/-- For a positive rotation of at least 45 degrees and less than 90
degrees, square fit gives opposite diagonal supports to the actual copies. -/
theorem positive_rotation_square_cones {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare) :
    P ⊆ cone45 ∧ (∀ q ∈ e '' P, 0 ≤ q 0 ∧ q 0 ≤ q 1) := by
  constructor
  · intro p hp
    have hpS := hP hp
    have hepS := heP (mem_image_of_mem e hp)
    have hrot : 0 ≤ c * p 0 - s * p 1 := by
      simpa [he p, directCoordinates] using hepS.1.1
    refine ⟨hpS.2.1, ?_⟩
    have hs : c * p 1 ≤ s * p 1 := mul_le_mul_of_nonneg_right hcs hpS.2.1
    exact (mul_le_mul_iff_right₀ hc).mp (by linarith)
  · rintro q ⟨p, hp, rfl⟩
    have hpS := hP hp
    have hepS := heP (mem_image_of_mem e hp)
    refine ⟨hepS.1.1, ?_⟩
    rw [he p]
    simp only [directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    have hx := mul_nonneg (sub_nonneg.mpr hcs) hpS.1.1
    have hy := mul_nonneg (show 0 ≤ c + s by linarith) hpS.2.1
    nlinarith only [hx, hy]

/-- Both actual copies have 45-degree supporting cones, and neither
contains an interior neighborhood of the square center. -/
theorem positive_rotation_support_and_center_exclusion {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare) :
    Supports45 P 0 ∧ Supports45 (e '' P) 0 ∧
      squareCenter ∉ interior P ∧ squareCenter ∉ interior (e '' P) := by
  obtain ⟨hbelow, habove⟩ := positive_rotation_square_cones e hc hcs he hP heP
  refine ⟨supports45_of_subset_cone hbelow, supports45_of_upper_cone habove, ?_, ?_⟩
  · exact squareCenter_not_mem_interior_of_diagonal_support
      (Or.inr (fun p hp => (hbelow hp).2))
  · exact squareCenter_not_mem_interior_of_diagonal_support
      (Or.inl (fun p hp => (habove p hp).2))

/-- The normalized positive 45-degree rotation is a specialization with
equal sine and cosine; no choice of square root is needed. -/
theorem rotation45_support_and_center_exclusion {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c : ℝ} (hc : 0 < c)
    (he : ∀ p, e p = directCoordinates c c 0 p)
    (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare) :
    Supports45 P 0 ∧ Supports45 (e '' P) 0 ∧
      squareCenter ∉ interior P ∧ squareCenter ∉ interior (e '' P) :=
  positive_rotation_support_and_center_exclusion e hc le_rfl he hP heP

/-- The reflected-angle version: a negative rotation whose magnitude is
at least 45 degrees puts the source above, and its image below, the diagonal. -/
theorem negative_rotation_square_cones {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ} (hc : 0 < c) (hcs : c ≤ -s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare) :
    (∀ p ∈ P, 0 ≤ p 0 ∧ p 0 ≤ p 1) ∧ e '' P ⊆ cone45 := by
  constructor
  · intro p hp
    have hpS := hP hp
    have hepS := heP (mem_image_of_mem e hp)
    have hrot : 0 ≤ s * p 0 + c * p 1 := by
      simpa [he p, directCoordinates] using hepS.2.1
    refine ⟨hpS.1.1, ?_⟩
    have hs := mul_le_mul_of_nonneg_right hcs hpS.1.1
    exact (mul_le_mul_iff_right₀ hc).mp (by nlinarith only [hs, hrot])
  · rintro q ⟨p, hp, rfl⟩
    have hpS := hP hp
    have hepS := heP (mem_image_of_mem e hp)
    refine ⟨hepS.2.1, ?_⟩
    rw [he p]
    simp only [directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    have hx := mul_nonneg (show 0 ≤ c - s by linarith) hpS.1.1
    have hy := mul_nonneg (show 0 ≤ -s - c by linarith) hpS.2.1
    nlinarith only [hx, hy]

theorem negative_rotation_support_and_center_exclusion {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ} (hc : 0 < c) (hcs : c ≤ -s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare) :
    Supports45 P 0 ∧ Supports45 (e '' P) 0 ∧
      squareCenter ∉ interior P ∧ squareCenter ∉ interior (e '' P) := by
  obtain ⟨habove, hbelow⟩ := negative_rotation_square_cones e hc hcs he hP heP
  refine ⟨supports45_of_upper_cone habove, supports45_of_subset_cone hbelow, ?_, ?_⟩
  · exact squareCenter_not_mem_interior_of_diagonal_support
      (Or.inl (fun p hp => (habove p hp).2))
  · exact squareCenter_not_mem_interior_of_diagonal_support
      (Or.inr (fun p hp => (hbelow hp).2))

/-- A coordinate level has no ambient planar interior. -/
theorem interior_coord_eq_empty (i : Fin 2) (a : ℝ) :
    interior {p : Plane | p i = a} = ∅ := by
  have hsurj : Function.Surjective (EuclideanSpace.proj (𝕜 := ℝ) i) := by
    intro r
    exact ⟨EuclideanSpace.single i r, by simp⟩
  change interior ((EuclideanSpace.proj (𝕜 := ℝ) i) ⁻¹' {a}) = ∅
  rw [(EuclideanSpace.proj (𝕜 := ℝ) i).interior_preimage hsurj]
  simp

/-- An origin-fixing quarter-turn can fit together with its source in the
square only if that source has empty interior. -/
theorem quarterTurn_square_fit_empty_interior {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {s : ℝ} (hs : s ≠ 0)
    (he : ∀ p, e p = directCoordinates 0 s 0 p)
    (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare) :
    interior P = ∅ := by
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have hlevel : P ⊆ {p : Plane | p 0 = 0} := by
      intro p hp
      have hpS := hP hp
      have hepS := heP (mem_image_of_mem e hp)
      have hrot : 0 ≤ s * p 0 := by
        simpa [he p, directCoordinates] using hepS.2.1
      have hle : p 0 ≤ 0 := ((mul_nonneg_iff_neg_imp_nonpos).mp hrot).1 hsneg
      exact le_antisymm hle hpS.1.1
    exact subset_empty_iff.mp (by simpa [interior_coord_eq_empty] using interior_mono hlevel)
  · have hlevel : P ⊆ {p : Plane | p 1 = 0} := by
      intro p hp
      have hpS := hP hp
      have hepS := heP (mem_image_of_mem e hp)
      have hrot : 0 ≤ -(s * p 1) := by
        simpa [he p, directCoordinates] using hepS.1.1
      have hle : p 1 ≤ 0 := by
        have hmul : 0 ≤ (-s) * p 1 := by nlinarith only [hrot]
        exact ((mul_nonneg_iff_neg_imp_nonpos).mp hmul).1 (by linarith)
      exact le_antisymm hle hpS.2.1
    exact subset_empty_iff.mp (by simpa [interior_coord_eq_empty] using interior_mono hlevel)

end

end Puzzling139335.DoubleCorner

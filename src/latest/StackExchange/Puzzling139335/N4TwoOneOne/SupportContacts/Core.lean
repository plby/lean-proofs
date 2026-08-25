import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.SourceFaceBridge.SupportingFaces
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# Actual supporting points of the three-corner source

The statements in this file concern points of the source itself. No convexity,
polygonal boundary, or positive boundary measure is assumed.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.SupportContacts

noncomputable section

abbrev SupportsAt := SourceFaceBridge.SupportsAt
abbrev HasTwoSupportPoints := SourceFaceBridge.HasTwoSupportPoints

/-- The actual source conditions used by the contact argument. -/
structure SourceSupport (P : Set Plane) (θ u v : ℝ) : Prop where
  subset_square : P ⊆ unitSquare
  base_left : corner 0 ∈ P
  base_right : corner 1 ∈ P
  upper_corner : sourceCorner θ u v ∈ P
  e_le : ∀ p ∈ P, eCoord θ p ≤ u
  f_le : ∀ p ∈ P, fCoord θ p ≤ v

theorem cos_sq_add_sin_sq (θ : ℝ) : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
  nlinarith only [Real.sin_sq_add_cos_sq θ]

@[simp] theorem eCoord_sourceCorner (θ u v : ℝ) :
    eCoord θ (sourceCorner θ u v) = u := by
  calc
    _ = u * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
      simp only [eCoord, sourceCorner, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
    _ = u := by rw [cos_sq_add_sin_sq, mul_one]

@[simp] theorem fCoord_sourceCorner (θ u v : ℝ) :
    fCoord θ (sourceCorner θ u v) = v := by
  calc
    _ = v * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
      simp only [fCoord, sourceCorner, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
    _ = v := by rw [cos_sq_add_sin_sq, mul_one]

theorem coordinate_zero_reconstruction (θ : ℝ) (p : Plane) :
    Real.cos θ * eCoord θ p - Real.sin θ * fCoord θ p = p 0 := by
  calc
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * p 0 := by
      simp only [eCoord, fCoord]
      ring
    _ = p 0 := by rw [cos_sq_add_sin_sq, one_mul]

theorem coordinate_one_reconstruction (θ : ℝ) (p : Plane) :
    Real.sin θ * eCoord θ p + Real.cos θ * fCoord θ p = p 1 := by
  calc
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * p 1 := by
      simp only [eCoord, fCoord]
      ring
    _ = p 1 := by rw [cos_sq_add_sin_sq, one_mul]

theorem eq_sourceCorner_of_coordinates {θ u v : ℝ} {p : Plane}
    (he : eCoord θ p = u) (hf : fCoord θ p = v) : p = sourceCorner θ u v := by
  apply PlaneIsometries.plane_ext
  · simpa only [he, hf, sourceCorner, Matrix.cons_val_zero, mul_comm] using
      (coordinate_zero_reconstruction θ p).symm
  · simpa only [he, hf, sourceCorner, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_comm] using
      (coordinate_one_reconstruction θ p).symm

/-- Expansion of an arbitrary normal in the two source-corner normals. -/
theorem normal_decomposition (θ a b : ℝ) (p : Plane) :
    a * p 0 + b * p 1 =
      (a * Real.cos θ + b * Real.sin θ) * eCoord θ p +
      (-a * Real.sin θ + b * Real.cos θ) * fCoord θ p := by
  calc
    _ = a * (Real.cos θ * eCoord θ p - Real.sin θ * fCoord θ p) +
        b * (Real.sin θ * eCoord θ p + Real.cos θ * fCoord θ p) := by
      rw [coordinate_zero_reconstruction, coordinate_one_reconstruction]
    _ = _ := by ring

/-- A strictly southwest normal uniquely supports the source at its left base corner. -/
theorem supportsAt_iff_eq_base_left {P : Set Plane} (hP : P ⊆ unitSquare)
    (hA : corner 0 ∈ P) {a b : ℝ} (ha : a < 0) (hb : b < 0) {p : Plane} :
    SupportsAt P a b p ↔ p = corner 0 := by
  constructor
  · rintro ⟨hp, hmax⟩
    have hbox := hP hp
    have hsum : 0 ≤ a * p 0 + b * p 1 := by
      simpa only [corner, show (0 : Fin 4) ≠ 1 by decide,
        show (0 : Fin 4) ≠ 2 by decide, show (0 : Fin 4) ≠ 3 by decide,
        or_self, if_false, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_zero, add_zero] using hmax (corner 0) hA
    have hax : a * p 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le hbox.1.1
    have hby : b * p 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb.le hbox.2.1
    have hpx : p 0 = 0 := by
      have hz : a * p 0 = 0 := by linarith only [hsum, hax, hby]
      exact (mul_eq_zero.mp hz).resolve_left ha.ne
    have hpy : p 1 = 0 := by
      have hz : b * p 1 = 0 := by linarith only [hsum, hax, hby]
      exact (mul_eq_zero.mp hz).resolve_left hb.ne
    apply PlaneIsometries.plane_ext <;> simp [corner, hpx, hpy]
  · rintro rfl
    refine ⟨hA, ?_⟩
    intro q hq
    have hbox := hP hq
    simpa [corner] using add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg ha.le hbox.1.1)
      (mul_nonpos_of_nonpos_of_nonneg hb.le hbox.2.1)

/-- A strictly southeast normal uniquely supports the source at its right base corner. -/
theorem supportsAt_iff_eq_base_right {P : Set Plane} (hP : P ⊆ unitSquare)
    (hB : corner 1 ∈ P) {a b : ℝ} (ha : 0 < a) (hb : b < 0) {p : Plane} :
    SupportsAt P a b p ↔ p = corner 1 := by
  constructor
  · rintro ⟨hp, hmax⟩
    have hbox := hP hp
    have hsum : a ≤ a * p 0 + b * p 1 := by
      simpa [corner] using hmax (corner 1) hB
    have hax : a * p 0 ≤ a := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbox.1.2 ha.le
    have hby : b * p 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb.le hbox.2.1
    have hpx : p 0 = 1 := by
      have hz : a * (p 0 - 1) = 0 := by nlinarith only [hsum, hax, hby]
      have hz' := (mul_eq_zero.mp hz).resolve_left ha.ne'
      linarith only [hz']
    have hpy : p 1 = 0 := by
      have hz : b * p 1 = 0 := by linarith only [hsum, hax, hby]
      exact (mul_eq_zero.mp hz).resolve_left hb.ne
    apply PlaneIsometries.plane_ext <;> simp [corner, hpx, hpy]
  · rintro rfl
    refine ⟨hB, ?_⟩
    intro q hq
    have hbox := hP hq
    have hax : a * q 0 ≤ a := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbox.1.2 ha.le
    have hby : b * q 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb.le hbox.2.1
    simpa [corner] using add_le_add hax hby

/-- Positive components in both outward source-corner normals give a unique maximizer. -/
theorem supportsAt_iff_eq_upper_corner {P : Set Plane} {θ u v a b : ℝ}
    (h : SourceSupport P θ u v)
    (hα : 0 < a * Real.cos θ + b * Real.sin θ)
    (hβ : 0 < -a * Real.sin θ + b * Real.cos θ) {p : Plane} :
    SupportsAt P a b p ↔ p = sourceCorner θ u v := by
  constructor
  · rintro ⟨hp, hmax⟩
    have he := h.e_le p hp
    have hf := h.f_le p hp
    have hαe := mul_le_mul_of_nonneg_left he hα.le
    have hβf := mul_le_mul_of_nonneg_left hf hβ.le
    have hsum := hmax (sourceCorner θ u v) h.upper_corner
    rw [normal_decomposition θ a b (sourceCorner θ u v),
      normal_decomposition θ a b p, eCoord_sourceCorner, fCoord_sourceCorner] at hsum
    have heq : eCoord θ p = u := by
      apply (mul_left_cancel₀ hα.ne')
      linarith only [hαe, hβf, hsum]
    have hfq : fCoord θ p = v := by
      apply (mul_left_cancel₀ hβ.ne')
      linarith only [hαe, hβf, hsum]
    exact eq_sourceCorner_of_coordinates heq hfq
  · rintro rfl
    refine ⟨h.upper_corner, ?_⟩
    intro q hq
    rw [normal_decomposition θ a b q,
      normal_decomposition θ a b (sourceCorner θ u v),
      eCoord_sourceCorner, fCoord_sourceCorner]
    exact add_le_add (mul_le_mul_of_nonneg_left (h.e_le q hq) hα.le)
      (mul_le_mul_of_nonneg_left (h.f_le q hq) hβ.le)

theorem not_hasTwoSupportPoints_downward {P : Set Plane} {θ u v a b : ℝ}
    (h : SourceSupport P θ u v) (ha : a ≠ 0) (hb : b < 0) :
    ¬ HasTwoSupportPoints P a b := by
  rintro ⟨p, q, hpq, hp, hq⟩
  rcases lt_or_gt_of_ne ha with ha | ha
  · exact hpq (((supportsAt_iff_eq_base_left h.subset_square h.base_left ha hb).mp hp).trans
      ((supportsAt_iff_eq_base_left h.subset_square h.base_left ha hb).mp hq).symm)
  · exact hpq (((supportsAt_iff_eq_base_right h.subset_square h.base_right ha hb).mp hp).trans
      ((supportsAt_iff_eq_base_right h.subset_square h.base_right ha hb).mp hq).symm)

theorem not_hasTwoSupportPoints_strict_upper {P : Set Plane} {θ u v a b : ℝ}
    (h : SourceSupport P θ u v)
    (hα : 0 < a * Real.cos θ + b * Real.sin θ)
    (hβ : 0 < -a * Real.sin θ + b * Real.cos θ) :
    ¬ HasTwoSupportPoints P a b := by
  rintro ⟨p, q, hpq, hp, hq⟩
  exact hpq (((supportsAt_iff_eq_upper_corner h hα hβ).mp hp).trans
    ((supportsAt_iff_eq_upper_corner h hα hβ).mp hq).symm)

end

end Puzzling139335.N4TwoOneOne.SupportContacts

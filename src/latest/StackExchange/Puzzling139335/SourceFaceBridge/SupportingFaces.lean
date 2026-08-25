import StackExchange.Puzzling139335.SourceFaceBridge.ProperModel

/-!
# Supporting points of a source containing the unit base

For a source inside the lower half-square, a downward nonvertical normal
has a unique maximizing source point: one of the two base endpoints.
Consequently, opposite nonaxis normals cannot both have two distinct
supporting points.  These statements concern the actual source set and
require neither convexity nor a topological assumption.
-/

open Set

namespace Puzzling139335.SourceFaceBridge

/-- An actual source point maximizing the linear functional with normal `(nx,ny)`. -/
def SupportsAt (P : Set Plane) (nx ny : ℝ) (p : Plane) : Prop :=
  p ∈ P ∧ ∀ q ∈ P, nx * q 0 + ny * q 1 ≤ nx * p 0 + ny * p 1

/-- A supporting line contains two distinct actual source points. -/
def HasTwoSupportPoints (P : Set Plane) (nx ny : ℝ) : Prop :=
  ∃ p q : Plane, p ≠ q ∧ SupportsAt P nx ny p ∧ SupportsAt P nx ny q

/-- A strictly southwest normal uniquely supports the actual source at the origin. -/
theorem supportsAt_iff_eq_origin {P : Set Plane} (hP : P ⊆ lowerHalfSquare)
    (hA : point 0 0 ∈ P) {nx ny : ℝ} (hx : nx < 0) (hy : ny < 0) {p : Plane} :
    SupportsAt P nx ny p ↔ p = point 0 0 := by
  constructor
  · rintro ⟨hp, hmax⟩
    have hbox := hP hp
    have hsum : 0 ≤ nx * p 0 + ny * p 1 := by
      simpa only [point_zero, point_one, mul_zero, add_zero] using hmax (point 0 0) hA
    have hxterm : nx * p 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hx.le hbox.1.1
    have hyterm : ny * p 1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hy.le hbox.2.1
    have hpx : p 0 = 0 := by
      have hprod : nx * p 0 = 0 := by linarith only [hsum, hxterm, hyterm]
      exact (mul_eq_zero.mp hprod).resolve_left hx.ne
    have hpy : p 1 = 0 := by
      have hprod : ny * p 1 = 0 := by linarith only [hsum, hxterm, hyterm]
      exact (mul_eq_zero.mp hprod).resolve_left hy.ne
    exact point_ext hpx hpy
  · rintro rfl
    refine ⟨hA, ?_⟩
    intro q hq
    have hbox := hP hq
    simp only [point_zero, point_one, mul_zero, add_zero]
    exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg hx.le hbox.1.1)
      (mul_nonpos_of_nonpos_of_nonneg hy.le hbox.2.1)

/-- A strictly southeast normal uniquely supports the actual source at `(1,0)`. -/
theorem supportsAt_iff_eq_baseRight {P : Set Plane} (hP : P ⊆ lowerHalfSquare)
    (hB : point 1 0 ∈ P) {nx ny : ℝ} (hx : 0 < nx) (hy : ny < 0) {p : Plane} :
    SupportsAt P nx ny p ↔ p = point 1 0 := by
  constructor
  · rintro ⟨hp, hmax⟩
    have hbox := hP hp
    have hsum : nx ≤ nx * p 0 + ny * p 1 := by
      simpa only [point_zero, point_one, mul_one, mul_zero, add_zero] using
        hmax (point 1 0) hB
    have hxterm : nx * p 0 ≤ nx := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbox.1.2 hx.le
    have hyterm : ny * p 1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hy.le hbox.2.1
    have hpx : p 0 = 1 := by
      have hprod : nx * (p 0 - 1) = 0 := by nlinarith only [hsum, hxterm, hyterm]
      have hz : p 0 - 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hx.ne'
      linarith only [hz]
    have hpy : p 1 = 0 := by
      have hprod : ny * p 1 = 0 := by linarith only [hsum, hxterm, hyterm]
      exact (mul_eq_zero.mp hprod).resolve_left hy.ne
    exact point_ext hpx hpy
  · rintro rfl
    refine ⟨hB, ?_⟩
    intro q hq
    have hbox := hP hq
    have hxterm : nx * q 0 ≤ nx := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbox.1.2 hx.le
    have hyterm : ny * q 1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hy.le hbox.2.1
    simpa only [point_zero, point_one, mul_one, mul_zero, add_zero] using
      add_le_add hxterm hyterm

/-- No downward nonvertical normal can have two distinct supporting points. -/
theorem not_hasTwoSupportPoints_of_downward {P : Set Plane} (hP : P ⊆ lowerHalfSquare)
    (hA : point 0 0 ∈ P) (hB : point 1 0 ∈ P) {nx ny : ℝ}
    (hx : nx ≠ 0) (hy : ny < 0) : ¬ HasTwoSupportPoints P nx ny := by
  rintro ⟨p, q, hpq, hp, hq⟩
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact hpq ((supportsAt_iff_eq_origin hP hA hx hy).mp hp |>.trans
      ((supportsAt_iff_eq_origin hP hA hx hy).mp hq).symm)
  · exact hpq ((supportsAt_iff_eq_baseRight hP hB hx hy).mp hp |>.trans
      ((supportsAt_iff_eq_baseRight hP hB hx hy).mp hq).symm)

/-- Opposite nonaxis normals cannot both have nontrivial supporting sets. -/
theorem no_opposite_nonaxis_supports {P : Set Plane} (hP : P ⊆ lowerHalfSquare)
    (hA : point 0 0 ∈ P) (hB : point 1 0 ∈ P) {nx ny : ℝ}
    (hx : nx ≠ 0) (hy : ny ≠ 0) :
    ¬ (HasTwoSupportPoints P nx ny ∧ HasTwoSupportPoints P (-nx) (-ny)) := by
  intro hboth
  rcases lt_or_gt_of_ne hy with hy | hy
  · exact not_hasTwoSupportPoints_of_downward hP hA hB hx hy hboth.1
  · exact not_hasTwoSupportPoints_of_downward hP hA hB
      (neg_ne_zero.mpr hx) (neg_lt_zero.mpr hy) hboth.2

namespace SupportedSource

variable {d : FaceData} {reversed : Bool} {P : Set Plane}

/-- Both named source lines support the actual source in the stated normal directions. -/
theorem supporting_lines (h : SupportedSource d reversed P) :
    ∀ p ∈ P, d.normal₁ p ≤ d.normal₁ d.M₁ ∧ d.normal₂ p ≤ d.normal₂ d.M₂ := by
  intro p hp
  exact ⟨(h.pointValid hp).normal1_upper, (h.pointValid hp).normal2_upper⟩

/-- The opposite nonaxis support obstruction specialized to supported source data. -/
theorem no_opposite_nonaxis_supports (h : SupportedSource d reversed P)
    {nx ny : ℝ} (hx : nx ≠ 0) (hy : ny ≠ 0) :
    ¬ (HasTwoSupportPoints P nx ny ∧ HasTwoSupportPoints P (-nx) (-ny)) :=
  SourceFaceBridge.no_opposite_nonaxis_supports h.source_subset
    (h.base_mem 0 (by norm_num)) (h.base_mem 1 (by norm_num)) hx hy

end SupportedSource

end Puzzling139335.SourceFaceBridge

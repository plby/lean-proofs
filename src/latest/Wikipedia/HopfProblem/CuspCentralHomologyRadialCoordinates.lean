import Wikipedia.HopfProblem.CuspCentralHomologyRadialGauge
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Explicit radial coordinates on the actual honeycomb cell

Dividing a nonzero vector by the displayed cell gauge puts it on the
literal frontier of the base cell. The inverse radial coordinate map
multiplies that frontier point by its positive radius.
-/

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.Radial

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

abbrev CellFrontier := frontier baseCell
abbrev RadialRadius := Ioc (0 : ℝ) 1
abbrev PuncturedCell := {x : Plane // x ∈ baseCell ∧ x ≠ 0}
abbrev Annulus (a : ℝ) := {x : Plane // a < cellGauge x ∧ cellGauge x < 1}
abbrev Collar (a : ℝ) := {x : Plane // a ≤ cellGauge x ∧ cellGauge x ≤ 1}

/-- Normalize using the explicit gauge of the actual cell. -/
noncomputable def normalize (x : Plane) : Plane := (cellGauge x)⁻¹ • x

theorem normalize_gauge (x : Plane) (hx : x ≠ 0) : cellGauge (normalize x) = 1 := by
  rw [normalize, cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (cellGauge_nonneg x))]
  exact inv_mul_cancel₀ ((cellGauge_pos_iff x).mpr hx).ne'

theorem normalize_frontier (x : CellFrontier) : normalize (x : Plane) = (x : Plane) := by
  rw [normalize, (mem_frontier_baseCell_iff (x : Plane)).mp x.2, inv_one, one_smul]

theorem normalize_continuousOn : ContinuousOn normalize {x : Plane | x ≠ 0} :=
  (cellGauge_continuous.continuousOn.inv₀
    (fun x hx => ((cellGauge_pos_iff x).mpr hx).ne')).smul continuous_id.continuousOn

/-- A nonzero vector determines its actual frontier direction. -/
noncomputable def direction (x : {x : Plane // x ≠ 0}) : CellFrontier :=
  ⟨normalize x, (mem_frontier_baseCell_iff _).mpr (normalize_gauge x x.2)⟩

theorem direction_continuous : Continuous direction :=
  normalize_continuousOn.domRestrict.subtype_mk _

theorem cellGauge_smul_frontier (c : ℝ) (hc : 0 ≤ c) (u : CellFrontier) :
    cellGauge (c • (u : Plane)) = c := by
  rw [cellGauge_smul_of_nonneg c hc, (mem_frontier_baseCell_iff _).mp u.2, mul_one]

/-- Radial coordinates on any explicitly specified positive range of radii. -/
noncomputable def radialRangeHomeomorph (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) :
    {x : Plane // cellGauge x ∈ R} ≃ₜ CellFrontier × R where
  toFun x :=
    (direction ⟨x, (cellGauge_pos_iff x).mp (hR _ x.2)⟩, ⟨cellGauge x, x.2⟩)
  invFun p := ⟨(p.2 : ℝ) • (p.1 : Plane), by
    rw [cellGauge_smul_frontier _ (hR _ p.2.2).le]
    exact p.2.2⟩
  left_inv x := by
    apply Subtype.ext
    change cellGauge x • ((cellGauge x)⁻¹ • (x : Plane)) = (x : Plane)
    rw [smul_smul, mul_inv_cancel₀ (hR _ x.2).ne', one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change normalize ((p.2 : ℝ) • (p.1 : Plane)) = (p.1 : Plane)
      rw [normalize, cellGauge_smul_frontier _ (hR _ p.2.2).le,
        smul_smul, inv_mul_cancel₀ (hR _ p.2.2).ne', one_smul]
    · apply Subtype.ext
      exact cellGauge_smul_frontier _ (hR _ p.2.2).le p.1
  continuous_toFun :=
    (direction_continuous.comp (continuous_subtype_val.subtype_mk _)).prodMk
      ((cellGauge_continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _

theorem radialRangeHomeomorph_direction (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (x : {x : Plane // cellGauge x ∈ R}) :
    ((radialRangeHomeomorph R hR x).1 : Plane) = normalize x := rfl

theorem radialRangeHomeomorph_radius (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (x : {x : Plane // cellGauge x ∈ R}) :
    ((radialRangeHomeomorph R hR x).2 : ℝ) = cellGauge x := rfl

theorem radialRangeHomeomorph_symm_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (p : CellFrontier × R) :
    ((radialRangeHomeomorph R hR).symm p : Plane) = (p.2 : ℝ) • (p.1 : Plane) := rfl

/-- The literal punctured closed cell is its actual frontier times `(0,1]`. -/
noncomputable def puncturedCellHomeomorph : PuncturedCell ≃ₜ CellFrontier × RadialRadius :=
  (Homeomorph.setCongr (by
    ext x
    change (x ∈ baseCell ∧ x ≠ 0) ↔ (0 < cellGauge x ∧ cellGauge x ≤ 1)
    rw [mem_baseCell_iff, ← cellGauge_pos_iff]
    exact and_comm)).trans
      (radialRangeHomeomorph (Ioc (0 : ℝ) 1) (fun _ hr => hr.1))

theorem puncturedCellHomeomorph_direction (x : PuncturedCell) :
    ((puncturedCellHomeomorph x).1 : Plane) = (cellGauge x)⁻¹ • (x : Plane) := rfl

theorem puncturedCellHomeomorph_radius (x : PuncturedCell) :
    ((puncturedCellHomeomorph x).2 : ℝ) = cellGauge x := rfl

theorem puncturedCellHomeomorph_symm_coe (p : CellFrontier × RadialRadius) :
    (puncturedCellHomeomorph.symm p : Plane) = (p.2 : ℝ) • (p.1 : Plane) := rfl

/-- The literal open gauge annulus has the displayed product coordinates. -/
noncomputable def annulusHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    Annulus a ≃ₜ CellFrontier × Ioo a 1 :=
  radialRangeHomeomorph (Ioo a 1) (fun _ hr => ha.trans_lt hr.1)

/-- The literal closed outward collar has the displayed product coordinates. -/
noncomputable def collarHomeomorph (a : ℝ) (ha : 0 < a) :
    Collar a ≃ₜ CellFrontier × Icc a 1 :=
  radialRangeHomeomorph (Icc a 1) (fun _ hr => ha.trans_le hr.1)

end Wikipedia.HopfProblem.CuspCentralHomology.Radial

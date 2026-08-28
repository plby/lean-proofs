import Wikipedia.HopfProblem.CuspCentralHomologyRadialCoordinates
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Convex.Basic

/-!
# Explicit radius-changing homotopies in the actual honeycomb cell

The homotopies below interpolate the gauge radius, keeping its actual frontier
direction fixed. On an open annulus the target radius is its midpoint; on a
closed outward collar the target radius is one and the frontier is fixed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.Radial

local notation "Plane" => CuspHoneycombTiling.Plane

abbrev RadialDomain (R : Set ℝ) := {x : Plane // cellGauge x ∈ R}

/-- The actual frontier direction of a point with positive gauge. -/
def radiusProjection (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) :
    C(RadialDomain R, CellFrontier) :=
  ⟨fun x => (radialRangeHomeomorph R hR x).1,
    continuous_fst.comp (radialRangeHomeomorph R hR).continuous⟩

/-- The section at the explicitly chosen radius `c`. -/
def radiusSection (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (c : ℝ) (hc : c ∈ R) :
    C(CellFrontier, RadialDomain R) :=
  ⟨fun u => (radialRangeHomeomorph R hR).symm (u, ⟨c, hc⟩),
    (radialRangeHomeomorph R hR).symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩

theorem radiusProjection_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (x : RadialDomain R) :
    (radiusProjection R hR x : Plane) = normalize x := rfl

theorem radiusSection_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (c : ℝ) (hc : c ∈ R)
    (u : CellFrontier) : (radiusSection R hR c hc u : Plane) = c • (u : Plane) := rfl

theorem radiusProjection_comp_section (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (c : ℝ) (hc : c ∈ R) :
    (radiusProjection R hR).comp (radiusSection R hR c hc) =
      ContinuousMap.id CellFrontier := by
  apply ContinuousMap.ext
  intro u
  change ((radialRangeHomeomorph R hR)
    ((radialRangeHomeomorph R hR).symm (u, ⟨c, hc⟩))).1 = u
  rw [Homeomorph.apply_symm_apply]

/-- The displayed affine interpolation of the gauge radius. -/
def radiusBlend (c : ℝ) (s : unitInterval) (r : ℝ) : ℝ :=
  (1 - (s : ℝ)) * r + (s : ℝ) * c

theorem radiusBlend_mem {R : Set ℝ} (hconv : Convex ℝ R)
    (c : ℝ) (hc : c ∈ R) (s : unitInterval) (r : ℝ) (hr : r ∈ R) :
    radiusBlend c s r ∈ R :=
  hconv hr hc (sub_nonneg.mpr s.2.2) s.2.1 (sub_add_cancel 1 (s : ℝ))

/-- Change the actual radius along a line segment in the specified radial range. -/
def radiusHomotopyMap (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (hconv : Convex ℝ R)
    (c : ℝ) (hc : c ∈ R) : C(unitInterval × RadialDomain R, RadialDomain R) where
  toFun p := (radialRangeHomeomorph R hR).symm
    ((radialRangeHomeomorph R hR p.2).1,
      ⟨radiusBlend c p.1 (cellGauge p.2), radiusBlend_mem hconv c hc p.1 _ p.2.2⟩)
  continuous_toFun := (radialRangeHomeomorph R hR).symm.continuous.comp
    ((continuous_fst.comp ((radialRangeHomeomorph R hR).continuous.comp continuous_snd)).prodMk
      ((((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (cellGauge_continuous.comp (continuous_subtype_val.comp continuous_snd))).add
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk _))

theorem radiusHomotopyMap_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R) :
    (radiusHomotopyMap R hR hconv c hc (s, x) : Plane) =
      radiusBlend c s (cellGauge x) • normalize x := rfl

theorem radiusHomotopyMap_gauge (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R) :
    cellGauge (radiusHomotopyMap R hR hconv c hc (s, x)) =
      radiusBlend c s (cellGauge x) :=
  cellGauge_smul_frontier _ (hR _ (radiusBlend_mem hconv c hc s _ x.2)).le
    (radialRangeHomeomorph R hR x).1

theorem radiusHomotopyMap_zero (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (x : RadialDomain R) :
    radiusHomotopyMap R hR hconv c hc (0, x) = x := by
  apply Subtype.ext
  rw [radiusHomotopyMap_coe]
  change ((1 - (0 : ℝ)) * cellGauge x + 0 * c) • normalize x = (x : Plane)
  rw [sub_zero, one_mul, zero_mul, add_zero, normalize, smul_smul,
    mul_inv_cancel₀ (hR _ x.2).ne', one_smul]

theorem radiusHomotopyMap_one (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (x : RadialDomain R) :
    radiusHomotopyMap R hR hconv c hc (1, x) =
      radiusSection R hR c hc (radiusProjection R hR x) := by
  apply Subtype.ext
  rw [radiusHomotopyMap_coe, radiusSection_coe, radiusProjection_coe]
  change ((1 - (1 : ℝ)) * cellGauge x + 1 * c) • normalize x = c • normalize x
  rw [sub_self, zero_mul, one_mul, zero_add]

theorem radiusHomotopyMap_fixed (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval)
    (x : RadialDomain R) (hx : cellGauge x = c) :
    radiusHomotopyMap R hR hconv c hc (s, x) = x := by
  have hblend : radiusBlend c s (cellGauge x) = cellGauge x := by
    rw [radiusBlend, hx]
    ring
  apply Subtype.ext
  rw [radiusHomotopyMap_coe, hblend, normalize, smul_smul,
    mul_inv_cancel₀ (hR _ x.2).ne', one_smul]

/-- This homotopy is constructed from the explicit radial formula. -/
def radiusHomotopy (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (hconv : Convex ℝ R)
    (c : ℝ) (hc : c ∈ R) :
    (ContinuousMap.id (RadialDomain R)).Homotopy
      ((radiusSection R hR c hc).comp (radiusProjection R hR)) where
  toContinuousMap := radiusHomotopyMap R hR hconv c hc
  map_zero_left := radiusHomotopyMap_zero R hR hconv c hc
  map_one_left := radiusHomotopyMap_one R hR hconv c hc

/-- Any nonempty convex positive range of radii has the actual frontier's homotopy type. -/
def radialHomotopyEquiv (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (hconv : Convex ℝ R)
    (c : ℝ) (hc : c ∈ R) : RadialDomain R ≃ₕ CellFrontier where
  toFun := radiusProjection R hR
  invFun := radiusSection R hR c hc
  left_inv := ⟨(radiusHomotopy R hR hconv c hc).symm⟩
  right_inv := by
    rw [radiusProjection_comp_section]

/-- The explicit open annulus contracts radially to its middle-radius copy of the frontier. -/
def annulusFrontierHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Annulus a ≃ₕ CellFrontier :=
  radialHomotopyEquiv (Ioo a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioo a 1)
    ((a + 1) / 2) ⟨by linarith, by linarith⟩

/-- The literal frontier inclusion into the closed collar. -/
def frontierIntoCollar (a : ℝ) (ha1 : a ≤ 1) : C(CellFrontier, Collar a) :=
  ⟨fun u => ⟨u, by
    rw [(mem_frontier_baseCell_iff _).mp u.2]
    exact ⟨ha1, le_rfl⟩⟩, continuous_subtype_val.subtype_mk _⟩

/-- The literal collar retraction is division by the displayed positive gauge. -/
def collarRetraction (a : ℝ) (ha : 0 < a) : C(Collar a, CellFrontier) :=
  radiusProjection (Icc a 1) (fun _ hr => ha.trans_le hr.1)

theorem collarRetraction_coe (a : ℝ) (ha : 0 < a) (x : Collar a) :
    (collarRetraction a ha x : Plane) = (cellGauge x)⁻¹ • (x : Plane) := rfl

theorem collarRetraction_frontier (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (collarRetraction a ha).comp (frontierIntoCollar a ha1) =
      ContinuousMap.id CellFrontier := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  exact normalize_frontier u

theorem radiusSection_one_eq_frontier (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    radiusSection (Icc a 1) (fun _ hr => ha.trans_le hr.1) 1 ⟨ha1, le_rfl⟩ =
      frontierIntoCollar a ha1 := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  exact one_smul ℝ (u : Plane)

/-- The actual outward collar deformation, fixed on the literal frontier. -/
def outwardCollarHomotopy (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (ContinuousMap.id (Collar a)).HomotopyRel
      ((frontierIntoCollar a ha1).comp (collarRetraction a ha))
        {x : Collar a | cellGauge x = 1} where
  toContinuousMap := radiusHomotopyMap (Icc a 1)
    (fun _ hr => ha.trans_le hr.1) (convex_Icc a 1) 1 ⟨ha1, le_rfl⟩
  map_zero_left := radiusHomotopyMap_zero (Icc a 1)
    (fun _ hr => ha.trans_le hr.1) (convex_Icc a 1) 1 ⟨ha1, le_rfl⟩
  map_one_left x := by
    apply Subtype.ext
    change ((1 - (1 : ℝ)) * cellGauge x + 1 * 1) • normalize x = normalize x
    rw [sub_self, zero_mul, one_mul, zero_add, one_smul]
  prop' s x hx := radiusHomotopyMap_fixed (Icc a 1)
    (fun _ hr => ha.trans_le hr.1) (convex_Icc a 1) 1 ⟨ha1, le_rfl⟩ s x hx

theorem outwardCollarHomotopy_coe (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (s : unitInterval) (x : Collar a) :
    (outwardCollarHomotopy a ha ha1 (s, x) : Plane) =
      ((1 - (s : ℝ)) + (s : ℝ) / cellGauge x) • (x : Plane) := by
  change radiusBlend 1 s (cellGauge x) • normalize x = _
  rw [normalize, smul_smul]
  congr 1
  rw [radiusBlend, mul_one, add_mul, mul_assoc,
    mul_inv_cancel₀ (ha.trans_le x.2.1).ne', mul_one, div_eq_mul_inv]

theorem outwardCollarHomotopy_gauge (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (s : unitInterval) (x : Collar a) :
    cellGauge (outwardCollarHomotopy a ha ha1 (s, x)) =
      (1 - (s : ℝ)) * cellGauge x + (s : ℝ) := by
  change cellGauge (radiusHomotopyMap (Icc a 1)
    (fun _ hr => ha.trans_le hr.1) (convex_Icc a 1) 1 ⟨ha1, le_rfl⟩ (s, x)) = _
  simpa only [radiusBlend, mul_one] using radiusHomotopyMap_gauge (Icc a 1)
    (fun _ hr => ha.trans_le hr.1) (convex_Icc a 1) 1 ⟨ha1, le_rfl⟩ s x

theorem outwardCollarHomotopy_fixed (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (s : unitInterval) (x : Collar a) (hx : (x : Plane) ∈ frontier CuspHoneycombTiling.baseCell) :
    outwardCollarHomotopy a ha ha1 (s, x) = x :=
  (outwardCollarHomotopy a ha ha1).eq_fst s ((mem_frontier_baseCell_iff _).mp hx)

theorem outwardCollarHomotopy_gauge_nondec (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (s : unitInterval) (x : Collar a) :
    cellGauge x ≤ cellGauge (outwardCollarHomotopy a ha ha1 (s, x)) := by
  rw [outwardCollarHomotopy_gauge]
  nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr x.2.2)]

/-- The outward collar open at its inner edge, as used in a radial open cover. -/
abbrev OpenCollar (a : ℝ) := {x : Plane // a < cellGauge x ∧ cellGauge x ≤ 1}

def frontierIntoOpenCollar (a : ℝ) (ha1 : a < 1) : C(CellFrontier, OpenCollar a) :=
  ⟨fun u => ⟨u, by
    rw [(mem_frontier_baseCell_iff _).mp u.2]
    exact ⟨ha1, le_rfl⟩⟩, continuous_subtype_val.subtype_mk _⟩

def openCollarRetraction (a : ℝ) (ha : 0 ≤ a) : C(OpenCollar a, CellFrontier) :=
  radiusProjection (Ioc a 1) (fun _ hr => ha.trans_lt hr.1)

theorem openCollarRetraction_coe (a : ℝ) (ha : 0 ≤ a) (x : OpenCollar a) :
    (openCollarRetraction a ha x : Plane) = (cellGauge x)⁻¹ • (x : Plane) := rfl

theorem openCollarRetraction_frontier (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (openCollarRetraction a ha).comp (frontierIntoOpenCollar a ha1) =
      ContinuousMap.id CellFrontier := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  exact normalize_frontier u

/-- The same explicit outward deformation on the open-inner-edge collar. -/
def outwardOpenCollarHomotopy (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (ContinuousMap.id (OpenCollar a)).HomotopyRel
      ((frontierIntoOpenCollar a ha1).comp (openCollarRetraction a ha))
        {x : OpenCollar a | cellGauge x = 1} where
  toContinuousMap := radiusHomotopyMap (Ioc a 1)
    (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1 ⟨ha1, le_rfl⟩
  map_zero_left := radiusHomotopyMap_zero (Ioc a 1)
    (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1 ⟨ha1, le_rfl⟩
  map_one_left x := by
    apply Subtype.ext
    change ((1 - (1 : ℝ)) * cellGauge x + 1 * 1) • normalize x = normalize x
    rw [sub_self, zero_mul, one_mul, zero_add, one_smul]
  prop' s x hx := radiusHomotopyMap_fixed (Ioc a 1)
    (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1 ⟨ha1, le_rfl⟩ s x hx

theorem outwardOpenCollarHomotopy_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : OpenCollar a) :
    (outwardOpenCollarHomotopy a ha ha1 (s, x) : Plane) =
      ((1 - (s : ℝ)) + (s : ℝ) / cellGauge x) • (x : Plane) := by
  change radiusBlend 1 s (cellGauge x) • normalize x = _
  rw [normalize, smul_smul]
  congr 1
  rw [radiusBlend, mul_one, add_mul, mul_assoc,
    mul_inv_cancel₀ (ha.trans_lt x.2.1).ne', mul_one, div_eq_mul_inv]

theorem outwardOpenCollarHomotopy_gauge (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : OpenCollar a) :
    cellGauge (outwardOpenCollarHomotopy a ha ha1 (s, x)) =
      (1 - (s : ℝ)) * cellGauge x + (s : ℝ) := by
  change cellGauge (radiusHomotopyMap (Ioc a 1)
    (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1 ⟨ha1, le_rfl⟩ (s, x)) = _
  simpa only [radiusBlend, mul_one] using radiusHomotopyMap_gauge (Ioc a 1)
    (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1 ⟨ha1, le_rfl⟩ s x

theorem outwardOpenCollarHomotopy_fixed (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : OpenCollar a)
    (hx : (x : Plane) ∈ frontier CuspHoneycombTiling.baseCell) :
    outwardOpenCollarHomotopy a ha ha1 (s, x) = x :=
  (outwardOpenCollarHomotopy a ha ha1).eq_fst s ((mem_frontier_baseCell_iff _).mp hx)

theorem outwardOpenCollarHomotopy_gauge_nondec (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : OpenCollar a) :
    cellGauge x ≤ cellGauge (outwardOpenCollarHomotopy a ha ha1 (s, x)) := by
  rw [outwardOpenCollarHomotopy_gauge]
  nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr x.2.2)]

end Wikipedia.HopfProblem.CuspCentralHomology.Radial

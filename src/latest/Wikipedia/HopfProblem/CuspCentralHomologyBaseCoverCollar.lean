import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverRadius
import Wikipedia.HopfProblem.CuspCentralHomologyRadialCollar
import Mathlib.Topology.CompactOpen

/-!
# The actual outer base-torus region retracts onto its boundary

The open-inner-edge collar in the literal fundamental hexagon presents
the original outer region of the marked base torus. Its outward radial
deformation respects this presentation: interior representatives are
unique, and all other identifications are on the fixed frontier.

Joint continuity descends through the actual proper collar map. The
result is a strong deformation retraction onto the original boundary
subspace, with the explicit division-by-gauge formula on representatives.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The literal inclusion of the open-inner-edge collar into the closed hexagon. -/
def collarCellInclusion (a : ℝ) (p : Radial.OpenCollar a) : baseCell :=
  ⟨(p : Plane), (Radial.mem_baseCell_iff _).mpr p.2.2⟩

@[simp] theorem collarCellInclusion_coe (a : ℝ) (p : Radial.OpenCollar a) :
    (collarCellInclusion a p : Plane) = p := rfl

theorem collarCellInclusion_continuous (a : ℝ) : Continuous (collarCellInclusion a) :=
  continuous_subtype_val.subtype_mk _

theorem collarCellInclusion_injective (a : ℝ) :
    Function.Injective (collarCellInclusion a) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun y : baseCell => (y : Plane)) h

variable (a : ℝ)

/-- The collar presentation takes values in the actual outer subspace. -/
def collarCellMap (p : Radial.OpenCollar a) : outerRegion a :=
  ⟨cellMap (collarCellInclusion a p),
    (cellMap_mem_outerRegion_iff a _).mpr p.2.1⟩

@[simp] theorem collarCellMap_coe (p : Radial.OpenCollar a) :
    (collarCellMap a p : BaseTorus) = basePoint (p : Plane) := rfl

theorem collarCellMap_eq_cellMap (p : Radial.OpenCollar a) :
    (collarCellMap a p : BaseTorus) = cellMap (collarCellInclusion a p) := rfl

@[simp] theorem radius_collarCellMap (p : Radial.OpenCollar a) :
    radius (collarCellMap a p) = Radial.cellGauge (p : Plane) :=
  radius_cellMap (collarCellInclusion a p)

theorem collarCellMap_continuous : Continuous (collarCellMap a) :=
  (cellMap.continuous.comp (collarCellInclusion_continuous a)).subtype_mk _

theorem collarCellMap_surjective : Function.Surjective (collarCellMap a) := by
  rintro ⟨q, hq⟩
  obtain ⟨y, hy⟩ := cellMap_surjective q
  have hg : a < Radial.cellGauge (y : Plane) := by
    apply (cellMap_mem_outerRegion_iff a y).mp
    rwa [hy]
  refine ⟨⟨(y : Plane), hg, (Radial.mem_baseCell_iff _).mp y.2⟩, ?_⟩
  apply Subtype.ext
  exact hy

/-- The literal collar is the preimage of the actual outer region under
the compact cell presentation, with its inherited topology. -/
def collarPreimageHomeomorph :
    Radial.OpenCollar a ≃ₜ (cellMap ⁻¹' outerRegion a) where
  toFun p := ⟨collarCellInclusion a p,
    (cellMap_mem_outerRegion_iff a _).mpr p.2.1⟩
  invFun p := ⟨(p.1 : Plane), (cellMap_mem_outerRegion_iff a p.1).mp p.2,
    (Radial.mem_baseCell_iff _).mp p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (collarCellInclusion_continuous a).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem collarPreimageHomeomorph_coe (p : Radial.OpenCollar a) :
    (collarPreimageHomeomorph a p : baseCell) = collarCellInclusion a p := rfl

theorem collarCellMap_isProperMap : IsProperMap (collarCellMap a) := by
  have hf := cellMap_isProperMap.restrictPreimage (outerRegion a)
  have hc := hf.comp (collarPreimageHomeomorph a).isProperMap
  have he : (outerRegion a).restrictPreimage cellMap ∘ collarPreimageHomeomorph a =
      collarCellMap a := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

theorem collarCellMap_isClosedMap : IsClosedMap (collarCellMap a) :=
  (collarCellMap_isProperMap a).isClosedMap

theorem collarCellMap_isQuotientMap : IsQuotientMap (collarCellMap a) :=
  (collarCellMap_isClosedMap a).isQuotientMap
    (collarCellMap_continuous a) (collarCellMap_surjective a)

/-- Every radial stage respects the exact fibres of the original base
quotient. The only nonsingleton fibres are on the fixed frontier. -/
theorem collarCellHomotopy_compatible (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p q : Radial.OpenCollar a)
    (h : collarCellMap a p = collarCellMap a q) :
    collarCellMap a (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)) =
      collarCellMap a (Radial.outwardOpenCollarHomotopy a ha ha1 (s, q)) := by
  have he : cellMap (collarCellInclusion a p) =
      cellMap (collarCellInclusion a q) := congrArg Subtype.val h
  rcases cellMap_eq_or_frontier (collarCellInclusion a p)
    (collarCellInclusion a q) he with hpq | ⟨hp, hq⟩
  · rw [collarCellInclusion_injective a hpq]
  · rw [Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p hp,
      Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s q hq]
    exact h

/-- The literal inclusion of the boundary into the outer region. -/
def outerRegionBoundaryInclusion (ha1 : a < 1) : C(boundary, outerRegion a) where
  toFun x := ⟨x, boundary_subset_outerRegion a ha1 x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem outerRegionBoundaryInclusion_coe (ha1 : a < 1) (x : boundary) :
    (outerRegionBoundaryInclusion a ha1 x : BaseTorus) = x := rfl

variable (ha : 0 ≤ a) (ha1 : a < 1)

/-- The actual outward deformation, independent of the chosen collar
representative by the proved fibre compatibility. -/
def outerRegionDeformation (s : unitInterval) (x : outerRegion a) : outerRegion a :=
  CuspHoneycombHexagon.CommonFibres.descend (collarCellMap a)
    (fun p => collarCellMap a (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective a) x

@[simp] theorem outerRegionDeformation_collarCellMap
    (s : unitInterval) (p : Radial.OpenCollar a) :
    outerRegionDeformation a ha ha1 s (collarCellMap a p) =
      collarCellMap a (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (collarCellMap a)
    (fun p => collarCellMap a (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective a) (collarCellHomotopy_compatible a ha ha1 s) p

/-- On actual representatives, the descended deformation is exactly
the displayed scalar multiplication in the honeycomb plane. -/
theorem outerRegionDeformation_collarCellMap_coe
    (s : unitInterval) (p : Radial.OpenCollar a) :
    (outerRegionDeformation a ha ha1 s (collarCellMap a p) : BaseTorus) =
      basePoint (((1 - (s : ℝ)) + (s : ℝ) / Radial.cellGauge p) • (p : Plane)) := by
  rw [outerRegionDeformation_collarCellMap, collarCellMap_coe,
    Radial.outwardOpenCollarHomotopy_coe]

@[simp] theorem outerRegionDeformation_zero (x : outerRegion a) :
    outerRegionDeformation a ha ha1 0 x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  rw [outerRegionDeformation_collarCellMap,
    (Radial.outwardOpenCollarHomotopy a ha ha1).apply_zero]
  rfl

/-- The radius follows the explicit affine interpolation to one. -/
theorem outerRegionDeformation_radius (s : unitInterval) (x : outerRegion a) :
    radius (outerRegionDeformation a ha ha1 s x) =
      (1 - (s : ℝ)) * radius x + (s : ℝ) := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  rw [outerRegionDeformation_collarCellMap, radius_collarCellMap, radius_collarCellMap]
  exact Radial.outwardOpenCollarHomotopy_gauge a ha ha1 s p

theorem outerRegionDeformation_one_mem_boundary (x : outerRegion a) :
    (outerRegionDeformation a ha ha1 1 x : BaseTorus) ∈ boundary := by
  change radius (outerRegionDeformation a ha ha1 1 x) = 1
  rw [outerRegionDeformation_radius]
  simp

/-- Every actual boundary point is fixed throughout the deformation. -/
theorem outerRegionDeformation_fixed (s : unitInterval) (x : outerRegion a)
    (hx : (x : BaseTorus) ∈ boundary) :
    outerRegionDeformation a ha ha1 s x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  have hp : (p : Plane) ∈ frontier baseCell := by
    apply (Radial.mem_frontier_baseCell_iff _).mpr
    change radius (collarCellMap a p) = 1 at hx
    rwa [radius_collarCellMap] at hx
  rw [outerRegionDeformation_collarCellMap,
    Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p hp]

/-- Joint continuity descends through the actual collar quotient. The
locally compact interval preserves the quotient property on products. -/
theorem outerRegionDeformation_continuous :
    Continuous (fun p : unitInterval × outerRegion a =>
      outerRegionDeformation a ha ha1 p.1 p.2) := by
  apply (collarCellMap_isQuotientMap a).continuous_lift_prod_right
  have hc := (collarCellMap_continuous a).comp
    (Radial.outwardOpenCollarHomotopy a ha ha1).continuous
  simpa only [outerRegionDeformation_collarCellMap, Function.comp_def, Prod.eta] using hc

/-- Time one of the actual deformation, restricted to the boundary subspace. -/
def outerRegionRetraction : C(outerRegion a, boundary) where
  toFun x := ⟨outerRegionDeformation a ha ha1 1 x,
    outerRegionDeformation_one_mem_boundary a ha ha1 x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      ((outerRegionDeformation_continuous a ha ha1).comp
        (continuous_const.prodMk continuous_id))).subtype_mk _

@[simp] theorem outerRegionRetraction_coe (x : outerRegion a) :
    (outerRegionRetraction a ha ha1 x : BaseTorus) =
      outerRegionDeformation a ha ha1 1 x := rfl

/-- The actual retraction divides a collar representative by its gauge. -/
theorem outerRegionRetraction_collarCellMap (p : Radial.OpenCollar a) :
    (outerRegionRetraction a ha ha1 (collarCellMap a p) : BaseTorus) =
      basePoint ((Radial.cellGauge p)⁻¹ • (p : Plane)) := by
  rw [outerRegionRetraction_coe, outerRegionDeformation_collarCellMap_coe]
  simp

/-- The endpoint formula directly on a representative in the original closed cell. -/
theorem outerRegionRetraction_cellMap (y : baseCell)
    (hy : a < Radial.cellGauge (y : Plane)) :
    (outerRegionRetraction a ha ha1
      ⟨cellMap y, (cellMap_mem_outerRegion_iff a y).mpr hy⟩ : BaseTorus) =
      basePoint ((Radial.cellGauge y)⁻¹ • (y : Plane)) :=
  outerRegionRetraction_collarCellMap a ha ha1
    ⟨(y : Plane), hy, (Radial.mem_baseCell_iff _).mp y.2⟩

@[simp] theorem outerRegionRetraction_comp_inclusion :
    (outerRegionRetraction a ha ha1).comp (outerRegionBoundaryInclusion a ha1) =
      ContinuousMap.id boundary := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (outerRegionDeformation a ha ha1 1
    (outerRegionBoundaryInclusion a ha1 x) : BaseTorus) = x
  exact congrArg Subtype.val (outerRegionDeformation_fixed a ha ha1 1
    (outerRegionBoundaryInclusion a ha1 x) x.2)

/-- The genuine strong deformation retraction of the outer region,
relative to the actual boundary with its original subspace topology. -/
def outerRegionHomotopyRel :
    (ContinuousMap.id (outerRegion a)).HomotopyRel
      ((outerRegionBoundaryInclusion a ha1).comp (outerRegionRetraction a ha ha1))
      {x : outerRegion a | (x : BaseTorus) ∈ boundary} where
  toFun p := outerRegionDeformation a ha ha1 p.1 p.2
  continuous_toFun := outerRegionDeformation_continuous a ha ha1
  map_zero_left := outerRegionDeformation_zero a ha ha1
  map_one_left _ := rfl
  prop' := outerRegionDeformation_fixed a ha ha1

/-- The actual outer base-torus region has the homotopy type of its literal boundary. -/
def outerRegionBoundaryHomotopyEquiv : outerRegion a ≃ₕ boundary where
  toFun := outerRegionRetraction a ha ha1
  invFun := outerRegionBoundaryInclusion a ha1
  left_inv := ⟨(outerRegionHomotopyRel a ha ha1).toHomotopy.symm⟩
  right_inv := by
    refine ⟨?_⟩
    rw [outerRegionRetraction_comp_inclusion]
    exact ContinuousMap.Homotopy.refl _

@[simp] theorem outerRegionHomotopyRel_apply (s : unitInterval) (x : outerRegion a) :
    outerRegionHomotopyRel a ha ha1 (s, x) = outerRegionDeformation a ha ha1 s x := rfl

@[simp] theorem outerRegionBoundaryHomotopyEquiv_apply (x : outerRegion a) :
    outerRegionBoundaryHomotopyEquiv a ha ha1 x = outerRegionRetraction a ha ha1 x := rfl

@[simp] theorem outerRegionBoundaryHomotopyEquiv_symm_apply (x : boundary) :
    (outerRegionBoundaryHomotopyEquiv a ha ha1).symm x =
      outerRegionBoundaryInclusion a ha1 x := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

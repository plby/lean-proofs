import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverRadius
import Wikipedia.HopfProblem.CuspCentralHomologyRadialInterior

/-!
# The actual open cell in the base torus

Restricting the proper compact-cell presentation to the saturated inner
region gives a homeomorphism from the literal interior of the hexagon.
Both sides retain their existing subspace topologies. The explicit radial
contraction of that interior then gives an actual homotopy equivalence
from the inner region to a point.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The literal inclusion of the open cell into the closed hexagon. -/
def interiorCellInclusion : C(Radial.InteriorCell, baseCell) where
  toFun y := ⟨(y : Plane), interior_subset y.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem interiorCellInclusion_coe (y : Radial.InteriorCell) :
    (interiorCellInclusion y : Plane) = (y : Plane) := rfl

/-- The existing marked base map on the literal open cell. -/
def interiorCellMap : C(Radial.InteriorCell, BaseTorus) :=
  cellMap.comp interiorCellInclusion

@[simp] theorem interiorCellMap_apply (y : Radial.InteriorCell) :
    interiorCellMap y = cellMap (interiorCellInclusion y) := rfl

/-- The marked map with codomain restricted to the actual inner region. -/
def interiorCellToInnerRegion : C(Radial.InteriorCell, innerRegion) where
  toFun y := ⟨cellMap (interiorCellInclusion y),
    (cellMap_mem_innerRegion_iff (interiorCellInclusion y)).mpr y.property⟩
  continuous_toFun := interiorCellMap.continuous.subtype_mk _

@[simp] theorem interiorCellToInnerRegion_coe (y : Radial.InteriorCell) :
    (interiorCellToInnerRegion y : BaseTorus) = cellMap (interiorCellInclusion y) := rfl

theorem interiorCellToInnerRegion_injective :
    Function.Injective interiorCellToInnerRegion := by
  intro y z h
  have he : interiorCellInclusion y = interiorCellInclusion z :=
    cellMap_eq_of_interior (interiorCellInclusion y) (interiorCellInclusion z)
      y.property (congrArg Subtype.val h)
  apply Subtype.ext
  exact congrArg (fun x : baseCell => (x : Plane)) he

theorem interiorCellToInnerRegion_surjective :
    Function.Surjective interiorCellToInnerRegion := by
  intro q
  obtain ⟨y, hy⟩ := cellMap_surjective (q : BaseTorus)
  have hyinner : (y : Plane) ∈ interior baseCell := by
    apply (cellMap_mem_innerRegion_iff y).mp
    rw [hy]
    exact q.property
  refine ⟨⟨(y : Plane), hyinner⟩, ?_⟩
  apply Subtype.ext
  exact hy

/-- The open cell is exactly the preimage used by the proper-map restriction. -/
def interiorPreimageHomeomorph :
    Radial.InteriorCell ≃ₜ (cellMap ⁻¹' innerRegion) where
  toFun y := ⟨interiorCellInclusion y,
    (cellMap_mem_innerRegion_iff (interiorCellInclusion y)).mpr y.property⟩
  invFun y := ⟨(y.1 : Plane), (cellMap_mem_innerRegion_iff y.1).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := interiorCellInclusion.continuous.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

@[simp] theorem interiorPreimageHomeomorph_coe (y : Radial.InteriorCell) :
    (interiorPreimageHomeomorph y : baseCell) = interiorCellInclusion y := rfl

@[simp] theorem interiorPreimageHomeomorph_symm_coe (y : cellMap ⁻¹' innerRegion) :
    (interiorPreimageHomeomorph.symm y : Plane) = (y.1 : Plane) := rfl

/-- Properness is for the map to the inherited inner region, not for its
inclusion into the entire base torus. -/
theorem interiorCellToInnerRegion_isProperMap : IsProperMap interiorCellToInnerRegion := by
  have h := (cellMap_isProperMap.restrictPreimage innerRegion).comp
    interiorPreimageHomeomorph.isProperMap
  have he : innerRegion.restrictPreimage cellMap ∘ interiorPreimageHomeomorph =
      interiorCellToInnerRegion := by
    funext y
    apply Subtype.ext
    rfl
  rw [he] at h
  exact h

theorem interiorCellToInnerRegion_isClosedMap : IsClosedMap interiorCellToInnerRegion :=
  interiorCellToInnerRegion_isProperMap.isClosedMap

/-- The literal hexagon interior is homeomorphic to the actual inner region
of the original marked base torus. -/
def interiorCellHomeomorph : Radial.InteriorCell ≃ₜ innerRegion :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective interiorCellToInnerRegion
      ⟨interiorCellToInnerRegion_injective, interiorCellToInnerRegion_surjective⟩)
    interiorCellToInnerRegion.continuous interiorCellToInnerRegion_isClosedMap

@[simp] theorem interiorCellHomeomorph_apply (y : Radial.InteriorCell) :
    interiorCellHomeomorph y = interiorCellToInnerRegion y := rfl

@[simp] theorem interiorCellHomeomorph_coe (y : Radial.InteriorCell) :
    (interiorCellHomeomorph y : BaseTorus) = cellMap (interiorCellInclusion y) := rfl

@[simp] theorem interiorCellHomeomorph_basePoint (y : Radial.InteriorCell) :
    (interiorCellHomeomorph y : BaseTorus) = basePoint (y : Plane) := rfl

/-- The inverse coordinate chart, on the literal inner subset of the torus. -/
def innerRegionCellHomeomorph : innerRegion ≃ₜ Radial.InteriorCell :=
  interiorCellHomeomorph.symm

@[simp] theorem innerRegionCellHomeomorph_map (y : Radial.InteriorCell) :
    innerRegionCellHomeomorph (interiorCellToInnerRegion y) = y :=
  interiorCellHomeomorph.symm_apply_apply y

@[simp] theorem cellMap_innerRegionCellHomeomorph (q : innerRegion) :
    cellMap (interiorCellInclusion (innerRegionCellHomeomorph q)) = (q : BaseTorus) :=
  congrArg Subtype.val (interiorCellHomeomorph.apply_symm_apply q)

/-- The parametrization is an open embedding into the existing base torus. -/
theorem interiorCellMap_isOpenEmbedding : IsOpenEmbedding interiorCellMap := by
  have h := innerRegion_isOpen.isOpenEmbedding_subtypeVal.comp
    interiorCellHomeomorph.isOpenEmbedding
  have he : (Subtype.val : innerRegion → BaseTorus) ∘ interiorCellHomeomorph =
      interiorCellMap := by
    funext y
    rfl
  rw [he] at h
  exact h

/-- The chosen point of the actual inner region is the marked image of zero. -/
def innerRegionCenter : innerRegion := interiorCellHomeomorph Radial.interiorCellZero

@[simp] theorem innerRegionCenter_coe :
    (innerRegionCenter : BaseTorus) = basePoint 0 := rfl

/-- The actual radial contraction transported through the proved interior chart. -/
def innerRegionPointHomotopyEquiv : innerRegion ≃ₕ Unit :=
  innerRegionCellHomeomorph.toHomotopyEquiv.trans Radial.interiorCellPointHomotopyEquiv

@[simp] theorem innerRegionPointHomotopyEquiv_apply (q : innerRegion) :
    innerRegionPointHomotopyEquiv q = () := rfl

@[simp] theorem innerRegionPointHomotopyEquiv_symm_apply (u : Unit) :
    innerRegionPointHomotopyEquiv.symm u = innerRegionCenter := rfl

/-- Contractibility uses the actual radial homotopy on the literal open cell. -/
instance innerRegion_contractibleSpace : ContractibleSpace innerRegion :=
  innerRegionPointHomotopyEquiv.contractibleSpace

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverInterior
import Wikipedia.HopfProblem.CuspCentralHomologyRadialAnnulus

/-!
# The actual annular overlap in the base torus

The literal intersection of the radial outer region and open-cell inner
region is homeomorphic to the strict gauge annulus in the actual hexagon.
The homeomorphism is the restriction of the already proved interior
chart. Radial coordinates then give its genuine circle homotopy type,
with explicit frontier direction and midpoint-radius inverse.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The actual intersection of the two open subsets of the base torus. -/
def overlapRegion (a : ℝ) : Set BaseTorus := outerRegion a ∩ innerRegion

theorem overlapRegion_isOpen (a : ℝ) : IsOpen (overlapRegion a) :=
  (outerRegion_isOpen a).inter innerRegion_isOpen

/-- Inclusion of the actual overlap into the inner region. -/
def overlapIntoInner (a : ℝ) : C(overlapRegion a, innerRegion) :=
  ⟨fun q => ⟨(q : BaseTorus), q.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of the actual overlap into the outer region. -/
def overlapIntoOuter (a : ℝ) : C(overlapRegion a, outerRegion a) :=
  ⟨fun q => ⟨(q : BaseTorus), q.property.1⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] theorem overlapIntoInner_coe (a : ℝ) (q : overlapRegion a) :
    (overlapIntoInner a q : BaseTorus) = (q : BaseTorus) := rfl

@[simp] theorem overlapIntoOuter_coe (a : ℝ) (q : overlapRegion a) :
    (overlapIntoOuter a q : BaseTorus) = (q : BaseTorus) := rfl

/-- The annulus sits in the literal open hexagon by the identity on points. -/
def annulusCellInclusion (a : ℝ) : C(Radial.Annulus a, Radial.InteriorCell) :=
  ⟨fun y => ⟨(y : Plane), (Radial.mem_interior_baseCell_iff _).mpr y.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem annulusCellInclusion_coe (a : ℝ) (y : Radial.Annulus a) :
    (annulusCellInclusion a y : Plane) = (y : Plane) := rfl

theorem annulusCellInclusion_injective (a : ℝ) :
    Function.Injective (annulusCellInclusion a) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun x : Radial.InteriorCell => (x : Plane)) h

@[simp] theorem interiorCellHomeomorph_radius (y : Radial.InteriorCell) :
    radius (interiorCellHomeomorph y : BaseTorus) = Radial.cellGauge (y : Plane) := by
  rw [interiorCellHomeomorph_coe, radius_cellMap]
  rfl

/-- Restriction of the existing interior chart to the strict annulus. -/
def overlapCellMap (a : ℝ) : C(Radial.Annulus a, overlapRegion a) where
  toFun y := ⟨(interiorCellHomeomorph (annulusCellInclusion a y) : BaseTorus), by
    constructor
    · change a < radius (interiorCellHomeomorph (annulusCellInclusion a y) : BaseTorus)
      rw [interiorCellHomeomorph_radius, annulusCellInclusion_coe]
      exact y.property.1
    · exact (interiorCellHomeomorph (annulusCellInclusion a y)).property⟩
  continuous_toFun := (continuous_subtype_val.comp
    (interiorCellHomeomorph.continuous.comp (annulusCellInclusion a).continuous)).subtype_mk _

@[simp] theorem overlapCellMap_coe (a : ℝ) (y : Radial.Annulus a) :
    (overlapCellMap a y : BaseTorus) = basePoint (y : Plane) := rfl

theorem overlapCellMap_intoInner (a : ℝ) (y : Radial.Annulus a) :
    overlapIntoInner a (overlapCellMap a y) =
      interiorCellHomeomorph (annulusCellInclusion a y) := rfl

@[simp] theorem overlapCellMap_radius (a : ℝ) (y : Radial.Annulus a) :
    radius (overlapCellMap a y : BaseTorus) = Radial.cellGauge (y : Plane) :=
  interiorCellHomeomorph_radius (annulusCellInclusion a y)

/-- The unique interior representative of an overlap point belongs to
the literal strict gauge annulus. -/
def overlapCellInverse (a : ℝ) : C(overlapRegion a, Radial.Annulus a) where
  toFun q :=
    let y := interiorCellHomeomorph.symm (overlapIntoInner a q)
    ⟨(y : Plane), by
      constructor
      · rw [← interiorCellHomeomorph_radius y]
        dsimp only [y]
        rw [Homeomorph.apply_symm_apply]
        exact q.property.1
      · exact (Radial.mem_interior_baseCell_iff _).mp y.property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      (interiorCellHomeomorph.symm.continuous.comp (overlapIntoInner a).continuous)).subtype_mk _

theorem overlapCellInverse_interior (a : ℝ) (q : overlapRegion a) :
    annulusCellInclusion a (overlapCellInverse a q) =
      interiorCellHomeomorph.symm (overlapIntoInner a q) := rfl

/-- The actual overlap, with its inherited topology, is exactly the
literal annulus under the marked base map. -/
def annulusOverlapHomeomorph (a : ℝ) : Radial.Annulus a ≃ₜ overlapRegion a where
  toFun := overlapCellMap a
  invFun := overlapCellInverse a
  left_inv y := by
    apply annulusCellInclusion_injective a
    rw [overlapCellInverse_interior, overlapCellMap_intoInner, Homeomorph.symm_apply_apply]
  right_inv q := by
    apply Subtype.ext
    change (interiorCellHomeomorph (annulusCellInclusion a (overlapCellInverse a q)) :
      BaseTorus) = (q : BaseTorus)
    rw [overlapCellInverse_interior, Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := (overlapCellMap a).continuous
  continuous_invFun := (overlapCellInverse a).continuous

@[simp] theorem annulusOverlapHomeomorph_coe (a : ℝ) (y : Radial.Annulus a) :
    (annulusOverlapHomeomorph a y : BaseTorus) = basePoint (y : Plane) := rfl

@[simp] theorem annulusOverlapHomeomorph_intoInner (a : ℝ) (y : Radial.Annulus a) :
    overlapIntoInner a (annulusOverlapHomeomorph a y) =
      interiorCellHomeomorph (annulusCellInclusion a y) := rfl

@[simp] theorem annulusOverlapHomeomorph_radius (a : ℝ) (y : Radial.Annulus a) :
    radius (annulusOverlapHomeomorph a y : BaseTorus) = Radial.cellGauge (y : Plane) :=
  overlapCellMap_radius a y

theorem annulusOverlapHomeomorph_symm_radius (a : ℝ) (q : overlapRegion a) :
    Radial.cellGauge ((annulusOverlapHomeomorph a).symm q : Plane) =
      radius (q : BaseTorus) := by
  simpa only [Homeomorph.apply_symm_apply] using
    (annulusOverlapHomeomorph_radius a ((annulusOverlapHomeomorph a).symm q)).symm

/-- Literal frontier direction and gauge radius on the actual overlap. -/
def overlapHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    overlapRegion a ≃ₜ Radial.CellFrontier × Ioo a 1 :=
  (annulusOverlapHomeomorph a).symm.trans (Radial.annulusHomeomorph a ha)

@[simp] theorem overlapHomeomorph_radius (a : ℝ) (ha : 0 ≤ a) (q : overlapRegion a) :
    ((overlapHomeomorph a ha q).2 : ℝ) = radius (q : BaseTorus) :=
  annulusOverlapHomeomorph_symm_radius a q

theorem overlapHomeomorph_direction (a : ℝ) (ha : 0 ≤ a) (q : overlapRegion a) :
    ((overlapHomeomorph a ha q).1 : Plane) =
      Radial.normalize ((annulusOverlapHomeomorph a).symm q : Plane) := rfl

theorem overlapHomeomorph_symm_coe (a : ℝ) (ha : 0 ≤ a)
    (p : Radial.CellFrontier × Ioo a 1) :
    ((overlapHomeomorph a ha).symm p : BaseTorus) =
      basePoint ((p.2 : ℝ) • (p.1 : Plane)) := rfl

/-- The frontier direction is a continuous normalization of actual
overlap representatives, without a choice of a new quotient topology. -/
def overlapDirection (a : ℝ) (ha : 0 ≤ a) : C(overlapRegion a, Radial.CellFrontier) :=
  ⟨fun q => (overlapHomeomorph a ha q).1,
    continuous_fst.comp (overlapHomeomorph a ha).continuous⟩

theorem overlapDirection_annulus (a : ℝ) (ha : 0 ≤ a) (y : Radial.Annulus a) :
    (overlapDirection a ha (annulusOverlapHomeomorph a y) : Plane) =
      (Radial.cellGauge (y : Plane))⁻¹ • (y : Plane) := by
  change ((Radial.annulusHomeomorph a ha
    ((annulusOverlapHomeomorph a).symm (annulusOverlapHomeomorph a y))).1 : Plane) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The actual annular overlap has the homotopy type of the unit complex circle. -/
def overlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    overlapRegion a ≃ₕ _root_.Circle :=
  (annulusOverlapHomeomorph a).symm.toHomotopyEquiv.trans
    (Radial.annulusCircleHomotopyEquiv a ha ha1)

theorem overlapCircleHomotopyEquiv_annulus (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (y : Radial.Annulus a) :
    overlapCircleHomotopyEquiv a ha ha1 (annulusOverlapHomeomorph a y) =
      Radial.annulusCircleHomotopyEquiv a ha ha1 y := by
  change Radial.annulusCircleHomotopyEquiv a ha ha1
    ((annulusOverlapHomeomorph a).symm (annulusOverlapHomeomorph a y)) = _
  rw [Homeomorph.symm_apply_apply]

theorem overlapCircleHomotopyEquiv_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion a) :
    (overlapCircleHomotopyEquiv a ha ha1 q : ℂ) =
      ‖Radial.circlePlaneComplexEquiv ((annulusOverlapHomeomorph a).symm q : Plane)‖⁻¹ •
        Radial.circlePlaneComplexEquiv ((annulusOverlapHomeomorph a).symm q : Plane) :=
  Radial.annulusCircleHomotopyEquiv_coe a ha ha1 ((annulusOverlapHomeomorph a).symm q)

/-- The inverse circle equivalence uses the explicit middle radius. -/
theorem overlapCircleHomotopyEquiv_symm_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (z : _root_.Circle) :
    ((overlapCircleHomotopyEquiv a ha ha1).symm z : BaseTorus) =
      basePoint (((a + 1) / 2) • (Radial.frontierCellCircleHomeomorph.symm z : Plane)) := rfl

/-- Under the explicit contraction of the inner region, the overlap
inclusion is the unique map to the point. -/
theorem overlapIntoInner_point (a : ℝ) (q : overlapRegion a) :
    innerRegionPointHomotopyEquiv (overlapIntoInner a q) = () := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

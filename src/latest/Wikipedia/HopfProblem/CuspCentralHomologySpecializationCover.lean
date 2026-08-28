import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverProduct
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverOverlap

/-!
# The actual specialization respects the two radial open covers

The marked product collapse retains the underlying hexagon point.  Its
only change in the open-cell coordinates is the already constructed
frozen phase character.  In particular its radial coordinate is exactly
the base-torus radius, and it restricts to maps of the original inner,
outer, and overlap subspaces.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCover

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling
open SpecializationModel PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem productCollapse_basePoint (u : CompactFibreTorus) (y : Plane) :
    productCollapse C ε hε (u, BaseCover.basePoint y) =
      honeycombCollapseMap C ε hε (u * sourcePhaseCharacter (C 0) y, y) := by
  change productCollapse C ε hε (u, coordinateProjection 2 (-realCuspVector y)) = _
  rw [productCollapse_coordinateProjection, realCuspVector_neg_realCuspVector]

theorem productCollapse_cellMap (u : CompactFibreTorus) (y : baseCell) :
    productCollapse C ε hε (u, BaseCover.cellMap y) =
      fundamentalCellMap C ε hε (u * sourcePhaseCharacter (C 0) (y : Plane), y) :=
  productCollapse_basePoint C ε hε u y

/-- The equality is between the actual descended radii on the two
original spaces, including all boundary representatives. -/
theorem productCollapse_radius (p : BaseCover.PhaseBase) :
    centralRadius C ε hε (productCollapse C ε hε p) = BaseCover.radius p.2 := by
  rcases p with ⟨u, b⟩
  obtain ⟨y, rfl⟩ := BaseCover.cellMap_surjective b
  rw [productCollapse_cellMap, centralRadius_fundamentalCellMap, BaseCover.radius_cellMap]

@[simp] theorem productCollapse_mem_outer_iff (a : ℝ) (p : BaseCover.PhaseBase) :
    productCollapse C ε hε p ∈ outerRegion C ε hε a ↔
      p ∈ BaseCover.phaseOuterRegion a := by
  change a < centralRadius C ε hε (productCollapse C ε hε p) ↔ a < BaseCover.radius p.2
  rw [productCollapse_radius]

@[simp] theorem productCollapse_mem_inner_iff (p : BaseCover.PhaseBase) :
    productCollapse C ε hε p ∈ innerRegion C ε hε ↔
      p ∈ BaseCover.phaseInnerRegion := by
  change centralRadius C ε hε (productCollapse C ε hε p) < 1 ↔ BaseCover.radius p.2 < 1
  rw [productCollapse_radius]

@[simp] theorem productCollapse_mem_overlap_iff (a : ℝ) (p : BaseCover.PhaseBase) :
    productCollapse C ε hε p ∈ overlapRegion C ε hε a ↔
      p ∈ BaseCover.phaseOverlapRegion a := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [productCollapse_mem_outer_iff, productCollapse_mem_inner_iff]

theorem productCollapse_mapsTo_outer (a : ℝ) :
    MapsTo (productCollapse C ε hε) (BaseCover.phaseOuterRegion a) (outerRegion C ε hε a) :=
  fun p hp => (productCollapse_mem_outer_iff C ε hε a p).mpr hp

theorem productCollapse_mapsTo_inner :
    MapsTo (productCollapse C ε hε) BaseCover.phaseInnerRegion (innerRegion C ε hε) :=
  fun p hp => (productCollapse_mem_inner_iff C ε hε p).mpr hp

/-- The actual restriction of specialization to the outer open region. -/
def outerMap (a : ℝ) : C(BaseCover.phaseOuterRegion a, outerRegion C ε hε a) where
  toFun p := ⟨productCollapse C ε hε p, productCollapse_mapsTo_outer C ε hε a p.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (productCollapse C ε hε).continuous.comp continuous_subtype_val

/-- The actual restriction to the open fundamental cell. -/
def innerMap : C(BaseCover.phaseInnerRegion, innerRegion C ε hε) where
  toFun p := ⟨productCollapse C ε hε p, productCollapse_mapsTo_inner C ε hε p.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (productCollapse C ε hε).continuous.comp continuous_subtype_val

/-- The actual restriction to the literal open-cover intersection. -/
def overlapMap (a : ℝ) : C(BaseCover.phaseOverlapRegion a, overlapRegion C ε hε a) where
  toFun p := ⟨productCollapse C ε hε p,
    (productCollapse_mem_overlap_iff C ε hε a p).mpr p.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (productCollapse C ε hε).continuous.comp continuous_subtype_val

@[simp] theorem outerMap_coe (a : ℝ) (p : BaseCover.phaseOuterRegion a) :
    (outerMap C ε hε a p : QuotientCentralFibre C ε) = productCollapse C ε hε p := rfl

@[simp] theorem innerMap_coe (p : BaseCover.phaseInnerRegion) :
    (innerMap C ε hε p : QuotientCentralFibre C ε) = productCollapse C ε hε p := rfl

@[simp] theorem overlapMap_coe (a : ℝ) (p : BaseCover.phaseOverlapRegion a) :
    (overlapMap C ε hε a p : QuotientCentralFibre C ε) = productCollapse C ε hε p := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCover

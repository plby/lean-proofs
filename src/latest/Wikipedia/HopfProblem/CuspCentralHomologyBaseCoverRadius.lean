import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverBasic
import Wikipedia.HopfProblem.CuspCentralHomologyRadialGauge
import Wikipedia.HopfProblem.CuspHoneycombStrata
import Wikipedia.HopfProblem.CuspHoneycombHexagonGluing

/-!
# The radial coordinate on the actual base torus

The gauge of the literal closed hexagon descends through its actual map
to the base torus. Interior representatives have singleton fibres by the
exact honeycomb-cell incidence theorem. All remaining identifications
are on the frontier, where the gauge is one.

The descended continuous radius defines the genuine boundary, the open
cell region, and the outer radial regions of the original base torus.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The actual quotient identifies no other cell point with an interior
representative of the literal fundamental hexagon. -/
theorem cellMap_eq_of_interior (y z : baseCell)
    (hy : (y : Plane) ∈ interior baseCell) (h : cellMap y = cellMap z) : y = z := by
  obtain ⟨v, hv⟩ := (cellMap_eq_iff y z).mp h
  have hyv : (y : Plane) ∈ cell v := by
    rw [hv, mem_cell, add_sub_cancel_right]
    exact z.property
  have hv0 : v = 0 := ((CuspHoneycombTiling.mem_interior_baseCell_iff _).mp hy v).mp hyv
  apply Subtype.ext
  simpa only [hv0, latticePoint_zero, add_zero] using hv

/-- Interior membership is saturated for the actual base-cell quotient. -/
theorem cellMap_interior_iff_of_eq (y z : baseCell) (h : cellMap y = cellMap z) :
    (y : Plane) ∈ interior baseCell ↔ (z : Plane) ∈ interior baseCell := by
  constructor
  · intro hy
    simpa only [← cellMap_eq_of_interior y z hy h] using hy
  · intro hz
    simpa only [← cellMap_eq_of_interior z y hz h.symm] using hz

/-- Distinct representatives of one base-torus point are both on the
literal frontier of the fundamental hexagon. -/
theorem cellMap_eq_or_frontier (y z : baseCell) (h : cellMap y = cellMap z) :
    y = z ∨ ((y : Plane) ∈ frontier baseCell ∧ (z : Plane) ∈ frontier baseCell) := by
  by_cases hy : (y : Plane) ∈ interior baseCell
  · exact Or.inl (cellMap_eq_of_interior y z hy h)
  · right
    rw [baseCell_isClosed.frontier_eq]
    refine ⟨⟨y.property, hy⟩, z.property, ?_⟩
    intro hz
    exact hy ((cellMap_interior_iff_of_eq y z h).mpr hz)

theorem cellMap_frontier_iff_of_eq (y z : baseCell) (h : cellMap y = cellMap z) :
    (y : Plane) ∈ frontier baseCell ↔ (z : Plane) ∈ frontier baseCell := by
  rw [mem_frontier_iff_notMem_interior y.property,
    mem_frontier_iff_notMem_interior z.property]
  exact not_congr (cellMap_interior_iff_of_eq y z h)

/-- The literal gauge is constant on every exact fibre of the base-cell map. -/
theorem cellGauge_eq_of_cellMap_eq (y z : baseCell) (h : cellMap y = cellMap z) :
    Radial.cellGauge (y : Plane) = Radial.cellGauge (z : Plane) := by
  rcases cellMap_eq_or_frontier y z h with rfl | ⟨hy, hz⟩
  · rfl
  · rw [(Radial.mem_frontier_baseCell_iff _).mp hy,
      (Radial.mem_frontier_baseCell_iff _).mp hz]

/-- The gauge on the original compact cell, before quotienting. -/
def cellRadius : C(baseCell, ℝ) :=
  ⟨fun y => Radial.cellGauge (y : Plane),
    Radial.cellGauge_continuous.comp continuous_subtype_val⟩

/-- The actual continuous radial coordinate on the literal base torus. -/
def radius : C(BaseTorus, ℝ) where
  toFun := CuspHoneycombHexagon.CommonFibres.descend cellMap cellRadius cellMap_surjective
  continuous_toFun := CuspHoneycombHexagon.CommonFibres.descend_continuous
    cellMap cellRadius cellMap_surjective cellMap_isQuotientMap cellRadius.continuous
    cellGauge_eq_of_cellMap_eq

@[simp] theorem radius_cellMap (y : baseCell) :
    radius (cellMap y) = Radial.cellGauge (y : Plane) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply cellMap cellRadius
    cellMap_surjective cellGauge_eq_of_cellMap_eq y

theorem radius_continuous : Continuous radius := radius.continuous

theorem radius_mem_Icc (q : BaseTorus) : radius q ∈ Icc 0 1 := by
  obtain ⟨y, rfl⟩ := cellMap_surjective q
  rw [radius_cellMap]
  exact ⟨Radial.cellGauge_nonneg _, (Radial.mem_baseCell_iff _).mp y.property⟩

theorem radius_nonneg (q : BaseTorus) : 0 ≤ radius q := (radius_mem_Icc q).1

theorem radius_le_one (q : BaseTorus) : radius q ≤ 1 := (radius_mem_Icc q).2

/-- The intrinsic boundary locus of the actual cell presentation. -/
def boundary : Set BaseTorus := {q | radius q = 1}

/-- The actual open-cell region. -/
def innerRegion : Set BaseTorus := {q | radius q < 1}

/-- The outer radial region at a real threshold. -/
def outerRegion (a : ℝ) : Set BaseTorus := {q | a < radius q}

theorem cellMap_mem_boundary_iff (y : baseCell) :
    cellMap y ∈ boundary ↔ (y : Plane) ∈ frontier baseCell := by
  change radius (cellMap y) = 1 ↔ _
  rw [radius_cellMap]
  exact (Radial.mem_frontier_baseCell_iff _).symm

theorem cellMap_mem_innerRegion_iff (y : baseCell) :
    cellMap y ∈ innerRegion ↔ (y : Plane) ∈ interior baseCell := by
  change radius (cellMap y) < 1 ↔ _
  rw [radius_cellMap]
  exact (Radial.mem_interior_baseCell_iff _).symm

theorem cellMap_mem_outerRegion_iff (a : ℝ) (y : baseCell) :
    cellMap y ∈ outerRegion a ↔ a < Radial.cellGauge (y : Plane) := by
  change a < radius (cellMap y) ↔ _
  rw [radius_cellMap]

theorem boundary_eq_image :
    boundary = cellMap '' {y : baseCell | (y : Plane) ∈ frontier baseCell} := by
  ext q
  constructor
  · intro hq
    obtain ⟨y, rfl⟩ := cellMap_surjective q
    exact ⟨y, (cellMap_mem_boundary_iff y).mp hq, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (cellMap_mem_boundary_iff y).mpr hy

theorem innerRegion_eq_image :
    innerRegion = cellMap '' {y : baseCell | (y : Plane) ∈ interior baseCell} := by
  ext q
  constructor
  · intro hq
    obtain ⟨y, rfl⟩ := cellMap_surjective q
    exact ⟨y, (cellMap_mem_innerRegion_iff y).mp hq, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (cellMap_mem_innerRegion_iff y).mpr hy

theorem boundary_isClosed : IsClosed boundary :=
  isClosed_eq radius.continuous continuous_const

theorem innerRegion_isOpen : IsOpen innerRegion :=
  isOpen_lt radius.continuous continuous_const

theorem outerRegion_isOpen (a : ℝ) : IsOpen (outerRegion a) :=
  isOpen_lt continuous_const radius.continuous

theorem innerRegion_eq_compl_boundary : innerRegion = boundaryᶜ := by
  ext q
  change radius q < 1 ↔ ¬radius q = 1
  exact ⟨fun h => h.ne, fun h => lt_of_le_of_ne (radius_le_one q) h⟩

theorem boundary_subset_outerRegion (a : ℝ) (ha : a < 1) : boundary ⊆ outerRegion a := by
  intro q hq
  change a < radius q
  change radius q = 1 at hq
  rwa [hq]

/-- The actual inner and outer regions cover the base torus at every
threshold strictly below the boundary radius. -/
theorem outerRegion_union_innerRegion (a : ℝ) (ha : a < 1) :
    outerRegion a ∪ innerRegion = univ := by
  apply Set.eq_univ_of_forall
  intro q
  by_cases hq : radius q < 1
  · exact Or.inr hq
  · exact Or.inl (ha.trans_le (le_of_not_gt hq))

theorem innerRegion_union_outerRegion (a : ℝ) (ha : a < 1) :
    innerRegion ∪ outerRegion a = univ := by
  rw [union_comm]
  exact outerRegion_union_innerRegion a ha

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

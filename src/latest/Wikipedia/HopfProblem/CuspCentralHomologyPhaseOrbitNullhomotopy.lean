import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverCompatibility
import Wikipedia.HopfProblem.CuspHoneycomb
import Mathlib.Topology.Homotopy.Contractible

/-!
# Explicit nullhomotopies of actual compact-phase orbits

The phase orbit over the centre of the fundamental hexagon contracts by
moving its positive base point along a straight segment to a triangle
barycenter. At that actual toric triple point every compact phase has the
same image. A second contraction stays on the literal hexagon frontier
and contracts the boundary-anchor phase orbit inside the actual central
boundary.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The first actual triangle barycenter on the boundary of the central
dual cell. -/
def phaseOrbitVertex : Radial.CellFrontier :=
  ⟨![(1 / 3 : ℝ), 1 / 3], (Radial.mem_frontier_baseCell_iff _).mpr (by
    norm_num [Radial.cellGauge])⟩

@[simp] theorem phaseOrbitVertex_coe :
    (phaseOrbitVertex : Plane) = ![(1 / 3 : ℝ), 1 / 3] := rfl

theorem phaseOrbitVertex_eq_triangleBarycenter :
    (phaseOrbitVertex : Plane) = triangleBarycenter (ToricComponent.zeroTriangle 0) := by
  rw [triangleBarycenter_zeroTriangle]
  funext i
  fin_cases i <;> norm_num [phaseOrbitVertex, ToricComponent.hexagonRay]

@[simp] theorem phaseOrbitVertex_gauge : Radial.cellGauge (phaseOrbitVertex : Plane) = 1 :=
  (Radial.mem_frontier_baseCell_iff _).mp phaseOrbitVertex.2

/-- The centre-to-vertex segment stays in the actual closed dual cell. -/
theorem phaseOrbitCentreSegment_mem_baseCell (s : unitInterval) :
    (s : ℝ) • (phaseOrbitVertex : Plane) ∈ baseCell := by
  apply (Radial.mem_baseCell_iff _).mpr
  rw [Radial.cellGauge_smul_of_nonneg _ s.2.1, phaseOrbitVertex_gauge, mul_one]
  exact s.2.2

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- All compact phases collapse at this literal toric triple point. -/
theorem honeycombCollapseMap_phaseOrbitVertex (φ : CompactFibreTorus) :
    honeycombCollapseMap C ε hε (φ, (phaseOrbitVertex : Plane)) =
      honeycombCollapseMap C ε hε (1, (phaseOrbitVertex : Plane)) := by
  apply (honeycombCollapseMap_eq_iff C ε hε _ _).mpr
  refine ⟨0, by simp, ?_⟩
  rw [phaseOrbitVertex_eq_triangleBarycenter, honeycombHomeomorph_stabilizer_triangleBarycenter]
  trivial

/-- The original compact-phase orbit over the centre of the honeycomb cell. -/
def centralPhaseOrbit : C(CompactFibreTorus, QuotientCentralFibre C ε) where
  toFun φ := honeycombCollapseMap C ε hε (φ, 0)
  continuous_toFun := (honeycombCollapseMap_continuous C ε hε).comp
    (continuous_id.prodMk continuous_const)

@[simp] theorem centralPhaseOrbit_apply (φ : CompactFibreTorus) :
    centralPhaseOrbit C ε hε φ = honeycombCollapseMap C ε hε (φ, 0) := rfl

/-- The explicit phase-preserving straight homotopy from the centre orbit
to the single original toric triple point. -/
def centralPhaseOrbitHomotopy :
    (centralPhaseOrbit C ε hε).Homotopy
      (ContinuousMap.const CompactFibreTorus
        (honeycombCollapseMap C ε hε (1, (phaseOrbitVertex : Plane)))) where
  toFun p := honeycombCollapseMap C ε hε (p.2, (p.1 : ℝ) • (phaseOrbitVertex : Plane))
  continuous_toFun := (honeycombCollapseMap_continuous C ε hε).comp
    (continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).smul continuous_const))
  map_zero_left φ := by
    change honeycombCollapseMap C ε hε (φ, (0 : ℝ) • (phaseOrbitVertex : Plane)) = _
    rw [zero_smul]
    rfl
  map_one_left φ := by
    change honeycombCollapseMap C ε hε (φ, (1 : ℝ) • (phaseOrbitVertex : Plane)) = _
    rw [one_smul]
    exact honeycombCollapseMap_phaseOrbitVertex C ε hε φ

@[simp] theorem centralPhaseOrbitHomotopy_apply (s : unitInterval) (φ : CompactFibreTorus) :
    centralPhaseOrbitHomotopy C ε hε (s, φ) =
      honeycombCollapseMap C ε hε (φ, (s : ℝ) • (phaseOrbitVertex : Plane)) := rfl

theorem centralPhaseOrbit_nullhomotopic : (centralPhaseOrbit C ε hε).Nullhomotopic :=
  ⟨honeycombCollapseMap C ε hε (1, (phaseOrbitVertex : Plane)),
    ⟨centralPhaseOrbitHomotopy C ε hε⟩⟩

theorem phaseOrbitAnchor_coe :
    (Radial.frontierCellCircleHomeomorph.symm 1 : Plane) = ![(1 / 2 : ℝ), 0] := by
  rw [Radial.frontierCellCircleHomeomorph_symm_coe]
  ext i
  fin_cases i <;> norm_num [Radial.cellGauge, Pi.smul_apply, smul_eq_mul]

theorem phaseOrbitSegment_coordinates (s : unitInterval) :
    (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : Plane) +
      (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : Plane) =
        ![(1 / 2 : ℝ) - (s : ℝ) / 6, (s : ℝ) / 3] := by
  ext i
  fin_cases i <;> simp [Pi.add_apply, smul_eq_mul] <;> ring

/-- This straight segment lies entirely on the literal supporting side
`2x₀ + x₁ = 1` of the closed dual hexagon. -/
theorem phaseOrbitSegment_mem_frontier (s : unitInterval) :
    (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : Plane) +
      (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : Plane) ∈ frontier baseCell := by
  apply (Radial.mem_frontier_baseCell_iff _).mpr
  rw [phaseOrbitSegment_coordinates]
  simp only [Radial.cellGauge, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : 2 * ((1 / 2 : ℝ) - (s : ℝ) / 6) + (s : ℝ) / 3 = 1 := by ring
  rw [h0, abs_one]
  apply max_eq_left
  apply max_le
  · apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2]
  · apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2]

/-- The explicit frontier path from the circle-coordinate anchor to the
actual toric triple-point vertex. -/
def phaseOrbitSegment : C(unitInterval, Radial.CellFrontier) where
  toFun s := ⟨(1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : Plane) +
    (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : Plane), phaseOrbitSegment_mem_frontier s⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)

@[simp] theorem phaseOrbitSegment_coe (s : unitInterval) :
    (phaseOrbitSegment s : Plane) =
      (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : Plane) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : Plane) := rfl

@[simp] theorem phaseOrbitSegment_zero :
    phaseOrbitSegment 0 = Radial.frontierCellCircleHomeomorph.symm 1 := by
  apply Subtype.ext
  rw [phaseOrbitSegment_coe, phaseOrbitAnchor_coe]
  simp

@[simp] theorem phaseOrbitSegment_one : phaseOrbitSegment 1 = phaseOrbitVertex := by
  apply Subtype.ext
  rw [phaseOrbitSegment_coe, phaseOrbitVertex_coe]
  simp

theorem boundaryCellMap_phaseOrbitVertex (φ : CompactFibreTorus) :
    boundaryCellMap C ε hε (φ, phaseOrbitVertex) =
      boundaryCellMap C ε hε (1, phaseOrbitVertex) :=
  Subtype.ext (honeycombCollapseMap_phaseOrbitVertex C ε hε φ)

/-- The original compact-phase orbit at the boundary anchor having circle
coordinate one. Its codomain is the actual central boundary. -/
def boundaryPhaseOrbit : C(CompactFibreTorus, centralBoundary C ε hε) :=
  (circleBoundaryCellMap C ε hε).comp
    ⟨fun φ => (φ, 1), continuous_id.prodMk continuous_const⟩

@[simp] theorem boundaryPhaseOrbit_apply (φ : CompactFibreTorus) :
    boundaryPhaseOrbit C ε hε φ = circleBoundaryCellMap C ε hε (φ, 1) := rfl

/-- The boundary-anchor orbit contracts inside the literal central boundary,
using the displayed straight path on one actual hexagon side. -/
def boundaryPhaseOrbitHomotopy :
    (boundaryPhaseOrbit C ε hε).Homotopy
      (ContinuousMap.const CompactFibreTorus (boundaryCellMap C ε hε (1, phaseOrbitVertex))) where
  toFun p := boundaryCellMap C ε hε (p.2, phaseOrbitSegment p.1)
  continuous_toFun := (boundaryCellMap C ε hε).continuous.comp
    (continuous_snd.prodMk (phaseOrbitSegment.continuous.comp continuous_fst))
  map_zero_left φ := by
    change boundaryCellMap C ε hε (φ, phaseOrbitSegment 0) = circleBoundaryCellMap C ε hε (φ, 1)
    rw [phaseOrbitSegment_zero, circleBoundaryCellMap_apply]
  map_one_left φ := by
    change boundaryCellMap C ε hε (φ, phaseOrbitSegment 1) = _
    rw [phaseOrbitSegment_one]
    exact boundaryCellMap_phaseOrbitVertex C ε hε φ

@[simp] theorem boundaryPhaseOrbitHomotopy_apply (s : unitInterval) (φ : CompactFibreTorus) :
    boundaryPhaseOrbitHomotopy C ε hε (s, φ) =
      boundaryCellMap C ε hε (φ, phaseOrbitSegment s) := rfl

theorem boundaryPhaseOrbitHomotopy_coe (s : unitInterval) (φ : CompactFibreTorus) :
    (boundaryPhaseOrbitHomotopy C ε hε (s, φ) : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε
        (φ, (1 - (s : ℝ)) • (Radial.frontierCellCircleHomeomorph.symm 1 : Plane) +
          (s : ℝ) • (phaseOrbitVertex : Plane)) := by
  rw [boundaryPhaseOrbitHomotopy_apply, boundaryCellMap_coe, phaseOrbitSegment_coe,
    phaseOrbitAnchor_coe, phaseOrbitVertex_coe]

theorem boundaryPhaseOrbit_nullhomotopic : (boundaryPhaseOrbit C ε hε).Nullhomotopic :=
  ⟨boundaryCellMap C ε hε (1, phaseOrbitVertex), ⟨boundaryPhaseOrbitHomotopy C ε hε⟩⟩

end Wikipedia.HopfProblem.CuspCentralHomology

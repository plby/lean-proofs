import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverOverlap
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverCollar

/-!
# Both actual open-cover inclusion maps in explicit coordinates

The inclusion of the overlap into the inner region is phase projection.
For the outer region, its constructed retraction sends a phase and an
annulus point to the original central quotient of that phase over the
normalized frontier point. This is the genuine boundary attaching map,
not a map supplied as a hypothesis.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

abbrev BoundaryPhaseCell := CompactFibreTorus × Radial.CellFrontier

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem honeycombCollapseMap_frontier_mem_boundary (p : BoundaryPhaseCell) :
    honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) ∈ centralBoundary C ε hε := by
  rw [centralBoundary_eq_image]
  exact ⟨(p.1, (p.2 : Plane)), ⟨mem_univ _, p.2.2⟩, rfl⟩

/-- The original phase-hexagon boundary map, with codomain its actual image. -/
def boundaryCellMap : C(BoundaryPhaseCell, centralBoundary C ε hε) where
  toFun p := ⟨honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)),
    honeycombCollapseMap_frontier_mem_boundary C ε hε p⟩
  continuous_toFun := by
    have hi : Continuous (fun p : BoundaryPhaseCell => (p.1, (p.2 : Plane))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact ((honeycombCollapseMap_continuous C ε hε).comp hi).subtype_mk _

@[simp] theorem boundaryCellMap_coe (p : BoundaryPhaseCell) :
    (boundaryCellMap C ε hε p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) := rfl

theorem boundaryCellMap_surjective : Function.Surjective (boundaryCellMap C ε hε) := by
  rintro ⟨q, hq⟩
  rw [centralBoundary_eq_image] at hq
  obtain ⟨⟨φ, x⟩, ⟨_, hx⟩, he⟩ := hq
  exact ⟨(φ, ⟨x, hx⟩), Subtype.ext he⟩

/-- The same genuine boundary map in ordinary circle coordinates for its direction. -/
def circleBoundaryCellMap : C(CompactFibreTorus × Circle, centralBoundary C ε hε) :=
  (boundaryCellMap C ε hε).comp
    ⟨fun p => (p.1, Radial.frontierCellCircleHomeomorph.symm p.2),
      continuous_fst.prodMk
        (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd)⟩

@[simp] theorem circleBoundaryCellMap_apply (p : CompactFibreTorus × Circle) :
    circleBoundaryCellMap C ε hε p =
      boundaryCellMap C ε hε (p.1, Radial.frontierCellCircleHomeomorph.symm p.2) := rfl

/-- The other actual inclusion from the overlap. -/
def overlapIntoOuter (a : ℝ) :
    C(overlapRegion C ε hε a, outerRegion C ε hε a) :=
  ⟨fun q => ⟨(q : QuotientCentralFibre C ε), q.2.1⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem overlapIntoOuter_coe (a : ℝ) (q : overlapRegion C ε hε a) :
    (overlapIntoOuter C ε hε a q : QuotientCentralFibre C ε) =
      (q : QuotientCentralFibre C ε) := rfl

/-- Inclusion of the strict annulus in the collar does not change its representatives. -/
def annulusIntoCollar (a : ℝ) (p : OverlapPhaseCell a) : CollarPhaseCell a :=
  (p.1, ⟨(p.2 : Plane), p.2.2.1, p.2.2.2.le⟩)

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

theorem overlapIntoOuter_phaseHomeomorph (a : ℝ) (p : OverlapPhaseCell a) :
    overlapIntoOuter C ε hε a (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
      collarCellMap C ε hε a (annulusIntoCollar a p) := by
  apply Subtype.ext
  rw [overlapIntoOuter_coe, overlapPhaseHomeomorph_coe, collarCellMap_coe]
  rfl

/-- Phase and frontier-direction coordinates on the actual overlap. -/
def overlapBoundaryCoordinates (a : ℝ) (ha : 0 ≤ a) :
    C(overlapRegion C ε hε a, BoundaryPhaseCell) where
  toFun q := ((overlapHomeomorph C ε hε hε1 hC hR a ha q).1,
    (overlapHomeomorph C ε hε hε1 hC hR a ha q).2.1)
  continuous_toFun :=
    (continuous_fst.comp (overlapHomeomorph C ε hε hε1 hC hR a ha).continuous).prodMk
      (continuous_fst.comp
        (continuous_snd.comp (overlapHomeomorph C ε hε hε1 hC hR a ha).continuous))

theorem overlapBoundaryCoordinates_phaseHomeomorph (a : ℝ) (ha : 0 ≤ a)
    (p : OverlapPhaseCell a) :
    overlapBoundaryCoordinates C ε hε hε1 hC hR a ha
      (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
        (p.1, (Radial.annulusHomeomorph a ha p.2).1) := by
  change (((Homeomorph.refl CompactFibreTorus).prodCongr (Radial.annulusHomeomorph a ha)
    ((overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
      (overlapPhaseHomeomorph C ε hε hε1 hC hR a p))).1,
    ((Homeomorph.refl CompactFibreTorus).prodCongr (Radial.annulusHomeomorph a ha)
      ((overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
        (overlapPhaseHomeomorph C ε hε hε1 hC hR a p))).2.1) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem outerRegionRetraction_overlapPhaseHomeomorph (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (p : OverlapPhaseCell a) :
    outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
      (overlapIntoOuter C ε hε a (overlapPhaseHomeomorph C ε hε hε1 hC hR a p)) =
        boundaryCellMap C ε hε (p.1, (Radial.annulusHomeomorph a ha p.2).1) := by
  apply Subtype.ext
  rw [overlapIntoOuter_phaseHomeomorph, outerRegionRetraction_collarCellMap,
    boundaryCellMap_coe]
  rfl

/-- The actual outer retraction on the overlap is precisely the boundary collapse
at its unchanged phase and normalized frontier direction. -/
theorem outerRegionRetraction_overlap (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion C ε hε a) :
    outerRegionRetraction C ε hε a ha ha1 hε1 hC hR (overlapIntoOuter C ε hε a q) =
      boundaryCellMap C ε hε (overlapBoundaryCoordinates C ε hε hε1 hC hR a ha q) := by
  obtain ⟨p, rfl⟩ := (overlapPhaseHomeomorph C ε hε hε1 hC hR a).surjective q
  rw [overlapBoundaryCoordinates_phaseHomeomorph]
  exact outerRegionRetraction_overlapPhaseHomeomorph C ε hε hε1 hC hR a ha ha1 p

theorem outerRegionRetraction_overlap_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR).comp
        (overlapIntoOuter C ε hε a) =
      (boundaryCellMap C ε hε).comp (overlapBoundaryCoordinates C ε hε hε1 hC hR a ha) := by
  apply ContinuousMap.ext
  intro q
  exact outerRegionRetraction_overlap C ε hε hε1 hC hR a ha ha1 q

theorem overlapCircleHomotopyEquiv_phaseHomeomorph (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (p : OverlapPhaseCell a) :
    overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1
      (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
        (p.1, Radial.annulusCircleHomotopyEquiv a ha ha1 p.2) := by
  change Radial.phaseAnnulusHomotopyEquiv CompactFibreTorus a ha ha1
    ((overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
      (overlapPhaseHomeomorph C ε hε hε1 hC hR a p)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- In the explicitly constructed circle homotopy coordinates, the outer inclusion
is the original boundary map on compact phases and the ordinary circle. -/
theorem overlapIntoOuter_boundary (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion C ε hε a) :
    outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR
        (overlapIntoOuter C ε hε a q) =
      circleBoundaryCellMap C ε hε
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1 q) := by
  obtain ⟨p, rfl⟩ := (overlapPhaseHomeomorph C ε hε hε1 hC hR a).surjective q
  rw [outerRegionBoundaryHomotopyEquiv_apply, outerRegionRetraction_overlapPhaseHomeomorph,
    overlapCircleHomotopyEquiv_phaseHomeomorph, circleBoundaryCellMap_apply]
  congr 1
  apply Prod.ext
  · rfl
  · change (Radial.annulusHomeomorph a ha p.2).1 =
      Radial.frontierCellCircleHomeomorph.symm
        (Radial.frontierCellCircleHomeomorph (Radial.annulusHomeomorph a ha p.2).1)
    exact (Radial.frontierCellCircleHomeomorph.symm_apply_apply _).symm

theorem overlapIntoOuter_boundary_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).toFun.comp
        (overlapIntoOuter C ε hε a) =
      (circleBoundaryCellMap C ε hε).comp
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  exact overlapIntoOuter_boundary C ε hε hε1 hC hR a ha ha1 q

end Wikipedia.HopfProblem.CuspCentralHomology

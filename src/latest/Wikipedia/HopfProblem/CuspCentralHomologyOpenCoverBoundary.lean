import Wikipedia.HopfProblem.CuspCentralHomologyOpenCover
import Wikipedia.HopfProblem.CuspCentralHomologyEdgeOrbits

/-!
# The actual compatible edge arcs cover the central boundary

The global honeycomb map agrees with the constructed compatible cell map
on the central hexagon.  Its literal frontier is therefore exactly the
union of the six actual compatible edge arcs.  Applying compact fibre
phases and the original central quotient map gives the radius-one locus,
including all edge endpoints, without analytic or small-drift assumptions.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse
open CuspHoneycomb CuspHoneycombHexagon CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The global map on the literal central hexagon is its compatible cell map. -/
theorem honeycombHomeomorph_baseCell_coe (x : baseCell) :
    ((honeycombHomeomorph C₀ (x : Plane)).1 : Space) =
      ((compatibleCellHomeomorph C₀ x).1 : Space) := by
  let y : cell 0 := cellTranslationHomeomorph 0 x
  have hy : (y : Plane) = (x : Plane) := by
    change (x : Plane) + latticePoint 0 = (x : Plane)
    rw [latticePoint_zero, add_zero]
  have hnorm : (cellTranslationHomeomorph 0).symm y = x :=
    (cellTranslationHomeomorph 0).symm_apply_apply x
  have h := honeycombHomeomorph_cell_coe C₀ 0 y
  rw [hy, hnorm, cuspVector_zero, neg_zero, twistedTranslate_zero] at h
  exact h

/-- The actual planar preimage of one of the chosen compatible edge points. -/
def edgeArcBase (k : Fin 6) (t : unitInterval) : baseCell :=
  (compatibleCellHomeomorph C₀).symm (compatibleBoundaryArc C₀ k t).1

@[simp] theorem compatibleCellHomeomorph_edgeArcBase (k : Fin 6) (t : unitInterval) :
    compatibleCellHomeomorph C₀ (edgeArcBase C₀ k t) =
      (compatibleBoundaryArc C₀ k t).1 :=
  (compatibleCellHomeomorph C₀).apply_symm_apply _

theorem edgeArcBase_mem_frontier (k : Fin 6) (t : unitInterval) :
    (edgeArcBase C₀ k t : Plane) ∈ frontier baseCell := by
  rw [frontier_baseCell, mem_iUnion]
  refine ⟨k, (edgeArcBase C₀ k t).2, ?_⟩
  apply (compatibleCellHomeomorph_mem_boundary_iff C₀ (edgeArcBase C₀ k t) k).mp
  rw [compatibleCellHomeomorph_edgeArcBase]
  exact (compatibleBoundaryArc C₀ k t).2

/-- The chosen planar boundary point maps to the actual positive edge point. -/
@[simp] theorem honeycombHomeomorph_edgeArcBase (k : Fin 6) (t : unitInterval) :
    honeycombHomeomorph C₀ (edgeArcBase C₀ k t : Plane) = edgeArcPositive C₀ k t := by
  apply Subtype.ext
  apply Subtype.ext
  change ((honeycombHomeomorph C₀ (edgeArcBase C₀ k t : Plane)).1 : Space) =
    ((compatibleBoundaryArc C₀ k t).1.1 : Space)
  rw [honeycombHomeomorph_baseCell_coe, compatibleCellHomeomorph_edgeArcBase]

/-- Every point of the literal central frontier is on a compatible arc. -/
theorem exists_edgeArcBase_of_mem_frontier (x : Plane) (hx : x ∈ frontier baseCell) :
    ∃ k : Fin 6, ∃ t : unitInterval, (edgeArcBase C₀ k t : Plane) = x := by
  obtain ⟨k, hbase, hside⟩ := mem_iUnion.mp ((congrArg (x ∈ ·) frontier_baseCell).mp hx)
  let a : baseCell := ⟨x, hbase⟩
  have ha : compatibleCellHomeomorph C₀ a ∈ positiveBoundary k :=
    (compatibleCellHomeomorph_mem_boundary_iff C₀ a k).mpr hside
  obtain ⟨t, ht⟩ := (compatibleBoundaryArc C₀ k).surjective
    ⟨compatibleCellHomeomorph C₀ a, ha⟩
  refine ⟨k, t, ?_⟩
  have hcell : edgeArcBase C₀ k t = a := by
    apply (compatibleCellHomeomorph C₀).injective
    rw [compatibleCellHomeomorph_edgeArcBase]
    exact congrArg Subtype.val ht
  exact congrArg Subtype.val hcell

/-- This range criterion is for the global map into the actual positive fibre. -/
theorem honeycombHomeomorph_mem_edgeArcs_iff (x : Plane) :
    (∃ k : Fin 6, ∃ t : unitInterval,
      honeycombHomeomorph C₀ x = edgeArcPositive C₀ k t) ↔ x ∈ frontier baseCell := by
  constructor
  · rintro ⟨k, t, h⟩
    have hx : x = (edgeArcBase C₀ k t : Plane) :=
      (honeycombHomeomorph C₀).injective
        (h.trans (honeycombHomeomorph_edgeArcBase C₀ k t).symm)
    rw [hx]
    exact edgeArcBase_mem_frontier C₀ k t
  · intro hx
    obtain ⟨k, t, ht⟩ := exists_edgeArcBase_of_mem_frontier C₀ x hx
    refine ⟨k, t, ?_⟩
    rw [← ht, honeycombHomeomorph_edgeArcBase]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The radius-one locus is exactly the actual quotient of all compact
phases over the six compatible boundary arcs, including their endpoints. -/
theorem mem_centralBoundary_iff_edgeArc (q : QuotientCentralFibre C ε) :
    q ∈ centralBoundary C ε hε ↔
      ∃ k : Fin 6, ∃ t : unitInterval, ∃ u : CompactFibreTorus,
        centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) = q := by
  rw [centralBoundary_eq_image]
  constructor
  · rintro ⟨⟨u, x⟩, ⟨_, hx⟩, hq⟩
    obtain ⟨k, t, ht⟩ := (honeycombHomeomorph_mem_edgeArcs_iff (C 0) x).mpr hx
    refine ⟨k, t, u, ?_⟩
    change centralCollapseMap C ε hε (u, honeycombHomeomorph (C 0) x) = q at hq
    rw [ht] at hq
    exact hq
  · rintro ⟨k, t, u, hq⟩
    refine ⟨(u, (edgeArcBase (C 0) k t : Plane)),
      ⟨mem_univ _, edgeArcBase_mem_frontier (C 0) k t⟩, ?_⟩
    change centralCollapseMap C ε hε
      (u, honeycombHomeomorph (C 0) (edgeArcBase (C 0) k t : Plane)) = q
    rw [honeycombHomeomorph_edgeArcBase]
    exact hq

theorem centralCollapseMap_edgeArc_mem_centralBoundary
    (k : Fin 6) (t : unitInterval) (u : CompactFibreTorus) :
    centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) ∈
      centralBoundary C ε hε :=
  (mem_centralBoundary_iff_edgeArc C ε hε _).mpr ⟨k, t, u, rfl⟩

/-- In particular the genuine circle cylinders lie in the central boundary. -/
theorem centralProject_edgeCylinder_mem_centralBoundary
    (k : Fin 6) (p : unitInterval × Circle) :
    centralProject C ε hε (edgeCylinder (C 0) k p) ∈ centralBoundary C ε hε :=
  centralCollapseMap_edgeArc_mem_centralBoundary C ε hε k p.1
    (hexagonCharacterSection k p.2)

end Wikipedia.HopfProblem.CuspCentralHomology

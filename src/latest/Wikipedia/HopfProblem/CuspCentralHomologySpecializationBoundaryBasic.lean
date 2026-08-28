import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct

/-!
# The actual product specialization restricted to the theta boundary

The marked theta map lands in the base torus. Its product with compact
fibre phases maps under the existing specialization collapse into the
literal central boundary. Restricting the codomain therefore gives a
continuous boundary lift with the original topology and an exact formula
on every oriented edge representative, including the two common poles.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling
open PeriodTorusHigherHomology SpecializationModel

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The global positive honeycomb coordinate on a literal straight dual
side is the actual chosen compatible boundary arc. -/
theorem honeycombHomeomorph_dualSidePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    honeycombHomeomorph C₀ (dualSidePoint k t) = edgeArcPositive C₀ k t := by
  rw [← edgeArcBase_eq_dualSidePoint C₀ k t, honeycombHomeomorph_edgeArcBase]

theorem dualSidePoint_mem_frontier (k : Fin 6) (t : unitInterval) :
    dualSidePoint k t ∈ frontier baseCell := by
  rw [← edgeArcBase_eq_dualSidePoint (0 : Matrix (Fin 2) (Fin 2) ℂ) k t]
  exact edgeArcBase_mem_frontier (0 : Matrix (Fin 2) (Fin 2) ℂ) k t

theorem orientedEdgeBasePoint_mem_frontier (t : unitInterval) (j : Fin 3) :
    orientedEdgeBasePoint t j ∈ frontier baseCell :=
  dualSidePoint_mem_frontier (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)

theorem honeycombHomeomorph_orientedEdgeBasePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (t : unitInterval) (j : Fin 3) :
    honeycombHomeomorph C₀ (orientedEdgeBasePoint t j) =
      edgeArcPositive C₀ (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t) :=
  honeycombHomeomorph_dualSidePoint C₀ (thetaEdgeIndex j)
    (if j = 1 then unitInterval.symm t else t)

/-- Identity on compact fibre phases and the actual marked theta map on the base. -/
def thetaProductMap : C(CompactFibreTorus × Theta, CompactFibreTorus × ProductTorus 2) :=
  (ContinuousMap.id CompactFibreTorus).prodMap thetaBaseMap

@[simp] theorem thetaProductMap_apply (p : CompactFibreTorus × Theta) :
    thetaProductMap p = (p.1, thetaBaseMap p.2) := rfl

@[simp] theorem thetaProductMap_mk (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaProductMap (u, Suspension.mk t j) =
      (u, baseTorusPoint (orientedEdgeBasePoint t j)) := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The marked product formula retains the actual frozen phase shear;
the two inverse quarter-turns cancel on the base representative. -/
theorem productCollapse_thetaProductMap_mk (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    productCollapse C ε hε (thetaProductMap (u, Suspension.mk t j)) =
      honeycombCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) := by
  rw [thetaProductMap_mk, baseTorusPoint_apply, productCollapse_coordinateProjection,
    realCuspVector_neg_realCuspVector]

/-- Every representative of this product map lies in the literal
central boundary, not merely in an auxiliary suspension model. -/
theorem productCollapse_thetaProductMap_mem_centralBoundary (p : CompactFibreTorus × Theta) :
    productCollapse C ε hε (thetaProductMap p) ∈ centralBoundary C ε hε := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [productCollapse_thetaProductMap_mk, centralBoundary_eq_image]
  exact ⟨(u * sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
    orientedEdgeBasePoint t j),
    ⟨mem_univ _, orientedEdgeBasePoint_mem_frontier t j⟩, rfl⟩

/-- The actual product specialization with its codomain restricted to
the central boundary, carrying its inherited topology. -/
def boundaryLift : C(CompactFibreTorus × Theta, centralBoundary C ε hε) where
  toFun p := ⟨productCollapse C ε hε (thetaProductMap p),
    productCollapse_thetaProductMap_mem_centralBoundary C ε hε p⟩
  continuous_toFun := ((productCollapse C ε hε).continuous.comp thetaProductMap.continuous).subtype_mk _

@[simp] theorem boundaryLift_coe (p : CompactFibreTorus × Theta) :
    (boundaryLift C ε hε p : QuotientCentralFibre C ε) =
      productCollapse C ε hε (thetaProductMap p) := rfl

/-- This is an equality of the original continuous maps. -/
theorem centralBoundaryInclusion_comp_boundaryLift :
    (centralBoundaryInclusion C ε hε).comp (boundaryLift C ε hε) =
      (productCollapse C ε hε).comp thetaProductMap := rfl

@[simp] theorem boundaryLift_mk_coe (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    (boundaryLift C ε hε (u, Suspension.mk t j) : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) :=
  productCollapse_thetaProductMap_mk C ε hε u t j

/-- The same representative formula expressed directly on the actual
compatible positive arcs, with their chosen orientations. -/
theorem boundaryLift_mk_centralCollapseMap (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    (boundaryLift C ε hε (u, Suspension.mk t j) : QuotientCentralFibre C ε) =
      centralCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          edgeArcPositive (C 0) (thetaEdgeIndex j)
            (if j = 1 then unitInterval.symm t else t)) := by
  rw [boundaryLift_mk_coe]
  change centralCollapseMap C ε hε
    (u * sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
      honeycombHomeomorph (C 0) (orientedEdgeBasePoint t j)) = _
  rw [honeycombHomeomorph_orientedEdgeBasePoint]

end Wikipedia.HopfProblem.CuspCentralHomology

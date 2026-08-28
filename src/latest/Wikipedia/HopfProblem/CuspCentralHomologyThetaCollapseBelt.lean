import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseSource
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseTarget

/-!
# The character collapse on actual middle-belt homology

At height one half each source edge gives a literal phase-torus section.
The collapse carries it to the corresponding target-circle section through
the actual hexagon character. Functoriality identifies the resulting
first-homology coordinates without assigning a matrix to the collapse.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual character on the indicated first-three hexagon edge. -/
def thetaEdgeCharacterMap (j : Fin 3) : C(CompactFibreTorus, _root_.Circle) :=
  ⟨hexagonCharacter (thetaEdgeIndex j),
    edgeCharacter_continuous (hexagonRay (thetaEdgeIndex j))⟩

/-- Restrict the actual collapse to the intersection of its actual cone cover. -/
def thetaBeltMap : C(ThetaBelt, Suspension.middleBand ThreeCircles) :=
  intersectionRestriction thetaCharacterCollapse thetaNorth thetaSouth
    Suspension.northOpen Suspension.southOpen
    thetaCharacterCollapse_mapsTo_north thetaCharacterCollapse_mapsTo_south

/-- On the literal midpoint section the restricted collapse is exactly its edge character. -/
theorem thetaBeltMap_comp_section (j : Fin 3) :
    thetaBeltMap.comp (thetaBeltSection j) =
      (suspensionMiddleSection ThreeCircles).comp
        ((thetaCircleMap j).comp (thetaEdgeCharacterMap j)) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change thetaCharacterCollapse (thetaBeltSection j u : CompactFibreTorus × Theta) =
    (suspensionMiddleSection ThreeCircles
      (thetaCircleMap j (thetaEdgeCharacterMap j u)) : ThreeCircleSuspension)
  rw [thetaBeltSection_coe, suspensionMiddleSection_coe, thetaCharacterCollapse_mk]
  rfl

/-- The actual induced map of an edge section occupies its corresponding circle coordinate. -/
theorem thetaBeltMap_homologyOne_section (j : Fin 3)
    (a : SingularHomology CompactFibreTorus 1) :
    thetaTargetBeltHomologyEquiv
      (singularHomologyMap thetaBeltMap 1 (singularHomologyMap (thetaBeltSection j) 1 a)) =
      Pi.single j (unitCircleHomologyOneEquiv
        (singularHomologyMap (thetaEdgeCharacterMap j) 1 a)) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, thetaBeltMap_comp_section,
    singularHomologyMap_comp, LinearMap.comp_apply,
    thetaTargetBeltHomologyEquiv_middleSection,
    singularHomologyMap_comp, LinearMap.comp_apply, thetaCircleMap_homologyOne]

/-- Adding the three actual edge-section classes gives the three actual character coordinates. -/
theorem thetaBeltMap_homologyOne_sum (v : Fin 3 → SingularHomology CompactFibreTorus 1) :
    thetaTargetBeltHomologyEquiv (singularHomologyMap thetaBeltMap 1 (thetaBeltSum v)) =
      fun j => unitCircleHomologyOneEquiv
        (singularHomologyMap (thetaEdgeCharacterMap j) 1 (v j)) := by
  simp only [thetaBeltSum, map_sum, thetaBeltMap_homologyOne_section]
  funext j
  simp

end Wikipedia.HopfProblem.CuspCentralHomology

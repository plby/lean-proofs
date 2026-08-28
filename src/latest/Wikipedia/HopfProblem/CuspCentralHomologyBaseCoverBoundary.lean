import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverBoundaryRange
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverBoundaryGeometry
import Wikipedia.HopfProblem.CuspCentralHomologyRadialCircle

/-!
# The literal base boundary is the three-edge theta graph

The actual three-edge map has exactly the suspension fibre relation,
including its two distinct endpoint poles, and its image is the
radius-one locus in the original marked product torus. Compactness
therefore gives the homeomorphism for the inherited boundary topology.
The final maps retain the original hexagonal-frontier attaching map.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

theorem thetaBaseMap_injective : Function.Injective thetaBaseMap := by
  intro x y h
  obtain ⟨⟨s, j⟩, rfl⟩ := Suspension.mk_surjective x
  obtain ⟨⟨t, k⟩, rfl⟩ := Suspension.mk_surjective y
  exact Quotient.sound ((thetaBaseCylinder_eq_iff (s, j) (t, k)).mp h)

theorem thetaBoundaryMap_injective : Function.Injective thetaBoundaryMap := by
  intro x y h
  exact thetaBaseMap_injective (congrArg Subtype.val h)

theorem thetaBaseMap_isClosedEmbedding : IsClosedEmbedding thetaBaseMap :=
  thetaBaseMap.continuous.isClosedEmbedding thetaBaseMap_injective

/-- The genuine theta graph maps homeomorphically to the literal
radius-one subspace of the actual marked base torus. -/
def thetaBoundaryHomeomorph : Theta ≃ₜ boundary :=
  (thetaBoundaryMap.continuous.isClosedEmbedding thetaBoundaryMap_injective).toIsEmbedding
    |>.toHomeomorphOfSurjective thetaBoundaryMap_surjective

@[simp] theorem thetaBoundaryHomeomorph_apply (q : Theta) :
    thetaBoundaryHomeomorph q = thetaBoundaryMap q := rfl

@[simp] theorem thetaBoundaryHomeomorph_coe (q : Theta) :
    (thetaBoundaryHomeomorph q : BaseTorus) = thetaBaseMap q := rfl

/-- The boundary-to-theta orientation is used by the actual radial
Mayer–Vietoris cover of the base torus. -/
def boundaryThetaHomeomorph : boundary ≃ₜ Theta := thetaBoundaryHomeomorph.symm

@[simp] theorem boundaryThetaHomeomorph_symm_coe (q : Theta) :
    (boundaryThetaHomeomorph.symm q : BaseTorus) = thetaBaseMap q := rfl

@[simp] theorem boundaryThetaHomeomorph_thetaBoundaryMap (q : Theta) :
    boundaryThetaHomeomorph (thetaBoundaryMap q) = q :=
  thetaBoundaryHomeomorph.symm_apply_apply q

theorem thetaBaseMap_boundaryThetaHomeomorph (q : boundary) :
    thetaBaseMap (boundaryThetaHomeomorph q) = (q : BaseTorus) :=
  congrArg Subtype.val (thetaBoundaryHomeomorph.apply_symm_apply q)

def boundaryInclusion : C(boundary, BaseTorus) := ⟨Subtype.val, continuous_subtype_val⟩

theorem boundaryInclusion_thetaBoundaryHomeomorph :
    boundaryInclusion.comp (thetaBoundaryHomeomorph : C(Theta, boundary)) =
      thetaBaseMap := rfl

/-- The original hexagonal frontier maps to its actual quotient boundary. -/
def frontierBoundaryMap : C(frontier baseCell, boundary) :=
  ⟨fun y => ⟨cellMap ⟨(y : Plane), baseCell_isClosed.frontier_subset y.2⟩,
      (cellMap_mem_boundary_iff _).mpr y.2⟩,
    (cellMap.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

@[simp] theorem frontierBoundaryMap_coe (y : frontier baseCell) :
    (frontierBoundaryMap y : BaseTorus) = baseTorusPoint (y : Plane) := rfl

theorem frontierBoundaryMap_surjective : Function.Surjective frontierBoundaryMap := by
  intro q
  obtain ⟨y, hy⟩ := cellMap_surjective (q : BaseTorus)
  have hfrontier : (y : Plane) ∈ frontier baseCell :=
    (cellMap_mem_boundary_iff y).mp (hy.symm ▸ q.2)
  exact ⟨⟨y, hfrontier⟩, Subtype.ext hy⟩

/-- The genuine attaching map, using the already constructed radial
circle coordinates on the literal hexagonal frontier. -/
def circleBoundaryMap : C(Circle, boundary) :=
  frontierBoundaryMap.comp (Radial.frontierCellCircleHomeomorph.symm :
    C(Circle, frontier baseCell))

@[simp] theorem circleBoundaryMap_coe (z : Circle) :
    (circleBoundaryMap z : BaseTorus) =
      baseTorusPoint (Radial.frontierCellCircleHomeomorph.symm z : Plane) := rfl

theorem circleBoundaryMap_surjective : Function.Surjective circleBoundaryMap :=
  frontierBoundaryMap_surjective.comp Radial.frontierCellCircleHomeomorph.symm.surjective

/-- The same actual attaching map expressed in the constructed theta coordinates. -/
def circleThetaMap : C(Circle, Theta) :=
  (boundaryThetaHomeomorph : C(boundary, Theta)).comp circleBoundaryMap

theorem thetaBaseMap_circleThetaMap :
    thetaBaseMap.comp circleThetaMap = boundaryInclusion.comp circleBoundaryMap := by
  apply ContinuousMap.ext
  intro z
  exact thetaBaseMap_boundaryThetaHomeomorph (circleBoundaryMap z)

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

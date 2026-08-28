import Wikipedia.HopfProblem.SixSphereCubeCollapseTopology
import Wikipedia.HopfProblem.SixSphereCubeInterior
import Wikipedia.HopfProblem.SixSphereCubeSphere

/-!
# The actual boundary-collapse quotient from the native six-cube to the unit sphere

The genuine compact collapse first maps the original cube to the native
one-point compactification of its boundary complement. The proved cube
interior homeomorphism and Mathlib's stereographic compactification give
the literal unit six-sphere. Exactly the original boundary is collapsed.
-/

noncomputable section

open scoped Topology unitInterval OnePoint

namespace Wikipedia.HopfProblem.SixSphereCube

/-- The one-point compactification of the original cube interior is the literal sphere. -/
def cubeInteriorSphereHomeomorph : OnePoint CubeInterior ≃ₜ StandardSphere :=
  cubeInteriorHomeomorph.onePointCongr.trans euclideanOnePointSphereHomeomorph

@[simp] theorem cubeInteriorSphereHomeomorph_infty :
    cubeInteriorSphereHomeomorph ∞ = sphereBasePoint := rfl

@[simp] theorem cubeInteriorSphereHomeomorph_symm_basePoint :
    cubeInteriorSphereHomeomorph.symm sphereBasePoint = ∞ :=
  cubeInteriorSphereHomeomorph.symm_apply_apply ∞

/-- The actual continuous quotient map on the original native six-cube. -/
def cubeSphereMap : C(Fin 6 → I, StandardSphere) :=
  (cubeInteriorSphereHomeomorph : C(OnePoint CubeInterior, StandardSphere)).comp
    (collapseMap (Cube.boundary (Fin 6)) isClosed_cubeBoundary)

@[simp] theorem cubeSphereMap_apply (u : Fin 6 → I) :
    cubeSphereMap u =
      cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) := rfl

/-- Every point of the entire original cube boundary maps to the same actual sphere point. -/
theorem cubeSphereMap_boundary (u : Fin 6 → I) (hu : u ∈ Cube.boundary (Fin 6)) :
    cubeSphereMap u = sphereBasePoint := by
  rw [cubeSphereMap_apply, collapse_of_mem _ hu, cubeInteriorSphereHomeomorph_infty]

/-- No point of the original cube interior maps to the collapsed boundary point. -/
theorem cubeSphereMap_eq_basePoint_iff (u : Fin 6 → I) :
    cubeSphereMap u = sphereBasePoint ↔ u ∈ Cube.boundary (Fin 6) := by
  change cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) =
    cubeInteriorSphereHomeomorph ∞ ↔ _
  rw [cubeInteriorSphereHomeomorph.injective.eq_iff, collapse_eq_infty_iff]

/-- These are precisely the fibers of the actual cube-boundary quotient. -/
theorem cubeSphereMap_eq_iff (u v : Fin 6 → I) :
    cubeSphereMap u = cubeSphereMap v ↔
      u = v ∨ u ∈ Cube.boundary (Fin 6) ∧ v ∈ Cube.boundary (Fin 6) := by
  change cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) =
    cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) v) ↔ _
  rw [cubeInteriorSphereHomeomorph.injective.eq_iff, collapse_eq_iff]

theorem cubeSphereMap_surjective : Function.Surjective cubeSphereMap :=
  cubeInteriorSphereHomeomorph.surjective.comp
    (collapse_surjective (Cube.boundary (Fin 6)) cubeBoundary_nonempty)

/-- The continuous surjection has the genuine quotient topology of the original sphere. -/
theorem isQuotientMap_cubeSphereMap : Topology.IsQuotientMap cubeSphereMap :=
  Topology.IsQuotientMap.of_surjective_continuous
    cubeSphereMap_surjective cubeSphereMap.continuous

/-- The actual quotient map is itself a native based six-loop in the literal standard sphere. -/
def cubeSphereLoop : GenLoop (Fin 6) StandardSphere sphereBasePoint :=
  ⟨cubeSphereMap, cubeSphereMap_boundary⟩

@[simp] theorem cubeSphereLoop_val : cubeSphereLoop.val = cubeSphereMap := rfl

end Wikipedia.HopfProblem.SixSphereCube

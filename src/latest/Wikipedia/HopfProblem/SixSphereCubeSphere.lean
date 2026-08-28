import Mathlib.Topology.Compactification.OnePoint.Sphere
import Wikipedia.HopfProblem.SphereHomologyBasic

/-!
# The native one-point compactification and the literal standard six-sphere

Mathlib's stereographic compactification is a genuine homeomorphism to
the unit sphere in real Euclidean seven-space. The distinguished sphere
point is its image of the actual point at infinity. No recognition
statement about any other space is used here.
-/

noncomputable section

open scoped OnePoint

namespace Wikipedia.HopfProblem.SixSphereCube

/-- The literal original unit six-sphere in Euclidean real seven-space. -/
abbrev StandardSphere := SphereHomology.UnitSphere 6

/-- Mathlib's genuine stereographic one-point compactification homeomorphism. -/
def euclideanOnePointSphereHomeomorph :
    OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 6)) (ι := Fin 7) (by simp)

/-- The actual sphere point to which the entire cube boundary will be collapsed. -/
def sphereBasePoint : StandardSphere :=
  euclideanOnePointSphereHomeomorph ∞

@[simp] theorem euclideanOnePointSphereHomeomorph_infty :
    euclideanOnePointSphereHomeomorph ∞ = sphereBasePoint := rfl

@[simp] theorem euclideanOnePointSphereHomeomorph_symm_basePoint :
    euclideanOnePointSphereHomeomorph.symm sphereBasePoint = ∞ :=
  euclideanOnePointSphereHomeomorph.symm_apply_apply ∞

end Wikipedia.HopfProblem.SixSphereCube

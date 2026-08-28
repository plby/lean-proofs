import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedNormalization
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedron

/-!
# Normalized tetrahedra and their actual native homotopy relation

The coherent endpoint map has a based whole one-skeleton, and its four
literal faces are exactly the normalized original faces. The geometric
tetrahedron relation therefore applies without any extra hypotheses.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The actual normalized tetrahedron, bundled with its based one-skeleton. -/
def normalizedTetrahedron (x : X) (smp : SingularSimplex X 3) : BasedTetrahedron x :=
  BasedTetrahedron.ofFaces (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

@[simp] theorem normalizedTetrahedron_face (x : X) (smp : SingularSimplex X 3)
    (i : Fin 4) :
    basedTetrahedronFace (normalizedTetrahedron x smp) i =
      normalizedTriangle x (smp.comp (simplexFace 2 i)) := by
  apply Subtype.ext
  exact normalizedTetrahedronMap_face x smp i

/-- The four normalized actual face spheres satisfy the native signed relation. -/
theorem normalizedTriangle_boundary_relation (x : X) (smp : SingularSimplex X 3) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      basedTriangleClass (normalizedTriangle x (smp.comp (simplexFace 2 i))) = 0 := by
  simpa only [normalizedTetrahedron_face] using
    basedTetrahedron_signed_relation (normalizedTetrahedron x smp)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

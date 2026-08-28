import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Normalization
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.EightSimplex

/-!
# The actual normalized eight-simplex with its based original faces

The terminal eight-simplex has its whole six-skeleton based, since
every seven-dimensional face has its entire boundary based. Its nine
faces are exactly the normalized original faces of the singular simplex.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The genuine degree-eight endpoint based on its complete geometric six-skeleton. -/
def normalizedEightSimplex (smp : SingularSimplex X 8) : BasedEightSimplex x :=
  BasedEightSimplex.ofFaces (normalizedEightSimplexMap x smp)
    (normalizedEightSimplexMap_face_boundary x smp)

@[simp] theorem normalizedEightSimplex_face (smp : SingularSimplex X 8) (i : Fin 9) :
    basedEightSimplexFace (normalizedEightSimplex x smp) i =
      normalizedSevenSimplex x (smp.comp (simplexFace 7 i)) := by
  apply Subtype.ext
  exact normalizedEightSimplexMap_face x smp i

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

import Wikipedia.HopfProblem.FifthHurewiczNormalization
import Wikipedia.HopfProblem.FifthHurewiczSixSimplex

/-!
# The actual normalized six-simplex with its based original faces

The terminal six-simplex has its whole four-skeleton based, since every
five-dimensional face has its entire boundary based. Its seven faces
are exactly the normalized original faces of the singular six-simplex.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The genuine degree-six endpoint based on its complete geometric four-skeleton. -/
def normalizedSixSimplex (smp : SingularSimplex X 6) : BasedSixSimplex x :=
  BasedSixSimplex.ofFaces (normalizedSixSimplexMap x smp)
    (normalizedSixSimplexMap_face_boundary x smp)

@[simp] theorem normalizedSixSimplex_face (smp : SingularSimplex X 6) (i : Fin 7) :
    basedSixSimplexFace (normalizedSixSimplex x smp) i =
      normalizedFiveSimplex x (smp.comp (simplexFace 5 i)) := by
  apply Subtype.ext
  exact normalizedSixSimplexMap_face x smp i

end Wikipedia.HopfProblem.FifthHurewicz

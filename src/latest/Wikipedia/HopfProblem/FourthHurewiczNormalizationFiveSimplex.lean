import Wikipedia.HopfProblem.FourthHurewiczNormalization
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexBasic

/-!
# The actual normalized five-simplex and its based four-dimensional faces

The full three-skeleton is based because every four-dimensional face has
its entire boundary based. These are the literal normalized original
faces used by the singular-chain class assignment.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The genuine degree-five endpoint with its whole geometric three-skeleton based. -/
def normalizedFiveSimplex (smp : SingularSimplex X 5) : BasedFiveSimplex x :=
  BasedFiveSimplex.ofFaces (normalizedFiveSimplexMap x smp)
    (normalizedFiveSimplexMap_face_boundary x smp)

@[simp] theorem normalizedFiveSimplex_face (smp : SingularSimplex X 5) (i : Fin 6) :
    basedFiveSimplexFace (normalizedFiveSimplex x smp) i =
      normalizedFourSimplex x (smp.comp (simplexFace 4 i)) := by
  apply Subtype.ext
  exact normalizedFiveSimplexMap_face x smp i

end Wikipedia.HopfProblem.FourthHurewicz

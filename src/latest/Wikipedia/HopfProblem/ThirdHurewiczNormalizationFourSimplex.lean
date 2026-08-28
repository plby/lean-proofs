import Wikipedia.HopfProblem.ThirdHurewiczNormalization
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexBasic

/-!
# Actual normalized four-simplices with based two-skeleton

The full geometric two-skeleton is based because the three-stage
normalization has based every boundary of every three-dimensional face.
The original faces retain their exact normalized continuous maps.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The genuine normalized four-simplex, with its whole two-skeleton based. -/
def normalizedFourSimplex (smp : SingularSimplex X 4) : BasedFourSimplex x :=
  BasedFourSimplex.ofFaces (normalizedFourSimplexMap x smp)
    (normalizedFourSimplexMap_face_boundary x smp)

@[simp] theorem normalizedFourSimplex_face (smp : SingularSimplex X 4) (i : Fin 5) :
    basedFourSimplexFace (normalizedFourSimplex x smp) i =
      normalizedThreeSimplex x (smp.comp (simplexFace 3 i)) := by
  apply Subtype.ext
  exact normalizedFourSimplexMap_face x smp i

end Wikipedia.HopfProblem.ThirdHurewicz

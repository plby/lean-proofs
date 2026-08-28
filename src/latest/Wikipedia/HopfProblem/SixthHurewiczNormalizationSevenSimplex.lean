import Wikipedia.HopfProblem.SixthHurewiczNormalization
import Wikipedia.HopfProblem.SixthHurewiczSevenSimplex

/-!
# The actual normalized seven-simplex with its based original faces

The terminal seven-simplex has its whole five-skeleton based, since
every six-dimensional face has its entire boundary based. Its eight
faces are exactly the normalized original faces of the singular simplex.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The genuine degree-seven endpoint based on its complete geometric five-skeleton. -/
def normalizedSevenSimplex (smp : SingularSimplex X 7) : BasedSevenSimplex x :=
  BasedSevenSimplex.ofFaces (normalizedSevenSimplexMap x smp)
    (normalizedSevenSimplexMap_face_boundary x smp)

@[simp] theorem normalizedSevenSimplex_face (smp : SingularSimplex X 7) (i : Fin 8) :
    basedSevenSimplexFace (normalizedSevenSimplex x smp) i =
      normalizedSixSimplex x (smp.comp (simplexFace 6 i)) := by
  apply Subtype.ext
  exact normalizedSevenSimplexMap_face x smp i

end Wikipedia.HopfProblem.SixthHurewicz

import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexComparison
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecoveryTetrahedraBasic

/-!
# The twelve original based tetrahedral restrictions of the two fillings

The restrictions are the ones used by native cube subdivision. Their
underlying maps retain both the original singular four-simplex and the
literal affine cube tetrahedron.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The first filling restricted to an actual ordered cube tetrahedron. -/
def fourSimplexTetrahedronA (τ : BasedFourSimplex x)
    (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  nativeBasedCubeTetrahedron (fourSimplexLoopA τ) (fourSimplexLoopA_internal τ) e

/-- The second filling restricted to an actual ordered cube tetrahedron. -/
def fourSimplexTetrahedronB (τ : BasedFourSimplex x)
    (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  nativeBasedCubeTetrahedron (fourSimplexLoopB τ) (fourSimplexLoopB_internal τ) e

@[simp] theorem fourSimplexTetrahedronA_apply (τ : BasedFourSimplex x)
    (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    (fourSimplexTetrahedronA τ e).val s =
      τ.val (fourSimplexFillA (Geometry.cubeTetrahedron e s)) := rfl

@[simp] theorem fourSimplexTetrahedronB_apply (τ : BasedFourSimplex x)
    (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    (fourSimplexTetrahedronB τ e).val s =
      τ.val (fourSimplexFillB (Geometry.cubeTetrahedron e s)) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz

import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientCellsSection
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientCellsBoundary
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic

/-!
# Based simplex loops on the actual permutation cells

The principal permutation cell recovers the original singular simplex
literally.  Every other cell is the constant singular simplex because the
quotient takes it into the whole based boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubeTriangulation

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Restriction of the based native loop to the principal cell is the original simplex. -/
theorem basedSimplexLoop_cubeSimplex_refl {n : ℕ} (τ : BasedSimplex n x) :
    (basedSimplexLoop τ).val.comp (cubeSimplex (Equiv.refl (Fin n))) = τ.val := by
  change (τ.val.comp (simplexQuotient n)).comp _ = _
  rw [ContinuousMap.comp_assoc, simplexQuotient_cubeSimplex_refl, ContinuousMap.comp_id]

/-- Restriction of the based native loop to any other cell is literally constant. -/
theorem basedSimplexLoop_cubeSimplex_other {n : ℕ} (τ : BasedSimplex n x)
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) :
    (basedSimplexLoop τ).val.comp (cubeSimplex e) =
      ContinuousMap.const (Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (simplexQuotient_cubeSimplex_boundary e he s)

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

import Wikipedia.NoExoticSixSphere.SmoothProjection
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# Smooth projections onto complements of actual injective operators

The Gram formula gives the orthogonal projection onto the operator's range
complement. All range, idempotence, and smoothness statements require actual
injectivity of that operator at the point in question.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.Stiefel.OperatorComplement

open GLOrthonormalization

variable {E : Type*} {N n : ℕ}

def projection (B : E → Vector n →L[ℝ] Vector N) (x : E) : Vector N →L[ℝ] Vector N :=
  1 - gramProjection (B x)

theorem projection_eq (B : E → Vector n →L[ℝ] Vector N) (x : E)
    (hi : Injective (B x)) : projection B x = (B x).rangeᗮ.starProjection := by
  rw [projection, gramProjection_eq_starProjection _ hi, Submodule.starProjection_orthogonal']

theorem range_projection (B : E → Vector n →L[ℝ] Vector N) (x : E)
    (hi : Injective (B x)) : (projection B x).range = (B x).rangeᗮ := by
  rw [projection_eq B x hi]
  exact (B x).rangeᗮ.range_starProjection

theorem idempotent_projection (B : E → Vector n →L[ℝ] Vector N) (x : E)
    (hi : Injective (B x)) : IsIdempotentElem (projection B x) := by
  rw [projection_eq B x hi]
  exact (B x).rangeᗮ.isIdempotentElem_starProjection

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffAt_projection (B : E → Vector n →L[ℝ] Vector N) (x : E)
    (hB : ContDiffAt ℝ ∞ B x) (hi : Injective (B x)) :
    ContDiffAt ℝ ∞ (projection B) x :=
  contDiffAt_const.sub
    (contMDiffAt_gramProjection (I := 𝓘(ℝ, E)) hB.contMDiffAt hi).contDiffAt

end NoExoticSixSphere.Stiefel.OperatorComplement

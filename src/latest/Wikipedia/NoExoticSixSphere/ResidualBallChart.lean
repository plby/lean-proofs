import Wikipedia.NoExoticSixSphere.ResidualLinkGeometry

/-!
# The residual linking ball retains its actual partial diffeomorphism

The scaled signed Euclidean coordinates are a genuine global linear
diffeomorphism. Composing with the residual inverse chart produces the
original ball map and retains an open chart source containing the whole ball.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne

def scaledResidualEquiv (ε : ℝ) (hε : 0 < ε) : Vector 4 ≃L[ℝ] Vector 4 :=
  WhitneyCusp.residualCoordinates.toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Vector 4) (Units.mk0 ε hε.ne'))

theorem scaledResidualEquiv_apply (ε : ℝ) (hε : 0 < ε) (z : Vector 4) :
    scaledResidualEquiv ε hε z = ε • WhitneyCusp.residualCoordinates z := rfl

variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {D : X → BlockMap E (Vector 4)}

def Data.ballChart (d : Data D) (ε : ℝ) (hε : 0 < ε) :
    PartialDiffeomorph (𝓡 4) 𝓘(ℝ, X) (Vector 4) X ∞ :=
  (scaledResidualEquiv ε hε).toDiffeomorph.toPartialDiffeomorph.trans d.coord.symm

theorem Data.ballChart_apply (d : Data D) (ε : ℝ) (hε : 0 < ε) (z : Vector 4) :
    d.ballChart ε hε z = d.ballMap ε z := rfl

theorem Data.closedBall_subset_ballChart_source (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    closedBall (0 : Vector 4) 1 ⊆ (d.ballChart ε hε).source := by
  intro z hz
  exact ⟨mem_univ _, hball (scaledVector_mem_closedBall hε hz)⟩

theorem Data.ballChart_mem_coord_source (d : Data D) {ε : ℝ} (hε : 0 < ε)
    {z : Vector 4} (hz : z ∈ (d.ballChart ε hε).source) :
    d.ballChart ε hε z ∈ d.coord.source :=
  d.coord.toOpenPartialHomeomorph.map_target hz.2

end NoExoticSixSphere.ResidualCoordinates

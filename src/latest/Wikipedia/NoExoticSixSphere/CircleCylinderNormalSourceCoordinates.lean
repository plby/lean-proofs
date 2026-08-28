import Wikipedia.NoExoticSixSphere.CircleCylinderEuclideanNormalFrame
import Wikipedia.NoExoticSixSphere.GramSchmidtIsometry

/-!
# The circle frame's actual ordered normal-source coordinates

The existing normal-coordinate map is the genuine dimension-change
isometry followed by the two retained head-coordinate splittings.
This exposes its exact ordered source columns for Gram--Schmidt.
-/

noncomputable section

namespace NoExoticSixSphere

open GLOrthonormalization

theorem cast_source_continuousLinearEquiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k l : ℕ} (h : k = l)
    (Q : Vector l ≃L[ℝ] F) :
    Eq.mpr (congrArg (fun q ↦ Vector q ≃L[ℝ] F) h) Q =
      (Stiefel.Orthonormalization.dimensionChange h).toContinuousLinearEquiv.trans Q := by
  subst l
  apply ContinuousLinearEquiv.ext
  funext v
  change Q v = Q (Stiefel.Orthonormalization.dimensionChange (rfl : k = k) v)
  congr 1

namespace CircleCylinder

def endpointNormalCoordinates (n : ℕ) : Vector (n + 1) ≃L[ℝ]
    WithLp 2 (ℝ × Vector n) :=
  (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry n
    ).symm.toContinuousLinearEquiv

def twoNormalCoordinates (n : ℕ) : Vector ((n + 1) + 1) ≃L[ℝ] NormalModel n :=
  ((Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry (n + 1)).symm.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ)
      (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry n).symm)
        ).toContinuousLinearEquiv

def normalDimensionChange {m n : ℕ} (k : ℕ) (hd : m = n + k) :
    Vector (2 + (m + 1) - (k + 1)) ≃ₗᵢ[ℝ] Vector ((n + 1) + 1) :=
  Stiefel.Orthonormalization.dimensionChange (by omega)

theorem normalCoordinates_factor {m n : ℕ} (k : ℕ) (hd : m = n + k) :
    normalCoordinates k hd =
      (normalDimensionChange k hd).toContinuousLinearEquiv.trans (twoNormalCoordinates n) := by
  unfold normalCoordinates
  exact cast_source_continuousLinearEquiv (by omega) (twoNormalCoordinates n)

theorem twoNormalCoordinates_apply (n : ℕ) (v : Vector ((n + 1) + 1)) :
    twoNormalCoordinates n v = WithLp.toLp 2 (v 0,
      endpointNormalCoordinates n (WithLp.toLp 2 (fun i : Fin (n + 1) ↦ v i.succ))) := rfl

end CircleCylinder
end NoExoticSixSphere

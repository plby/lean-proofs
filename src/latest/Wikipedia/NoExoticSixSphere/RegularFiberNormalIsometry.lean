import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# The isometry underlying the original regular-fiber normal coordinates

The original normal-coordinate equivalence is a dimension-cast ordered
Euclidean head isometry. This exposes that same isometry without changing
the original frame or its coordinates.
-/

noncomputable section

namespace NoExoticSixSphere.RegularSphereFiber

theorem normalCoordinates_cast_toContinuousLinearEquiv (d d' n : ℕ) (h : d = d')
    (Q : EuclideanSpace ℝ (Fin d') ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) :
    (Eq.mpr (congrArg (fun q ↦ EuclideanSpace ℝ (Fin q) ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) h) Q).toContinuousLinearEquiv =
    Eq.mpr (congrArg (fun q ↦ EuclideanSpace ℝ (Fin q) ≃L[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) h) Q.toContinuousLinearEquiv := by
  subst d'
  rfl

def normalCoordinatesIsometry {m n : ℕ} (k : ℕ) (hd : m = n + k) :
    EuclideanSpace ℝ (Fin (m + 1 - k)) ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) := by
  have he : m + 1 - k = n + 1 := by omega
  rw [he]
  exact (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry n).symm

theorem normalCoordinatesIsometry_toContinuousLinearEquiv {m n : ℕ}
    (k : ℕ) (hd : m = n + k) :
    (normalCoordinatesIsometry k hd).toContinuousLinearEquiv = normalCoordinates k hd := by
  unfold normalCoordinatesIsometry normalCoordinates
  exact normalCoordinates_cast_toContinuousLinearEquiv (m + 1 - k) (n + 1) n (by omega)
    (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry n).symm

end NoExoticSixSphere.RegularSphereFiber

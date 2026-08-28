import Wikipedia.NoExoticSixSphere.HilbertSchmidt
import Mathlib.Analysis.Real.Sqrt

/-!
# The operator norm is bounded by the Hilbert--Schmidt norm

Expansion in the actual Euclidean orthonormal basis and finite
Cauchy--Schwarz give the comparison without changing the operator norm or
installing an incompatible inner-product instance.
-/

namespace NoExoticSixSphere.HilbertSchmidt

open GLOrthonormalization

variable {n : ℕ}

theorem norm_apply_le_sqrt_squareNorm (A : Vector n →L[ℝ] Vector n) (x : Vector n) :
    ‖A x‖ ≤ Real.sqrt (squareNorm A) * ‖x‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he : A x = ∑ i : Fin n, inner ℝ (b i) x • A (b i) := by
    have h := congrArg A (b.sum_repr' x)
    simpa only [map_sum, map_smul] using h.symm
  calc
    ‖A x‖ = ‖∑ i : Fin n, inner ℝ (b i) x • A (b i)‖ := congrArg norm he
    _ ≤ ∑ i : Fin n, ‖inner ℝ (b i) x‖ * ‖A (b i)‖ := by
      simpa only [norm_smul] using norm_sum_le (Finset.univ : Finset (Fin n))
        (fun i ↦ inner ℝ (b i) x • A (b i))
    _ ≤ Real.sqrt (∑ i : Fin n, ‖inner ℝ (b i) x‖ ^ 2) *
        Real.sqrt (∑ i : Fin n, ‖A (b i)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (squareNorm A) * ‖x‖ := by
      rw [b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg x)]
      change ‖x‖ * Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) = _
      rw [← squareNorm_eq_sum, mul_comm]

theorem norm_le_sqrt_squareNorm (A : Vector n →L[ℝ] Vector n) :
    ‖A‖ ≤ Real.sqrt (squareNorm A) :=
  ContinuousLinearMap.opNorm_le_bound A (Real.sqrt_nonneg _) (norm_apply_le_sqrt_squareNorm A)

theorem norm_sq_le_squareNorm (A : Vector n →L[ℝ] Vector n) : ‖A‖ ^ 2 ≤ squareNorm A := by
  have h := (sq_le_sq₀ (norm_nonneg A) (Real.sqrt_nonneg (squareNorm A))).mpr
    (norm_le_sqrt_squareNorm A)
  rwa [Real.sq_sqrt (squareNorm_nonneg A)] at h

end NoExoticSixSphere.HilbertSchmidt

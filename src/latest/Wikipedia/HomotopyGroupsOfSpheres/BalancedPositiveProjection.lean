import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealClassification
import Wikipedia.HomotopyGroupsOfSpheres.FiniteSubmoduleProjection
import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Trace

/-!
# Rank-n orthogonal projections from balanced real involutions

The positive projection is `(1+J)/2`, expressed in the standard Euclidean
coordinates used by the actual Stiefel spaces. It is continuous, self-adjoint,
idempotent, and has rank exactly `n`. It determines the original involution.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open NoExoticSixSphere.GLOrthonormalization

def projectionRepresentation (n : ℕ) :
    Matrix (Index n) (Index n) ℝ ≃ₐ[ℝ] (Vector (n + n) →L[ℝ] Vector (n + n)) :=
  (Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv).trans Matrix.toEuclideanCLM.toAlgEquiv

theorem continuous_projectionRepresentation (n : ℕ) : Continuous (projectionRepresentation n) :=
  (finiteLinearMap_contDiff (projectionRepresentation n).toLinearMap).continuous

theorem projectionRepresentation_star (n : ℕ) (A : Matrix (Index n) (Index n) ℝ) :
    projectionRepresentation n (star A) = star (projectionRepresentation n A) := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (n + n))
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (star A)) =
      star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (n + n))
        (Matrix.reindex finSumFinEquiv finSumFinEquiv A))
  rw [← map_star]
  exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (n + n)))
    (Matrix.conjTranspose_reindex finSumFinEquiv finSumFinEquiv A).symm

theorem projectionRepresentation_trace (n : ℕ) (A : Matrix (Index n) (Index n) ℝ) :
    LinearMap.trace ℝ (Vector (n + n)) (projectionRepresentation n A).toLinearMap = A.trace := by
  change LinearMap.trace ℝ _ (Matrix.toEuclideanLin
    (Matrix.reindex finSumFinEquiv finSumFinEquiv A)) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  exact Matrix.trace_map (Matrix.reindexAlgEquiv ℝ ℝ
    (finSumFinEquiv : Index n ≃ Fin (n + n))) A

def positiveMatrix {n : ℕ} (J : Space n) : Matrix (Index n) (Index n) ℝ :=
  (1 / 2 : ℝ) • (1 + J.val)

theorem positiveMatrix_idempotent {n : ℕ} (J : Space n) :
    IsIdempotentElem (positiveMatrix J) := by
  change positiveMatrix J * positiveMatrix J = positiveMatrix J
  simp only [positiveMatrix, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one, square_eq]
  module

theorem positiveMatrix_transpose {n : ℕ} (J : Space n) :
    (positiveMatrix J).transpose = positiveMatrix J := by
  rw [positiveMatrix, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_one, transpose_eq]

theorem positiveMatrix_trace {n : ℕ} (J : Space n) :
    (positiveMatrix J).trace = (n : ℝ) := by
  rw [positiveMatrix, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, trace_eq_zero]
  simp only [Index, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, add_zero, smul_eq_mul]
  ring

def positiveProjection {n : ℕ} (J : Space n) : Vector (n + n) →L[ℝ] Vector (n + n) :=
  projectionRepresentation n (positiveMatrix J)

theorem continuous_positiveProjection (n : ℕ) : Continuous (positiveProjection (n := n)) := by
  have hm : Continuous (positiveMatrix (n := n)) :=
    (continuous_const.add continuous_subtype_val).const_smul (1 / 2 : ℝ)
  exact (continuous_projectionRepresentation n).comp hm

theorem positiveProjection_idempotent {n : ℕ} (J : Space n) :
    IsIdempotentElem (positiveProjection J) := by
  change projectionRepresentation n (positiveMatrix J) *
    projectionRepresentation n (positiveMatrix J) = projectionRepresentation n (positiveMatrix J)
  rw [← map_mul, positiveMatrix_idempotent J]

theorem positiveProjection_selfAdjoint {n : ℕ} (J : Space n) :
    IsSelfAdjoint (positiveProjection J) := by
  change star (projectionRepresentation n (positiveMatrix J)) =
    projectionRepresentation n (positiveMatrix J)
  rw [← projectionRepresentation_star]
  rw [RealUnitaryMatrices.star_eq_transpose, positiveMatrix_transpose]

theorem positiveProjection_trace {n : ℕ} (J : Space n) :
    LinearMap.trace ℝ (Vector (n + n)) (positiveProjection J).toLinearMap = (n : ℝ) :=
  (projectionRepresentation_trace n (positiveMatrix J)).trans (positiveMatrix_trace J)

theorem positiveProjection_rank {n : ℕ} (J : Space n) :
    Module.finrank ℝ (positiveProjection J).range = n := by
  have hi : IsIdempotentElem (positiveProjection J).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (positiveProjection_idempotent J)
  have ht := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hi).trace
  have htrace := positiveProjection_trace J
  rw [ht] at htrace
  exact_mod_cast htrace

theorem positiveProjection_injective (n : ℕ) :
    Function.Injective (positiveProjection (n := n)) := by
  intro J K h
  have hm := (projectionRepresentation n).injective h
  have he := congrArg (fun A : Matrix (Index n) (Index n) ℝ ↦ (2 : ℝ) • A) hm
  have he' : 1 + J.val = 1 + K.val := by
    simpa only [positiveMatrix, smul_smul, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),
      one_smul] using he
  exact Subtype.ext (add_left_cancel he')

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Appending a unit column orthogonal to an actual Euclidean frame -/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalFrameAppend

open GLOrthonormalization

variable {N k : ℕ}

def column (ν : Vector N) : Vector 1 →L[ℝ] Vector N :=
  EuclideanTailCoordinates.scalar.symm.toContinuousLinearMap.smulRight ν

theorem column_apply (ν : Vector N) (t : Vector 1) :
    column ν t = EuclideanTailCoordinates.scalar.symm t • ν := rfl

/-- The last coordinate is the new column; the previous columns keep their order. -/
def operator (B : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    Vector (k + 1) →L[ℝ] Vector N := OperatorSum.operator B (column ν)

theorem operator_apply (B : Vector k →L[ℝ] Vector N) (ν : Vector N)
    (w : Vector (k + 1)) : operator B ν w =
      B (EuclideanSpace.finAddEquivProd w).1 +
        EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd w).2 • ν := rfl

theorem inner_operator (B : Stiefel.Space N k) (ν : Vector N) (hν : ‖ν‖ = 1)
    (ho : ∀ v, inner ℝ ν (B.val v) = 0) (u v : Vector (k + 1)) :
    inner ℝ (operator B.val ν u) (operator B.val ν v) = inner ℝ u v := by
  have ho' (w : Vector k) : inner ℝ (B.val w) ν = 0 :=
    (real_inner_comm _ _).trans (ho w)
  have hB := (Stiefel.toIsometry B).inner_map_map
    (EuclideanSpace.finAddEquivProd u).1 (EuclideanSpace.finAddEquivProd v).1
  change inner ℝ (B.val _) (B.val _) = _ at hB
  have hs := EuclideanTailCoordinates.scalar.symm.inner_map_map
    (EuclideanSpace.finAddEquivProd u).2 (EuclideanSpace.finAddEquivProd v).2
  simp only [Real.inner_apply] at hs
  rw [mul_comm] at hs
  rw [operator_apply, operator_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ho, ho', mul_zero, add_zero, zero_add]
  rw [hB, real_inner_self_eq_norm_sq, hν]
  simpa only [one_pow, mul_one, hs] using (inner_finAdd_split u v).symm

theorem norm_operator (B : Stiefel.Space N k) (ν : Vector N) (hν : ‖ν‖ = 1)
    (ho : ∀ v, inner ℝ ν (B.val v) = 0) (w : Vector (k + 1)) :
    ‖operator B.val ν w‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_operator B ν hν ho w w

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem contMDiff_column {ν : X → Vector N} (hν : ContMDiff I (𝓡 N) ∞ ν) :
    ContMDiff I 𝓘(ℝ, Vector 1 →L[ℝ] Vector N) ∞ (fun x ↦ column (ν x)) :=
  ((ContinuousLinearMap.smulRightL ℝ (Vector 1) (Vector N)
    EuclideanTailCoordinates.scalar.symm.toContinuousLinearMap).contDiff.contMDiff).comp hν

theorem contMDiff_operator {B : X → Vector k →L[ℝ] Vector N} {ν : X → Vector N}
    (hB : ContMDiff I 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ B)
    (hν : ContMDiff I (𝓡 N) ∞ ν) :
    ContMDiff I 𝓘(ℝ, Vector (k + 1) →L[ℝ] Vector N) ∞
      (fun x ↦ operator (B x) (ν x)) :=
  ((hB.clm_comp contMDiff_const).add
    ((contMDiff_column hν).clm_comp contMDiff_const)).clm_comp contMDiff_const

end NoExoticSixSphere.OrthogonalFrameAppend

/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.StructuredAveraging

open scoped BigOperators Matrix

namespace Erdos88.GaussianQuadratic

open BooleanSlices

attribute [local instance] Classical.propDecidable

noncomputable def bucketShiftQuadraticMatrix {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  bucketProjectionMatrix P.bucket hbucket.choose *
    RobustRank.graphAdjacencyMatrix G *
      bucketProjectionMatrix P.bucket hbucket.choose

noncomputable def bucketShiftResidualMatrix {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Structured.centeredProjection
      (bucketProjectionMatrix P.bucket hbucket.choose) *
    RobustRank.graphAdjacencyMatrix G *
      bucketProjectionMatrix P.bucket hbucket.choose

noncomputable def bucketShiftVarianceMatrix {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (n : ℝ)⁻¹ * ∑ k,
    bucketShiftResidualMatrix P hbucket G k i *
      bucketShiftResidualMatrix P hbucket G k j

/-- The variance-shift matrix is the source expression
`n⁻¹ Q M (I-Q)² M Q`. -/
lemma bucketShiftVarianceMatrix_eq_source {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) :
    bucketShiftVarianceMatrix P hbucket G =
      (n : ℝ)⁻¹ •
        (bucketProjectionMatrix P.bucket hbucket.choose *
          RobustRank.graphAdjacencyMatrix G *
          (Structured.centeredProjection
            (bucketProjectionMatrix P.bucket hbucket.choose) *
           Structured.centeredProjection
            (bucketProjectionMatrix P.bucket hbucket.choose)) *
          RobustRank.graphAdjacencyMatrix G *
          bucketProjectionMatrix P.bucket hbucket.choose) := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  let C := Structured.centeredProjection Q
  let R := bucketShiftResidualMatrix P hbucket G
  have hQ : Qᵀ = Q := bucketProjectionMatrix_transpose P.bucket
  have hM : Mᵀ = M := graphAdjacencyMatrix_transpose G
  have hC : Cᵀ = C := by
    exact Structured.centeredProjection_transpose
      ⟨hQ, bucketProjectionMatrix_mul_self P.bucket hbucket⟩
  have hR : R = C * M * Q := rfl
  have hRtR : Rᵀ * R = Q * M * (C * C) * M * Q := by
    rw [hR, Matrix.transpose_mul, Matrix.transpose_mul, hQ, hM, hC]
    noncomm_ring
  ext i j
  change (n : ℝ)⁻¹ * ∑ k, R k i * R k j =
    (n : ℝ)⁻¹ * (Q * M * (C * C) * M * Q) i j
  have hentry : (∑ k, R k i * R k j) = (Rᵀ * R) i j := by
    rw [Matrix.mul_apply]
    rfl
  rw [hentry, hRtR]

/-- The linear shift `y·Qx/2` is the Rademacher linear form with
coefficient vector `Qy/2`. -/
lemma bucketShiftLinear_eq {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y x : Fin n → ℝ) :
    (1 / 2 : ℝ) *
        (y ⬝ᵥ Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose) x) =
      (1 / 2 : ℝ) * ∑ i,
        (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i * x i := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  have hQ : Qᵀ = Q := bucketProjectionMatrix_transpose P.bucket
  have hdot : y ⬝ᵥ (Q *ᵥ x) = (Q *ᵥ y) ⬝ᵥ x := by
    calc
      y ⬝ᵥ (Q *ᵥ x) = y ⬝ᵥ (Qᵀ *ᵥ x) := by rw [hQ]
      _ = x ⬝ᵥ (Q *ᵥ y) := Matrix.dotProduct_transpose_mulVec Q y x
      _ = (Q *ᵥ y) ⬝ᵥ x := dotProduct_comm _ _
  rw [Structured.delta, hdot]
  rfl

/-- The quadratic shift `ΔᵀMΔ/8` is the quadratic form of `QMQ/8`. -/
lemma bucketShiftQuadratic_eq {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) :
    (1 / 8 : ℝ) *
        (Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
          (RobustRank.graphAdjacencyMatrix G *ᵥ
            Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x)) =
      (1 / 8 : ℝ) *
        (∑ i, ∑ j, bucketShiftQuadraticMatrix P hbucket G i j * x i * x j) := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  have hQ : Qᵀ = Q := bucketProjectionMatrix_transpose P.bucket
  have hform :
      (Q *ᵥ x) ⬝ᵥ (M *ᵥ (Q *ᵥ x)) =
        x ⬝ᵥ ((Q * M * Q) *ᵥ x) := by
    calc
      (Q *ᵥ x) ⬝ᵥ (M *ᵥ (Q *ᵥ x)) =
          (M *ᵥ (Q *ᵥ x)) ⬝ᵥ (Q *ᵥ x) := dotProduct_comm _ _
      _ = x ⬝ᵥ (Qᵀ *ᵥ (M *ᵥ (Q *ᵥ x))) :=
        (Matrix.dotProduct_transpose_mulVec Q x (M *ᵥ (Q *ᵥ x))).symm
      _ = x ⬝ᵥ ((Q * M * Q) *ᵥ x) := by
        rw [hQ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [Structured.delta, hform]
  simp only [dotProduct, Matrix.mulVec, bucketShiftQuadraticMatrix, Q, M]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The variance-shift quadratic form is exactly
`‖(I-Q)MQx/4‖₂²`. -/
lemma bucketShiftVarianceQuadratic_eq {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) :
    ((n : ℝ) / 16) *
        (∑ i, ∑ j, bucketShiftVarianceMatrix P hbucket G i j * x i * x j) =
      ∑ i, ((1 / 4 : ℝ) *
        (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2 := by
  let R := bucketShiftResidualMatrix P hbucket G
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hBmat : bucketShiftVarianceMatrix P hbucket G =
      (n : ℝ)⁻¹ • (Rᵀ * R) := by
    ext i j
    rw [Matrix.smul_apply]
    change (n : ℝ)⁻¹ * ∑ k, R k i * R k j =
      (n : ℝ)⁻¹ * (Rᵀ * R) i j
    rw [Matrix.mul_apply]
    rfl
  have hsumForm :
      (∑ i, ∑ j, bucketShiftVarianceMatrix P hbucket G i j * x i * x j) =
        x ⬝ᵥ (bucketShiftVarianceMatrix P hbucket G *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdot : x ⬝ᵥ ((Rᵀ * R) *ᵥ x) =
      ∑ i, (R *ᵥ x) i ^ 2 := by
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_transpose_mulVec]
    simp only [dotProduct, pow_two]
  rw [hsumForm, hBmat, Matrix.smul_mulVec, dotProduct_smul, hdot]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  rw [show (n : ℝ) / 16 * (n : ℝ)⁻¹ = 1 / 16 by
    field_simp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [R]
  ring

lemma matrix_mul_entry_nonneg {I : Type*} [Fintype I]
    (A B : Matrix I I ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (i j : I) :
    0 ≤ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA i k) (hB k j)

lemma bucketProjectionMatrix_entry_nonneg {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket) (i j : Fin n) :
    0 ≤ bucketProjectionMatrix P.bucket hbucket.choose i j := by
  simp only [bucketProjectionMatrix]
  split <;> positivity

/-- Equal-bucket averaging preserves the total coordinate sum. -/
lemma sum_bucketProjectionMatrix_mulVec {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) :
    ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i = ∑ i, y i := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let one : Fin n → ℝ := fun _ ↦ 1
  have hone : Q *ᵥ one = one := by
    simpa only [Q, one, Structured.delta] using
      (delta_bucketConstant P hbucket (fun _ ↦ (1 : ℝ)))
  have hQ : Qᵀ = Q := bucketProjectionMatrix_transpose P.bucket
  calc
    (∑ i, (Q *ᵥ y) i) = one ⬝ᵥ (Q *ᵥ y) := by
      simp only [dotProduct, one_mul, one]
    _ = y ⬝ᵥ (Qᵀ *ᵥ one) :=
      (Matrix.dotProduct_transpose_mulVec Q y one).symm
    _ = y ⬝ᵥ one := by rw [hQ, hone]
    _ = ∑ i, y i := by simp only [dotProduct, mul_one, one]

/-- A lower bound on the total nonnegative mass gives the cubic squared-mass
bound required after bucket averaging. -/
lemma sum_sq_bucketProjectionMatrix_mulVec_lower {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hsum : A * (n : ℝ) ^ 2 ≤ ∑ i, y i) :
    A ^ 2 * (n : ℝ) ^ 3 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2 := by
  let z := bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsumz : A * (n : ℝ) ^ 2 ≤ ∑ i, z i := by
    rw [sum_bucketProjectionMatrix_mulVec P hbucket y]
    exact hsum
  have hleft0 : 0 ≤ A * (n : ℝ) ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hsumz0 : 0 ≤ ∑ i, z i := hleft0.trans hsumz
  have hsquare : (A * (n : ℝ) ^ 2) ^ 2 ≤ (∑ i, z i) ^ 2 :=
    (sq_le_sq₀ hleft0 hsumz0).2 hsumz
  have hcauchy : (∑ i, z i) ^ 2 ≤
      (n : ℝ) * ∑ i, z i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n))) (f := z))
  apply (mul_le_mul_iff_of_pos_right hnR).mp
  calc
    A ^ 2 * (n : ℝ) ^ 3 * (n : ℝ) = (A * (n : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (∑ i, z i) ^ 2 := hsquare
    _ ≤ (n : ℝ) * ∑ i, z i ^ 2 := hcauchy
    _ = (∑ i, z i ^ 2) * (n : ℝ) := by ring

/-- A nonnegative coordinatewise bound is preserved by equal-bucket
averaging. -/
lemma abs_bucketProjectionMatrix_mulVec_le_of_nonneg {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hy0 : ∀ i, 0 ≤ y i) (hyB : ∀ i, y i ≤ B) (i : Fin n) :
    |(bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i| ≤ B := by
  exact abs_bucketProjection_mulVec_le P hbucket y hB
    (fun j ↦ by rw [abs_of_nonneg (hy0 j)]; exact hyB j) i

lemma graphAdjacencyMatrix_entry_nonneg {n : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    0 ≤ RobustRank.graphAdjacencyMatrix G i j := by
  classical
  simp only [RobustRank.graphAdjacencyMatrix]
  split <;> norm_num

lemma abs_bucketShiftQuadraticMatrix_le_one {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    |bucketShiftQuadraticMatrix P hbucket G i j| ≤ 1 := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  have hM : ∀ a b, |M a b| ≤ 1 := by
    intro a b
    classical
    simp only [M, RobustRank.graphAdjacencyMatrix]
    split <;> norm_num
  have hQM : ∀ a b, |(Q * M) a b| ≤ 1 :=
    abs_bucketProjection_mul_matrix_le_one P hbucket M hM
  exact abs_matrix_mul_bucketProjection_le_one P hbucket (Q * M) hQM i j

lemma bucketShiftQuadraticMatrix_symmetric {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    bucketShiftQuadraticMatrix P hbucket G i j =
      bucketShiftQuadraticMatrix P hbucket G j i := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  have hQ : Qᵀ = Q := bucketProjectionMatrix_transpose P.bucket
  have hM : Mᵀ = M := graphAdjacencyMatrix_transpose G
  have hmat : (Q * M * Q)ᵀ = Q * M * Q := by
    simp only [Matrix.transpose_mul, hQ, hM, Matrix.mul_assoc]
  have hij := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ ↦ X j i) hmat
  simpa only [bucketShiftQuadraticMatrix, Q, M, Matrix.transpose_apply] using hij

lemma abs_bucketShiftResidualMatrix_le_one {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    |bucketShiftResidualMatrix P hbucket G i j| ≤ 1 := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  have hQnonneg : ∀ a b, 0 ≤ Q a b :=
    bucketProjectionMatrix_entry_nonneg P hbucket
  have hMnonneg : ∀ a b, 0 ≤ M a b :=
    graphAdjacencyMatrix_entry_nonneg G
  have hM : ∀ a b, |M a b| ≤ 1 := by
    intro a b
    classical
    simp only [M, RobustRank.graphAdjacencyMatrix]
    split <;> norm_num
  have hMQnonneg : ∀ a b, 0 ≤ (M * Q) a b :=
    matrix_mul_entry_nonneg M Q hMnonneg hQnonneg
  have hQMnonneg : ∀ a b, 0 ≤ (Q * M) a b :=
    matrix_mul_entry_nonneg Q M hQnonneg hMnonneg
  have hQMQnonneg : ∀ a b, 0 ≤ (Q * M * Q) a b :=
    matrix_mul_entry_nonneg (Q * M) Q hQMnonneg hQnonneg
  have hMQ : ∀ a b, |(M * Q) a b| ≤ 1 :=
    abs_matrix_mul_bucketProjection_le_one P hbucket M hM
  have hQM : ∀ a b, |(Q * M) a b| ≤ 1 :=
    abs_bucketProjection_mul_matrix_le_one P hbucket M hM
  have hQMQ : ∀ a b, |(Q * M * Q) a b| ≤ 1 :=
    abs_matrix_mul_bucketProjection_le_one P hbucket (Q * M) hQM
  have hentry : bucketShiftResidualMatrix P hbucket G i j =
      (M * Q) i j - (Q * M * Q) i j := by
    dsimp only [bucketShiftResidualMatrix, Structured.centeredProjection, Q, M]
    have hmat : (1 - Q) * M * Q = M * Q - Q * M * Q := by noncomm_ring
    rw [hmat]
    rfl
  rw [hentry]
  apply abs_le.mpr
  constructor
  · have := (abs_le.mp (hMQ i j)).2
    have := (abs_le.mp (hQMQ i j)).2
    linarith [hMQnonneg i j, hQMQnonneg i j]
  · have := (abs_le.mp (hMQ i j)).2
    have := (abs_le.mp (hQMQ i j)).2
    linarith [hMQnonneg i j, hQMQnonneg i j]

lemma abs_bucketShiftVarianceMatrix_le_one {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    |bucketShiftVarianceMatrix P hbucket G i j| ≤ 1 := by
  let R := bucketShiftResidualMatrix P hbucket G
  have hR : ∀ a b, |R a b| ≤ 1 :=
    abs_bucketShiftResidualMatrix_le_one P hbucket G
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : |∑ k : Fin n, R k i * R k j| ≤ (n : ℝ) := by
    calc
      |∑ k : Fin n, R k i * R k j| ≤
          ∑ k : Fin n, |R k i * R k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        nlinarith [abs_nonneg (R k i), abs_nonneg (R k j),
          hR k i, hR k j]
      _ = (n : ℝ) := by simp
  change |(n : ℝ)⁻¹ * ∑ k : Fin n, R k i * R k j| ≤ 1
  rw [abs_mul, abs_inv, abs_of_pos hnR]
  calc
    (n : ℝ)⁻¹ * |∑ k : Fin n, R k i * R k j| ≤
        (n : ℝ)⁻¹ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnR.le)
    _ = 1 := inv_mul_cancel₀ hnR.ne'

lemma bucketShiftVarianceMatrix_quadratic_nonneg {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, bucketShiftVarianceMatrix P hbucket G i j *
      x i * x j := by
  let R := bucketShiftResidualMatrix P hbucket G
  have hnR : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hdot :
      x ⬝ᵥ ((Rᵀ * R) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec]
    exact Matrix.dotProduct_transpose_mulVec R x (R *ᵥ x)
  have hnonneg : 0 ≤ x ⬝ᵥ ((Rᵀ * R) *ᵥ x) := by
    rw [hdot, dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hBmat : bucketShiftVarianceMatrix P hbucket G =
      (n : ℝ)⁻¹ • (Rᵀ * R) := by
    ext i j
    rw [Matrix.smul_apply]
    change (n : ℝ)⁻¹ * ∑ k, R k i * R k j =
      (n : ℝ)⁻¹ * (Rᵀ * R) i j
    rw [Matrix.mul_apply]
    rfl
  have hsumForm :
      (∑ i, ∑ j, bucketShiftVarianceMatrix P hbucket G i j * x i * x j) =
        x ⬝ᵥ (bucketShiftVarianceMatrix P hbucket G *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsumForm, hBmat, Matrix.smul_mulVec, dotProduct_smul]
  exact mul_nonneg hnR hnonneg

/-- Claim 12.2 on a source-sized fixed window, with both shift matrices
instantiated from the equal-bucket projection of an actual graph. -/
theorem bucketShiftMoment_fixedWindow_le_sourceScale {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (beta : Fin n → ℝ)
    (center scale q : ℝ) (hscale : 0 < scale)
    (hbeta : ∀ i, |beta i| ≤ Real.pi / 4)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 8 ≤ ∑ i, beta i ^ 2)
    (hqmass : q * (n : ℝ) ≤ ∑ i, beta i ^ 2) :
    Fourier.finExpectation (Fin n → Bool) (fun xi ↦
      if |scale * (∑ i, beta i * Fourier.rademacherSign (xi i)) - center| ≤
          scale then
        ((1 / 8 : ℝ) *
          (∑ i, ∑ j, bucketShiftQuadraticMatrix P hbucket G i j *
            Fourier.rademacherSign (xi i) * Fourier.rademacherSign (xi j))) ^ 2 +
        ((n : ℝ) / 16) *
          (∑ i, ∑ j, bucketShiftVarianceMatrix P hbucket G i j *
            Fourier.rademacherSign (xi i) * Fourier.rademacherSign (xi j))
      else 0) ≤
      ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hunit :=
    LinearLCDCancellation.finExpectation_shiftMoment_fixedWindow_le_sourceScale
    beta (bucketShiftQuadraticMatrix P hbucket G)
      (bucketShiftVarianceMatrix P hbucket G) center scale q hscale hbeta
      (bucketShiftQuadraticMatrix_symmetric P hbucket G)
      (abs_bucketShiftQuadraticMatrix_le_one P hbucket G)
      (abs_bucketShiftVarianceMatrix_le_one hn P hbucket G)
      (fun xi ↦ bucketShiftVarianceMatrix_quadratic_nonneg hn P hbucket G
        (fun i ↦ Fourier.rademacherSign (xi i)))
      hq hq1 hmass (by simpa only [Fintype.card_fin] using hqmass)
  simpa only [Fintype.card_fin] using hunit

/-- Claim 12.2 on one source-sized window, expressed in the paper's shift
variables.  The hypotheses are the coordinate and squared-mass conditions
on the bucket-averaged effective linear coefficient that remain to be
supplied by the RLCD decomposition. -/
theorem bucketShiftMoment_source_fixedWindow_le {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    (center scale q : ℝ) (hscale : 0 < scale)
    (hQy : ∀ i,
      |(bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i| ≤ scale)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 32 * scale ^ 2 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2)
    (hqmass : 4 * q * (n : ℝ) * scale ^ 2 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2) :
    Fourier.finExpectation (Fin n → Bool) (fun xi ↦
      let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
      if |(1 / 2 : ℝ) *
          (y ⬝ᵥ Structured.delta
            (bucketProjectionMatrix P.bucket hbucket.choose) x) - center| ≤
          scale then
        ((1 / 8 : ℝ) *
          (Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
            (RobustRank.graphAdjacencyMatrix G *ᵥ
              Structured.delta
                (bucketProjectionMatrix P.bucket hbucket.choose) x))) ^ 2 +
        ∑ i, ((1 / 4 : ℝ) *
          (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2
      else 0) ≤
      ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
        (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
        3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ) := by
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let beta : Fin n → ℝ := fun i ↦ (Q *ᵥ y) i / (2 * scale)
  have hbeta : ∀ i, |beta i| ≤ Real.pi / 4 := by
    intro i
    have hden : 0 < 2 * scale := mul_pos (by norm_num) hscale
    calc
      |beta i| = |(Q *ᵥ y) i| / (2 * scale) := by
        simp only [beta, abs_div, abs_of_pos hden]
      _ ≤ scale / (2 * scale) := div_le_div_of_nonneg_right (hQy i) hden.le
      _ = 1 / 2 := by field_simp
      _ ≤ Real.pi / 4 := by nlinarith [Real.pi_gt_three]
  have hbetaSq : (∑ i, beta i ^ 2) =
      (∑ i, (Q *ᵥ y) i ^ 2) / (4 * scale ^ 2) := by
    simp only [beta, div_pow]
    rw [← Finset.sum_div]
    congr 1
    ring
  have hmassBeta : 8 ≤ ∑ i, beta i ^ 2 := by
    rw [hbetaSq]
    apply (le_div_iff₀ (by positivity : 0 < 4 * scale ^ 2)).2
    nlinarith
  have hqmassBeta : q * (n : ℝ) ≤ ∑ i, beta i ^ 2 := by
    rw [hbetaSq]
    apply (le_div_iff₀ (by positivity : 0 < 4 * scale ^ 2)).2
    nlinarith
  have hraw := bucketShiftMoment_fixedWindow_le_sourceScale hn P hbucket G
    beta center scale q hscale hbeta hq hq1 hmassBeta hqmassBeta
  have hlinear (xi : Fin n → Bool) :
      scale * (∑ i, beta i * Fourier.rademacherSign (xi i)) =
        (1 / 2 : ℝ) *
          (y ⬝ᵥ Structured.delta Q
            (fun i ↦ Fourier.rademacherSign (xi i))) := by
    rw [bucketShiftLinear_eq P hbucket y]
    simp only [beta]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    ring
  simpa only [Q, hlinear, bucketShiftQuadratic_eq P hbucket G,
    bucketShiftVarianceQuadratic_eq hn P hbucket G] using hraw

/-- A closed interval of controlled length is covered by the consecutive
source-sized windows used in the Claim 12.2 summation. -/
lemma exists_sourceWindow_of_mem_Icc (K : ℕ) {a b scale t : ℝ}
    (hscale : 0 < scale) (hspan : b - a ≤ (2 * (K : ℝ) + 1) * scale)
    (ht : a ≤ t ∧ t ≤ b) :
    ∃ j : Fin (K + 1),
      |t - (a + 2 * (j : ℕ) * scale)| ≤ scale := by
  induction K generalizing b t with
  | zero =>
      refine ⟨⟨0, by omega⟩, ?_⟩
      norm_num at hspan ⊢
      rw [abs_le]
      constructor <;> linarith
  | succ K ih =>
      let c : ℝ := a + (2 * (K : ℝ) + 1) * scale
      by_cases htc : t ≤ c
      · obtain ⟨j, hj⟩ := ih (b := c) (t := t)
          (by dsimp only [c]; linarith) ⟨ht.1, htc⟩
        refine ⟨⟨j, by omega⟩, ?_⟩
        simpa using hj
      · refine ⟨⟨K + 1, by omega⟩, ?_⟩
        rw [abs_le]
        constructor
        · dsimp only [c] at htc
          push_cast at htc ⊢
          linarith
        · push_cast at hspan ⊢
          nlinarith [ht.2]

/-- Finite-window form of Claim 12.2.  An interval covered by `K+1`
consecutive source-sized windows incurs exactly the corresponding linear
factor. -/
theorem bucketShiftMoment_source_interval_le {n m K : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    (a b scale q : ℝ) (hscale : 0 < scale)
    (hspan : b - a ≤ (2 * (K : ℝ) + 1) * scale)
    (hQy : ∀ i,
      |(bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i| ≤ scale)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hmass : 32 * scale ^ 2 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2)
    (hqmass : 4 * q * (n : ℝ) * scale ^ 2 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2) :
    Fourier.finExpectation (Fin n → Bool) (fun xi ↦
      let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
      let E := (1 / 2 : ℝ) *
        (y ⬝ᵥ Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose) x)
      let W :=
        ((1 / 8 : ℝ) *
          (Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
            (RobustRank.graphAdjacencyMatrix G *ᵥ
              Structured.delta
                (bucketProjectionMatrix P.bucket hbucket.choose) x))) ^ 2 +
        ∑ i, ((1 / 4 : ℝ) *
          (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2
      if a ≤ E ∧ E ≤ b then W else 0) ≤
      ((K + 1 : ℕ) : ℝ) *
        (((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
          (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
          3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ)) := by
  let E : (Fin n → Bool) → ℝ := fun xi ↦
    let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
    (1 / 2 : ℝ) *
      (y ⬝ᵥ Structured.delta
        (bucketProjectionMatrix P.bucket hbucket.choose) x)
  let W : (Fin n → Bool) → ℝ := fun xi ↦
    let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
    ((1 / 8 : ℝ) *
      (Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
        (RobustRank.graphAdjacencyMatrix G *ᵥ
          Structured.delta
            (bucketProjectionMatrix P.bucket hbucket.choose) x))) ^ 2 +
    ∑ i, ((1 / 4 : ℝ) *
      (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2
  let T : Fin (K + 1) → (Fin n → Bool) → ℝ := fun j xi ↦
    if |E xi - (a + 2 * (j : ℕ) * scale)| ≤ scale then W xi else 0
  have hW (xi : Fin n → Bool) : 0 ≤ W xi := by
    dsimp only [W]
    exact add_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hT (j : Fin (K + 1)) :
      Fourier.finExpectation (Fin n → Bool) (T j) ≤
        ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
          (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
          3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    simpa only [T, E, W] using
      (bucketShiftMoment_source_fixedWindow_le hn P hbucket G y
        (a + 2 * (j : ℕ) * scale) scale q hscale hQy hq hq1 hmass hqmass)
  have hpoint (xi : Fin n → Bool) :
      (if a ≤ E xi ∧ E xi ≤ b then W xi else 0) ≤ ∑ j, T j xi := by
    by_cases hi : a ≤ E xi ∧ E xi ≤ b
    · rw [if_pos hi]
      obtain ⟨j, hj⟩ := exists_sourceWindow_of_mem_Icc K hscale hspan hi
      calc
        W xi = T j xi := by simp only [T, if_pos hj]
        _ ≤ ∑ j, T j xi := Finset.single_le_sum
          (f := fun k ↦ T k xi)
          (fun k _ ↦ by
            dsimp only [T]
            split
            · exact hW xi
            · exact le_rfl)
          (Finset.mem_univ j)
    · rw [if_neg hi]
      exact Finset.sum_nonneg fun j _ ↦ by
        dsimp only [T]
        split
        · exact hW xi
        · exact le_rfl
  have hmono := QuadraticCancellation.finExpectation_mono_real
    (Fin n → Bool) hpoint
  have hsum :
      Fourier.finExpectation (Fin n → Bool) (fun xi ↦ ∑ j, T j xi) =
        ∑ j, Fourier.finExpectation (Fin n → Bool) (T j) := by
    rw [Fourier.finExpectation]
    simp_rw [Fourier.finExpectation]
    rw [Finset.sum_comm, Finset.sum_div]
  rw [hsum] at hmono
  refine hmono.trans ?_
  calc
    (∑ j, Fourier.finExpectation (Fin n → Bool) (T j)) ≤
        ∑ _j : Fin (K + 1),
          (((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
            (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
            3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Finset.sum_le_sum fun j _ ↦ hT j
    _ = ((K + 1 : ℕ) : ℝ) *
        (((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
          (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
          3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ)) := by
      simp

/-- Claim 12.2 specialized to an actual graph effective-linear vector.
Edge density supplies the averaged cubic squared mass, while the perturbation
and degree bounds supply the source scale `(H+1)n`. -/
theorem bucketShiftMoment_graph_interval_le {n m K : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A q a b : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hqcoef : 4 * q * (H + 1) ^ 2 ≤ A ^ 2)
    (hgrowth : 32 * (H + 1) ^ 2 ≤ A ^ 2 * (n : ℝ))
    (hspan : b - a ≤ (2 * (K : ℝ) + 1) * ((H + 1) * (n : ℝ))) :
    Fourier.finExpectation (Fin n → Bool) (fun xi ↦
      let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
      let E := (1 / 2 : ℝ) *
        (GraphQuadratic.graphEffectiveLinear G c ⬝ᵥ Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose) x)
      let W :=
        ((1 / 8 : ℝ) *
          (Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
            (RobustRank.graphAdjacencyMatrix G *ᵥ
              Structured.delta
                (bucketProjectionMatrix P.bucket hbucket.choose) x))) ^ 2 +
        ∑ i, ((1 / 4 : ℝ) *
          (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2
      if a ≤ E ∧ E ≤ b then W else 0) ≤
      ((K + 1 : ℕ) : ℝ) *
        (((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
          (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
          3 * (q / 32) ^ (-(3 : ℝ) / 2)) * (n : ℝ) ^ (3 / 2 : ℝ)) := by
  let y := GraphQuadratic.graphEffectiveLinear G c
  let scale := (H + 1) * (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < scale := mul_pos (by linarith) hnR
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i
    exact add_nonneg (hc0 i) (div_nonneg (by positivity) (by norm_num))
  have hyB : ∀ i, y i ≤ scale := by
    intro i
    have hdegNat : G.degree i ≤ n :=
      Nat.le_of_lt (by simpa using G.degree_lt_card_verts i)
    have hdeg : (G.degree i : ℝ) ≤ n := by exact_mod_cast hdegNat
    dsimp only [y, scale, GraphQuadratic.graphEffectiveLinear]
    nlinarith [hcH i]
  have hQy : ∀ i,
      |(bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i| ≤ scale :=
    abs_bucketProjectionMatrix_mulVec_le_of_nonneg P hbucket y hscale.le hy0 hyB
  have hsumc : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ ↦ hc0 i
  have hsum : A * (n : ℝ) ^ 2 ≤ ∑ i, y i := by
    rw [GraphQuadratic.sum_graphEffectiveLinear]
    exact hedge.trans (by linarith)
  have hmassLower : A ^ 2 * (n : ℝ) ^ 3 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2 :=
    sum_sq_bucketProjectionMatrix_mulVec_lower hn P hbucket y hA hsum
  have hmass : 32 * scale ^ 2 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2 := by
    apply (show 32 * scale ^ 2 ≤ A ^ 2 * (n : ℝ) ^ 3 by
      dsimp only [scale]
      nlinarith [sq_nonneg (n : ℝ)]).trans hmassLower
  have hqmass : 4 * q * (n : ℝ) * scale ^ 2 ≤
      ∑ i, (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i ^ 2 := by
    apply (show 4 * q * (n : ℝ) * scale ^ 2 ≤ A ^ 2 * (n : ℝ) ^ 3 by
      dsimp only [scale]
      calc
        4 * q * (n : ℝ) * ((H + 1) * (n : ℝ)) ^ 2 =
            (4 * q * (H + 1) ^ 2) * (n : ℝ) ^ 3 := by ring
        _ ≤ A ^ 2 * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hqcoef (by positivity)).trans hmassLower
  exact bucketShiftMoment_source_interval_le hn P hbucket G y a b scale q
    hscale (by simpa only [scale] using hspan) hQy hq hq1 hmass hqmass

/-- Source-shaped Claim 12.2 for graph effective-linear coefficients.  The
interval hypothesis `d n ≤ b-a` is the form obtained from the robust-rank
lower bound on `‖M*‖_F`; the conclusion is linear in the interval length. -/
theorem bucketShiftMoment_graph_claim122 {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A q d a b : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A) (hd : 0 < d)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hqcoef : 4 * q * (H + 1) ^ 2 ≤ A ^ 2)
    (hgrowth : 32 * (H + 1) ^ 2 ≤ A ^ 2 * (n : ℝ))
    (hlength : d * (n : ℝ) ≤ b - a) :
    Fourier.finExpectation (Fin n → Bool) (fun xi ↦
      let x : Fin n → ℝ := fun i ↦ Fourier.rademacherSign (xi i)
      let E := (1 / 2 : ℝ) *
        (GraphQuadratic.graphEffectiveLinear G c ⬝ᵥ Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose) x)
      let W :=
        ((1 / 8 : ℝ) *
          (Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose) x ⬝ᵥ
            (RobustRank.graphAdjacencyMatrix G *ᵥ
              Structured.delta
                (bucketProjectionMatrix P.bucket hbucket.choose) x))) ^ 2 +
        ∑ i, ((1 / 4 : ℝ) *
          (bucketShiftResidualMatrix P hbucket G *ᵥ x) i) ^ 2
      if a ≤ E ∧ E ≤ b then W else 0) ≤
      ((1 / (2 * (H + 1)) + 2 / d) *
        ((45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
          (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
          3 * (q / 32) ^ (-(3 : ℝ) / 2))) *
        Real.sqrt n * (b - a) := by
  let scale : ℝ := (H + 1) * (n : ℝ)
  let L : ℝ := b - a
  let K : ℕ := Nat.ceil (L / (2 * scale))
  let Cq : ℝ :=
    (45 / 4 : ℝ) * (q / 32) ^ (-(5 : ℝ) / 2) +
      (1 / 8 : ℝ) * (q / 32) ^ (-(1 : ℝ) / 2) +
      3 * (q / 32) ^ (-(3 : ℝ) / 2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < H + 1 := by linarith
  have hscale : 0 < scale := mul_pos hS hnR
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hd hnR) hlength
  have hx0 : 0 ≤ L / (2 * scale) := div_nonneg hL.le (by positivity)
  have hceilLower : L / (2 * scale) ≤ (K : ℝ) := by
    exact Nat.le_ceil _
  have hspan : L ≤ (2 * (K : ℝ) + 1) * scale := by
    have hbase : L ≤ 2 * (K : ℝ) * scale := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * scale)).mp at hceilLower
      nlinarith
    nlinarith
  have hbase := bucketShiftMoment_graph_interval_le hn P hbucket G c
    H A q a b hH hA hc0 hcH hedge hq hq1 hqcoef hgrowth
    (by simpa only [scale, L] using hspan)
  have hceilUpper : (K : ℝ) < L / (2 * scale) + 1 :=
    Nat.ceil_lt_add_one hx0
  have hnDiv : (n : ℝ) ≤ L / d := by
    exact (le_div_iff₀ hd).2 (by nlinarith)
  have hcount : ((K + 1 : ℕ) : ℝ) * (n : ℝ) ≤
      (1 / (2 * (H + 1)) + 2 / d) * L := by
    calc
      ((K + 1 : ℕ) : ℝ) * (n : ℝ) ≤
          (L / (2 * scale) + 2) * (n : ℝ) := by
        push_cast
        exact mul_le_mul_of_nonneg_right (by linarith) hnR.le
      _ = L / (2 * (H + 1)) + 2 * (n : ℝ) := by
        dsimp only [scale]
        field_simp
      _ ≤ L / (2 * (H + 1)) + 2 * (L / d) := by gcongr
      _ = (1 / (2 * (H + 1)) + 2 / d) * L := by ring
  have hCq : 0 ≤ Cq := by
    dsimp only [Cq]
    positivity
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) =
      Real.sqrt n * (n : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring]
    rw [Real.rpow_add hnR]
    simp only [Real.rpow_one]
    rw [← Real.sqrt_eq_rpow]
  refine hbase.trans ?_
  change ((K + 1 : ℕ) : ℝ) * (Cq * (n : ℝ) ^ (3 / 2 : ℝ)) ≤
    ((1 / (2 * (H + 1)) + 2 / d) * Cq) * Real.sqrt n * (b - a)
  rw [hpow]
  calc
    ((K + 1 : ℕ) : ℝ) * (Cq * (Real.sqrt n * (n : ℝ))) =
        (Cq * Real.sqrt n) * (((K + 1 : ℕ) : ℝ) * (n : ℝ)) := by ring
    _ ≤ (Cq * Real.sqrt n) *
        ((1 / (2 * (H + 1)) + 2 / d) * L) :=
      mul_le_mul_of_nonneg_left hcount (mul_nonneg hCq hsqrt)
    _ = ((1 / (2 * (H + 1)) + 2 / d) * Cq) *
        Real.sqrt n * (b - a) := by dsimp only [L]; ring

end Erdos88.GaussianQuadratic

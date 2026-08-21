import ErdosProblems.Erdos88.GaussianDiagonalization
import ErdosProblems.Erdos88.RobustRank101
import ErdosProblems.Erdos88.Structured

/-!
# Robust block rank to Gaussian spectral rank

This module supplies the exact bridge used in KSSS Claim 12.1.  Lemma 10.1
controls distance from the graph adjacency matrix to every matrix of bounded
rank on each bucket rectangle.  Subtracting one fixed low-block-rank matrix
therefore leaves a matrix with genuine global robust rank.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Erdos88.GaussianQuadratic

open Erdos88.RobustRank

/-- Matrix rank is subadditive over `ℝ`. -/
lemma matrix_rank_add_le {m n : Type*} [Fintype n]
    (A B : Matrix m n ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by ext; simp
  rw [h]
  exact (Submodule.finrank_mono
    (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Adding a globally rank-`r` matrix to a matrix of block rank at most `q`
produces block rank at most `q+r`. -/
lemma blockRankAtMost_add_of_rank {n m q r : ℕ}
    (bucket : Fin n → Fin m) (B A : Matrix (Fin n) (Fin n) ℝ)
    (hB : BlockRankAtMost q bucket B) (hA : A.rank ≤ r) :
    BlockRankAtMost (q + r) bucket (B + A) := by
  intro j k
  calc
    (bucketBlock bucket (B + A) j k).rank =
        (bucketBlock bucket B j k + bucketBlock bucket A j k).rank := by
      rfl
    _ ≤ (bucketBlock bucket B j k).rank +
        (bucketBlock bucket A j k).rank := matrix_rank_add_le _ _
    _ ≤ q + r := Nat.add_le_add (hB j k)
      ((Matrix.rank_submatrix_le A Subtype.val Subtype.val).trans hA)

private lemma boolean_frobeniusSq_eq_robustRank_frobeniusSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    BooleanSlices.frobeniusSq A = frobeniusSq A := by
  rfl

/-- A blockwise Frobenius-distance estimate for the original adjacency
matrix becomes global robust rank after subtracting a fixed low-block-rank
approximant. -/
theorem robustRankAt_graphAdjacency_sub_of_blockRank_lower
    {n m q r : ℕ} {c : ℝ} (bucket : Fin n → Fin m)
    (G : SimpleGraph (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : BlockRankAtMost q bucket B)
    (hlower : ∀ D : Matrix (Fin n) (Fin n) ℝ,
      BlockRankAtMost (q + r) bucket D →
        c ≤ frobeniusSq (graphAdjacencyMatrix G - D)) :
    RobustRankAt r c (graphAdjacencyMatrix G - B) := by
  intro A hArank
  have hblock : BlockRankAtMost (q + r) bucket (B + A) :=
    blockRankAtMost_add_of_rank bucket B A hB hArank
  have h := hlower (B + A) hblock
  rw [frobenius_norm_sq_eq_frobeniusSq,
    boolean_frobeniusSq_eq_robustRank_frobeniusSq]
  convert h using 1
  congr 1
  abel

/-- Unconditional eventual form of the preceding bridge, obtained from
KSSS Lemma 10.1. -/
theorem exists_eventual_robustRankAt_graphAdjacency_sub_of_blockRank
    (C delta : ℝ) (q r : ℕ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta1 : delta < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n))
        (B : Matrix (Fin n) (Fin n) ℝ),
        0 < m →
        Real.rpow (n : ℝ) delta / 2 ≤ (m : ℝ) →
        (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) delta →
        HasEqualBuckets bucket → RamseyFree C G →
        BlockRankAtMost q bucket B →
          RobustRankAt r (c * (n : ℝ) ^ 2)
            (graphAdjacencyMatrix G - B) := by
  obtain ⟨c, hc, N, hN⟩ :=
    ksssLemma101 C delta (q + r) hC hdelta hdelta1
  refine ⟨c, hc, N, ?_⟩
  intro n hn m bucket G B hm hmLower hmUpper hbucket hG hB
  apply robustRankAt_graphAdjacency_sub_of_blockRank_lower
    bucket G B hB
  intro D hD
  exact hN n hn m bucket G D hm hmLower hmUpper hbucket hG hD

/-- The matrix averaging coordinates inside each equal bucket. -/
noncomputable def bucketProjectionMatrix {n m : ℕ}
    (bucket : Fin n → Fin m) (s : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if bucket i = bucket j then (s : ℝ)⁻¹ else 0

lemma bucketProjectionMatrix_col_eq {n m s : ℕ}
    (bucket : Fin n → Fin m) {j k : Fin n} (hjk : bucket j = bucket k)
    (i : Fin n) :
    bucketProjectionMatrix bucket s i j = bucketProjectionMatrix bucket s i k := by
  simp only [bucketProjectionMatrix]
  rw [hjk]

lemma bucketProjectionMatrix_row_eq {n m s : ℕ}
    (bucket : Fin n → Fin m) {i k : Fin n} (hik : bucket i = bucket k)
    (j : Fin n) :
    bucketProjectionMatrix bucket s i j = bucketProjectionMatrix bucket s k j := by
  simp only [bucketProjectionMatrix]
  rw [hik]

lemma mul_bucketProjectionMatrix_col_eq {n m s : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    {j k : Fin n} (hjk : bucket j = bucket k) (i : Fin n) :
    (M * bucketProjectionMatrix bucket s) i j =
      (M * bucketProjectionMatrix bucket s) i k := by
  classical
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [bucketProjectionMatrix_col_eq bucket hjk]

lemma bucketProjectionMatrix_mul_row_eq {n m s : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    {i k : Fin n} (hik : bucket i = bucket k) (j : Fin n) :
    (bucketProjectionMatrix bucket s * M) i j =
      (bucketProjectionMatrix bucket s * M) k j := by
  classical
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [bucketProjectionMatrix_row_eq bucket hik]

lemma bucketProjectionMatrix_mul_mul_row_eq {n m s : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    {i k : Fin n} (hik : bucket i = bucket k) (j : Fin n) :
    (bucketProjectionMatrix bucket s * M * bucketProjectionMatrix bucket s) i j =
      (bucketProjectionMatrix bucket s * M * bucketProjectionMatrix bucket s) k j := by
  classical
  have hrow : (bucketProjectionMatrix bucket s * M) i =
      (bucketProjectionMatrix bucket s * M) k := by
    funext x
    exact bucketProjectionMatrix_mul_row_eq bucket M hik x
  calc
    (bucketProjectionMatrix bucket s * M * bucketProjectionMatrix bucket s) i j =
        ∑ x, (bucketProjectionMatrix bucket s * M) i x *
          bucketProjectionMatrix bucket s x j := rfl
    _ = ∑ x, (bucketProjectionMatrix bucket s * M) k x *
          bucketProjectionMatrix bucket s x j := by rw [hrow]
    _ = (bucketProjectionMatrix bucket s * M *
          bucketProjectionMatrix bucket s) k j := rfl

lemma bucketProjectionMatrix_mul_mul_col_eq {n m s : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    {j k : Fin n} (hjk : bucket j = bucket k) (i : Fin n) :
    (bucketProjectionMatrix bucket s * M * bucketProjectionMatrix bucket s) i j =
      (bucketProjectionMatrix bucket s * M * bucketProjectionMatrix bucket s) i k := by
  exact mul_bucketProjectionMatrix_col_eq bucket
    (bucketProjectionMatrix bucket s * M) hjk i

/-- The low-block-rank part `MQ + QM - QMQ` removed by bucket centering. -/
noncomputable def bucketLowRankPart {n m : ℕ}
    (bucket : Fin n → Fin m) (s : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let Q := bucketProjectionMatrix bucket s
  M * Q + Q * M - Q * M * Q

/-- The matrix `MQ + QM - QMQ` has rank at most three on every bucket
rectangle. -/
theorem blockRankAtMost_bucketLowRankPart {n m : ℕ}
    (bucket : Fin n → Fin m) (M : Matrix (Fin n) (Fin n) ℝ)
    (hbucket : HasEqualBuckets bucket) :
    BlockRankAtMost 3 bucket
      (bucketLowRankPart bucket hbucket.choose M) := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hcard : ∀ a, (bucketFiber bucket a).card = s :=
    hbucket.choose_spec.2
  let Q := bucketProjectionMatrix bucket s
  intro a b
  have hnonempty (k : Fin m) : (bucketFiber bucket k).Nonempty := by
    exact Finset.card_pos.mp (by rw [hcard]; exact hs)
  let ra : bucketFiber bucket a :=
    ⟨(hnonempty a).choose, (hnonempty a).choose_spec⟩
  let rb : bucketFiber bucket b :=
    ⟨(hnonempty b).choose, (hnonempty b).choose_spec⟩
  let L : Matrix (bucketFiber bucket a) (Fin 3) ℝ := fun i t ↦
    if t = 0 then (M * Q) i.1 rb.1 else 1
  let R : Matrix (Fin 3) (bucketFiber bucket b) ℝ := fun t j ↦
    if t = 0 then 1 else if t = 1 then (Q * M) ra.1 j.1
      else -(Q * M * Q) ra.1 rb.1
  have sum_fin_three (f : Fin 3 → ℝ) :
      ∑ t, f t = f 0 + f 1 + f 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp
    ring
  have hfac : bucketBlock bucket (bucketLowRankPart bucket s M) a b = L * R := by
    ext i j
    have hi : bucket i.1 = bucket ra.1 := by
      have hii := (mem_bucketFiber bucket a i.1).mp i.property
      have hra := (mem_bucketFiber bucket a ra.1).mp ra.property
      exact hii.trans hra.symm
    have hj : bucket j.1 = bucket rb.1 := by
      have hjj := (mem_bucketFiber bucket b j.1).mp j.property
      have hrb := (mem_bucketFiber bucket b rb.1).mp rb.property
      exact hjj.trans hrb.symm
    have hMQ := mul_bucketProjectionMatrix_col_eq (s := s) bucket M hj i.1
    have hQM := bucketProjectionMatrix_mul_row_eq (s := s) bucket M hi j.1
    have hQMQ : (Q * M * Q) i.1 j.1 = (Q * M * Q) ra.1 rb.1 :=
      (bucketProjectionMatrix_mul_mul_row_eq (s := s) bucket M hi j.1).trans
        (bucketProjectionMatrix_mul_mul_col_eq (s := s) bucket M hj ra.1)
    change (M * Q) i.1 j.1 + (Q * M) i.1 j.1 - (Q * M * Q) i.1 j.1 =
      (L * R) i j
    rw [hMQ, hQM, hQMQ]
    change (M * Q) i.1 rb.1 + (Q * M) ra.1 j.1 - (Q * M * Q) ra.1 rb.1 =
      ∑ t : Fin 3, L i t * R t j
    rw [sum_fin_three]
    simp [L, R]
    ring
  rw [hfac]
  exact (Matrix.rank_mul_le_left L R).trans
    (by simpa using Matrix.rank_le_card_width L)

/-- Lemma 10.1 gives robust rank for the bucket-centered adjacency residual
`M - (MQ + QM - QMQ)`. -/
theorem exists_eventual_robustRankAt_bucketCenteredAdjacency
    (C delta : ℝ) (r : ℕ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta1 : delta < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n)),
        0 < m →
        Real.rpow (n : ℝ) delta / 2 ≤ (m : ℝ) →
        (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) delta →
        ∀ hbucket : HasEqualBuckets bucket, RamseyFree C G →
          RobustRankAt r (c * (n : ℝ) ^ 2)
            (graphAdjacencyMatrix G -
              bucketLowRankPart bucket hbucket.choose
                (graphAdjacencyMatrix G)) := by
  obtain ⟨c, hc, N, hN⟩ :=
    exists_eventual_robustRankAt_graphAdjacency_sub_of_blockRank
      C delta 3 r hC hdelta hdelta1
  refine ⟨c, hc, N, ?_⟩
  intro n hn m bucket G hm hmLower hmUpper hbucket hG
  exact hN n hn m bucket G
    (bucketLowRankPart bucket hbucket.choose (graphAdjacencyMatrix G))
    hm hmLower hmUpper hbucket hG
    (blockRankAtMost_bucketLowRankPart bucket (graphAdjacencyMatrix G) hbucket)

/-- Scaling a robust-rank matrix by `1/8` scales its squared-distance
threshold by `1/64`. -/
theorem robustRankAt_one_eighth_smul {n r : ℕ} {s : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hrob : RobustRankAt r s A) :
    RobustRankAt r (s / 64) ((1 / 8 : ℝ) • A) := by
  intro B hBrank
  have hRank : ((8 : ℝ) • B).rank ≤ r := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors B (by norm_num)]
    exact hBrank
  have h := hrob ((8 : ℝ) • B) hRank
  have hmat : A - (8 : ℝ) • B =
      (8 : ℝ) • ((1 / 8 : ℝ) • A - B) := by
    module
  rw [hmat, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)] at h
  nlinarith [sq_nonneg ‖(1 / 8 : ℝ) • A - B‖]

/-- The centered quadratic matrix `M* = (1/8)(M-(MQ+QM-QMQ))` from
KSSS Section 12, written on the original finite vertex type. -/
noncomputable def bucketCenteredAdjacency {n m : ℕ}
    (bucket : Fin n → Fin m) (s : ℕ) (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 8 : ℝ) •
    (graphAdjacencyMatrix G -
      bucketLowRankPart bucket s (graphAdjacencyMatrix G))

lemma bucketProjectionMatrix_transpose {n m s : ℕ}
    (bucket : Fin n → Fin m) :
    (bucketProjectionMatrix bucket s)ᵀ = bucketProjectionMatrix bucket s := by
  ext i j
  simp only [Matrix.transpose_apply, bucketProjectionMatrix]
  by_cases h : bucket i = bucket j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Equal bucket sizes make the concrete bucket-averaging matrix
idempotent. -/
lemma bucketProjectionMatrix_mul_self {n m : ℕ}
    (bucket : Fin n → Fin m) (hbucket : HasEqualBuckets bucket) :
    bucketProjectionMatrix bucket hbucket.choose *
        bucketProjectionMatrix bucket hbucket.choose =
      bucketProjectionMatrix bucket hbucket.choose := by
  classical
  let s := hbucket.choose
  have hs : 0 < s := hbucket.choose_spec.1
  have hcard : ∀ a, (bucketFiber bucket a).card = s :=
    hbucket.choose_spec.2
  ext i j
  simp only [Matrix.mul_apply, bucketProjectionMatrix]
  change (∑ x : Fin n,
      (if bucket i = bucket x then (s : ℝ)⁻¹ else 0) *
        if bucket x = bucket j then (s : ℝ)⁻¹ else 0) =
    if bucket i = bucket j then (s : ℝ)⁻¹ else 0
  by_cases hij : bucket i = bucket j
  · rw [if_pos hij]
    have hsum :
        (∑ x : Fin n,
          (if bucket i = bucket x then (s : ℝ)⁻¹ else 0) *
            if bucket x = bucket j then (s : ℝ)⁻¹ else 0) =
          ∑ x ∈ bucketFiber bucket (bucket i),
            (s : ℝ)⁻¹ * (s : ℝ)⁻¹ := by
      rw [bucketFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hix : bucket i = bucket x
      · rw [if_pos hix, if_pos (hix.symm.trans hij)]
        simp only [hix.symm, if_pos]
      · have hxi : bucket x ≠ bucket i := fun h ↦ hix h.symm
        rw [if_neg hix, if_neg hxi]
        simp
    rw [hsum, Finset.sum_const, nsmul_eq_mul, hcard]
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro x _hx
    by_cases hix : bucket i = bucket x
    · have hxj : bucket x ≠ bucket j := fun h ↦ hij (hix.trans h)
      rw [if_pos hix, if_neg hxj, mul_zero]
    · rw [if_neg hix, zero_mul]

/-- The concrete averaging matrix satisfies the abstract projection
interface used by the deterministic structured decomposition. -/
lemma bucketProjectionMatrix_isOrthogonalProjection {n m : ℕ}
    (bucket : Fin n → Fin m) (hbucket : HasEqualBuckets bucket) :
    Erdos88.Structured.IsOrthogonalProjection
      (bucketProjectionMatrix bucket hbucket.choose) :=
  ⟨bucketProjectionMatrix_transpose bucket,
    bucketProjectionMatrix_mul_self bucket hbucket⟩

lemma graphAdjacencyMatrix_transpose {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphAdjacencyMatrix G)ᵀ = graphAdjacencyMatrix G := by
  ext i j
  classical
  simp only [Matrix.transpose_apply, graphAdjacencyMatrix]
  by_cases h : G.Adj i j
  · rw [if_pos h, if_pos (G.adj_symm h)]
  · have h' : ¬G.Adj j i := fun hji ↦ h (G.adj_symm hji)
    rw [if_neg h, if_neg h']

/-- Expanding the bucket-centered sandwich gives exactly the adjacency
residual used above. -/
lemma graphAdjacency_sub_bucketLowRankPart_eq_centered {n m : ℕ}
    (bucket : Fin n → Fin m) (s : ℕ) (G : SimpleGraph (Fin n)) :
    graphAdjacencyMatrix G -
        bucketLowRankPart bucket s (graphAdjacencyMatrix G) =
      (1 - bucketProjectionMatrix bucket s) * graphAdjacencyMatrix G *
        (1 - bucketProjectionMatrix bucket s) := by
  unfold bucketLowRankPart
  noncomm_ring

/-- The centered adjacency matrix is real Hermitian, so its robust rank may
be transported to its eigenvalue diagonal. -/
theorem bucketCenteredAdjacency_isHermitian {n m : ℕ}
    (bucket : Fin n → Fin m) (s : ℕ) (G : SimpleGraph (Fin n)) :
    (bucketCenteredAdjacency bucket s G).IsHermitian := by
  let Q := bucketProjectionMatrix bucket s
  let M := graphAdjacencyMatrix G
  have hQ : Qᵀ = Q := bucketProjectionMatrix_transpose bucket
  have hM : Mᵀ = M := graphAdjacencyMatrix_transpose G
  have hcenter : bucketCenteredAdjacency bucket s G =
      (1 / 8 : ℝ) • ((1 - Q) * M * (1 - Q)) := by
    rw [bucketCenteredAdjacency,
      graphAdjacency_sub_bucketLowRankPart_eq_centered]
  rw [hcenter]
  apply Matrix.IsHermitian.smul
  · unfold Matrix.IsHermitian
    have hreal (A : Matrix (Fin n) (Fin n) ℝ) : A.conjTranspose = Aᵀ := by
      ext i j
      simp [Matrix.conjTranspose]
    rw [hreal]
    simp [Matrix.transpose_mul, hQ, hM, Matrix.mul_assoc]
  · simp

/-- The graph matrix controlled by Lemma 10.1 is definitionally the
`M* = (1/8)(I-Q)M(I-Q)` in the structured decomposition. -/
lemma bucketCenteredAdjacency_eq_mStar {n m : ℕ}
    (bucket : Fin n → Fin m) (s : ℕ) (G : SimpleGraph (Fin n)) :
    bucketCenteredAdjacency bucket s G =
      Erdos88.Structured.mStar (bucketProjectionMatrix bucket s)
        (graphAdjacencyMatrix G) := by
  rw [bucketCenteredAdjacency,
    graphAdjacency_sub_bucketLowRankPart_eq_centered]
  rfl

/-- Equation (12.3) for an actual graph bucket partition, with its quadratic
term written as the same centered adjacency matrix controlled by Lemma 10.1. -/
theorem graph_structured_decomposition {n m : ℕ}
    (bucket : Fin n → Fin m) (hbucket : HasEqualBuckets bucket)
    (G : SimpleGraph (Fin n)) (E : ℝ) (y x : Fin n → ℝ) :
    Erdos88.Structured.structuredQuadratic E (graphAdjacencyMatrix G) y x =
      Erdos88.Structured.conditionalShift E (graphAdjacencyMatrix G) y
          (Erdos88.Structured.delta
            (bucketProjectionMatrix bucket hbucket.choose) x) +
        Erdos88.Structured.wStar
            (bucketProjectionMatrix bucket hbucket.choose)
            (graphAdjacencyMatrix G) y
            (Erdos88.Structured.delta
              (bucketProjectionMatrix bucket hbucket.choose) x) ⬝ᵥ x +
          x ⬝ᵥ (bucketCenteredAdjacency bucket hbucket.choose G *ᵥ x) := by
  have h := Erdos88.Structured.structured_decomposition
    (bucketProjectionMatrix bucket hbucket.choose)
    (graphAdjacencyMatrix G)
    (bucketProjectionMatrix_isOrthogonalProjection bucket hbucket)
    (graphAdjacencyMatrix_transpose G) E y x
  rw [bucketCenteredAdjacency_eq_mStar]
  exact h

/-- The centered adjacency quadratic matrix kills the bucket-average
component, as required in the conditional decomposition. -/
lemma bucketCenteredAdjacency_delta_eq_zero {n m : ℕ}
    (bucket : Fin n → Fin m) (hbucket : HasEqualBuckets bucket)
    (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) :
    bucketCenteredAdjacency bucket hbucket.choose G *ᵥ
        Erdos88.Structured.delta
          (bucketProjectionMatrix bucket hbucket.choose) x = 0 := by
  rw [bucketCenteredAdjacency_eq_mStar]
  exact Erdos88.Structured.mStar_delta_eq_zero
    (bucketProjectionMatrix bucket hbucket.choose)
    (graphAdjacencyMatrix G)
    (bucketProjectionMatrix_isOrthogonalProjection bucket hbucket) x

/-- The centered linear coefficient in (12.3) has zero bucket-average
component. -/
lemma bucket_wStar_delta_eq_zero {n m : ℕ}
    (bucket : Fin n → Fin m) (hbucket : HasEqualBuckets bucket)
    (G : SimpleGraph (Fin n)) (y d : Fin n → ℝ) :
    bucketProjectionMatrix bucket hbucket.choose *ᵥ
        Erdos88.Structured.wStar
          (bucketProjectionMatrix bucket hbucket.choose)
          (graphAdjacencyMatrix G) y d = 0 := by
  exact Erdos88.Structured.delta_wStar_eq_zero
    (bucketProjectionMatrix bucket hbucket.choose)
    (graphAdjacencyMatrix G)
    (bucketProjectionMatrix_isOrthogonalProjection bucket hbucket) y d

/-- Unconditional robust rank for the actual centered quadratic matrix
`M*`, with the factor `1/64` absorbed into the positive constant. -/
theorem exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
    (C delta : ℝ) (r : ℕ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta1 : delta < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n)),
        0 < m →
        Real.rpow (n : ℝ) delta / 2 ≤ (m : ℝ) →
        (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) delta →
        ∀ hbucket : HasEqualBuckets bucket, RamseyFree C G →
          RobustRankAt r (c * (n : ℝ) ^ 2)
            (bucketCenteredAdjacency bucket hbucket.choose G) := by
  obtain ⟨c₀, hc₀, N, hN⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency
      C delta r hC hdelta hdelta1
  let c := c₀ / 64
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨c, hc, N, ?_⟩
  intro n hn m bucket G hm hmLower hmUpper hbucket hG
  have hraw := hN n hn m bucket G hm hmLower hmUpper hbucket hG
  have hscaled := robustRankAt_one_eighth_smul hraw
  simpa only [bucketCenteredAdjacency, c, div_mul_eq_mul_div] using hscaled

/-- For every sufficiently large Ramsey-free graph with equal buckets at
scale `n^delta`, the actual centered adjacency quadratic form has a
continuous normalized Gaussian density.  The displayed estimate is the
four-spectral-block density comparison obtained from Lemma 10.1. -/
theorem exists_eventual_continuousDensity_bucketCenteredAdjacency
    (C delta : ℝ) (r : ℕ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdelta1 : delta < 1) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n)),
        0 < m →
        Real.rpow (n : ℝ) delta / 2 ≤ (m : ℝ) →
        (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) delta →
        ∀ hbucket : HasEqualBuckets bucket, RamseyFree C G →
        ∀ (f : Fin n → ℝ) (sigma : ℝ), 0 < sigma →
          sigma ^ 2 =
            2 * Erdos88.BooleanSlices.frobeniusSq
              (bucketCenteredAdjacency bucket hbucket.choose G) +
              Erdos88.BooleanSlices.vectorSqNorm f →
          ∃ p : ℝ → ℝ,
            Erdos88.Esseen.HasContinuousDensity
                ((gaussianQuadraticCenteredLaw f
                  (bucketCenteredAdjacency bucket hbucket.choose G)).map
                    (fun x ↦ x / sigma)) p ∧
              ∀ u : ℝ,
                |p u - standardNormalDensity u| ≤
                  (2 * Real.pi)⁻¹ *
                    (1280 /
                        lyapunovGamma
                          (fun i ↦ eigenLinearCoefficient
                            (bucketCenteredAdjacency_isHermitian
                              bucket hbucket.choose G) f i / sigma)
                          (fun i ↦ (bucketCenteredAdjacency_isHermitian
                            bucket hbucket.choose G).eigenvalues i / sigma) +
                      16 /
                        (((c * (n : ℝ) ^ 2) / (8 * sigma ^ 2)) *
                          lyapunovGamma
                            (fun i ↦ eigenLinearCoefficient
                              (bucketCenteredAdjacency_isHermitian
                                bucket hbucket.choose G) f i / sigma)
                            (fun i ↦ (bucketCenteredAdjacency_isHermitian
                              bucket hbucket.choose G).eigenvalues i / sigma))) := by
  obtain ⟨c, hc, N, hN⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta r hC hdelta hdelta1
  refine ⟨c, hc, max N 1, ?_⟩
  intro n hn m bucket G hm hmLower hmUpper hbucket hG f sigma hsigma hsigmaSq
  let hF := bucketCenteredAdjacency_isHermitian bucket hbucket.choose G
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hrob := hN n hnN m bucket G hm hmLower hmUpper hbucket hG
  exact exists_continuousDensity_gaussianQuadratic_normalized_of_robustRankAt
    f hF hsigma hsigmaSq hrob hr (mul_pos hc (sq_pos_of_pos hnpos))

end Erdos88.GaussianQuadratic

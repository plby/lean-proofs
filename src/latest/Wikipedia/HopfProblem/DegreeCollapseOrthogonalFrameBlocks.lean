import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-! # Exact orthogonal blocks of actual Euclidean frames -/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.OrthogonalFrameBlocks

open NoExoticSixSphere GLOrthonormalization

variable {N n k : ℕ}

def leftInclusion (n k : ℕ) : Vector n →L[ℝ] Vector (n + k) :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Vector n) (Vector k))

def rightInclusion (n k : ℕ) : Vector k →L[ℝ] Vector (n + k) :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (Vector n) (Vector k))

theorem inner_left (u v : Vector n) :
    inner ℝ (leftInclusion n k u) (leftInclusion n k v) = inner ℝ u v := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm (u, (0 : Vector k)))
    (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector k))) = _
  simp only [inner_finAdd_symm, inner_zero_left, add_zero]

theorem inner_right (u v : Vector k) :
    inner ℝ (rightInclusion n k u) (rightInclusion n k v) = inner ℝ u v := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm ((0 : Vector n), u))
    (EuclideanSpace.finAddEquivProd.symm ((0 : Vector n), v)) = _
  simp only [inner_finAdd_symm, inner_zero_left, zero_add]

theorem inner_left_right (u : Vector n) (v : Vector k) :
    inner ℝ (leftInclusion n k u) (rightInclusion n k v) = 0 := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm (u, (0 : Vector k)))
    (EuclideanSpace.finAddEquivProd.symm ((0 : Vector n), v)) = _
  simp only [inner_finAdd_symm, inner_zero_left, inner_zero_right, add_zero]

theorem norm_left (u : Vector n) : ‖leftInclusion n k u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_left (k := k) u u

theorem norm_right (u : Vector k) : ‖rightInclusion n k u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_right (n := n) u u

def left (B : Vector (n + k) →L[ℝ] Vector N) : Vector n →L[ℝ] Vector N :=
  B.comp (leftInclusion n k)

def right (B : Vector (n + k) →L[ℝ] Vector N) : Vector k →L[ℝ] Vector N :=
  B.comp (rightInclusion n k)

theorem left_operator (C : Vector n →L[ℝ] Vector N) (T : Vector k →L[ℝ] Vector N) :
    left (OperatorSum.operator C T) = C := by
  apply ContinuousLinearMap.ext
  intro u
  change OperatorSum.operator C T (EuclideanSpace.finAddEquivProd.symm (u, 0)) = C u
  rw [OperatorSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

theorem right_operator (C : Vector n →L[ℝ] Vector N) (T : Vector k →L[ℝ] Vector N) :
    right (OperatorSum.operator C T) = T := by
  apply ContinuousLinearMap.ext
  intro u
  change OperatorSum.operator C T (EuclideanSpace.finAddEquivProd.symm (0, u)) = T u
  rw [OperatorSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

theorem norm_operator (C : Vector n →L[ℝ] Vector N) (T : Vector k →L[ℝ] Vector N)
    (hC : ∀ u, ‖C u‖ = ‖u‖) (hT : ∀ v, ‖T v‖ = ‖v‖)
    (ho : C.range ≤ T.rangeᗮ) (w : Vector (n + k)) :
    ‖OperatorSum.operator C T w‖ = ‖w‖ := by
  let c : Vector n →ₗᵢ[ℝ] Vector N := ⟨C.toLinearMap, hC⟩
  let t : Vector k →ₗᵢ[ℝ] Vector N := ⟨T.toLinearMap, hT⟩
  have htc (u : Vector k) (v : Vector n) : inner ℝ (T u) (C v) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (show T u ∈ T.range from ⟨u, rfl⟩) (ho ⟨v, rfl⟩)
  have hct (u : Vector n) (v : Vector k) : inner ℝ (C u) (T v) = 0 :=
    (real_inner_comm _ _).trans (htc v u)
  have he : inner ℝ (OperatorSum.operator C T w) (OperatorSum.operator C T w) =
      inner ℝ w w := by
    rw [OperatorSum.operator_apply]
    simp only [inner_add_left, inner_add_right, hct, htc, add_zero, zero_add]
    have hc := c.inner_map_map (EuclideanSpace.finAddEquivProd w).1
      (EuclideanSpace.finAddEquivProd w).1
    have ht := t.inner_map_map (EuclideanSpace.finAddEquivProd w).2
      (EuclideanSpace.finAddEquivProd w).2
    change inner ℝ (C _) (C _) = _ at hc
    change inner ℝ (T _) (T _) = _ at ht
    rw [hc, ht]
    exact (inner_finAdd_split w w).symm
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using he

theorem norm_left_block (B : Vector (n + k) →L[ℝ] Vector N)
    (hB : ∀ w, ‖B w‖ = ‖w‖) (u : Vector n) : ‖left B u‖ = ‖u‖ :=
  (hB _).trans (norm_left u)

theorem norm_right_block (B : Vector (n + k) →L[ℝ] Vector N)
    (hB : ∀ w, ‖B w‖ = ‖w‖) (u : Vector k) : ‖right B u‖ = ‖u‖ :=
  (hB _).trans (norm_right u)

theorem left_range_le (B : Vector (n + k) →L[ℝ] Vector N) : (left B).range ≤ B.range := by
  rintro _ ⟨u, rfl⟩
  exact ⟨leftInclusion n k u, rfl⟩

theorem right_range_le (B : Vector (n + k) →L[ℝ] Vector N) : (right B).range ≤ B.range := by
  rintro _ ⟨u, rfl⟩
  exact ⟨rightInclusion n k u, rfl⟩

theorem left_right_orthogonal (B : Vector (n + k) →L[ℝ] Vector N)
    (hB : ∀ w, ‖B w‖ = ‖w‖) : (left B).range ≤ (right B).rangeᗮ := by
  let b : Vector (n + k) →ₗᵢ[ℝ] Vector N := ⟨B.toLinearMap, hB⟩
  rintro _ ⟨u, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  have h := b.inner_map_map (rightInclusion n k v) (leftInclusion n k u)
  change inner ℝ (right B v) (left B u) = _ at h
  exact h.trans ((real_inner_comm _ _).trans (inner_left_right u v))

end Wikipedia.HopfProblem.DegreeCollapse.OrthogonalFrameBlocks

import Util.IncidenceGeometry.PolygonalArcInteriorRayPairExists
import Util.IncidenceGeometry.SegmentSameRayInitialSubsegment

open Classical
noncomputable section

lemma PolygonalArcNoSharedSubarcTransverse
    (Q R : PolygonalArc)
    (hNoShared :
      ¬ ∃ i j : ℕ,
        ∃ (hi : i + 1 < Q.vertices.length)
          (hj : j + 1 < R.vertices.length),
          ∃ a b : EuclideanSpace ℝ (Fin 2),
            a ≠ b ∧
              segment ℝ a b ⊆
                segment ℝ Q.vertices[i] Q.vertices[i + 1] ∩
                  segment ℝ R.vertices[j] R.vertices[j + 1])
    (p : EuclideanSpace ℝ (Fin 2))
    (hpQ : p ∈ Q.relativeInterior) (hpR : p ∈ R.relativeInterior) :
    ∃ i j : ℕ,
      ∃ (hi : i + 1 < Q.vertices.length)
        (hj : j + 1 < R.vertices.length),
        p ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1] ∧
          p ∈ segment ℝ R.vertices[j] R.vertices[j + 1] ∧
            ¬ ∃ c : ℝ,
              R.vertices[j + 1] - R.vertices[j] =
                c • (Q.vertices[i + 1] - Q.vertices[i]) := by
  obtain ⟨qRays⟩ := PolygonalArcInteriorRayPairExists Q p hpQ
  obtain ⟨rRays⟩ := PolygonalArcInteriorRayPairExists R p hpR
  have hqIndexNext : qRays.firstIndex + 1 < Q.vertices.length :=
    qRays.firstIndex_valid
  have hqIndex : qRays.firstIndex < Q.vertices.length :=
    Nat.lt_trans (Nat.lt_succ_self _) hqIndexNext
  have hrFirstIndexNext : rRays.firstIndex + 1 < R.vertices.length :=
    rRays.firstIndex_valid
  have hrFirstIndex : rRays.firstIndex < R.vertices.length :=
    Nat.lt_trans (Nat.lt_succ_self _) hrFirstIndexNext
  have hrSecondIndexNext : rRays.secondIndex + 1 < R.vertices.length :=
    rRays.secondIndex_valid
  have hrSecondIndex : rRays.secondIndex < R.vertices.length :=
    Nat.lt_trans (Nat.lt_succ_self _) hrSecondIndexNext
  have hpQseg :
      p ∈ segment ℝ Q.vertices[qRays.firstIndex]
        Q.vertices[qRays.firstIndex + 1] :=
    qRays.firstRay_subset (left_mem_segment ℝ p (p + qRays.firstVector))
  have hpRfirst :
      p ∈ segment ℝ R.vertices[rRays.firstIndex]
        R.vertices[rRays.firstIndex + 1] :=
    rRays.firstRay_subset (left_mem_segment ℝ p (p + rRays.firstVector))
  have hpRsecond :
      p ∈ segment ℝ R.vertices[rRays.secondIndex]
        R.vertices[rRays.secondIndex + 1] :=
    rRays.secondRay_subset (left_mem_segment ℝ p (p + rRays.secondVector))
  by_cases hfirst :
      ¬ ∃ c : ℝ,
        R.vertices[rRays.firstIndex + 1] - R.vertices[rRays.firstIndex] =
          c • (Q.vertices[qRays.firstIndex + 1] -
            Q.vertices[qRays.firstIndex])
  · exact ⟨qRays.firstIndex, rRays.firstIndex,
      qRays.firstIndex_valid, rRays.firstIndex_valid,
      hpQseg, hpRfirst, hfirst⟩
  by_cases hsecond :
      ¬ ∃ c : ℝ,
        R.vertices[rRays.secondIndex + 1] - R.vertices[rRays.secondIndex] =
          c • (Q.vertices[qRays.firstIndex + 1] -
            Q.vertices[qRays.firstIndex])
  · exact ⟨qRays.firstIndex, rRays.secondIndex,
      qRays.firstIndex_valid, rRays.secondIndex_valid,
      hpQseg, hpRsecond, hsecond⟩
  push Not at hfirst hsecond
  rcases hfirst with ⟨c1, hc1⟩
  rcases hsecond with ⟨c2, hc2⟩
  have hqdir :
      Q.vertices[qRays.firstIndex + 1] - Q.vertices[qRays.firstIndex] ≠ 0 := by
    intro hzero
    apply qRays.firstVector_ne_zero
    rw [qRays.firstVector_eq, hzero, smul_zero]
  have hrdir1 :
      R.vertices[rRays.firstIndex + 1] - R.vertices[rRays.firstIndex] ≠ 0 := by
    intro hzero
    apply rRays.firstVector_ne_zero
    rw [rRays.firstVector_eq, hzero, smul_zero]
  have hrdir2 :
      R.vertices[rRays.secondIndex + 1] - R.vertices[rRays.secondIndex] ≠ 0 := by
    intro hzero
    apply rRays.secondVector_ne_zero
    rw [rRays.secondVector_eq, hzero, smul_zero]
  have hc1ne : c1 ≠ 0 := by
    intro hzero
    subst c1
    simp at hc1
    exact hrdir1 hc1
  have hc2ne : c2 ≠ 0 := by
    intro hzero
    subst c2
    simp at hc2
    exact hrdir2 hc2
  let k1 : ℝ := rRays.firstScale * c1 * qRays.firstScale⁻¹
  let k2 : ℝ := rRays.secondScale * c2 * qRays.firstScale⁻¹
  have hk1ne : k1 ≠ 0 := by
    dsimp [k1]
    exact mul_ne_zero (mul_ne_zero rRays.firstScale_ne_zero hc1ne)
      (inv_ne_zero qRays.firstScale_ne_zero)
  have hk2ne : k2 ≠ 0 := by
    dsimp [k2]
    exact mul_ne_zero (mul_ne_zero rRays.secondScale_ne_zero hc2ne)
      (inv_ne_zero qRays.firstScale_ne_zero)
  have hrvec1 : rRays.firstVector = k1 • qRays.firstVector := by
    rw [rRays.firstVector_eq, hc1, qRays.firstVector_eq]
    simp only [smul_smul]
    dsimp [k1]
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ qRays.firstScale_ne_zero,
      mul_one]
  have hrvec2 : rRays.secondVector = k2 • qRays.firstVector := by
    rw [rRays.secondVector_eq, hc2, qRays.firstVector_eq]
    simp only [smul_smul]
    dsimp [k2]
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ qRays.firstScale_ne_zero,
      mul_one]
  have shared_of_positive :
      ∀ (j : ℕ) (hj : j + 1 < R.vertices.length)
        (v : EuclideanSpace ℝ (Fin 2))
        (hRay : segment ℝ p (p + v) ⊆
          segment ℝ R.vertices[j] R.vertices[j + 1])
        (k : ℝ), v = k • qRays.firstVector → 0 < k → False := by
    intro j hj v hRay k hv hk
    rcases SegmentSameRayInitialSubsegment p qRays.firstVector k
        qRays.firstVector_ne_zero hk with ⟨z, hpz, hzsub⟩
    apply hNoShared
    refine ⟨qRays.firstIndex, j, qRays.firstIndex_valid, hj, p, z, hpz, ?_⟩
    intro w hw
    have hw' := hzsub hw
    refine ⟨qRays.firstRay_subset hw'.1, hRay ?_⟩
    simpa [hv] using hw'.2
  by_cases hk1pos : 0 < k1
  · exact False.elim (shared_of_positive rRays.firstIndex rRays.firstIndex_valid
      rRays.firstVector rRays.firstRay_subset k1 hrvec1 hk1pos)
  have hk1neg : k1 < 0 := lt_of_le_of_ne (le_of_not_gt hk1pos) hk1ne
  by_cases hk2pos : 0 < k2
  · exact False.elim (shared_of_positive rRays.secondIndex rRays.secondIndex_valid
      rRays.secondVector rRays.secondRay_subset k2 hrvec2 hk2pos)
  have hk2neg : k2 < 0 := lt_of_le_of_ne (le_of_not_gt hk2pos) hk2ne
  exact False.elim (rRays.rays_not_same_positive ⟨k2 / k1,
    div_pos_of_neg_of_neg hk2neg hk1neg, by
      rw [hrvec2, hrvec1, smul_smul]
      congr 1
      field_simp [hk1ne]⟩)

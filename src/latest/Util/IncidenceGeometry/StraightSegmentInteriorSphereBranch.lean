import Util.IncidenceGeometry.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor

open Classical
noncomputable section

lemma StraightSegmentInteriorSphereBranch {a b x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ openSegment ℝ a b) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρlt_left : ρ < dist x a) (hρlt_right : ρ < dist x b) :
    ∃ q₁ q₂ : EuclideanSpace ℝ (Fin 2),
      q₁ ≠ q₂ ∧
        q₁ ∈ Metric.sphere x ρ ∧
          q₁ ∈ segment ℝ a b ∧
            q₂ ∈ Metric.sphere x ρ ∧
              q₂ ∈ segment ℝ a b ∧
                ∀ q,
                  q ∈ Metric.sphere x ρ →
                    q ∈ segment ℝ a b → q = q₁ ∨ q = q₂ := by
  rw [openSegment_eq_image_lineMap] at hx
  rcases hx with ⟨t, ht, rfl⟩
  let d : ℝ := dist a b
  have hcenter_a_pos : 0 < dist (AffineMap.lineMap a b t) a := hρpos.trans hρlt_left
  have hab : a ≠ b := by
    intro hab
    have hcenter_eq : AffineMap.lineMap a b t = a := by
      simp [hab]
    exact (dist_pos.mp hcenter_a_pos) hcenter_eq
  have hdpos : 0 < d := by
    dsimp [d]
    exact dist_pos.mpr hab
  let α : ℝ := ρ / d
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos hρpos hdpos
  have hdist_left : dist (AffineMap.lineMap a b t) a = t * d := by
    rw [dist_lineMap_left]
    dsimp [d]
    rw [abs_of_pos ht.1]
  have hdist_right : dist (AffineMap.lineMap a b t) b = (1 - t) * d := by
    rw [dist_lineMap_right]
    dsimp [d]
    rw [abs_of_pos (sub_pos.mpr ht.2)]
  have hα_lt_t : α < t := by
    dsimp [α, d]
    rw [hdist_left] at hρlt_left
    exact (div_lt_iff₀ hdpos).2 hρlt_left
  have hα_lt_one_sub_t : α < 1 - t := by
    dsimp [α, d]
    rw [hdist_right] at hρlt_right
    exact (div_lt_iff₀ hdpos).2 hρlt_right
  let q₁ : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap a b (t - α)
  let q₂ : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap a b (t + α)
  have ht_minus_nonneg : 0 ≤ t - α := by linarith
  have ht_minus_le_one : t - α ≤ 1 := by linarith [ht.2, hαpos]
  have ht_plus_nonneg : 0 ≤ t + α := by linarith [ht.1, hαpos]
  have ht_plus_le_one : t + α ≤ 1 := by linarith
  have hdist_param_left : dist (t - α) t = α := by
    rw [Real.dist_eq]
    have : t - α - t = -α := by ring
    rw [this, abs_neg, abs_of_pos hαpos]
  have hdist_param_right : dist (t + α) t = α := by
    rw [Real.dist_eq]
    have : t + α - t = α := by ring
    rw [this, abs_of_pos hαpos]
  have hα_mul_d : α * d = ρ := by
    dsimp [α]
    field_simp [hdpos.ne']
  have hq₁_sphere : q₁ ∈ Metric.sphere (AffineMap.lineMap a b t) ρ := by
    rw [Metric.mem_sphere]
    dsimp [q₁]
    rw [dist_lineMap_lineMap, hdist_param_left, hα_mul_d]
  have hq₂_sphere : q₂ ∈ Metric.sphere (AffineMap.lineMap a b t) ρ := by
    rw [Metric.mem_sphere]
    dsimp [q₂]
    rw [dist_lineMap_lineMap, hdist_param_right, hα_mul_d]
  have hq₁_segment : q₁ ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    exact ⟨t - α, ⟨ht_minus_nonneg, ht_minus_le_one⟩, rfl⟩
  have hq₂_segment : q₂ ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    exact ⟨t + α, ⟨ht_plus_nonneg, ht_plus_le_one⟩, rfl⟩
  have hq_ne : q₁ ≠ q₂ := by
    intro hq
    have hparam : t - α = t + α := by
      exact (AffineMap.lineMap_injective ℝ hab) hq
    linarith
  refine ⟨q₁, q₂, hq_ne, hq₁_sphere, hq₁_segment, hq₂_sphere, hq₂_segment, ?_⟩
  intro q hqSphere hqSegment
  rw [segment_eq_image_lineMap] at hqSegment
  rcases hqSegment with ⟨s, _hs, rfl⟩
  have hdist_eq : dist (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) = ρ := by
    exact Metric.mem_sphere.mp hqSphere
  have hmul : |s - t| * d = ρ := by
    rw [dist_lineMap_lineMap, Real.dist_eq] at hdist_eq
    simpa [d] using hdist_eq
  have habs : |s - t| = α := by
    dsimp [α]
    exact (eq_div_iff hdpos.ne').2 hmul
  rcases (abs_eq hαpos.le).1 habs with hst | hst
  · right
    have hs_eq : s = t + α := by linarith
    simp [q₂, hs_eq]
  · left
    have hs_eq : s = t - α := by linarith
    simp [q₁, hs_eq]

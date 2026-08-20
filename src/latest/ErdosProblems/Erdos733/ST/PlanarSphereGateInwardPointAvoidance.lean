import ErdosProblems.Erdos733.ST.FinitePointLineAvoidance
import Mathlib.Analysis.InnerProductSpace.Convex

open Classical
noncomputable section

-- [TABLET NODE: PlanarSphereGateInwardPointAvoidance]
lemma PlanarSphereGateInwardPointAvoidance
    (p q : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (U : Set (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (n : EuclideanSpace ℝ (Fin 2))
    (points : Finset (EuclideanSpace ℝ (Fin 2)))
    (lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hradius : 0 < radius)
    (hqSphere : q ∈ Metric.sphere p radius)
    (hUopen : IsOpen U) (hqU : q ∈ U)
    (hqside : 0 ≤ f (q - p)) (hnside : 0 < f n)
    (hline : ∀ ℓ ∈ lines,
      (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧
        Module.finrank ℝ ℓ.direction = 1) :
    ∃ x, x ∈ U ∩ Metric.ball p radius ∧
      0 < f (x - p) ∧
        x ∉ (points : Set (EuclideanSpace ℝ (Fin 2))) ∧
          ∀ ℓ ∈ lines, x ∉ (ℓ : Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  have hn_ne : n ≠ 0 := by
    intro hn
    simpa [hn] using hnside
  have hnorm_n : 0 < ‖n‖ := norm_pos_iff.mpr hn_ne
  let delta : ℝ := radius / (2 * ‖n‖)
  have hdelta : 0 < delta :=
    div_pos hradius (mul_pos (by norm_num) hnorm_n)
  let x0 : E := p + delta • n
  have hx0_dist : dist x0 p = radius / 2 := by
    rw [dist_eq_norm]
    dsimp [x0]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hdelta]
    dsimp [delta]
    field_simp [hnorm_n.ne']
  have hx0_ball : x0 ∈ Metric.ball p radius := by
    rw [Metric.mem_ball, hx0_dist]
    linarith
  have hx0_closed : x0 ∈ Metric.closedBall p radius :=
    Metric.ball_subset_closedBall hx0_ball
  have hx0_side : 0 < f (x0 - p) := by
    dsimp [x0]
    rw [add_sub_cancel_left, map_smul]
    exact mul_pos hdelta hnside
  have hq_closed : q ∈ Metric.closedBall p radius :=
    Metric.sphere_subset_closedBall hqSphere
  have hq_ne_x0 : q ≠ x0 := by
    intro hqx
    have hqdist : dist q p = radius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hqSphere
    rw [hqx, hx0_dist] at hqdist
    linarith
  obtain ⟨eps, heps, hepsU⟩ := (Metric.isOpen_iff.mp hUopen) q hqU
  have hdqx0 : 0 < dist q x0 := dist_pos.mpr hq_ne_x0
  let t : ℝ := min (1 / 2 : ℝ) (eps / (2 * dist q x0))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num)
      (div_pos heps (mul_pos (by norm_num) hdqx0))
  have ht_half : t ≤ 1 / 2 := min_le_left _ _
  have ht_one : t < 1 := lt_of_le_of_lt ht_half (by norm_num)
  have ht_dist : t * dist q x0 < eps := by
    have ht_le : t ≤ eps / (2 * dist q x0) := min_le_right _ _
    have hmul_le :=
      mul_le_mul_of_nonneg_right ht_le (dist_nonneg : 0 ≤ dist q x0)
    have heq : eps / (2 * dist q x0) * dist q x0 = eps / 2 := by
      field_simp [hdqx0.ne']
    rw [heq] at hmul_le
    linarith
  let xbase : E := AffineMap.lineMap q x0 t
  have hxbase_openSegment : xbase ∈ openSegment ℝ q x0 := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨ht, ht_one⟩, rfl⟩
  have hxbase_ball : xbase ∈ Metric.ball p radius :=
    openSegment_subset_ball_of_ne hq_closed hx0_closed hq_ne_x0
      hxbase_openSegment
  have hxbase_near : dist xbase q < eps := by
    rw [dist_eq_norm]
    dsimp [xbase]
    rw [AffineMap.lineMap_apply_module]
    have hsub : (1 - t) • q + t • x0 - q = t • (x0 - q) := by
      module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    simpa [dist_eq_norm, norm_sub_rev] using ht_dist
  have hxbaseU : xbase ∈ U :=
    hepsU (by simpa [Metric.mem_ball] using hxbase_near)
  have hxbase_side : 0 < f (xbase - p) := by
    dsimp [xbase]
    rw [AffineMap.lineMap_apply_module]
    have hsub : (1 - t) • q + t • x0 - p =
        (1 - t) • (q - p) + t • (x0 - p) := by
      module
    rw [hsub, map_add, map_smul, map_smul]
    have hone_nonneg : 0 ≤ 1 - t := by linarith
    have hfirst : 0 ≤ (1 - t) * f (q - p) :=
      mul_nonneg hone_nonneg hqside
    have hsecond : 0 < t * f (x0 - p) :=
      mul_pos ht hx0_side
    simpa [smul_eq_mul] using add_pos_of_nonneg_of_pos hfirst hsecond
  let W : Set E := U ∩ Metric.ball p radius ∩ {x | 0 < f (x - p)}
  have hside_open : IsOpen {x : E | 0 < f (x - p)} := by
    exact isOpen_lt continuous_const
      (f.continuous.comp (continuous_id.sub continuous_const))
  have hWopen : IsOpen W := (hUopen.inter Metric.isOpen_ball).inter hside_open
  have hWnonempty : W.Nonempty :=
    ⟨xbase, ⟨⟨hxbaseU, hxbase_ball⟩, hxbase_side⟩⟩
  obtain ⟨x, hxW, hxpoints, hxlines⟩ :=
    FinitePointLineAvoidance W points lines hWopen hWnonempty hline
  exact ⟨x, hxW.1, hxW.2, hxpoints, hxlines⟩

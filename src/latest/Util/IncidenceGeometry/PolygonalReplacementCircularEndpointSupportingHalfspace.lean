import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma PolygonalReplacementCircularEndpointSupportingHalfspace
    {c a b : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : 0 ≤ r)
    (ha : a ∈ Metric.sphere c r)
    (hb : r ^ 2 ≤ inner ℝ (b - c) (a - c)) :
    (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ segment ℝ a b →
          p ∈ Metric.closedBall c r →
            p = a) ∧
      Disjoint (openSegment ℝ a b) (Metric.ball c r) := by
  classical
  have closedBall_only_endpoint :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ segment ℝ a b →
          p ∈ Metric.closedBall c r →
            p = a := by
    intro p hpseg hpball
    rw [segment_eq_image_lineMap] at hpseg
    rcases hpseg with ⟨t, ht, hp⟩
    rcases ht with ⟨ht0, ht1⟩
    subst p
    let q : EuclideanSpace ℝ (Fin 2) := (AffineMap.lineMap a b t) - c
    let v : EuclideanSpace ℝ (Fin 2) := a - c
    let u : EuclideanSpace ℝ (Fin 2) := b - c
    have hvnorm : ‖v‖ = r := by
      have hdist : dist a c = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using ha
      simpa [v, dist_eq_norm] using hdist
    have hvinner : inner ℝ v v = r ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      exact congrArg (fun x : ℝ => x ^ 2) hvnorm
    have hpball_norm : ‖q‖ ≤ r := by
      have hdist : dist (AffineMap.lineMap a b t) c ≤ r := by
        simpa [Metric.mem_closedBall] using hpball
      simpa [q, dist_eq_norm] using hdist
    have hq_expr : q = (1 - t) • v + t • u := by
      change (AffineMap.lineMap a b t) - c =
        (1 - t) • (a - c) + t • (b - c)
      rw [AffineMap.lineMap_apply_module]
      module
    have hinner_expr :
        inner ℝ q v = (1 - t) * inner ℝ v v + t * inner ℝ u v := by
      rw [hq_expr]
      simp [inner_add_left, inner_smul_left]
    have hinner_ge : r ^ 2 ≤ inner ℝ q v := by
      rw [hinner_expr]
      have hbuv : r ^ 2 ≤ inner ℝ u v := by
        simpa [u, v] using hb
      nlinarith
    have hinner_le : inner ℝ q v ≤ r ^ 2 := by
      have hle1 : inner ℝ q v ≤ ‖q‖ * ‖v‖ := real_inner_le_norm q v
      have hle2 : ‖q‖ * ‖v‖ ≤ r * r := by
        rw [hvnorm]
        exact mul_le_mul_of_nonneg_right hpball_norm hr
      nlinarith
    have hinner_eq : inner ℝ q v = r ^ 2 := le_antisymm hinner_le hinner_ge
    have hqnorm_sq_le : ‖q‖ ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg q) hpball_norm 2
    have hqv_norm_sq :
        ‖q - v‖ ^ 2 = ‖q‖ ^ 2 - 2 * inner ℝ q v + ‖v‖ ^ 2 :=
      norm_sub_sq_real q v
    have hqv_sq_nonpos : ‖q - v‖ ^ 2 ≤ 0 := by
      rw [hqv_norm_sq, hinner_eq, hvnorm]
      nlinarith
    have hqv_sq_zero : ‖q - v‖ ^ 2 = 0 := by
      have hnonneg : 0 ≤ ‖q - v‖ ^ 2 := sq_nonneg _
      exact le_antisymm hqv_sq_nonpos hnonneg
    have hqv_zero : q - v = 0 := by
      have hnorm_zero : ‖q - v‖ = 0 :=
        sq_eq_zero_iff.mp hqv_sq_zero
      exact norm_eq_zero.mp hnorm_zero
    have hq_eq_v : q = v := sub_eq_zero.mp hqv_zero
    have hline_sub : (AffineMap.lineMap a b t) - c = a - c := by
      simpa [q, v] using hq_eq_v
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z + c) hline_sub
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  refine ⟨closedBall_only_endpoint, ?_⟩
  rw [Set.disjoint_left]
  intro p hpOpen hpBall
  have hpClosed : p ∈ Metric.closedBall c r :=
    Metric.ball_subset_closedBall hpBall
  have hpa : p = a :=
    closedBall_only_endpoint p (openSegment_subset_segment ℝ a b hpOpen)
      hpClosed
  have ha_not_ball : a ∉ Metric.ball c r := by
    have hdist : dist a c = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ha
    simp [Metric.mem_ball, hdist]
  exact ha_not_ball (hpa ▸ hpBall)

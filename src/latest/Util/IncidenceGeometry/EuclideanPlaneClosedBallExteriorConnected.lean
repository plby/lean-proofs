import Util.IncidenceGeometry.Basic
import Mathlib.Analysis.Normed.Module.Connected

open Classical
noncomputable section

lemma EuclideanPlaneClosedBallExteriorConnected
    (R : ℝ) (hR : 0 ≤ R) :
    IsConnected
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ := by
  let r : ℝ := R + 1
  have hr : 0 < r := by dsimp [r]; linarith
  have hRr : R < r := by dsimp [r]; linarith
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hsphere : IsPathConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r) :=
    isPathConnected_sphere hrank 0 hr.le
  have hradial : ∀ (x : EuclideanSpace ℝ (Fin 2)),
      x ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ →
        let px := (r / ‖x‖) • x
        px ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r ∧
          JoinedIn (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ x px := by
    intro x hx
    have hxnorm : R < ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hxnormpos : 0 < ‖x‖ := hR.trans_lt hxnorm
    have hxnormne : ‖x‖ ≠ 0 := hxnormpos.ne'
    dsimp
    constructor
    · rw [Metric.mem_sphere, dist_zero_right]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hxnormpos)]
      exact div_mul_cancel₀ r hxnormne
    · apply JoinedIn.of_segment_subset
      rw [segment_eq_image]
      rintro z ⟨t, ht, rfl⟩
      have hcoeff : 0 < (1 - t) + t * (r / ‖x‖) := by
        have hdiv : 0 < r / ‖x‖ := div_pos hr hxnormpos
        by_cases ht0 : t = 0
        · simp [ht0]
        · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2)
            (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hdiv)
      have hnorm :
          ‖(1 - t) • x + t • ((r / ‖x‖) • x)‖ =
            (1 - t) * ‖x‖ + t * r := by
        rw [smul_smul, ← add_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hcoeff]
        field_simp
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
      rw [hnorm]
      apply not_le_of_gt
      by_cases ht0 : t = 0
      · simpa [ht0] using hxnorm
      · calc
          R = (1 - t) * R + t * R := by ring
          _ < (1 - t) * ‖x‖ + t * r :=
            add_lt_add_of_le_of_lt
              (mul_le_mul_of_nonneg_left hxnorm.le (sub_nonneg.mpr ht.2))
              (mul_lt_mul_of_pos_left hRr (lt_of_le_of_ne ht.1 (Ne.symm ht0)))
  apply IsPathConnected.isConnected
  rw [isPathConnected_iff]
  constructor
  · rcases hsphere.nonempty with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hznorm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    simp [Metric.mem_closedBall, dist_zero_right, hznorm, hRr]
  · intro x hx y hy
    rcases hradial x hx with ⟨hpxsphere, hxjoin⟩
    rcases hradial y hy with ⟨hpysphere, hyjoin⟩
    have hsphere_sub :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r ⊆
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ := by
      intro z hz
      have hznorm : ‖z‖ = r := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      simp [Metric.mem_closedBall, dist_zero_right, hznorm, hRr]
    exact hxjoin.trans
      ((hsphere.joinedIn _ hpxsphere _ hpysphere).mono hsphere_sub |>.trans hyjoin.symm)

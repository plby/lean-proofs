import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierDerivativesBasic

/-!
# A uniform first base derivative estimate for the genuine inverse modes

Shrink the proved common open neighborhood to concentric complex discs.
The Cauchy estimate on a radius-`r` circle centred at any point of the
inner radius-`r` disc is controlled by the original inverse-mode bound
on the outer disc. The constant is independent of the integer mode.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Set Topology TopologicalSpace Metric

/-- The first-derivative Cauchy estimate is uniform throughout the inner disc. -/
theorem norm_deriv_le_on_inner_disc {f : ℂ → ℂ} {W : Set ℂ} {b₀ : ℂ} {r C : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f W)
    (houter : closedBall b₀ (2 * r) ⊆ W)
    (hbound : ∀ z ∈ W, ‖f z‖ ≤ C) {b : ℂ} (hb : b ∈ closedBall b₀ r) :
    ‖deriv f b‖ ≤ C / r := by
  have hlocal : closedBall b r ⊆ closedBall b₀ (2 * r) :=
    closedBall_subset_closedBall' (by
      have hdist := mem_closedBall.mp hb
      linarith)
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hf.diffContOnCl_ball (hlocal.trans houter))
  intro z hz
  exact hbound z (houter (hlocal (sphere_subset_closedBall hz)))

variable {U₀ : Opens ℂ} (P : HolomorphicPeriodMap ℂ U₀)

/-- Actual concentric discs inside the original base, with holomorphicity
and the inverse-frequency estimate on one common outer disc. -/
theorem exists_concentric_discs_uniform_inverse (b₀ : U₀) :
    ∃ (r c : ℝ), 0 < r ∧ 0 < c ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U₀ ∧
      (∀ k : Fin 4 → ℤ, DifferentiableOn ℂ (ambientInverse P (P.point b₀) k)
        (ball (b₀ : ℂ) (3 * r))) ∧
      (∀ b ∈ closedBall (b₀ : ℂ) (3 * r), ∀ k : Fin 4 → ℤ,
        ‖ambientInverse P (P.point b₀) k b‖ ≤ c⁻¹ * ‖k‖⁻¹) := by
  obtain ⟨W, c, hW, hb₀, hWU, hc, hdiff, hbound⟩ :=
    exists_open_ambient_uniform_inverse P b₀
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hb₀)
  have hclosed : closedBall (b₀ : ℂ) (3 * (R / 4)) ⊆ W :=
    (closedBall_subset_ball (by linarith : 3 * (R / 4) < R)).trans hRW
  refine ⟨R / 4, c, by positivity, hc, hclosed.trans hWU, ?_, ?_⟩
  · intro k
    exact (hdiff k).mono (ball_subset_closedBall.trans hclosed)
  · intro b hb k
    exact hbound b (hclosed hb) k

/-- The first derivative of each actual inverse Fourier mode obeys an
unconditional locally uniform order-minus-one estimate in the original base. -/
theorem exists_uniform_first_derivative_bound (b₀ : U₀) :
    ∃ (r c : ℝ), 0 < r ∧ 0 < c ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U₀ ∧
      ∀ k : Fin 4 → ℤ, ∀ b ∈ closedBall (b₀ : ℂ) r,
        ‖deriv (ambientInverse P (P.point b₀) k) b‖ ≤ (c⁻¹ / r) * ‖k‖⁻¹ := by
  obtain ⟨r, c, hr, hc, hbase, hdiff, hbound⟩ :=
    exists_concentric_discs_uniform_inverse P b₀
  refine ⟨r, c, hr, hc, hbase, ?_⟩
  intro k b hb
  have houter : closedBall (b₀ : ℂ) (2 * r) ⊆ ball (b₀ : ℂ) (3 * r) :=
    closedBall_subset_ball (by linarith)
  have h := norm_deriv_le_on_inner_disc hr (hdiff k) houter
    (fun z hz => hbound z (ball_subset_closedBall hz) k) hb
  exact h.trans_eq (by ring)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierDerivativesFirst

/-!
# All-order locally uniform base derivative bounds

The original inverse-frequency bound and the proved concentric discs
give the Cauchy estimate at every derivative order. The inner disc is
independent of both the order and the integer mode; only the displayed
factorial-over-radius constant changes with the derivative order.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Set Topology TopologicalSpace Metric

/-- The explicit Cauchy constant, independent of the base point in the
inner disc and of the Fourier mode. -/
def baseDerivativeConstant (r c : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * c⁻¹ / r ^ n

theorem baseDerivativeConstant_pos {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (n : ℕ) :
    0 < baseDerivativeConstant r c n := by
  exact div_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (inv_pos.mpr hc))
    (pow_pos hr n)

@[simp] theorem baseDerivativeConstant_zero (r c : ℝ) :
    baseDerivativeConstant r c 0 = c⁻¹ := by
  simp only [baseDerivativeConstant, Nat.factorial_zero, Nat.cast_one, one_mul,
    pow_zero, div_one]

@[simp] theorem baseDerivativeConstant_one (r c : ℝ) :
    baseDerivativeConstant r c 1 = c⁻¹ / r := by
  simp only [baseDerivativeConstant, Nat.factorial_one, Nat.cast_one, one_mul, pow_one]

/-- Every Cauchy derivative estimate is uniform throughout the inner disc. -/
theorem norm_iteratedDeriv_le_on_inner_disc (n : ℕ) {f : ℂ → ℂ}
    {W : Set ℂ} {b₀ : ℂ} {r C : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f W)
    (houter : closedBall b₀ (2 * r) ⊆ W)
    (hbound : ∀ z ∈ W, ‖f z‖ ≤ C) {b : ℂ} (hb : b ∈ closedBall b₀ r) :
    ‖iteratedDeriv n f b‖ ≤ (n.factorial : ℝ) * C / r ^ n := by
  have hlocal : closedBall b r ⊆ closedBall b₀ (2 * r) :=
    closedBall_subset_closedBall' (by
      have hdist := mem_closedBall.mp hb
      linarith)
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hf.diffContOnCl_ball (hlocal.trans houter))
  intro z hz
  exact hbound z (houter (hlocal (sphere_subset_closedBall hz)))

variable {U₀ : Opens ℂ} (P : HolomorphicPeriodMap ℂ U₀)

/-- The genuine inverse modes have uniform bounds of every base derivative
order on one fixed inner disc, with the explicit Cauchy constants. -/
theorem exists_uniform_iterated_derivative_bound (b₀ : U₀) :
    ∃ (r c : ℝ), 0 < r ∧ 0 < c ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U₀ ∧
      ∀ n : ℕ, ∀ k : Fin 4 → ℤ, ∀ b ∈ closedBall (b₀ : ℂ) r,
        ‖iteratedDeriv n (ambientInverse P (P.point b₀) k) b‖ ≤
          baseDerivativeConstant r c n * ‖k‖⁻¹ := by
  obtain ⟨r, c, hr, hc, hbase, hdiff, hbound⟩ :=
    exists_concentric_discs_uniform_inverse P b₀
  refine ⟨r, c, hr, hc, hbase, ?_⟩
  intro n k b hb
  have houter : closedBall (b₀ : ℂ) (2 * r) ⊆ ball (b₀ : ℂ) (3 * r) :=
    closedBall_subset_ball (by linarith)
  have h := norm_iteratedDeriv_le_on_inner_disc n hr (hdiff k) houter
    (fun z hz => hbound z (ball_subset_closedBall hz) k) hb
  exact h.trans_eq (by unfold baseDerivativeConstant; ring)

/-- Existence form with an actual positive constant for each derivative order,
all on the same original-base disc and all independent of the Fourier mode. -/
theorem exists_uniform_all_derivative_bounds (b₀ : U₀) :
    ∃ (r : ℝ) (C : ℕ → ℝ), 0 < r ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U₀ ∧
      (∀ n, 0 < C n) ∧
      ∀ n : ℕ, ∀ k : Fin 4 → ℤ, ∀ b ∈ closedBall (b₀ : ℂ) r,
        ‖iteratedDeriv n (ambientInverse P (P.point b₀) k) b‖ ≤ C n * ‖k‖⁻¹ := by
  obtain ⟨r, c, hr, hc, hbase, hbound⟩ :=
    exists_uniform_iterated_derivative_bound P b₀
  exact ⟨r, baseDerivativeConstant r c, hr, hbase,
    baseDerivativeConstant_pos hr hc, hbound⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

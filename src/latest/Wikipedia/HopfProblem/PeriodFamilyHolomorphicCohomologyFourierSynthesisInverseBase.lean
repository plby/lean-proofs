import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierDerivatives

/-!
# One genuine inverse-mode disc with its actual Cauchy estimates

The radius and elliptic constant come from the previously proved common
neighborhood of the original fixed-centre selector. We retain both the
outer-disc holomorphicity and all Cauchy estimates for that same witness.
The functions are literally the original `RelativeFourier.ambientInverse`;
no new choice of multiplier or selector is made.
-/

noncomputable section

open TopologicalSpace Metric

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open PeriodTorusLineBundleClassification

/-- Reciprocal integer-frequency norms are at most one, including the actual zero vector. -/
theorem inverse_integerVector_norm_le_one (k : Fin 4 → ℤ) : ‖k‖⁻¹ ≤ (1 : ℝ) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have h := one_div_le_one_div_of_le zero_lt_one (one_le_norm_integerVector hk)
    simpa only [one_div, inv_one] using h

/-- The explicit real-direction Cauchy constant for a fixed list of base vectors. -/
def directionListConstant (r c : ℝ) (s : List ℂ) : ℝ :=
  RelativeFourier.baseDerivativeConstant r c s.length * ‖s.prod‖

theorem directionListConstant_nonneg {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (s : List ℂ) : 0 ≤ directionListConstant r c s :=
  mul_nonneg (RelativeFourier.baseDerivativeConstant_pos hr hc s.length).le (norm_nonneg _)

@[simp] theorem directionListConstant_nil (r c : ℝ) :
    directionListConstant r c [] = c⁻¹ := by
  simp only [directionListConstant, List.length_nil, RelativeFourier.baseDerivativeConstant_zero,
    List.prod_nil, norm_one, mul_one]

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- One original-centre disc carries holomorphicity and all complex derivative estimates
simultaneously, with the original inverse functions and one pair of proved constants. -/
theorem exists_common_disc_complex_inverse (b₀ : U) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U ∧
      (∀ k : Fin 4 → ℤ,
        DifferentiableOn ℂ (RelativeFourier.ambientInverse P (P.point b₀) k)
          (ball (b₀ : ℂ) (3 * r))) ∧
      ∀ n : ℕ, ∀ k : Fin 4 → ℤ, ∀ z ∈ closedBall (b₀ : ℂ) r,
        ‖iteratedDeriv n (RelativeFourier.ambientInverse P (P.point b₀) k) z‖ ≤
          RelativeFourier.baseDerivativeConstant r c n * ‖k‖⁻¹ := by
  obtain ⟨r, c, hr, hc, hbase, hdiff, hbound⟩ :=
    RelativeFourier.exists_concentric_discs_uniform_inverse P b₀
  refine ⟨r, c, hr, hc, hbase, hdiff, ?_⟩
  intro n k z hz
  have houter : closedBall (b₀ : ℂ) (2 * r) ⊆ ball (b₀ : ℂ) (3 * r) :=
    closedBall_subset_ball (by linarith)
  have h := RelativeFourier.norm_iteratedDeriv_le_on_inner_disc n hr (hdiff k) houter
    (fun w hw => hbound w (ball_subset_closedBall hw) k) hz
  exact h.trans_eq (by unfold RelativeFourier.baseDerivativeConstant; ring)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

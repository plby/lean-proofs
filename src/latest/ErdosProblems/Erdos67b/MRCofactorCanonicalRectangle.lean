import ErdosProblems.Erdos67b.MRCofactorRectangleSmallMean
import ErdosProblems.Erdos67b.MRCofactorScheduledBlocks

/-!
# Smallness of the actual canonical scheduled cofactor

The cutoff, all block conditions, and the lower cofactor threshold are
discharged. The remaining hypotheses are the source schedule, the natural
rectangle bounds, and ambient nonpretentiousness of the original function.
-/

open Filter

namespace Erdos67b

noncomputable section

theorem mrExists_uniform_small_canonical_cofactor_rectangle
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ I ∈ mrScheduledBlocks p₁ q₁ J,
      ∀ {P Q : ℕ}, 4 ≤ P → P ≤ Q → Q ≤ 2 * P → 2 * Q ^ 2 ≤ X →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
          (mrFiniteCofactorLineCoefficient (primesInBlock I) f) (-t)‖ ≤ epsilon := by
  obtain ⟨delta, hdelta, _, M₀, Y₀, hM₀, hY₀, hrectangle⟩ :=
    mrExists_uniform_small_scheduled_cofactor_rectangle hepsilon
  have heventual : ∀ᶠ X : ℕ in atTop,
      Y₀ ^ 2 ≤ X ∧ 1024 ≤ Real.log (X : ℝ) ∧
        4 ≤ delta ^ 2 * Real.log (X : ℝ) := by
    filter_upwards [eventually_ge_atTop (Y₀ ^ 2),
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1024),
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / delta ^ 2))]
      with X hsquare hlog hdeltaLog
    refine ⟨hsquare, hlog, ?_⟩
    have hh := (div_le_iff₀ (sq_pos_of_pos hdelta)).mp hdeltaLog
    nlinarith
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 heventual
  refine ⟨M₀, max X₁ 1, hM₀, le_max_right _ _, ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens
    J hupper I hI P Q hP hPQ hQP hsize f hmul hbound hnonpret t ht
  obtain ⟨hsquare, hlog, hdeltaLog⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hQpos : 0 < Q := by omega
  have hXY := mrCofactor_rectangle_log_lower hQpos hsize
  have hXsquare := mrCofactor_rectangle_lower_sq_ge hQpos hsize
  have hY : Y₀ ≤ X / Q :=
    le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (Nat.zero_le _)
      (hsquare.trans hXsquare)
  obtain ⟨hB, hdisj, hsmall, hmass, hcutoff, hlarge⟩ :=
    mrScheduledBlocks_cofactor_conditions heta hp hq hpq hlogq hbudget hmertens
      hdelta (hY₀.trans hY) hlog hXY hdeltaLog hupper
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI
  apply hrectangle hM hY hP hPQ hQP hsize
    (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j))
    (fun p hpB ↦ (mem_primesInBlock.mp hpB).1) p₁ q₁ J
    (mrScheduledPrimeInterval p₁ q₁ j) hB hdisj hsmall hmass
    (fun p hpB ↦ hcutoff j hj p hpB) hcutoff hlarge hmul hbound hnonpret t ht

end

end Erdos67b

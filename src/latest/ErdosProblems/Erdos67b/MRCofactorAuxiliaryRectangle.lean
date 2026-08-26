import ErdosProblems.Erdos67b.MRCofactorRectangleSmallMean
import ErdosProblems.Erdos67b.MRCofactorScheduledBlocks

/-!
# The additional Ramaré denominator at the cofactor scale

The auxiliary prime set may extend to `exp (log X / log (log X))`.
It is not identified with a scheduled block. Its cutoff is discharged
separately, while the actual typical support and denominator are preserved.
-/

open Filter

namespace Erdos67b

noncomputable section

theorem mrCofactor_auxiliary_log_le_power {delta : ℝ} (hdelta : 0 < delta)
    {X Y : ℕ} (hX : 0 ≤ Real.log (X : ℝ))
    (hXY : Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ))
    (hloglog : 1 ≤ Real.log (Real.log (X : ℝ)))
    (hlarge : 2 ≤ delta * Real.log (Real.log (X : ℝ))) :
    Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) ≤ delta * Real.log (Y : ℝ) := by
  have hfirst : Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) ≤
      delta * Real.log (X : ℝ) / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (Real.log (X : ℝ)))).mpr
    have hh := mul_le_mul_of_nonneg_left hlarge hX
    nlinarith
  have hsecond := mul_le_mul_of_nonneg_left hXY hdelta.le
  exact hfirst.trans (by linarith)

theorem mrExists_uniform_small_auxiliary_cofactor_rectangle
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤
          Real.log (X : ℝ) / Real.log (Real.log (X : ℝ))) →
      ∀ {P Q : ℕ}, 4 ≤ P → P ≤ Q → Q ≤ 2 * P → 2 * Q ^ 2 ≤ X →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
          (mrFiniteCofactorLineCoefficient A f) (-t)‖ ≤ epsilon := by
  obtain ⟨delta, hdelta, _, M₀, Y₀, hM₀, hY₀, hrectangle⟩ :=
    mrExists_uniform_small_scheduled_cofactor_rectangle hepsilon
  have hloglogTendsto : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp EulerSubpower.tendsto_log_nat_atTop
  have heventual : ∀ᶠ X : ℕ in atTop,
      Y₀ ^ 2 ≤ X ∧ 1024 ≤ Real.log (X : ℝ) ∧
        4 ≤ delta ^ 2 * Real.log (X : ℝ) ∧
        1 ≤ Real.log (Real.log (X : ℝ)) ∧
        2 ≤ delta * Real.log (Real.log (X : ℝ)) := by
    filter_upwards [eventually_ge_atTop (Y₀ ^ 2),
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1024),
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / delta ^ 2)),
      hloglogTendsto.eventually (eventually_ge_atTop 1),
      hloglogTendsto.eventually (eventually_ge_atTop (2 / delta))]
      with X hsquare hlog hdeltaLog hll hdeltaLL
    refine ⟨hsquare, hlog, ?_, hll, ?_⟩
    · have hh := (div_le_iff₀ (sq_pos_of_pos hdelta)).mp hdeltaLog
      nlinarith
    · have hh := (div_le_iff₀ hdelta).mp hdeltaLL
      nlinarith
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 heventual
  refine ⟨M₀, max X₁ 1, hM₀, le_max_right _ _, ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens
    J hupper I A hA hAlog P Q hP hPQ hQP hsize f hmul hbound hnonpret t ht
  obtain ⟨hsquare, hlog, hdeltaLog, hll, hdeltaLL⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hQpos : 0 < Q := by omega
  have hXY := mrCofactor_rectangle_log_lower hQpos hsize
  have hXsquare := mrCofactor_rectangle_lower_sq_ge hQpos hsize
  have hY : Y₀ ≤ X / Q :=
    le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (Nat.zero_le _)
      (hsquare.trans hXsquare)
  obtain ⟨hB, hdisj, hsmall, hmass, hcutoff, hlarge⟩ :=
    mrScheduledBlocks_cofactor_conditions heta hp hq hpq hlogq hbudget hmertens
      hdelta (hY₀.trans hY) hlog hXY hdeltaLog hupper
  have hAcut : ∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta (X / Q) := by
    intro p hpA
    have hpower := mrCofactor_auxiliary_log_le_power hdelta
      (by linarith : 0 ≤ Real.log (X : ℝ)) hXY hll hdeltaLL
    have hh := Real.exp_le_exp.mpr ((hAlog p hpA).trans hpower)
    rw [Real.exp_log (show (0 : ℝ) < p by exact_mod_cast (hA p hpA).pos)] at hh
    exact_mod_cast hh.trans (mrCofactorPowerCutoff_exp_le delta (X / Q))
  exact hrectangle hM hY hP hPQ hQP hsize A hA p₁ q₁ J I
    hB hdisj hsmall hmass hAcut hcutoff hlarge hmul hbound hnonpret t ht

end

end Erdos67b

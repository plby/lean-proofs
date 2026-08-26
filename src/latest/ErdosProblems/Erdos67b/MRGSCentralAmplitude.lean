import ErdosProblems.Erdos67b.MRCofactorLocalTwistedPrefixes
import ErdosProblems.Erdos67b.MRCofactorScheduledBlocks

/-!
# Uniform smallness of the actual scheduled central prefix amplitude

The denominator is removed by choosing its prime set empty. All source
block conditions and the local contour height are discharged uniformly.
-/

open Filter
open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrIndexedTypicalCofactorCoefficient_empty {ι : Type*}
    (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) :
    mrIndexedTypicalCofactorCoefficient ∅ J B f = mrIndexedTypicalCoefficient J B f := by
  funext n
  simp [mrIndexedTypicalCofactorCoefficient, mrCommonDenominator,
    primeDivisorCount, primeDivisorSet]

theorem mrEventually_central_localHeight :
    ∀ᶠ X : ℕ in atTop, 2 ≤ X ∧ Real.log ((2 * X : ℕ) : ℝ) ^ 2 ≤ (X : ℝ) / 4 := by
  filter_upwards [eventually_ge_atTop 2,
    MRHalaszBands.eventually_log_pow_div_self_le 2 (by norm_num : (0 : ℝ) < 1 / 16)]
    with X hX hratio
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogtwo : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hlog : Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hXpos.ne']
    linarith
  have hnonneg : 0 ≤ Real.log ((2 * X : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * X by omega))
  have hsquare := pow_le_pow_left₀ hnonneg hlog 2
  have hsmall := (div_le_iff₀ hXpos).1 hratio
  refine ⟨hX, ?_⟩
  nlinarith

theorem mrExists_uniform_small_scheduled_central_prefixes
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ 3 * (X : ℝ) / 4 → ∀ Z ∈ Finset.Icc X (2 * X),
        ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient (Finset.Icc 1 J)
          (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f) t Z /
          (Z : ℂ)‖ ≤ epsilon := by
  obtain ⟨delta, hdelta, _, M₀, Y₀, hM₀, hY₀, hprefix⟩ :=
    mrExists_uniform_small_local_twisted_cofactor_prefixes hepsilon
  have heventual : ∀ᶠ X : ℕ in atTop,
      Y₀ ≤ X ∧ 1024 ≤ Real.log (X : ℝ) ∧
        4 ≤ delta ^ 2 * Real.log (X : ℝ) ∧
        Real.log ((2 * X : ℕ) : ℝ) ^ 2 ≤ (X : ℝ) / 4 := by
    filter_upwards [eventually_ge_atTop Y₀,
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1024),
      EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / delta ^ 2)),
      mrEventually_central_localHeight] with X hY hlog hd hheight
    refine ⟨hY, hlog, ?_, hheight.2⟩
    have hh := (div_le_iff₀ (sq_pos_of_pos hdelta)).1 hd
    nlinarith
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 heventual
  refine ⟨M₀, max X₁ 2, hM₀, le_max_right _ _, ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens
    J hupper f hmul hbound hnonpret t ht Z hZ
  obtain ⟨hY, hlog, hdeltaLog, hheight⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hXtwo : 2 ≤ X := hY₀.trans hY
  obtain ⟨hB, hdisj, hsmall, hmass, hcutoff, hlarge⟩ :=
    mrScheduledBlocks_cofactor_conditions heta hp hq hpq hlogq hbudget hmertens
      hdelta hXtwo hlog (by linarith) hdeltaLog hupper
  have hwindow : |t| + Real.log ((2 * X : ℕ) : ℝ) ^ 2 ≤ (X : ℝ) := by linarith
  have hmean := hprefix hM hY (show X ≤ 2 * X by omega) ∅ (by simp)
    (Finset.Icc 1 J) (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j))
    (fun j hj ↦ (Finset.mem_Icc.1 hj).1) hB hdisj hsmall hmass (by simp)
    hcutoff hlarge hmul hbound hnonpret t hwindow Z hZ
  rw [mrPositivePrefix_typicalCofactor_untwist_eq,
    mrIndexedTypicalCofactorCoefficient_empty] at hmean
  simpa only [norm_div, Complex.norm_natCast] using hmean

end

end Erdos67b

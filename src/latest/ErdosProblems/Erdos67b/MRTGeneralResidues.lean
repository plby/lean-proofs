import ErdosProblems.Erdos67b.MRTResidueAverage
import ErdosProblems.Erdos67b.MRTResidueGeometry

/-! # One fixed typical family for every small residue modulus -/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos67b

noncomputable section

theorem mrtExists_logPower_residue_short_firstMoment {rho R : ℝ}
    (hrho : 0 < rho) (hR : 1 ≤ R) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K A₀ Y₀ : ℕ, 0 < K ∧ 0 < A₀ ∧ H ≤ Y₀ ∧
        ∀ {A X Y : ℕ}, A₀ ≤ A → Y₀ ≤ Y → Y ≤ X →
          Real.log (X : ℝ) ≤ R * Real.log
            ((Y / mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℕ) : ℝ) →
        ∀ {f : ℕ → ℂ}, IsCompletelyMultiplicativeOnPositive f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
        ∀ {q : ℕ}, 0 < q → q ≤ mrtLogPowerNatWindow (Real.log (H : ℝ)) →
        ∀ b : ℕ, ∀ {h Z : ℕ},
          2 * (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 2 ≤ h →
          h ≤ H → 2 * Y ≤ Z →
          (∑ n ∈ Finset.Ioc Y (2 * Y),
            ‖mrtResidueShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n h q b‖) ≤
              (h : ℝ) * Y / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 + 2 * h + Y := by
  obtain ⟨H₁, hH₁, hunit⟩ := mrtExists_logPower_unit_residue_short_firstMoment hrho hR
  obtain ⟨H₂, hH₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (mrtEventually_logPower_source hrho))
  refine ⟨max H₁ H₂, hH₁.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hHH₁ : H₁ ≤ H := (le_max_left _ _).trans hH
  have hHpos : 0 < H := by omega
  obtain ⟨hW, hratio, K, A₁, Y₁, hK, hA₁, hY₁, hfirst⟩ := hunit H hHH₁
  obtain ⟨_, _, hp, hq, _, _, _, _, _, _, hc⟩ := hH₂ H ((le_max_right _ _).trans hH)
  let w := mrtLogPowerNatWindow (Real.log (H : ℝ))
  have hw : 2 ≤ w := (mrtLogPowerNatWindow_bounds hW).1
  have hwpos : 0 < w := by omega
  let A₀ := max A₁ w
  let Y₀ := w * Y₁
  have hA₀ : 0 < A₀ := hA₁.trans_le (le_max_left _ _)
  have hY₀ : H ≤ Y₀ := by
    apply hY₁.trans
    simpa only [one_mul] using Nat.mul_le_mul_right Y₁ (show 1 ≤ w by omega)
  refine ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret q hqpos hqw b h Z hshort hhH hZ
  let d := Nat.gcd b q
  obtain ⟨hd, hdqle, hqdpos, hcoprime⟩ := mrtGcd_residue_parameters b hqpos
  have hdpos : 0 < d := hd
  have hdw : d ≤ w := hdqle.trans hqw
  have hAd : q / d ≤ A := (Nat.div_le_self q d).trans
    (hqw.trans ((le_max_right _ _).trans hA))
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans hA
  have hYdiv : Y₁ ≤ Y / d := mrtDivided_ambient_threshold hdpos hdw hY
  have hYbase : Y₁ ≤ Y / w := mrtDivided_ambient_threshold hwpos (le_refl _) hY
  have hbasepos : (0 : ℝ) < ((Y / w : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Y / w by omega)
  have hlogdiv : Real.log (X : ℝ) ≤ R * Real.log ((Y / d : ℕ) : ℝ) :=
    hlog.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hbasepos (by exact_mod_cast mrtDivided_scale_mono hdpos hdw Y))
      (zero_le_one.trans hR))
  have hlength := mrtLogPower_divided_shortLength_bounds hHpos hW
    (by linarith only [hc]) hdpos hdw hshort hhH
  have hlarge := mrtLogPower_scheduled_primes_large hW (by linarith only [hp])
    ((Real.one_le_exp_iff.2 (by norm_num : (0 : ℝ) ≤ 1)).trans hq) hdw K
  apply mrtSum_norm_residueShortSum_le_divisor_power hdpos
    (Nat.gcd_dvd_right b q) (Nat.gcd_dvd_left b q) hlarge hmul hbound Z Y h
    (pow_pos (mrtLogPowerWindow_pos _) 3)
  have hunitbound := hfirst hA₁A hYdiv ((Nat.div_le_self Y d).trans hYX) hlogdiv
    hmul.isMultiplicativeOnPositiveNat hbound hnonpret hqdpos hAd
    ((b / d : ℕ) : ZMod (q / d))
    ((ZMod.isUnit_iff_coprime (b / d) (q / d)).2 hcoprime)
    hlength.1 hlength.2 (mrtDivided_cutoff hdpos hZ)
  simpa only [mrtResidueShortSum] using hunitbound

end

end Erdos67b

import ErdosProblems.Erdos67b.MRTPhasePartialSummation
import ErdosProblems.Erdos67b.MRTMajorArcBudget

/-! # The small-modulus major arcs for the actual fixed typical family -/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos67b

noncomputable section

theorem mrtMajorArc_phase_prefactor_le {H W q α β : ℝ} (hH : 0 < H) (hq : 0 < q)
    (happrox : |α - β| ≤ W / (H * q)) :
    1 + 2 * Real.pi * H * |α - β| ≤ 1 + 2 * Real.pi * W / q := by
  have hprod : H * |α - β| ≤ W / q := by
    calc
      _ ≤ H * (W / (H * q)) := mul_le_mul_of_nonneg_left happrox hH.le
      _ = _ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * Real.pi by positivity)
  simpa only [mul_assoc, mul_div_assoc] using add_le_add (le_refl (1 : ℝ)) hh

theorem mrtExists_logPower_majorArc_typical_firstMoment {ε rho R : ℝ}
    (hε : 0 < ε) (hrho : 0 < rho) (hR : 1 ≤ R) :
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
        ∀ a : ℤ, ∀ α : ℝ,
          |α - (a : ℝ) / q| ≤ mrtLogPowerWindow (Real.log (H : ℝ)) / ((H : ℝ) * q) →
        ∀ {Z : ℕ}, 2 * Y ≤ Z →
          (∑ n ∈ Finset.Ioc Y (2 * Y),
            ‖typicalModulatedShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n H α‖) ≤
              ε * H * Y := by
  obtain ⟨H₁, hH₁, hrat⟩ := mrtExists_logPower_rational_prefix_firstMoment hrho hR
  obtain ⟨H₂, hH₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually
      (mrtTendsto_logPower_majorArcError.eventually (gt_mem_nhds hε)))
  refine ⟨max H₁ H₂, hH₁.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hHH₁ : H₁ ≤ H := (le_max_left _ _).trans hH
  have hHpos : 0 < H := by omega
  have hHR : (0 : ℝ) < H := by exact_mod_cast hHpos
  obtain ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, hprefix⟩ := hrat H hHH₁
  refine ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret q hq hqw a α happrox Z hZ
  let W := mrtLogPowerWindow (Real.log (H : ℝ))
  let B : ℝ := 2 * (H : ℝ) * Y / W ^ 2 +
    (q : ℝ) * ((H : ℝ) * Y / W ^ 3 + 2 * H + Y)
  have hWpos : 0 < W := mrtLogPowerWindow_pos _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqWR : (q : ℝ) ≤ W :=
    (show (q : ℝ) ≤ (mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℝ) by
      exact_mod_cast hqw).trans (mrtLogPowerNatWindow_bounds hW).2.2
  have hHY : (H : ℝ) ≤ Y := by exact_mod_cast hY₀.trans hY
  have herror : mrtMajorArcNormalizedError W H ≤ ε := by
    have hh := hH₂ H ((le_max_right _ _).trans hH)
    simpa only [Real.exp_log hHR] using hh.le
  have hphase := mrtSum_norm_typical_phase_transfer
    (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
      (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z Y H f (α := α) hB
    (fun h hhH ↦ hprefix hA hY hYX hlog hmul hbound hnonpret hq hqw a hhH hZ)
  calc
    _ ≤ (1 + 2 * Real.pi * (H : ℝ) * |α - (a : ℝ) / q|) * B := hphase
    _ ≤ (1 + 2 * Real.pi * W / q) * B :=
      mul_le_mul_of_nonneg_right (mrtMajorArc_phase_prefactor_le hHR hqR happrox) hB
    _ = mrtMajorArcTypicalBudget W H Y q := rfl
    _ ≤ mrtMajorArcNormalizedError W H * H * Y :=
      mrtMajorArc_budget_le_normalized (by linarith only [hW]) hHR hHY
        (by exact_mod_cast hq) hqWR
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right herror hHR.le) (Nat.cast_nonneg Y)

end

end Erdos67b

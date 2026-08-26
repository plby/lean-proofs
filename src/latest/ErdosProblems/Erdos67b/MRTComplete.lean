import ErdosProblems.Erdos67b.MRTLogWindowEstimate
import ErdosProblems.Erdos67b.MRTFiniteLocalThresholds
import ErdosProblems.Erdos67b.MRTLogWindowParameters

/-! # The complete modulated short-interval input for logarithmic Elliott

The weighted-window assembly retains the original ambient pretentiousness
condition. Thresholds are selected in the order `Hmin`, `Hmax`, `A₀`.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtModulatedShortIntervalUnrestricted :
    ∀ ε : ℝ, 0 < ε →
      ∃ Hmin : ℕ, 10 ≤ Hmin ∧ ∀ Hmax : ℕ, Hmin ≤ Hmax →
        ∃ A₀ : ℕ, Hmax ≤ A₀ ∧ ∀ A X W H : ℕ,
          A₀ ≤ A → A ≤ W → W ≤ X → Hmin ≤ H → H ≤ Hmax →
          ∀ f : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f →
            (∀ n, 0 < n → ‖f n‖ = 1) → MRTNonpretentious f A X →
          ∀ α : ℝ, logAverageModulatedShortSum f X W H α ≤ ε * Real.log W := by
  intro ε hε
  let R : ℝ := max 1 (8 / ε)
  let δ : ℝ := ε / 16
  have hR : 1 ≤ R := le_max_left _ _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Hmin, hHmin, hfinite⟩ := mrtExists_uniform_finite_firstMoment hδ hR
  refine ⟨Hmin, hHmin, ?_⟩
  intro Hmax hHmax
  obtain ⟨N, hNmax, hlocal⟩ := hfinite Hmax hHmax
  let S := Finset.Icc Hmin Hmax
  let wmax := S.sup (fun H ↦ mrtLogPowerNatWindow (Real.log (H : ℝ)))
  let K := Nat.log 2 (max N (4 * wmax)) + 1
  have hK : max N (4 * wmax) ≤ 2 ^ K :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _).le
  obtain ⟨A₀, hA₀, hlogThreshold⟩ := mrtExists_logWindow_threshold K N hε
  have hNA : N ≤ A₀ := (le_max_left _ _).trans hA₀
  have hA4 : 4 ≤ A₀ := (le_max_right _ _).trans hA₀
  refine ⟨A₀, hNmax.trans hNA, ?_⟩
  intro A X W H hA hAW hWX hHlo hHhi f hmul hunit hnonpret α
  have hWpos : 0 < W := by omega
  have hHpos : 0 < H := by omega
  have hH4 : 4 ≤ H := by omega
  let w := mrtLogPowerNatWindow (Real.log (H : ℝ))
  have hw : 0 < w := mrtLogPowerNatWindow_pos_of_four_le hH4
  have hHS : H ∈ S := Finset.mem_Icc.2 ⟨hHlo, hHhi⟩
  have hwwmax : w ≤ wmax := by
    dsimp only [w, wmax]
    exact Finset.le_sup (f := fun h : ℕ ↦ mrtLogPowerNatWindow (Real.log (h : ℝ))) hHS
  have hKw : max N (4 * w) ≤ 2 ^ K :=
    (max_le_max (le_refl N) (Nat.mul_le_mul_left 4 hwwmax)).trans hK
  have hf : ∀ n, 0 < n → ‖f n‖ ≤ 1 := fun n hn ↦ (hunit n hn).le
  obtain ⟨hlogW, hconstant⟩ := hlogThreshold W (hA.trans hAW)
  have hrough : logAverageModulatedShortSum f X W H α ≤
      (K : ℝ) + 1 + (2 / R + 4 * δ) * Real.log W := by
    apply mrtLogAverage_le_of_local_firstMoment hWpos hWX hHpos hw hR hδ.le hlogW hKw f α hf
    intro Y hY hYX hscale
    exact hlocal H hHlo hHhi (hNA.trans hA) hY hYX hscale hmul hf hnonpret α
  have hcoefficient : 2 / R + 4 * δ ≤ ε / 2 := mrtLogWindow_small_coefficient hε
  calc
    _ ≤ (K : ℝ) + 1 + (2 / R + 4 * δ) * Real.log W := hrough
    _ ≤ (ε / 2) * Real.log W + (ε / 2) * Real.log W :=
      add_le_add hconstant (mul_le_mul_of_nonneg_right hcoefficient (zero_le_one.trans hlogW))
    _ = _ := by ring

theorem mrtModulatedShortIntervalInput : MRTModulatedShortIntervalInput := by
  intro ε hε
  obtain ⟨Hmin, hHmin, hbound⟩ := mrtModulatedShortIntervalUnrestricted ε hε
  refine ⟨Hmin, hHmin, ?_⟩
  intro Hmax hHmax
  obtain ⟨A₀, hA₀, hboundA⟩ := hbound Hmax hHmax
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W H hA hAW hWX _hrestricted hHlo hHhi f hmul hunit hnonpret α
  exact hboundA A X W H hA hAW hWX hHlo hHhi f hmul hunit hnonpret α

end

end Erdos67b

import ErdosProblems.Erdos67b.MRTDyadicMinorArcSaving
import ErdosProblems.Erdos67b.MRTMinorArcLimits

/-! # The full minor-arc first-moment bound for the actual typical short sums -/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos67b

noncomputable section

theorem mrtExists_logPower_minorArc_typical_firstMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      ∀ (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (Z Y : ℕ) (f : ℕ → ℂ),
        mrtLogPowerNatWindow (Real.log (H : ℝ)) ^ 200 ≤ I.1 →
        I.2 ≤ H / mrtLogPowerNatWindow (Real.log (H : ℝ)) ^ 3 →
        I ∈ blocks →
        (∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J)) →
        H ≤ Y → IsMultiplicativeOnPositiveNat f → (∀ r, 0 < r → ‖f r‖ ≤ 1) →
        ∀ (q : ℕ) (a : ℤ) (α : ℝ),
          mrtLogPowerNatWindow (Real.log (H : ℝ)) ≤ q →
          q ≤ H / mrtLogPowerNatWindow (Real.log (H : ℝ)) + 1 →
          Nat.Coprime a.natAbs q →
          |α - (a : ℝ) / q| ≤ (mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℝ) /
            ((H : ℝ) * q) →
          (∑ n ∈ Finset.Ioc Y (2 * Y), ‖typicalModulatedShortSum blocks Z f n H α‖) ≤
            ε * H * Y := by
  obtain ⟨C, hC, hsaving⟩ := mrtExists_dyadicRamare_minorArc_saving
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (mrtEventually_minorArc_budgets C hε))
  refine ⟨max 10 H₁, le_max_left _ _, ?_⟩
  intro H hH
  have hHpos : 0 < H := by omega
  obtain ⟨hlog, hW, hmain, herror⟩ := hH₁ H ((le_max_right _ _).trans hH)
  refine ⟨hW, ?_⟩
  intro blocks I Z Y f hIlo hIhi hI hdisj hHY hmul hf q a α hwq hq ha hα
  let w := mrtLogPowerNatWindow (Real.log (H : ℝ))
  have hw : 2 ≤ w := (mrtLogPowerNatWindow_bounds hW).1
  have hwpow : 0 < w ^ 200 := pow_pos (by omega) _
  have hIpos : 0 < I.1 := hwpow.trans_le hIlo
  obtain ⟨θ, hθ, htyp⟩ := mrtTypical_firstMoment_le_dual_ramare hI hIpos Z H Y hHY f α hmul hf
  let D : ℂ := ∑ n ∈ Finset.Ioc Y (2 * Y),
    θ n * mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α
  have hfour : ‖D‖ ^ 4 ≤ (ε / 2 * H * Y) ^ 4 := by
    calc
      _ ≤ C * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H ^ 5 / w :=
        hsaving H w q a α hlog hw hwq hq ha hα blocks I Z Y f θ hIlo hIhi hHY
          hdisj hf (fun n _ ↦ hθ n)
      _ = ((H : ℝ) ^ 4 * (Y : ℝ) ^ 4) * (C * Real.log H ^ 5 / w) := by ring
      _ ≤ ((H : ℝ) ^ 4 * (Y : ℝ) ^ 4) * (ε / 2) ^ 4 :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = _ := by ring
  have hnorm : ‖D‖ ≤ ε / 2 * H * Y := by
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).1 hfour
  have herr : 12 * (H : ℝ) * Y / I.1 ≤ ε / 2 * H * Y := by
    have hden : ((w : ℝ) ^ 200) ≤ I.1 := by exact_mod_cast hIlo
    have hinv : 12 / (I.1 : ℝ) ≤ ε / 2 :=
      (div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hwpow) hden).trans herror
    calc
      _ = (12 / (I.1 : ℝ)) * H * Y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg H)) (Nat.cast_nonneg Y)
  calc
    _ ≤ ‖D‖ + 12 * H * Y / I.1 := htyp
    _ ≤ ε / 2 * H * Y + ε / 2 * H * Y := add_le_add hnorm herr
    _ = _ := by ring

end

end Erdos67b

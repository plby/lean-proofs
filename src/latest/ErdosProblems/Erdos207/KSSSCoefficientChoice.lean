/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationStateDrift
import ErdosProblems.Erdos207.KSSSTaylorSourceScale
import ErdosProblems.Erdos207.KSSSEnvelopeExponent
import ErdosProblems.Erdos207.DyadicPowerScale

/-! # Fixed envelope and scale choices for the actual indexed KSSS coefficients -/

namespace Erdos207

open Finset

noncomputable section

def ksssIndexedConfigurationDriftCoefficient (q : ℕ) (b : ℕ → ℝ) (i : CrudeOrderIndex q 4) : ℝ :=
  if i.chosen = 0 then ksssConfigurationZeroDriftCoefficient q b (i.order - 3)
  else ksssConfigurationSuccDriftCoefficient q b (i.order - 3) (i.chosen - 1)

theorem exists_ksss_indexed_envelope_exponent (q : ℕ) (b : ℕ → ℝ) :
    ∃ B : ℕ, 4 * q ≤ B ∧
      ksssPairDriftCoefficient q b + ksssPairTaylorCoefficient (ksssOrders q) b ≤ 3 * (B : ℝ) ∧
      ∀ i : CrudeOrderIndex q 4, ksssIndexedConfigurationDriftCoefficient q b i +
        ksssConfigurationTaylorCoefficient (ksssOrders q) b (i.order - 3) i.chosen ≤ 3 * (B : ℝ) / 2 :=
  exists_coupled_envelope_exponent q
    (ksssPairDriftCoefficient q b + ksssPairTaylorCoefficient (ksssOrders q) b)
    (fun i : CrudeOrderIndex q 4 ↦ ksssIndexedConfigurationDriftCoefficient q b i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) b (i.order - 3) i.chosen)

theorem exists_nat_uniform_finite_bound {I : Type*} [Fintype I]
    (c : ℝ) (f : I → ℝ) (Nmin : ℕ) :
    ∃ T : ℕ, Nmin ≤ T ∧ c ≤ (T : ℝ) ∧ ∀ i, f i ≤ (T : ℝ) := by
  classical
  let S : ℝ := ∑ i, |f i|
  have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hN : (0 : ℝ) ≤ Nmin := Nat.cast_nonneg _
  obtain ⟨T, hT⟩ := exists_nat_ge ((Nmin : ℝ) + |c| + S)
  refine ⟨T, ?_, ?_, ?_⟩
  · have hb : (Nmin : ℝ) ≤ T := by linarith [abs_nonneg c]
    exact_mod_cast hb
  · have hc := le_abs_self c
    linarith
  · intro i
    have hi : |f i| ≤ S := single_le_sum (fun j _ ↦ abs_nonneg (f j)) (mem_univ i)
    have hf := le_abs_self (f i)
    linarith [abs_nonneg c]

structure KSSSPowerCoefficientBounds (q : ℕ) (b : ℕ → ℝ) (B : ℕ) (t : ℝ) : Prop where
  poisson : Real.exp (∑ d ∈ ksssOrders q, b d) ≤ t
  envelope : 6 * (B : ℝ) * 2 ^ B ≤ t
  pair : 9 * (ksssThreatCoefficient (ksssOrders q) b + 1) + ksssPairDriftCoefficient q b ≤ t
  threat : 12 * (ksssThreatCoefficient (ksssOrders q) b + ((q : ℝ) + 5)) ≤ t
  pairTaylor : ksssPairTaylorCoefficient (ksssOrders q) b ≤ t
  configuration : ∀ i : CrudeOrderIndex q 4,
    ((i.order - 3).choose i.chosen : ℝ) * b (i.order - 3) + 1 ≤ t ∧
      ksssConfigurationTaylorCoefficient (ksssOrders q) b (i.order - 3) i.chosen ≤ t

theorem KSSSPowerCoefficientBounds.mono {q B : ℕ} {b : ℕ → ℝ} {t u : ℝ}
    (h : KSSSPowerCoefficientBounds q b B t) (htu : t ≤ u) : KSSSPowerCoefficientBounds q b B u :=
  ⟨h.poisson.trans htu, h.envelope.trans htu, h.pair.trans htu, h.threat.trans htu,
    h.pairTaylor.trans htu, fun i ↦ ⟨(h.configuration i).1.trans htu, (h.configuration i).2.trans htu⟩⟩

theorem exists_ksss_power_coefficient_threshold (q B Nmin : ℕ) (b : ℕ → ℝ) :
    ∃ T : ℕ, Nmin ≤ T ∧ KSSSPowerCoefficientBounds q b B (T : ℝ) := by
  let c := max (Real.exp (∑ d ∈ ksssOrders q, b d))
    (max (6 * (B : ℝ) * 2 ^ B)
      (max (9 * (ksssThreatCoefficient (ksssOrders q) b + 1) + ksssPairDriftCoefficient q b)
        (max (12 * (ksssThreatCoefficient (ksssOrders q) b + ((q : ℝ) + 5)))
          (ksssPairTaylorCoefficient (ksssOrders q) b))))
  let f := fun i : CrudeOrderIndex q 4 ↦ max (((i.order - 3).choose i.chosen : ℝ) * b (i.order - 3) + 1)
    (ksssConfigurationTaylorCoefficient (ksssOrders q) b (i.order - 3) i.chosen)
  obtain ⟨T, hN, hc, hf⟩ := exists_nat_uniform_finite_bound c f Nmin
  obtain ⟨hpoisson, hrest⟩ := max_le_iff.mp hc
  obtain ⟨henvelope, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hpair, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hthreat, hTaylor⟩ := max_le_iff.mp hrest
  exact ⟨T, hN, ⟨hpoisson, henvelope, hpair, hthreat, hTaylor, fun i ↦ max_le_iff.mp (hf i)⟩⟩

theorem eventually_ksss_power_coefficient_bounds
    (q B R Nmin : ℕ) (b : ℕ → ℝ) (hR : 0 < R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nmin ≤ dyadicPowerScale R n ∧ KSSSPowerCoefficientBounds q b B (dyadicPowerScale R n : ℝ) := by
  obtain ⟨T, hmin, hT⟩ := exists_ksss_power_coefficient_threshold q B Nmin b
  obtain ⟨N, hN⟩ := eventually_le_dyadicPowerScale hR T
  refine ⟨N, fun n hn ↦ ⟨hmin.trans (hN n hn), hT.mono ?_⟩⟩
  exact_mod_cast hN n hn

end

end Erdos207

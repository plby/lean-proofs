/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerAmbientBudgets
import ErdosProblems.Erdos207.KSSSDyadicPairBounds
import ErdosProblems.Erdos207.DyadicCrudeCutoffs
import ErdosProblems.Erdos207.CrudeStateConsequences
import ErdosProblems.Erdos207.KSSSIndexedThreat

/-! # Actual overlap and redundant-gain budgets from the power hierarchy -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem ksssPairTrajectory_power_lower
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ) (b : ℕ)
    (hE : 0 < E) (hTime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hN : 0 ≤ N) (ht : 0 < t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (hratio : N / t ^ b ≤ A / E) (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ t) :
    N / t ^ (3 * b + 1) ≤ ksssPairTrajectory orders a E A time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hr := ksssPoisson_exp_neg_ge_inverse_scale orders a coeff E time t ha hab hTime
    (by linarith) hexp
  calc
    _ ≤ 3 * (A / E) * ksssEdgeDensity E time ^ 2 * Real.exp (-ksssPoissonExponent orders a time) :=
      pair_polynomial_power_lower N t _ _ _ b hN ht hfloor hratio hr
    _ = _ := by rw [ksssPairTrajectory_source orders a E A time hE.ne' hp.ne']; ring

theorem ksssConfigurationScale_power_lower
    (E A time N t : ℝ) (b : ℕ) (hE : 0 < E) (hclock : 3 * time < E)
    (hN : 0 ≤ N) (ht : 0 < t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time) (hratio : N / t ^ b ≤ A / E) :
    N / t ^ (3 * b) ≤ ksssConfigurationScale E A time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hratio0 : 0 ≤ A / E := (div_nonneg hN (pow_nonneg ht.le b)).trans hratio
  calc
    _ = (1 / t ^ b) ^ 2 * (N / t ^ b) := by
      have hexp : 3 * b = b * 2 + b := by omega
      rw [hexp, pow_add, pow_mul]
      ring
    _ ≤ ksssEdgeDensity E time ^ 2 * (A / E) := by gcongr
    _ = _ := by unfold ksssConfigurationScale; ring

theorem ksssConfigurationErrorEnvelope_power_lower
    (E A time N t : ℝ) (a b B z : ℕ) (hE : 0 < E) (hTime : 0 ≤ time)
    (hclock : 3 * time < E) (hN : 0 ≤ N) (ht : 0 < t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time) (hratio : N / t ^ b ≤ A / E) :
    N ^ (z + 1) / t ^ (a + 3 * b * z) ≤
      ksssConfigurationErrorEnvelope E A (N / t ^ a) B z time := by
  have hw := ksssConfigurationScale_power_lower E A time N t b hE hclock hN ht hfloor hratio
  have he := ksssErrorEnvelope_ge_scale E (N / t ^ a) time B hE (by positivity) hTime hclock
  have he0 : 0 ≤ ksssErrorEnvelope E (N / t ^ a) B time :=
    (div_nonneg hN (pow_nonneg ht.le a)).trans he
  calc
    _ = (N / t ^ a) * (N / t ^ (3 * b)) ^ z := by
      rw [pow_add, pow_succ, div_pow, pow_mul]
      ring
    _ ≤ ksssErrorEnvelope E (N / t ^ a) B time * ksssConfigurationScale E A time ^ z := by gcongr
    _ = _ := rfl

theorem CrudeStateBounds.dyadic_closed_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (ht : 16 ≤ t) {T T' : TripleOn V} (hT : T ∈ S.available) (hT' : T' ∈ S.available)
    (hdis : (T.1 ∩ T'.1).card ≤ 1) :
    (greedyClosedThreats F S T ∩ greedyClosedThreats F S T').card ≤ t ^ (k + 1) := by
  have hraw := h.closed_inter hS hpack hT hT' hdis
  dsimp only [dyadicCrudeThresholds] at hraw
  have hreal : ((greedyClosedThreats F S T ∩ greedyClosedThreats F S T').card : ℝ) ≤
      9 + 6 * (t : ℝ) ^ k + (t : ℝ) ^ k := by
    exact_mod_cast hraw
  have hupper := power_crude_overlap_le (t : ℝ) k (by exact_mod_cast ht)
  have hbound : ((greedyClosedThreats F S T ∩ greedyClosedThreats F S T').card : ℝ) ≤
      (t : ℝ) ^ (k + 1) := by linarith only [hreal, hupper]
  exact_mod_cast hbound

theorem CrudeStateBounds.dyadic_redundant_gain_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k R s b B : ℕ}
    {a coeff : ℕ → ℝ} {E A time : ℝ}
    (h : CrudeStateBounds (minimalForbiddenFamily F) S q (dyadicCrudeThresholds V t k))
    (j c : ℕ) {T : TripleOn V} (hT : T ∈ S.available) (hj : j ≤ q) (hc : c + 5 ≤ j)
    (hE : 0 < E) (hTime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d) (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hN : 1 ≤ Fintype.card V) (ht : 1 ≤ t) (hscale : t ^ R ≤ Fintype.card V)
    (hconst : 2 ^ q ≤ t) (hgap : k + s + 3 * b * (j - c - 4) + 2 ≤ R)
    (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time)
    (hratio : (Fintype.card V : ℝ) / (t : ℝ) ^ b ≤ A / E)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, coeff d) ≤ t) :
    (∑ D ∈ greedyConfigurationClass (forbiddenFamilyOfOrder (minimalForbiddenFamily F) j) S T c,
      ((greedyConfigurationRedundantWitnesses (minimalForbiddenFamily F) S D).card : ℝ)) ≤
      ksssPairTrajectory (ksssOrders q) a E A time *
        ksssConfigurationErrorEnvelope E A ((Fintype.card V : ℝ) / (t : ℝ) ^ s)
          B (j - 4 - (c + 1)) time := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hN1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hcount := sum_redundantWitnesses_le_of_crude_minimal F S q _ h j c hT hj (by omega)
  dsimp only [dyadicCrudeThresholds] at hcount
  have hcountR : (∑ D ∈ greedyConfigurationClass (forbiddenFamilyOfOrder (minimalForbiddenFamily F) j) S T c,
      ((greedyConfigurationRedundantWitnesses (minimalForbiddenFamily F) S D).card : ℝ)) ≤
      (Fintype.card V + 1 : ℝ) ^ (j - c - 4) * (t : ℝ) ^ k := by
    exact_mod_cast hcount
  have hx := ksssPairTrajectory_power_lower (ksssOrders q) a coeff E A time (Fintype.card V) t b
    hE hTime hclock ha hab (by positivity) htpos hfloor hratio hexp
  have hh := ksssConfigurationErrorEnvelope_power_lower E A time (Fintype.card V) t s b B
    (j - c - 5) hE hTime hclock (by positivity) htpos hfloor hratio
  have hdeg : j - c - 4 = (j - c - 5) + 1 := by omega
  have hdeg' : j - 4 - (c + 1) = j - c - 5 := by omega
  rw [hdeg] at hcountR
  rw [hdeg']
  exact hcountR.trans (power_configuration_gain_budget (Fintype.card V) t _ _ R q (j - c - 5) k s b
    htR hN1 (by exact_mod_cast hscale) (by exact_mod_cast hconst) (by omega)
    (by simpa only [← hdeg] using hgap) hx hh)

end

end Erdos207

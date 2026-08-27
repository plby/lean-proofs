/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialRootPerturbation
import ErdosProblems.Erdos207.InitialRootPowerArithmetic

/-! # Initial rooted regularity from the explicit perturbation budgets -/

namespace Erdos207

open Finset

noncomputable section

theorem initialRootErrorBound_le_power
    {V : Type*} [Fintype V] [DecidableEq V] (q j u : ℕ) (bank ambient : TripleSystemOn V) (t : ℝ)
    (hj : 4 ≤ j) (hjq : j ≤ q) (hN : 1 ≤ (Fintype.card V : ℝ)) (ht : 3 ≤ t)
    (hconst : (2 : ℝ) ^ q ≤ t)
    (hbankCoefficient : (pairExactBankExtensionCoefficient q bank : ℝ) ≤ t ^ u)
    (hunavailable : (((univ : TripleSystemOn V) \ ambient).card : ℝ) *
      pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) ≤ t ^ u * Fintype.card V)
    (hbankVertices : ((verticesOn bank).card : ℝ) * (2 ^ (j ^ 3) * (j + 1) : ℕ) ≤ t ^ u) :
    (initialRootErrorBound q j bank ambient : ℝ) ≤ (Fintype.card V : ℝ) ^ (j - 4) * t ^ (u + 2) := by
  by_cases hj4 : j = 4
  · subst j
    simp only [initialRootErrorBound, ite_true, initialRootExtraBound,
      Nat.sub_self, pow_zero, mul_one, one_mul]
    exact hbankCoefficient.trans (pow_le_pow_right₀ (by linarith) (by omega))
  · have h := initial_three_errors_power (Fintype.card V) t
      (pairExactBankExtensionCoefficient q bank)
      ((((univ : TripleSystemOn V) \ ambient).card : ℝ) * pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V))
      (((verticesOn bank).card : ℝ) * (2 ^ (j ^ 3) * (j + 1) : ℕ))
      q u (j - 4) hN ht hconst (by omega) (by omega) hbankCoefficient hunavailable hbankVertices
    have hz : j - 4 - 1 = j - 5 := by omega
    simpa only [initialRootErrorBound, if_neg hj4, initialRootExtraBound, initialRootDeletionBound,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hz, mul_assoc, add_assoc] using h

theorem initial_root_configuration_power_regularity
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j u R s b : ℕ) (bank ambient : TripleSystemOn V) (T : TripleOn V) (hT : T ∈ ambient)
    (E A t : ℝ) (hA : 0 < A)
    (hj : 4 ≤ j) (hjq : j ≤ q) (hdisjoint : Disjoint ambient bank)
    (hlegal : ∀ U ∈ ambient, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ U)
    (hN : 1 ≤ (Fintype.card V : ℝ)) (ht : 3 ≤ t) (hconst : (2 : ℝ) ^ q ≤ t)
    (hbankCoefficient : (pairExactBankExtensionCoefficient q bank : ℝ) ≤ t ^ u)
    (hunavailable : (((univ : TripleSystemOn V) \ ambient).card : ℝ) *
      pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) ≤ t ^ u * Fintype.card V)
    (hbankVertices : ((verticesOn bank).card : ℝ) * (2 ^ (j ^ 3) * (j + 1) : ℕ) ≤ t ^ u)
    (hscale : t ^ R ≤ (Fintype.card V : ℝ)) (hgap : u + 2 + s + b * q ≤ R)
    (hratio : (Fintype.card V : ℝ) / t ^ b ≤ A / E) :
    |(((forbiddenFamilyOfOrder (initialRestrictedAbsorberFamily q bank ambient) j).filter
      (fun C ↦ T ∈ C)).card : ℝ) - initialErdosTrajectoryCoefficient V A (j - 3) * A ^ (j - 3)| ≤
      (1 / t ^ s) * (A / E) ^ (j - 3) := by
  have herr := (initial_root_configuration_target_error q j bank ambient T hT hj hjq hdisjoint hlegal A hA).trans
    (initialRootErrorBound_le_power q j u bank ambient t hj hjq hN ht hconst hbankCoefficient hunavailable hbankVertices)
  have hz : j - 3 - 1 = j - 4 := by omega
  exact initial_error_power_budget (Fintype.card V) t (A / E) _ q R (j - 3) (u + 2) s b
    (Nat.cast_nonneg _) (by linarith) (by omega) (by omega) hscale hgap hratio
    (by simpa only [hz] using herr)

end

end Erdos207

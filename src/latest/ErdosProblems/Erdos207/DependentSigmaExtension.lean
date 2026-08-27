/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightSystem

/-!
# Extension bounds for a finite dependent union

The localized rooted families are naturally indexed first by an ordered
vertex pair and then by a witness over that pair.  These lemmas combine the
pairwise extension estimates into one estimate on the dependent sum and
recover each component from the combined estimate.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem hasExtensionBound_sigma
    {W E : Type*} [DecidableEq W] [Fintype E]
    {I : E → Type*} [∀ e, Fintype (I e)]
    (F : ∀ e, I e → Finset W) (pi : W → ℝ≥0) (kappa : ℝ≥0)
    (hF : ∀ e, HasExtensionBound (F e) pi kappa) :
    HasExtensionBound (fun z : Σ e, I e ↦ F z.1 z.2) pi
      ((Fintype.card E : ℝ≥0) * kappa) := by
  intro A
  unfold extensionWeight
  change (∑ z : Σ e, I e,
    if A ⊆ F z.1 z.2 then setWeight pi (F z.1 z.2 \ A) else 0) ≤ _
  rw [Fintype.sum_sigma]
  calc
    (∑ e, ∑ i,
      (if A ⊆ F e i then setWeight pi (F e i \ A) else 0)) ≤
        ∑ _e : E, kappa := by
      apply sum_le_sum
      intro e _he
      exact hF e A
    _ = (Fintype.card E : ℝ≥0) * kappa := by simp

theorem HasExtensionBound.sigma_component
    {W E : Type*} [DecidableEq W] [Fintype E] [DecidableEq E]
    {I : E → Type*} [∀ e, Fintype (I e)]
    (F : ∀ e, I e → Finset W) (pi : W → ℝ≥0) {kappa : ℝ≥0}
    (hF : HasExtensionBound (fun z : Σ e, I e ↦ F z.1 z.2) pi kappa)
    (e : E) : HasExtensionBound (F e) pi kappa := by
  intro A
  have hall := hF A
  unfold extensionWeight at hall ⊢
  change (∑ z : Σ e, I e,
    if A ⊆ F z.1 z.2 then setWeight pi (F z.1 z.2 \ A) else 0) ≤
      kappa at hall
  rw [Fintype.sum_sigma] at hall
  apply le_trans ?_ hall
  exact Finset.single_le_sum
    (fun e' _he' ↦ show (0 : ℝ≥0) ≤
      ∑ i, (if A ⊆ F e' i then setWeight pi (F e' i \ A) else 0) from
        zero_le)
    (mem_univ e)

end

end Erdos207

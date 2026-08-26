/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos19.Pippenger.PippengerSpencer
import ErdosProblems.Erdos19.Pippenger.FiniteProductBoundedDifferences

/-!
# Whole-batch concentration for Pippenger--Spencer

This downstream module applies finite-product McDiarmid concentration to
`batchResidualDegree`.  A coordinate is one whole randomized matching trial,
so the bounded-differences constant is one per trial.
-/

open Finset Real
open scoped BigOperators

namespace Erdos76

noncomputable section

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Lower-tail McDiarmid bound for a residual vertex degree after a batch of
independent, not necessarily identically distributed trials. -/
theorem lowerTailMass_batchResidualDegree_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ)
    (hw₀ : ∀ j S, 0 ≤ w j S) (hw : ∀ j, ∑ S, w j S = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteProduct.lowerTailMass w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
        (FiniteProduct.expectation w
            (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) - t) ≤
      exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  have hcard : (0 : ℝ) < Fintype.card J := by
    exact_mod_cast Fintype.card_pos
  have hsquares :
      ∑ _j : J, ((1 : ℝ) ^ 2) = (Fintype.card J : ℝ) := by simp
  have htail := FiniteProduct.lowerTailMass_le_mcdiarmid w
    (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
    (fun _ : J ↦ (1 : ℝ)) hw₀ hw
    (H.batchResidualDegree_hasBoundedDifferences v) ht
    (by simpa [hsquares] using hcard)
  simpa [hsquares] using htail

/-- Sum of the upper and lower residual-degree tail masses. -/
theorem twoSidedTailMass_batchResidualDegree_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ)
    (hw₀ : ∀ j S, 0 ≤ w j S) (hw : ∀ j, ∑ S, w j S = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteProduct.upperTailMass w
          (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
          (FiniteProduct.expectation w
              (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t) +
        FiniteProduct.lowerTailMass w
          (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
          (FiniteProduct.expectation w
              (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) - t) ≤
      2 * exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  calc
    _ ≤ exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) +
          exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) :=
      add_le_add (H.upperTailMass_batchResidualDegree_le v w hw₀ hw ht)
        (H.lowerTailMass_batchResidualDegree_le v w hw₀ hw ht)
    _ = 2 * exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by ring

/-- Explicit mass of the two-sided residual-degree bad event. -/
def batchResidualDegreeBadMass
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ) (t : ℝ) : ℝ :=
  ∑ X with t ≤
      |(H.batchResidualDegree X v : ℝ) -
        FiniteProduct.expectation w
          (fun Y : J → Finset E ↦ (H.batchResidualDegree Y v : ℝ))|,
    FiniteProduct.mass w X

/-- The explicit two-sided bad-event mass is bounded by the sum of the two
one-sided McDiarmid tails. -/
theorem batchResidualDegreeBadMass_le_twoSidedTailMass
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ) (hw₀ : ∀ j S, 0 ≤ w j S) (t : ℝ) :
    H.batchResidualDegreeBadMass v w t ≤
      FiniteProduct.upperTailMass w
          (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
          (FiniteProduct.expectation w
              (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t) +
        FiniteProduct.lowerTailMass w
          (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
          (FiniteProduct.expectation w
              (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) - t) := by
  let F : (J → Finset E) → ℝ := fun X ↦ H.batchResidualDegree X v
  let m : ℝ := FiniteProduct.expectation w F
  change (∑ X with t ≤ |F X - m|, FiniteProduct.mass w X) ≤
    FiniteProduct.upperTailMass w F (m + t) +
      FiniteProduct.lowerTailMass w F (m - t)
  rw [Finset.sum_filter]
  calc
    (∑ X, if t ≤ |F X - m| then FiniteProduct.mass w X else 0) ≤
        ∑ X, ((if m + t ≤ F X then FiniteProduct.mass w X else 0) +
          if F X ≤ m - t then FiniteProduct.mass w X else 0) := by
      apply sum_le_sum
      intro X _
      by_cases hbad : t ≤ |F X - m|
      · rcases le_abs.mp hbad with hupper | hlower
        · have hupper' : m + t ≤ F X := by linarith
          simp only [hbad, hupper', if_true]
          split_ifs <;> simp [FiniteProduct.mass_nonneg w hw₀ X]
        · have hlower' : F X ≤ m - t := by linarith
          simp only [hbad, hlower', if_true]
          split_ifs <;> simp [FiniteProduct.mass_nonneg w hw₀ X]
      · simp only [hbad, if_false]
        split_ifs <;> simp [FiniteProduct.mass_nonneg w hw₀ X]
    _ = FiniteProduct.upperTailMass w F (m + t) +
          FiniteProduct.lowerTailMass w F (m - t) := by
      rw [sum_add_distrib]
      simp only [FiniteProduct.upperTailMass, FiniteProduct.lowerTailMass,
        ← Finset.sum_filter]

/-- Explicit two-sided bad-event McDiarmid estimate in the form consumed by
the finite local lemma. -/
theorem batchResidualDegreeBadMass_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ)
    (hw₀ : ∀ j S, 0 ≤ w j S) (hw : ∀ j, ∑ S, w j S = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    H.batchResidualDegreeBadMass v w t ≤
      2 * exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) :=
  (H.batchResidualDegreeBadMass_le_twoSidedTailMass v w hw₀ t).trans
    (H.twoSidedTailMass_batchResidualDegree_le v w hw₀ hw ht)

/-- The two-sided estimate rewritten directly as `FiniteLocalLemma.eventMass`. -/
theorem eventMass_batchResidualDegree_bad_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ)
    (hw₀ : ∀ j S, 0 ≤ w j S) (hw : ∀ j, ∑ S, w j S = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteLocalLemma.eventMass (FiniteProduct.mass w)
        (fun X : J → Finset E ↦ t ≤
          |(H.batchResidualDegree X v : ℝ) -
            FiniteProduct.expectation w
              (fun Y : J → Finset E ↦ (H.batchResidualDegree Y v : ℝ))|) ≤
      2 * exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  rw [FiniteLocalLemma.eventMass, ← Finset.sum_filter]
  exact H.batchResidualDegreeBadMass_le v w hw₀ hw ht

/-- A threshold at least `t` above the mean has at most the usual upper-tail
mass.  This is the one-sided event form used for residual-degree LLL events. -/
theorem upperTailMass_batchResidualDegree_threshold_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ)
    (hw₀ : ∀ j S, 0 ≤ w j S) (hw : ∀ j, ∑ S, w j S = 1)
    {t B : ℝ} (ht : 0 ≤ t)
    (hB : FiniteProduct.expectation w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t ≤ B) :
    FiniteProduct.upperTailMass w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) B ≤
      exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  apply (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
    (H.upperTailMass_batchResidualDegree_le v w hw₀ hw ht)
  · intro X hX
    simp only [mem_filter, mem_univ, true_and] at hX ⊢
    exact hB.trans hX
  · intro X _ _
    exact FiniteProduct.mass_nonneg w hw₀ X

/-- Identically distributed specialization of the one-sided LLL event.  The
left-hand side unfolds to the explicit sum of `productMass w X` over batches
whose residual degree is at least `B`. -/
theorem productUpperTailMass_batchResidualDegree_threshold_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : Finset E → ℝ)
    (hw₀ : ∀ S, 0 ≤ w S) (hw : ∑ S, w S = 1)
    {t B : ℝ} (ht : 0 ≤ t)
    (hB : FiniteProduct.productExpectation w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t ≤ B) :
    FiniteProduct.productUpperTailMass w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) B ≤
      exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  change FiniteProduct.upperTailMass (fun _ : J ↦ w)
      (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) B ≤
    exp (-2 * t ^ 2 / (Fintype.card J : ℝ))
  apply H.upperTailMass_batchResidualDegree_threshold_le v (fun _ ↦ w)
    (fun _ ↦ hw₀) (fun _ ↦ hw) ht
  change FiniteProduct.productExpectation w
      (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t ≤ B
  exact hB

/-- Identically distributed threshold estimate in the exact `eventMass`
shape used as a finite-LLL marginal hypothesis. -/
theorem eventMass_product_batchResidualDegree_ge_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : Finset E → ℝ)
    (hw₀ : ∀ S, 0 ≤ w S) (hw : ∑ S, w S = 1)
    {t B : ℝ} (ht : 0 ≤ t)
    (hB : FiniteProduct.productExpectation w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t ≤ B) :
    FiniteLocalLemma.eventMass (FiniteProduct.productMass w)
        (fun X : J → Finset E ↦ B ≤ (H.batchResidualDegree X v : ℝ)) ≤
      exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  rw [FiniteLocalLemma.eventMass, ← Finset.sum_filter]
  exact H.productUpperTailMass_batchResidualDegree_threshold_le v w hw₀ hw ht hB

end FiniteHypergraph

end

end Erdos76

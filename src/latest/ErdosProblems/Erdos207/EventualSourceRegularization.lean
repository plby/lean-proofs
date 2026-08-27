/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualRegularizationAllInputs
import ErdosProblems.Erdos207.SourceRegularizationAllOrders

/-! # All forbidden orders are regularizable under fixed power-scale hypotheses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_exists_source_regularization_all_orders
    (q K Y D A v w L R : ℕ) (C : ℝ≥0) (hC : 0 < C)
    (hD : K + 1 ≤ D) (hA : D + 1 ≤ A) (hv : K + 1 ≤ v)
    (hLmass : w + 2 ≤ L) (hLdensity : w * (q - 3) + 1 ≤ L)
    (hLsquare : 2 * D ≤ L) (hLy : D + Y ≤ L) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I] {ell : ℕ},
      ∀ (W : Vortex V ell) (e : I ↪ TripleOn V),
      (∀ i, (e i).1 ⊆ W.U (Fin.last ell)) →
      ∀ (localFamily : ℕ → Finset (Finset I)) (F : ℕ → ForbiddenFamilyOn V)
        (y z B : ℕ → ℝ≥0) (sigma : ℝ≥0),
      (∀ j ∈ Icc 4 q, ∀ E ∈ localFamily j, E.card = j - 2) →
      (∀ j ∈ Icc 4 q, SourceVortexWellSpread W j (F j) (y j) (z j)) →
      t ^ L ≤ W.terminalSize → Fintype.card V ≤ t ^ R →
      1 / (t : ℝ≥0) ^ w ≤ sigma → sigma ≤ 1 / (t : ℝ≥0) ^ v →
      (∀ j ∈ Icc 4 q, B j ≤ (t : ℝ≥0) ^ K) →
      (∀ j ∈ Icc 4 q, y j ≤ (t : ℝ≥0) ^ Y) →
      sigma * (W.terminalSize : ℝ≥0) ^ 3 / C ≤ Fintype.card I →
      (∀ j ∈ Icc 4 q, (finiteHypergraphMaxDegree (localFamily j) : ℝ≥0) ≤
        B j * sigma ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3)) →
      ∃ Lstar : ℕ → Finset (Finset I), ∃ Fsup : ℕ → ForbiddenFamilyOn V,
        ∀ j ∈ Icc 4 q,
          SourceRegularizationOrderResult W e j (8192 * t) (localFamily j)
            ((Ico 4 j).biUnion Lstar) (F j) (y j + (t : ℝ≥0) ^ A) (z j + 3 * (t : ℝ≥0) ^ A)
            (Lstar j) (Fsup j) ∧
          SourceAugmentationCounts j W.terminalSize (F j) (Fsup j \ F j) ((t : ℝ≥0) ^ A) := by
  obtain ⟨T, hT1, hT⟩ := eventually_sourceRegularizationAllInputs q K Y D A v w L R C hC
    hD hA hv hLmass hLdensity hLsquare hLy
  refine ⟨T, hT1, ?_⟩
  intro t ht V I _ _ _ _ _ ell W e hsupport localFamily F y z B sigma huniform hspread hn hN
    hsigmaLo hsigmaHi hB hy hmass hdegree
  obtain ⟨hq, hinputs⟩ := hT t ht W e hsupport localFamily F y z B sigma huniform hspread hn hN
    hsigmaLo hsigmaHi hB hy hmass hdegree
  exact exists_source_regularization_all_orders_with_counts W e hsupport q hq localFamily F
    (fun _ ↦ 8192 * t) (fun _ ↦ t) y z (fun _ ↦ (t : ℝ≥0) ^ A) (fun _ ↦ (t : ℝ≥0) ^ D) B sigma C hinputs

end

end Erdos207

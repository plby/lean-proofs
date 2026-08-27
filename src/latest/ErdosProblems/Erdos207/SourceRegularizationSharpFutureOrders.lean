/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationAllOrders
import ErdosProblems.Erdos207.SourceFutureIncrementTransport

/-! # All-order augmentation with separate coefficients at every future prefix -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_source_regularization_all_orders_sharp_future_prefixes
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell : ℕ} (W : Vortex V ell) (k : Fin ell) (e : I ↪ TripleOn V)
    (hshell : ∀ i, (e i).1 ⊆ W.U k.castSucc ∧ ¬ (e i).1 ⊆ W.U k.succ)
    (q : ℕ) (hq : q ≤ (W.U k.castSucc).card)
    (L : ℕ → Finset (Finset I)) (F : ℕ → ForbiddenFamilyOn V)
    (b s : ℕ → ℕ) (y z a delta B : ℕ → ℝ≥0) (sigma C : ℝ≥0)
    (yFuture zFuture : Fin (ell + 1) → ℕ → ℝ≥0)
    (hinputs : ∀ j ∈ Icc 4 q, SourceRegularizationOrderInput (W.prefix k.castSucc) j (L j) (F j)
      (b j) (s j) (y j) (z j) (a j) (delta j) sigma C (B j))
    (hfuture : ∀ j ∈ Icc 4 q, ∀ m : Fin (ell + 1), k.val < m.val →
      SourceVortexWellSpread (W.prefix m) j (F j) (yFuture m j) (zFuture m j)) :
    ∃ Lstar : ℕ → Finset (Finset I), ∃ Fsup : ℕ → ForbiddenFamilyOn V,
      (∀ j ∈ Icc 4 q,
        SourceRegularizationOrderResult (W.prefix k.castSucc) e j (b j) (L j)
          ((Ico 4 j).biUnion Lstar) (F j) (y j + a j) (z j + 3 * a j) (Lstar j) (Fsup j) ∧
        SourceAugmentationCounts j (W.prefix k.castSucc).terminalSize (F j) (Fsup j \ F j) (a j)) ∧
      (∀ j ∈ Icc 4 q, ∀ m : Fin (ell + 1), k.val < m.val →
        SourceVortexWellSpread (W.prefix m) j (Fsup j) (yFuture m j + a j) (zFuture m j + 3 * a j)) := by
  have hsupport : ∀ i, (e i).1 ⊆ (W.prefix k.castSucc).U (Fin.last k.val) := by
    intro i
    change (e i).1 ⊆ W.U (vortexPrefixEmbedding k.castSucc (Fin.last k.castSucc.val))
    rw [vortexPrefixEmbedding_last]
    exact (hshell i).1
  obtain ⟨Lstar, Fsup, hresult⟩ := exists_source_regularization_all_orders_with_counts (W.prefix k.castSucc)
    e hsupport q (by simpa only [Vortex.prefix_terminalSize] using hq) L F b s y z a delta B sigma C hinputs
  refine ⟨Lstar, Fsup, hresult, ?_⟩
  intro j hj m hkm
  apply SourceAugmentationCounts.future_prefix_superset W k m hkm (hresult j hj).2
    (hfuture j hj m hkm) (hresult j hj).1.contains_original
  intro E hE T hT
  have hmap := (hresult j hj).1.new_support E hE hT
  obtain ⟨i, _hi, rfl⟩ := mem_map.mp hmap
  exact hshell i

end

end Erdos207

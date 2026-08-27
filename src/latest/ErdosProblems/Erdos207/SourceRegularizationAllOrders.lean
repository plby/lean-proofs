/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationOrderData

/-! # Finite forbidden-order induction from the explicit regularization budgets -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem finset_biUnion_update_of_not_mem
    {K J : Type*} [DecidableEq K] [DecidableEq J]
    (S : Finset K) (f : K → Finset J) (k : K) (v : Finset J) (hk : k ∉ S) :
    S.biUnion (Function.update f k v) = S.biUnion f := by
  apply biUnion_congr rfl
  intro i hi
  exact Function.update_of_ne (show i ≠ k from fun heq ↦ hk (heq ▸ hi)) v f

theorem exists_source_regularization_all_orders_with_counts
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell : ℕ} (W : Vortex V ell) (e : I ↪ TripleOn V)
    (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell)) (q : ℕ) (hq : q ≤ W.terminalSize)
    (L : ℕ → Finset (Finset I)) (F : ℕ → ForbiddenFamilyOn V)
    (b s : ℕ → ℕ) (y z a delta B : ℕ → ℝ≥0) (sigma C : ℝ≥0)
    (hinputs : ∀ j ∈ Icc 4 q, SourceRegularizationOrderInput W j (L j) (F j)
      (b j) (s j) (y j) (z j) (a j) (delta j) sigma C (B j)) :
    ∃ Lstar : ℕ → Finset (Finset I), ∃ Fsup : ℕ → ForbiddenFamilyOn V,
      ∀ j ∈ Icc 4 q, SourceRegularizationOrderResult W e j (b j) (L j)
        ((Ico 4 j).biUnion Lstar) (F j) (y j + a j) (z j + 3 * a j) (Lstar j) (Fsup j) ∧
          SourceAugmentationCounts j W.terminalSize (F j) (Fsup j \ F j) (a j) := by
  have hbuild : ∀ r : ℕ, r ≤ q →
      ∃ Lstar : ℕ → Finset (Finset I), ∃ Fsup : ℕ → ForbiddenFamilyOn V,
        ∀ j ∈ Icc 4 r, SourceRegularizationOrderResult W e j (b j) (L j)
          ((Ico 4 j).biUnion Lstar) (F j) (y j + a j) (z j + 3 * a j) (Lstar j) (Fsup j) ∧
          SourceAugmentationCounts j W.terminalSize (F j) (Fsup j \ F j) (a j) := by
    intro r
    induction r with
    | zero =>
      intro _hr
      refine ⟨fun _ ↦ ∅, F, ?_⟩
      intro j hj
      have hh := mem_Icc.mp hj
      omega
    | succ r ih =>
      intro hr
      obtain ⟨Lprev, Fprev, hprev⟩ := ih (by omega)
      by_cases hfour : 4 ≤ r + 1
      · have hcurrent := hinputs (r + 1) (mem_Icc.mpr ⟨hfour, hr⟩)
        have horders : (Ico 4 (r + 1)).card ≤ W.terminalSize := by
          rw [Nat.card_Ico]
          omega
        have hprevIndex : ∀ i ∈ Ico 4 (r + 1), i ∈ Icc 4 r := by
          intro i hi
          have hh := mem_Ico.mp hi
          exact mem_Icc.mpr ⟨hh.1, by omega⟩
        have hglobalIndex : ∀ i ∈ Ico 4 (r + 1), i ∈ Icc 4 q := by
          intro i hi
          have hh := mem_Icc.mp (hprevIndex i hi)
          exact mem_Icc.mpr ⟨hh.1, by omega⟩
        obtain ⟨Lnew, Fnew, hnew⟩ := hcurrent.exists_result_with_counts e hsupport
          (Ico 4 (r + 1)) Lprev (fun i ↦ i - 2) horders
          (fun i hi ↦ by have hh := mem_Ico.mp hi; constructor <;> omega)
          (fun i hi ↦ (hprev i (hprevIndex i hi)).1.uniform)
          (fun i hi ↦ by
            have hb := (hprev i (hprevIndex i hi)).1.maximum.trans
              (hinputs i (hglobalIndex i hi)).maximum_power
            have he : i - 2 - 1 = i - 3 := by omega
            simpa only [he] using hb)
        refine ⟨Function.update Lprev (r + 1) Lnew, Function.update Fprev (r + 1) Fnew, ?_⟩
        intro j hj
        by_cases hjeq : j = r + 1
        · subst j
          have hnot : r + 1 ∉ Ico 4 (r + 1) := by simp
          simpa only [Function.update_self,
            finset_biUnion_update_of_not_mem (Ico 4 (r + 1)) Lprev (r + 1) Lnew hnot] using hnew
        · have hjbounds := mem_Icc.mp hj
          have hjold : j ∈ Icc 4 r := mem_Icc.mpr ⟨hjbounds.1, by omega⟩
          have hnot : r + 1 ∉ Ico 4 j := by
            intro hmem
            have hh := mem_Ico.mp hmem
            omega
          simpa only [Function.update_of_ne hjeq,
            finset_biUnion_update_of_not_mem (Ico 4 j) Lprev (r + 1) Lnew hnot] using hprev j hjold
      · refine ⟨Lprev, Fprev, ?_⟩
        intro j hj
        have hh := mem_Icc.mp hj
        omega
  exact hbuild q le_rfl

theorem exists_source_regularization_all_orders
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell : ℕ} (W : Vortex V ell) (e : I ↪ TripleOn V)
    (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell)) (q : ℕ) (hq : q ≤ W.terminalSize)
    (L : ℕ → Finset (Finset I)) (F : ℕ → ForbiddenFamilyOn V)
    (b s : ℕ → ℕ) (y z a delta B : ℕ → ℝ≥0) (sigma C : ℝ≥0)
    (hinputs : ∀ j ∈ Icc 4 q, SourceRegularizationOrderInput W j (L j) (F j)
      (b j) (s j) (y j) (z j) (a j) (delta j) sigma C (B j)) :
    ∃ Lstar : ℕ → Finset (Finset I), ∃ Fsup : ℕ → ForbiddenFamilyOn V,
      ∀ j ∈ Icc 4 q, SourceRegularizationOrderResult W e j (b j) (L j)
        ((Ico 4 j).biUnion Lstar) (F j) (y j + a j) (z j + 3 * a j) (Lstar j) (Fsup j) := by
  obtain ⟨Lstar, Fsup, hresult⟩ := exists_source_regularization_all_orders_with_counts W e hsupport q hq
    L F b s y z a delta B sigma C hinputs
  exact ⟨Lstar, Fsup, fun j hj ↦ (hresult j hj).1⟩

end

end Erdos207

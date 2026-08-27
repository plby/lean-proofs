/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFullRootWeight

/-! # Exact exposure of an additional full-configuration root -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem setWeight_sdiff_insert_root
    {A : Type*} [DecidableEq A] (w : A → ℝ≥0) {E Q : Finset A} {T : A}
    (hT : T ∈ E) (hTQ : T ∉ Q) :
    setWeight w (E \ Q) = w T * setWeight w (E \ insert T Q) := by
  unfold setWeight
  rw [sdiff_insert]
  exact (mul_prod_erase (E \ Q) w (mem_sdiff.mpr ⟨hT, hTQ⟩)).symm

theorem fullRootWeight_expose_eq
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (w : TripleOn V → ℝ≥0) (Q : TripleSystemOn V) (T : TripleOn V)
    (hTQ : T ∉ Q) :
    (∑ E ∈ familyExtensions F Q, if T ∈ E then setWeight w (E \ Q) else 0) =
      w T * ∑ E ∈ familyExtensions F (insert T Q), setWeight w (E \ insert T Q) := by
  classical
  rw [← sum_filter]
  have hfilter : (familyExtensions F Q).filter (fun E ↦ T ∈ E) =
      familyExtensions F (insert T Q) := by
    ext E
    simp only [mem_filter, mem_familyExtensions_iff, insert_subset_iff]
    tauto
  rw [hfilter, mul_sum]
  apply sum_congr rfl
  intro E hE
  exact setWeight_sdiff_insert_root w
    ((mem_familyExtensions_iff.mp hE).2 (mem_insert_self _ _)) hTQ

theorem fullRootWeight_expose_cover_le
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (w : TripleOn V → ℝ≥0) (Q B : TripleSystemOn V)
    (G : ForbiddenFamilyOn V) (hG : G ⊆ familyExtensions F Q)
    (hcover : ∀ E ∈ G, ∃ T ∈ B, T ∈ E)
    (hBQ : Disjoint B Q) :
    (∑ E ∈ G, setWeight w (E \ Q)) ≤
      ∑ T ∈ B, w T *
        ∑ E ∈ familyExtensions F (insert T Q), setWeight w (E \ insert T Q) := by
  classical
  calc
    _ ≤ ∑ E ∈ G, ∑ T ∈ B, if T ∈ E then setWeight w (E \ Q) else 0 := by
      apply sum_le_sum
      intro E hE
      obtain ⟨T, hTB, hTE⟩ := hcover E hE
      simpa only [if_pos hTE] using
        (single_le_sum (s := B)
          (f := fun S ↦ if S ∈ E then setWeight w (E \ Q) else 0)
          (fun _ _ ↦ zero_le) hTB)
    _ = ∑ T ∈ B, ∑ E ∈ G, if T ∈ E then setWeight w (E \ Q) else 0 := sum_comm
    _ ≤ ∑ T ∈ B, ∑ E ∈ familyExtensions F Q,
        if T ∈ E then setWeight w (E \ Q) else 0 := by
      apply sum_le_sum
      intro T _
      exact sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ ↦ zero_le)
    _ = _ := by
      apply sum_congr rfl
      intro T hTB
      exact fullRootWeight_expose_eq F w Q T
        (fun hTQ ↦ (disjoint_left.mp hBQ) hTB hTQ)

end

end Erdos207

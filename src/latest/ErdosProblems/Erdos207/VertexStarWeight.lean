/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberWeightBudget
import ErdosProblems.Erdos207.UniformExtensionWeight

/-!
# The weight system of triangles through one vertex

Viewing every triangle through `v` as a singleton configuration gives a
sharp extension bound: the empty-root weight is the star size times `p`, and
every nonempty root has at most one extension.  This is the combinatorial
input for vertex-degree moments.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Point-weighted version of the singleton vertex-star extension bound. -/
theorem singletonVertexStar_hasExtensionBound_pointWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (pi : TripleOn V → ℝ≥0) :
    HasExtensionBound
      (fun T : universeTriplesThrough v ↦ ({T.1} : TripleSystemOn V))
      pi
      ((∑ T : universeTriplesThrough v, pi T.1) + 1) := by
  classical
  intro H
  by_cases hHempty : H = ∅
  · subst H
    unfold extensionWeight
    simp [setWeight]
  · by_cases hHcard : H.card = 1
    · obtain ⟨h, rfl⟩ := card_eq_one.mp hHcard
      have hle : extensionWeight
          (fun T : universeTriplesThrough v ↦
            ({T.1} : TripleSystemOn V)) pi {h} ≤ 1 := by
        by_cases hh : h ∈ universeTriplesThrough v
        · let T0 : universeTriplesThrough v := ⟨h, hh⟩
          unfold extensionWeight
          rw [sum_eq_single T0]
          · simp [T0, setWeight]
          · intro T hT hTne
            have hne : h ≠ T.1 := by
              intro heq
              apply hTne
              apply Subtype.ext
              exact heq.symm
            simp [hne]
          · simp
        · unfold extensionWeight
          have hzero : (∑ T : universeTriplesThrough v,
              if ({h} : TripleSystemOn V) ⊆ {T.1} then
                setWeight pi ({T.1} \ {h}) else 0) = 0 := by
            apply sum_eq_zero
            intro T hT
            have hne : h ≠ T.1 := by
              intro heq
              apply hh
              simpa [heq] using T.2
            simp [hne]
          rw [hzero]
          exact zero_le_one
      exact hle.trans (le_add_of_nonneg_left bot_le)
    · have hHtwo : 2 ≤ H.card := by
        have hHpos : 0 < H.card := card_pos.mpr
          (nonempty_iff_ne_empty.mpr hHempty)
        omega
      have hnot (T : universeTriplesThrough v) :
          ¬ H ⊆ ({T.1} : TripleSystemOn V) := by
        intro hsub
        have hc := card_le_card hsub
        simp at hc
        omega
      simp [extensionWeight, hnot]

/-- Singleton configurations indexed by all ambient triangles through `v`
have extension weight at most `|star(v)| p + 1`. -/
theorem singletonVertexStar_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (p : ℝ≥0) :
    HasExtensionBound
      (fun T : universeTriplesThrough v ↦ ({T.1} : TripleSystemOn V))
      (constantTripleWeight p)
      ((universeTriplesThrough v).card * p + 1) := by
  classical
  intro H
  by_cases hHempty : H = ∅
  · subst H
    simp [extensionWeight, setWeight, constantTripleWeight]
  · by_cases hHcard : H.card = 1
    · obtain ⟨h, rfl⟩ := card_eq_one.mp hHcard
      have hle : extensionWeight
          (fun T : universeTriplesThrough v ↦
            ({T.1} : TripleSystemOn V))
          (constantTripleWeight p) {h} ≤ 1 := by
        by_cases hh : h ∈ universeTriplesThrough v
        · let T₀ : universeTriplesThrough v := ⟨h, hh⟩
          unfold extensionWeight
          rw [Finset.sum_eq_single T₀]
          · simp [T₀, setWeight, constantTripleWeight]
          · intro T _hT hTne
            have hne : h ≠ T.1 := by
              intro heq
              apply hTne
              apply Subtype.ext
              exact heq.symm
            simp [hne]
          · simp
        · unfold extensionWeight
          have hzero : (∑ T : universeTriplesThrough v,
              if ({h} : TripleSystemOn V) ⊆ {T.1} then
                setWeight (constantTripleWeight p) ({T.1} \ {h}) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro T _hT
            have hne : h ≠ T.1 := by
              intro heq
              apply hh
              simpa [heq] using T.2
            simp [hne]
          rw [hzero]
          exact zero_le_one
      exact hle.trans (le_add_of_nonneg_left bot_le)
    · have hHtwo : 2 ≤ H.card := by
        have hHpos : 0 < H.card := card_pos.mpr
          (nonempty_iff_ne_empty.mpr hHempty)
        omega
      have hnot (T : universeTriplesThrough v) :
          ¬ H ⊆ ({T.1} : TripleSystemOn V) := by
        intro hsub
        have hc := card_le_card hsub
        simp at hc
        omega
      simp [extensionWeight, hnot]

/-- The singleton-star selected count is exactly the number of selected
triangles through `v`. -/
theorem selectedCount_singletonVertexStar
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (P : TripleSystemOn V) :
    selectedCount
      (fun T : universeTriplesThrough v ↦ ({T.1} : TripleSystemOn V)) P =
      (triplesThrough P v).card := by
  classical
  have hstar : (universeTriplesThrough v).filter (fun T ↦ T ∈ P) =
      triplesThrough P v := by
    ext T
    simp [universeTriplesThrough, triplesThrough, and_comm]
  unfold selectedCount
  calc
    (∑ T : universeTriplesThrough v,
        if ({T.1} : TripleSystemOn V) ⊆ P then 1 else 0) =
        ∑ T ∈ universeTriplesThrough v,
          if ({T} : TripleSystemOn V) ⊆ P then 1 else 0 := by
      exact (Finset.sum_subtype
        (p := fun T : TripleOn V ↦ T ∈ universeTriplesThrough v)
        (universeTriplesThrough v) (fun _ ↦ Iff.rfl)
        (fun T ↦ if ({T} : TripleSystemOn V) ⊆ P then
          (1 : ℝ≥0) else 0)).symm
    _ = ∑ T ∈ (universeTriplesThrough v).filter (fun T ↦ T ∈ P),
          (1 : ℝ≥0) := by
      rw [sum_filter]
      apply Finset.sum_congr rfl
      intro T _hT
      simp only [singleton_subset_iff]
    _ = ∑ T ∈ triplesThrough P v, (1 : ℝ≥0) := by rw [hstar]
    _ = (triplesThrough P v).card := by simp

end

end Erdos207

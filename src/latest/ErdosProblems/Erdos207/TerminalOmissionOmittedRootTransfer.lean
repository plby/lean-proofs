/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGeneralMomentWeights

/-! # Exposing terminal omitted triangles as an enlarged root -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem terminalOmission_move_omitted_to_root
    {V : Type*} [Fintype V] [DecidableEq V] {ell f : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {Q K : TripleSystemOn V}
    {x : TripleSystemOn V × TripleSystemOn V}
    (hx : x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f)
    (hK : K ⊆ (x.1 \ Q) \ x.2) :
    x ∈ terminalOmissionCodes W (familyExtensions F (Q ∪ K)) (fun E ↦ E \ (Q ∪ K)) f := by
  have hm := mem_terminalOmissionCodes_iff.mp hx
  have hE := mem_familyExtensions_iff.mp hm.1
  have hA := mem_terminalRemainderChoices_iff.mp hm.2
  apply mem_terminalOmissionCodes_iff.mpr
  refine ⟨mem_familyExtensions_iff.mpr ⟨hE.1, union_subset hE.2 (hK.trans (sdiff_subset.trans sdiff_subset))⟩,
    mem_terminalRemainderChoices_iff.mpr ⟨?_, hA.2.1, ?_⟩⟩
  · intro T hT
    have he := mem_sdiff.mp (hA.1 hT)
    refine mem_sdiff.mpr ⟨he.1, ?_⟩
    intro hmem
    rcases mem_union.mp hmem with hQ | hK'
    · exact he.2 hQ
    · exact (mem_sdiff.mp (hK hK')).2 hT
  · intro T hT
    have ht := mem_sdiff.mp hT
    have he := mem_sdiff.mp ht.1
    exact hA.2.2 T (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨he.1, fun hQ ↦ he.2 (mem_union_left _ hQ)⟩, ht.2⟩)

theorem sourceRootOmission_omitted_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (Q K : TripleSystemOn V) (f : ℕ) (w : ℝ≥0) :
    (∑ x ∈ (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f).filter
        (fun x ↦ K ⊆ (x.1 \ Q) \ x.2), setWeight (vortexTripleWeight W w) x.2) ≤
      sourceRootOmissionWeight W F (Q ∪ K) f w := by
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ ↦ zero_le)
  intro x hx
  exact terminalOmission_move_omitted_to_root (mem_filter.mp hx).1 (mem_filter.mp hx).2

end

end Erdos207

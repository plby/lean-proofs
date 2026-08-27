/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleMaximumWeight

/-! # Pair-local source extension bounds by pinning a nonempty mixed edge root -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourcePinnedEdgeCodes
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j : ℕ) (e : Sym2 V) :=
  (sourceNibbleCodes W F T 4 j).filter (fun x ↦ e ∈ (sourceNibbleCoordinates T x).toRight)

theorem sourcePinnedEdge_extension_le_mixed
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j : ℕ)
    (e : Sym2 V) (w : ℝ≥0) (H : TripleSystemOn V) :
    extensionWeight (fun x : sourcePinnedEdgeCodes W F T j e ↦ x.1.2) (vortexTripleWeight W w) H ≤
      extensionWeight (fun x : sourceNibbleCodes W F T 4 j ↦ sourceNibbleCoordinates T x.1)
        (sourceNibbleMixedWeight W w 1) (H.disjSum {e}) := by
  classical
  unfold extensionWeight
  rw [← Finset.sum_subtype (sourcePinnedEdgeCodes W F T j e)
    (p := fun x ↦ x ∈ sourcePinnedEdgeCodes W F T j e) (fun _ ↦ Iff.rfl)
    (fun x ↦ if H ⊆ x.2 then setWeight (vortexTripleWeight W w) (x.2 \ H) else 0)]
  rw [← Finset.sum_subtype (sourceNibbleCodes W F T 4 j)
    (p := fun x ↦ x ∈ sourceNibbleCodes W F T 4 j) (fun _ ↦ Iff.rfl)
    (fun x ↦ if H.disjSum {e} ⊆ sourceNibbleCoordinates T x then
      setWeight (sourceNibbleMixedWeight W w 1) (sourceNibbleCoordinates T x \ H.disjSum {e}) else 0)]
  rw [sourcePinnedEdgeCodes, sum_filter]
  apply sum_le_sum
  intro x _hx
  by_cases he : e ∈ (sourceNibbleCoordinates T x).toRight
  · rw [if_pos he]
    by_cases hH : H ⊆ x.2
    · rw [if_pos hH]
      have hroot : H.disjSum {e} ⊆ sourceNibbleCoordinates T x := by
        change H.disjSum {e} ⊆ x.2.disjSum ((sourceNibbleRemaining T x).biUnion tripleEdgeFinset)
        rw [subset_disjSum]
        constructor
        · simpa only [toLeft_disjSum] using hH
        · simpa only [sourceNibbleCoordinates, toRight_disjSum, singleton_subset_iff] using he
      rw [if_pos hroot, sourceNibbleMixedWeight_factor]
      simp only [toLeft_sdiff, sourceNibbleCoordinates, toLeft_disjSum, one_pow, mul_one, le_refl]
    · rw [if_neg hH]
      exact zero_le
  · rw [if_neg he]
    exact zero_le

theorem SourceVortexWellSpread.pinned_edge_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (T : TripleOn V) (e : Sym2 V) (w : ℝ≥0) (hw : 1 ≤ w) :
    HasExtensionBound (fun x : sourcePinnedEdgeCodes W F T j e ↦ x.1.2)
      (vortexTripleWeight W w) (sourceNibbleMomentCoefficient ell j w * z) := by
  intro H
  have hroot : (H.disjSum {e}).Nonempty := ⟨Sum.inr e, by simp⟩
  have hbound := h.nibble_mixed_nonempty_uniform_weight_le T 4 (by omega) h.order w 1 hw (by norm_num)
    (H.disjSum {e}) hroot
  apply (sourcePinnedEdge_extension_le_mixed W F T j e w H).trans
  simpa only [Nat.sub_self, pow_zero, mul_one] using hbound

end

end Erdos207

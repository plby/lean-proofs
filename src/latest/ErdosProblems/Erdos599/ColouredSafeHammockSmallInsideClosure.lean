/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeHammockOmegaClosure

/-!
# Small closing carriers inside successor-cap closed sets

Thin an actual successor-cap maximal family, retaining its original global
eligibility predicate and containment. This does not assume that all good
routes are confined to the ambient closing set.
-/

noncomputable section

namespace Erdos599.Blueprint

open Set Cardinal Order DirectedPath

universe u

namespace CarrierHammock

variable {Route V : Type u} {good : Set Route} {carrier : Route → Set V}
variable {ends : Set V} {rho : Cardinal.{u}} {H : Set Route}

theorem exists_maximalUpTo_subset_of_succ
    (hH : MaximalUpTo {K | Admissible good carrier ends K} (succ rho) H) :
    ∃ K : Set Route, K ⊆ H ∧ MaximalUpTo {J | Admissible good carrier ends J} rho K := by
  by_cases hsmall : #H ≤ rho
  · exact ⟨H, Set.Subset.rfl, maximalUpTo_of_maximal hH.mem
      (hH.maximal_of_card_lt (hsmall.trans_lt (lt_succ rho))) hsmall⟩
  · have hcard : #H = succ rho :=
      le_antisymm hH.card_le (succ_le_of_lt (lt_of_not_ge hsmall))
    obtain ⟨a, ha⟩ := Cardinal.le_mk_iff_exists_set.mp
      ((le_succ rho).trans hcard.ge)
    have haH : Subtype.val '' a ⊆ H := by
      rintro q ⟨r, _, rfl⟩
      exact r.property
    refine ⟨Subtype.val '' a, haH,
      maximalUpTo_of_large (hH.mem.subset haH) ?_ hH.mem hcard⟩
    exact (Cardinal.mk_image_eq_of_injOn Subtype.val a Set.injOn_subtype_val).trans ha

end CarrierHammock

namespace ColouredSafeHammock

open ColouredSafeAmbientOccurrence ColouredSafeHammockOmegaClosure

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s : V}
variable {e : Option V} {extra : Occurrence Y s → Prop} {rho : Cardinal.{u}} {Z : Set V}

/-- A small closing set consists of the actual carriers of a subfamily of
the supplied contained successor-cap witness. -/
theorem ClosedAt.exists_small_within (hZ : ClosedAt Y s e extra (succ rho) Z)
    (hrho : aleph0 ≤ rho) :
    ∃ X : Set V, #X ≤ rho ∧ X ⊆ Z ∧ ClosedAt Y s e extra rho X := by
  obtain ⟨H, hH, hHZ⟩ := hZ
  obtain ⟨K, hKH, hK⟩ := CarrierHammock.exists_maximalUpTo_subset_of_succ hH
  refine ⟨familyVertices K, mk_familyVertices_le hrho hK.card_le, ?_, K, hK, ?_⟩
  · intro x hx
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hx
    exact hHZ A.1 (hKH A.2) hxA
  · intro A hA x hx
    exact Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩

end ColouredSafeHammock

#print axioms CarrierHammock.exists_maximalUpTo_subset_of_succ
#print axioms ColouredSafeHammock.ClosedAt.exists_small_within

end Erdos599.Blueprint

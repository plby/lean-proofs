/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeHammockOmegaClosure

/-!
# Successor-cap closure contains actual large native hammocks

A family maximal up to `succ kappa` has exactly that size whenever a
`succ kappa`-sized hammock exists globally. If it were smaller, it would
be inclusion-maximal of size at most `kappa`; countable route carriers
then bound every hammock by `kappa`, a contradiction.

Thus closure at the successor cap supplies the internally contained
large families needed by the local native transactions. Closure merely
at the predecessor cap is not enough for this conclusion.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeHammock

open Cardinal Set Order
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {s : V} {e : Option V} {extra : Occurrence Y s → Prop}
variable {kappa : Cardinal.{u}}

/-- The actual maximal-up-to family, not an unrelated global witness,
has successor size. -/
theorem cardinal_eq_succ_of_maximalUpTo
    (hkappa : aleph0 ≤ kappa) {M : Set (Occurrence Y s)}
    (hM : MaximalUpTo {K | Hammock Y s e extra K} (succ kappa) M)
    (hlarge : HasCard Y s e extra (succ kappa)) : #M = succ kappa := by
  apply le_antisymm (MaximalUpTo.card_le hM)
  by_contra hnot
  have hlt : #M < succ kappa := lt_of_not_ge hnot
  have hmax : Maximal (Hammock Y s e extra) M :=
    hM.maximal_of_card_lt hlt
  obtain ⟨H, hH, hHcard⟩ := hlarge
  have hbound : #H ≤ kappa :=
    CarrierHammock.mk_le_of_maximal_of_countable hkappa hmax
      (lt_succ_iff.mp hlt) (fun A _ ↦ A.vertexSet_countable) hH
  exact (not_le_of_gt (lt_succ kappa)) (hHcard ▸ hbound)

/-- Successor-cap closure localizes a genuinely large hammock without
changing its validity, endpoint, or nondegeneracy filter. -/
theorem ClosedAt.hasCard_within
    (hkappa : aleph0 ≤ kappa) {Z : Set V}
    (hclosed : ClosedAt Y s e extra (succ kappa) Z)
    (hlarge : HasCard Y s e extra (succ kappa)) :
    HasCard Y s e (fun A ↦ extra A ∧ A.vertexSet ⊆ Z) (succ kappa) := by
  obtain ⟨M, hM, hMZ⟩ := hclosed
  refine ⟨M, ⟨?_, (MaximalUpTo.mem hM).2⟩,
    cardinal_eq_succ_of_maximalUpTo hkappa hM hlarge⟩
  intro A hA
  obtain ⟨hvalid, hend, hs, ht, hextra⟩ := (MaximalUpTo.mem hM).1 hA
  exact ⟨hvalid, hend, hs, ht, hextra, hMZ A hA⟩

end Erdos599.Blueprint.ColouredSafeHammock

namespace Erdos599.Blueprint.ColouredSafeHammockOmegaClosure

open Cardinal Set Order
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {Z : Set V} {s t : V}

/-- Every global finite-end large hammock with ends in the successor-closed
set has an equally large actual subgraph-contained witness. -/
theorem OmegaClosed.finite_hasCard_within
    (hZ : OmegaClosed Y (succ kappa) Z) (hkappa : aleph0 ≤ kappa)
    (hs : s ∈ Z) (ht : t ∈ Z)
    (h : HasCard Y s (some t) (fun _ ↦ True) (succ kappa)) :
    HasCard Y s (some t) (fun A ↦ A.vertexSet ⊆ Z) (succ kappa) := by
  simpa only [true_and] using ((hZ.2 s hs t ht).1.hasCard_within hkappa h)

/-- Nondegeneracy is retained while localizing the strong hammock. -/
theorem OmegaClosed.nondegenerate_hasCard_within
    (hZ : OmegaClosed Y (succ kappa) Z) (hkappa : aleph0 ≤ kappa)
    (hs : s ∈ Z) (ht : t ∈ Z)
    (h : HasCard Y s (some t)
      (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) (succ kappa)) :
    HasCard Y s (some t)
      (fun A ↦ ¬A.HasFiniteSwitchedPathTo t ∧ A.vertexSet ⊆ Z) (succ kappa) :=
  (hZ.2 s hs t ht).2.hasCard_within hkappa h

/-- The infinite-end branch needs only its initial vertex in the closing
set; every carrier of the selected large family is actually contained. -/
theorem OmegaClosed.infinite_hasCard_within
    (hZ : OmegaClosed Y (succ kappa) Z) (hkappa : aleph0 ≤ kappa)
    (hs : s ∈ Z)
    (h : HasCard Y s none (fun _ ↦ True) (succ kappa)) :
    HasCard Y s none (fun A ↦ A.vertexSet ⊆ Z) (succ kappa) := by
  simpa only [true_and] using ((hZ.1 s hs).hasCard_within hkappa h)

#print axioms ColouredSafeHammock.cardinal_eq_succ_of_maximalUpTo
#print axioms ColouredSafeHammock.ClosedAt.hasCard_within
#print axioms OmegaClosed.finite_hasCard_within
#print axioms OmegaClosed.nondegenerate_hasCard_within
#print axioms OmegaClosed.infinite_hasCard_within

end Erdos599.Blueprint.ColouredSafeHammockOmegaClosure

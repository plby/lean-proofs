/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointHammockClosure
import ErdosProblems.Erdos599.ColouredSafeReferenceClosedCarrier

/-!
# Joint ordinary, endpoint-indexed and whole-reference closure

Interleave the actual two small closure operations. The endpoint-closed
sets and the ordinary/reference-closed sets have the same increasing union.
This produces all three certificates on the same carrier before any future
interval row is chosen. No closure under arbitrary enlargement is assumed.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointReferenceClosedCarrier

open Set Cardinal Order DirectedPath LinkageBlueprint
open ColouredSafeHammockOmegaClosure

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Close a small seed inside the limiting roof under both kinds of
captured hammocks and every whole limiting-reference owner it meets. -/
theorem exists_captured_jointClosed_superset
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {seed : Set V} (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    ∃ Z : Set V, seed ⊆ Z ∧ #Z ≤ kappa ∧ Z ⊆ C.ladder.limitRoof ∧
      FilteredOmegaClosed C.ladder.limitWarp
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa Z ∧
      ClosedUnderPaths Gamma C.ladder.limitWarp Z ∧
      ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
        (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa Z := by
  let Small := {X : Set V // #X ≤ kappa ∧ X ⊆ C.ladder.limitRoof}
  have hEndpoint : ∀ A : Small, ∃ B : Small, A.1 ⊆ B.1 ∧
      ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
        (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa B.1 := by
    intro A
    obtain ⟨B, hAB, hBcard, hBroof, hBclosed⟩ :=
      ColouredSafeEndpointHammock.exists_capturedClosed_superset C.ladder
        C.capacity_infinite A.2.1 A.2.2
    exact ⟨⟨B, hBcard, hBroof⟩, hAB, hBclosed⟩
  choose endpoint endpoint_sub endpoint_closed using hEndpoint
  have hOrdinary : ∀ A : Small, ∃ B : Small, A.1 ⊆ B.1 ∧
      FilteredOmegaClosed C.ladder.limitWarp
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa B.1 ∧
      ClosedUnderPaths Gamma C.ladder.limitWarp B.1 := by
    intro A
    obtain ⟨B, hAB, hBcard, hBroof, hBclosed, hBref, _hlater⟩ :=
      ColouredSafeReferenceClosedCarrier.exists_captured_referenceClosed_later
        C A.2.1 A.2.2
    exact ⟨⟨B, hBcard, hBroof⟩, hAB, hBclosed, hBref⟩
  choose ordinary ordinary_sub ordinary_closed ordinary_reference using hOrdinary
  let A : Nat → Small := fun n ↦
    Nat.rec (endpoint ⟨seed, hcard, hroof⟩) (fun _ a ↦ endpoint (ordinary a)) n
  let B : Nat → Small := fun n ↦ ordinary (A n)
  have hAB : ∀ n, (A n).1 ⊆ (B n).1 := fun n ↦ ordinary_sub (A n)
  have hBA : ∀ n, (B n).1 ⊆ (A (n + 1)).1 := fun n ↦ endpoint_sub (B n)
  have hAmono : Monotone (fun n ↦ (A n).1) :=
    monotone_nat_of_le_succ (fun n ↦ (hAB n).trans (hBA n))
  have hBmono : Monotone (fun n ↦ (B n).1) :=
    monotone_nat_of_le_succ (fun n ↦ (hBA n).trans (hAB (n + 1)))
  have hAclosed : ∀ n, ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa (A n).1 := by
    intro n
    cases n with
    | zero => exact endpoint_closed ⟨seed, hcard, hroof⟩
    | succ n => exact endpoint_closed (B n)
  let Z : Set V := ⋃ n, (A n).1
  have hZeq : Z = ⋃ n, (B n).1 := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n, hAB n hn⟩
    · intro x hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n + 1, hBA n hn⟩
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (endpoint_sub ⟨seed, hcard, hroof⟩).trans
      (Set.subset_iUnion (fun n ↦ (A n).1) 0)
  · exact DWeb.mk_iUnion_nat_le C.capacity_infinite (fun n ↦ (A n).2.1)
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact (A n).2.2 hn
  · rw [hZeq]
    exact FilteredOmegaClosed.iUnion_nat hBmono (fun n ↦ ordinary_closed (A n))
  · rw [hZeq]
    exact closedUnderPaths_iUnion (fun n ↦ ordinary_reference (A n))
  · exact ColouredSafeEndpointHammock.Closed.iUnion_nat hAmono hAclosed

#print axioms exists_captured_jointClosed_superset

end Erdos599.Blueprint.ColouredSafeEndpointReferenceClosedCarrier

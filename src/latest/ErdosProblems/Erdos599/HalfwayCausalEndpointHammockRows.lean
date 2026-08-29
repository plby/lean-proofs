/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalGlobalLargeHammockClosure
import ErdosProblems.Erdos599.ColouredSafeEndpointTrackerClosure

/-!
# Native endpoint closure of the actual Section 9 causal carrier

The enlarged row rule stores endpoint tracker carriers computed on its
strict-prior ladder. Prefix agreement identifies these with the choices
on the final ladder. Endpoints in the global carrier enter all sufficiently
late prior carriers, so the actual global tracker is contained there.
Decoding gives the native ordinary and nondegenerate closure predicates
at the successor cap, in the same carrier as the safe target completions.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order Ladder
open CardinalInduction.RegularRows
open ColouredSafeEndpointTracker

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

theorem nativeEndpointHammockIncrement_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Stage (succ kappa)) :
    nativeEndpointHammockIncrement Gamma kappa a (fun b _ ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  apply Set.Subset.trans ?_ (coherentHammockIncrement_subset_rowAt
    (Gamma := Gamma) hkappa hGamma hseed a)
  intro x hx
  exact Or.inr (Or.inr (Or.inr hx))

theorem nativeSelectedAt_eq_prior
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (s : V) (e : Option V) (strong : Bool) (a : Stage (succ kappa)) :
    selectedAt (finalLadder Gamma kappa hkappa hGamma seed hseed) s e strong a =
      selectedAt (priorCore Gamma a (fun b _ ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b)) s e strong a := by
  symm
  apply selectedAt_congr_le
  intro b hba
  rcases hba.lt_or_eq with hba | rfl
  · exact prior_geometry_eq_final_of_lt (Gamma := Gamma) hkappa hGamma hseed hba
  · exact prior_geometry_eq_final (Gamma := Gamma) hkappa hGamma hseed b

theorem nativeSelectedCarrierAt_contained
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (s : V) (e : Option V) (strong : Bool) (a : Stage (succ kappa))
    (hs : s ∈ priorCarrier a (fun b _ ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b))
    (he : ∀ t, e = some t → t ∈ priorCarrier a (fun b _ ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b)) :
    selectedCarrierAt (finalLadder Gamma kappa hkappa hGamma seed hseed) s e strong a ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  apply Set.Subset.trans ?_ ((nativeEndpointHammockIncrement_subset_rowAt
    (Gamma := Gamma) hkappa hGamma hseed a).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed a))
  unfold selectedCarrierAt
  rw [nativeSelectedAt_eq_prior hkappa hGamma hseed s e strong a]
  exact selectedCarrierAt_subset_requestedCarriers _ s e strong a hs he

theorem exists_eventually_mem_priorCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {x : V} (hx : x ∈ globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ d : Stage (succ kappa), ∀ a, d ≤ a →
      x ∈ priorCarrier a (fun b _ ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b) := by
  let hsucc := hkappa.trans (le_succ kappa)
  let Q := rule Gamma kappa hkappa hGamma seed hseed
  change x ∈ (Q.rowSystem hsucc).carrier at hx
  obtain ⟨c, hxc⟩ := RowSystem.mem_carrier.mp hx
  let d : Stage (succ kappa) :=
    ⟨c.1 + 1, (Cardinal.isSuccLimit_ord hsucc).succ_lt c.2⟩
  have hcd : c < d := lt_add_one c.1
  refine ⟨d, ?_⟩
  intro a hda
  exact Set.mem_iUnion.mpr ⟨⟨c, hcd.trans_le hda⟩, hxc⟩

theorem exists_eventually_endpoint_request
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (s : V) (e : Option V)
    (hends : ColouredSafeHammock.endpoints s e ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ d : Stage (succ kappa), ∀ a, d ≤ a →
      ColouredSafeHammock.endpoints s e ⊆ priorCarrier a (fun b _ ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b) := by
  obtain ⟨ds, hds⟩ := exists_eventually_mem_priorCarrier hkappa hGamma hseed
    (hends (Or.inl rfl))
  cases e with
  | none =>
      refine ⟨ds, ?_⟩
      intro a hda
      simpa only [ColouredSafeHammock.endpoints_none, Set.singleton_subset_iff]
        using hds a hda
  | some t =>
      obtain ⟨dt, hdt⟩ := exists_eventually_mem_priorCarrier hkappa hGamma hseed
        (hends (Or.inr rfl))
      refine ⟨max ds dt, ?_⟩
      intro a hda
      rw [ColouredSafeHammock.endpoints_some, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨hds a ((le_max_left ds dt).trans hda),
        hdt a ((le_max_right ds dt).trans hda)⟩

/-- The exact native successor-cap closure in the actual causal carrier.
No confinement assumption on all globally eligible occurrences is used. -/
theorem endpointHammockClosed_limitWarp
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    ColouredSafeEndpointHammock.Closed
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof
        (finalLadder Gamma kappa hkappa hGamma seed hseed))
      (succ kappa) (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  intro s e hends
  obtain ⟨d, hd⟩ := exists_eventually_endpoint_request hkappa hGamma hseed s e hends
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hL := finalLadder_halfwayGeometry (Gamma := Gamma) hkappa hGamma hseed
  have hcontained : ∀ strong a, d ≤ a →
      selectedCarrierAt L s e strong a ⊆
        globalCarrier Gamma kappa hkappa hGamma seed hseed := by
    intro strong a hda
    exact nativeSelectedCarrierAt_contained hkappa hGamma hseed s e strong a
      (hd a hda (Or.inl rfl)) (fun t ht ↦ hd a hda (Or.inr ht))
  constructor
  · exact ordinary_closedAt_of_eventual_carrier L s e
      (hkappa.trans (le_succ kappa)) hL d (hcontained false)
  · intro t ht
    cases ht
    exact nondegenerate_closedAt_of_eventual_carrier L s t
      (hkappa.trans (le_succ kappa)) hL d (hcontained true)

#print axioms nativeSelectedAt_eq_prior
#print axioms nativeSelectedCarrierAt_contained
#print axioms exists_eventually_endpoint_request
#print axioms endpointHammockClosed_limitWarp

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

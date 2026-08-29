/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointReference
import ErdosProblems.Erdos599.ColouredSafeHammockOmegaClosure
import ErdosProblems.Erdos599.ColouredSafeCapturedClosure

/-!
# Static small closure for endpoint-dependent reference hammocks

The reference of a route is fixed by its source and optional terminal, not
by the current closing approximation. One small carrier closes each pair
for both ordinary and finite nondegenerate routes. An omega iteration then
closes all endpoint pairs which enter the set, within the prescribed region.
No future interval row, moving closure, or simultaneous switching is assumed.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointHammock

open Set Cardinal Order DirectedPath
open ColouredSafeHammock ColouredSafeAmbientOccurrence ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

abbrev Route (Y : Set Gamma.DPath) (s : V) (e : Option V) :=
  Occurrence (reference Y s e) s

structure PairCarrier (Y : Set Gamma.DPath)
    (extra : ∀ s e, Route Y s e → Prop) (roof : Set V)
    (rho : Cardinal.{u}) (s : V) (e : Option V) where
  carrier : Set V
  card_le : #carrier ≤ rho
  subset_roof : carrier ⊆ roof
  ordinary : ClosedAt (reference Y s e) s e (extra s e) rho carrier
  nondegenerate : ∀ t, e = some t →
    ClosedAt (reference Y s e) s e
      (fun A ↦ extra s e A ∧ ¬A.HasFiniteSwitchedPathTo t) rho carrier

theorem exists_pairCarrier (Y : Set Gamma.DPath)
    (extra : ∀ s e, Route Y s e → Prop) (roof : Set V)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    (hroof : ∀ s e A, extra s e A → A.vertexSet ⊆ roof)
    (s : V) (e : Option V) : Nonempty (PairCarrier Y extra roof rho s e) := by
  obtain ⟨O, _hEmpty, hOcard, hO⟩ :=
    exists_closedAt_superset (reference Y s e) s e (extra s e) hrho
      (X := ∅) (by simp)
  let O' := O ∩ roof
  have hO' : ClosedAt (reference Y s e) s e (extra s e) rho O' :=
    hO.inter_of_extra_subset (hroof s e)
  have hO'card : #O' ≤ rho := (Cardinal.mk_subtype_mono Set.inter_subset_left).trans hOcard
  cases e with
  | none =>
      exact ⟨⟨O', hO'card, Set.inter_subset_right, hO', by simp⟩⟩
  | some t =>
      obtain ⟨N, _hEmpty, hNcard, hN⟩ :=
        exists_closedAt_superset (reference Y s (some t)) s (some t)
          (fun A ↦ extra s (some t) A ∧ ¬A.HasFiniteSwitchedPathTo t) hrho
          (X := ∅) (by simp)
      let N' := N ∩ roof
      have hN' : ClosedAt (reference Y s (some t)) s (some t)
          (fun A ↦ extra s (some t) A ∧ ¬A.HasFiniteSwitchedPathTo t) rho N' :=
        hN.inter_of_extra_subset (fun A hA ↦ hroof s (some t) A hA.1)
      have hN'card : #N' ≤ rho :=
        (Cardinal.mk_subtype_mono Set.inter_subset_left).trans hNcard
      refine ⟨⟨O' ∪ N', ?_, Set.union_subset Set.inter_subset_right Set.inter_subset_right,
        hO'.mono Set.subset_union_left, ?_⟩⟩
      · exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hrho hO'card hN'card)
      · intro v hv
        have htv : t = v := Option.some.inj hv
        subst v
        exact hN'.mono Set.subset_union_right

/-- The actual endpoint-indexed closure, including the finite nondegenerate
filter. Each reference is indexed by the same displayed optional endpoint. -/
def Closed (Y : Set Gamma.DPath) (extra : ∀ s e, Route Y s e → Prop)
    (rho : Cardinal.{u}) (X : Set V) : Prop :=
  ∀ s e, endpoints s e ⊆ X →
    ClosedAt (reference Y s e) s e (extra s e) rho X ∧
      ∀ t, e = some t → ClosedAt (reference Y s e) s e
        (fun A ↦ extra s e A ∧ ¬A.HasFiniteSwitchedPathTo t) rho X

/-- Increasing countable unions preserve the actual endpoint-indexed
closure, because the at most two displayed endpoints occur together. -/
theorem Closed.iUnion_nat
    {extra : ∀ s e, Route Y s e → Prop} {rho : Cardinal.{u}} {X : Nat → Set V}
    (hmono : Monotone X) (hclosed : ∀ n, Closed Y extra rho (X n)) :
    Closed Y extra rho (⋃ n, X n) := by
  intro s e hends
  have hstage : ∃ n, endpoints s e ⊆ X n := by
    obtain ⟨ns, hs⟩ := Set.mem_iUnion.mp (hends (Or.inl rfl))
    cases e with
    | none =>
        exact ⟨ns, by simpa only [endpoints_none, Set.singleton_subset_iff] using hs⟩
    | some t =>
        obtain ⟨nt, ht⟩ := Set.mem_iUnion.mp (hends (Or.inr rfl))
        refine ⟨max ns nt, ?_⟩
        rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hmono (Nat.le_max_left ns nt) hs, hmono (Nat.le_max_right ns nt) ht⟩
  obtain ⟨n, hn⟩ := hstage
  have h := hclosed n s e hn
  exact ⟨h.1.mono (Set.subset_iUnion X n),
    fun t ht ↦ (h.2 t ht).mono (Set.subset_iUnion X n)⟩

/-- A genuine small carrier closed for all endpoint-dependent reference
hammocks, confined by the route filter to the given region. -/
theorem exists_closed_superset_within (Y : Set Gamma.DPath)
    (extra : ∀ s e, Route Y s e → Prop) (roof : Set V)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    (hroof : ∀ s e A, extra s e A → A.vertexSet ⊆ roof)
    {X0 : Set V} (hX0card : #X0 ≤ rho) (hX0roof : X0 ⊆ roof) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ Z ⊆ roof ∧ Closed Y extra rho Z := by
  let K := fun s e ↦ (exists_pairCarrier Y extra roof hrho hroof s e).some
  let step : Set V → Set V := fun X ↦
    (X ∪ ⋃ s : X, (K s.1 none).carrier) ∪
      ⋃ s : X, ⋃ t : X, (K s.1 (some t.1)).carrier
  have hinflate : ∀ X, X ⊆ step X := fun _ _ hx ↦ Or.inl (Or.inl hx)
  have hstepCard : ∀ X : Set V, #X ≤ rho → #(step X) ≤ rho := by
    intro X hX
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hrho
    · apply (Cardinal.mk_union_le _ _).trans
      apply Cardinal.add_le_of_le hrho hX
      exact DWeb.mk_iUnion_le_of_le hrho hX (fun s ↦ (K s.1 none).card_le)
    · apply DWeb.mk_iUnion_le_of_le hrho hX
      intro s
      exact DWeb.mk_iUnion_le_of_le hrho hX (fun t ↦ (K s.1 (some t.1)).card_le)
  have hstepRoof : ∀ X, X ⊆ roof → step X ⊆ roof := by
    intro X hX x hx
    rcases hx with (hx | hx) | hx
    · exact hX hx
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      exact (K s.1 none).subset_roof hs
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hs
      exact (K s.1 (some t.1)).subset_roof ht
  let Z := omegaClosure step X0
  have hstageCard := mk_closureStage_le hX0card hstepCard
  have hstageRoof := closureStage_subset_roof hX0roof hstepRoof
  have hmono : Monotone (closureStage step X0) := by
    apply monotone_nat_of_le_succ
    intro n
    exact hinflate _
  have hZcard : #Z ≤ rho := by
    change #(⋃ n, closureStage step X0 n) ≤ rho
    let stages : ULift.{u} Nat → Set V :=
      fun n ↦ closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ n, stages n := by
      ext x
      simp [stages]
    rw [heq]
    apply DWeb.mk_iUnion_le_of_le hrho
    · simpa [Cardinal.mk_nat] using hrho
    · intro n
      exact hstageCard n.down
  have hK : ∀ s e, endpoints s e ⊆ Z → (K s e).carrier ⊆ Z := by
    intro s e hends
    obtain ⟨ns, hs⟩ := Set.mem_iUnion.mp (hends (Or.inl rfl))
    cases e with
    | none =>
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (ns + 1)
        exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩))
    | some t =>
        obtain ⟨nt, ht⟩ := Set.mem_iUnion.mp (hends (Or.inr rfl))
        have hs' := hmono (Nat.le_max_left ns nt) hs
        have ht' := hmono (Nat.le_max_right ns nt) ht
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (max ns nt + 1)
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨s, hs'⟩,
          Set.mem_iUnion.mpr ⟨⟨t, ht'⟩, hx⟩⟩)
  refine ⟨Z, closureStage_subset_omegaClosure step X0 0, hZcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hstageRoof n hn
  · intro s e hends
    exact ⟨(K s e).ordinary.mono (hK s e hends),
      fun t ht ↦ ((K s e).nondegenerate t ht).mono (hK s e hends)⟩

/-- Literal stage-roof capture for a route whose reference depends on its
endpoints; this does not reuse a predicate with the wrong reference index. -/
def CapturedByStageRoof {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (s : V) (e : Option V) (A : Route L.limitWarp s e) : Prop :=
  ∃ a : Ladder.Stage kappa, A.vertexSet ⊆ Gamma.roof (L.frontier a)

theorem exists_capturedClosed_superset {kappa rho : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (hrho : aleph0 ≤ rho)
    {X0 : Set V} (hX0card : #X0 ≤ rho) (hX0roof : X0 ⊆ L.limitRoof) :
    ∃ Z : Set V, X0 ⊆ Z ∧ #Z ≤ rho ∧ Z ⊆ L.limitRoof ∧
      Closed L.limitWarp (CapturedByStageRoof L) rho Z := by
  apply exists_closed_superset_within L.limitWarp (CapturedByStageRoof L) L.limitRoof
    hrho ?_ hX0card hX0roof
  intro s e A hA x hx
  obtain ⟨a, hroof⟩ := hA
  exact Set.mem_iUnion.mpr ⟨a, hroof hx⟩

#print axioms exists_pairCarrier
#print axioms Closed.iUnion_nat
#print axioms exists_closed_superset_within
#print axioms exists_capturedClosed_superset

end Erdos599.Blueprint.ColouredSafeEndpointHammock

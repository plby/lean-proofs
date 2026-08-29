/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CarrierHammockClosure
import ErdosProblems.Erdos599.ColouredSafeAmbientOccurrence

/-!
# Native occurrence hammocks and their closing implication

Routes have an erased ambient forward-warp index and an intrinsic honest
finite-character ownership certificate. Their interiors are literal word
carriers minus the prescribed endpoints. These are additive definitions;
the older `AltPath` hammock and main problem statement are not changed.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeHammock

open Cardinal Set Order DirectedPath
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s t : V}

def endpoints (s : V) (e : Option V) : Set V := {s} ∪ {t | e = some t}

@[simp] theorem endpoints_some (s t : V) : endpoints s (some t) = {s, t} := by
  ext x
  simp [endpoints, eq_comm, or_comm]

@[simp] theorem endpoints_none (s : V) : endpoints s none = {s} := by
  ext x
  simp [endpoints]

/-- Exact validity and exposure conditions on an ambient occurrence, with
an optional genuine route filter such as nondegeneracy. -/
def goodRoutes (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (extra : Occurrence Y s → Prop) : Set (Occurrence Y s) :=
  {A | Valid A ∧ A.terminal? = e ∧ s ∉ Gamma.vertexSet Y ∧
    (∀ t, e = some t → t ∉ Gamma.vertexSet Y) ∧ extra A}

def Hammock (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (extra : Occurrence Y s → Prop) (H : Set (Occurrence Y s)) : Prop :=
  CarrierHammock.Admissible (goodRoutes Y s e extra)
    CurrentSafeOccurrence.vertexSet (endpoints s e) H

def HasCard (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (extra : Occurrence Y s → Prop) (rho : Cardinal.{u}) : Prop :=
  ∃ H : Set (Occurrence Y s), Hammock Y s e extra H ∧ #H = rho

/-- The literal closure requirement for one source/end pair and one filter.
Its construction below is independent of any final ladder claim. -/
def ClosedAt (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (extra : Occurrence Y s → Prop) (rho : Cardinal.{u}) (X : Set V) : Prop :=
  ∃ H : Set (Occurrence Y s),
    MaximalUpTo {K | Hammock Y s e extra K} rho H ∧
      ∀ A ∈ H, A.vertexSet ⊆ X

theorem exists_maximalUpTo (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (extra : Occurrence Y s → Prop) (rho : Cardinal.{u}) :
    ∃ H : Set (Occurrence Y s),
      MaximalUpTo {K | Hammock Y s e extra K} rho H :=
  CarrierHammock.exists_maximalUpTo rho

/-- If the route filter already confines every admissible carrier to `R`,
intersecting a closing set with `R` preserves its actual maximal family. -/
theorem ClosedAt.inter_of_extra_subset
    {e : Option V} {extra : Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {X R : Set V}
    (hclosed : ClosedAt Y s e extra rho X)
    (hR : ∀ A, extra A → A.vertexSet ⊆ R) :
    ClosedAt Y s e extra rho (X ∩ R) := by
  obtain ⟨H, hH, hHX⟩ := hclosed
  refine ⟨H, hH, ?_⟩
  intro A hA x hx
  have hgood := (MaximalUpTo.mem hH).1 hA
  exact ⟨hHX A hA hx, hR A hgood.2.2.2.2 hx⟩

theorem ClosedAt.mono
    {e : Option V} {extra : Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {X Z : Set V}
    (hclosed : ClosedAt Y s e extra rho X) (hXZ : X ⊆ Z) :
    ClosedAt Y s e extra rho Z := by
  obtain ⟨H, hH, hHX⟩ := hclosed
  exact ⟨H, hH, fun A hA ↦ (hHX A hA).trans hXZ⟩

/-- Construct a small actual carrier closed at this pair, extending a given
small seed. No full-ladder closure is assumed or concluded. -/
theorem exists_closedAt_superset (Y : Set Gamma.DPath) (s : V) (e : Option V)
    (extra : Occurrence Y s → Prop) {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    {X : Set V} (hX : #X ≤ rho) :
    ∃ Z : Set V, X ⊆ Z ∧ #Z ≤ rho ∧ ClosedAt Y s e extra rho Z := by
  obtain ⟨H, hH⟩ := exists_maximalUpTo Y s e extra rho
  let Z := X ∪ ⋃ A : H, A.1.vertexSet
  have hcarriers : #(⋃ A : H, A.1.vertexSet) ≤ rho :=
    CarrierHammock.mk_carrierUnion_le hrho (MaximalUpTo.card_le hH)
      (fun A _ ↦ A.vertexSet_countable)
  refine ⟨Z, Set.subset_union_left, ?_, H, hH, ?_⟩
  · exact (Cardinal.mk_union_le X _).trans (Cardinal.add_le_of_le hrho hX hcarriers)
  · intro A hA x hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hx⟩)

/-- The native Claim-2 mechanism: an external good occurrence extends every
small maximal family, hence the closure has a successor-sized witness. -/
theorem hasCard_of_external {e : Option V} {extra : Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {X : Set V}
    (hclosed : ClosedAt Y s e extra rho X)
    {A : Occurrence Y s} (hA : A ∈ goodRoutes Y s e extra)
    (hcap : A.vertexSet ∩ X ⊆ endpoints s e) (hout : ¬A.vertexSet ⊆ X) :
    HasCard Y s e extra (succ rho) := by
  obtain ⟨H, hH, hHX⟩ := hclosed
  exact CarrierHammock.exists_large_of_external hH hHX hA hcap hout

/-- Insertion into the nondegenerate filtered closure makes every external
non-strong finite occurrence relationally degenerate. -/
theorem hasFiniteSwitchedPath_of_not_large_filtered
    {rho : Cardinal.{u}} {X : Set V} {extra : Occurrence Y s → Prop}
    (hclosed : ClosedAt Y s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) rho X)
    {A : Occurrence Y s} (hvalid : Valid A) (hend : A.terminal? = some t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hextra : extra A)
    (hcap : A.vertexSet ∩ X ⊆ {s, t}) (hout : ¬A.vertexSet ⊆ X)
    (hnotLarge : ¬HasCard Y s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ rho)) :
    A.HasFiniteSwitchedPathTo t := by
  by_contra hnondeg
  apply hnotLarge
  apply hasCard_of_external hclosed ?_ (by simpa using hcap) hout
  refine ⟨hvalid, hend, hs, ?_, hextra, hnondeg⟩
  intro v hv
  exact Option.some.inj hv ▸ ht

/-- Unfiltered nondegenerate specialization. -/
theorem hasFiniteSwitchedPath_of_not_large_nondegenerate
    {rho : Cardinal.{u}} {X : Set V}
    (hclosed : ClosedAt Y s (some t) (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) rho X)
    {A : Occurrence Y s} (hvalid : Valid A) (hend : A.terminal? = some t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    (hcap : A.vertexSet ∩ X ⊆ {s, t}) (hout : ¬A.vertexSet ⊆ X)
    (hnotLarge : ¬HasCard Y s (some t) (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) (succ rho)) :
    A.HasFiniteSwitchedPathTo t := by
  by_contra hnondeg
  apply hnotLarge
  apply hasCard_of_external hclosed ?_ (by simpa using hcap) hout
  refine ⟨hvalid, hend, hs, ?_, hnondeg⟩
  intro v hv
  have htv : t = v := Option.some.inj hv
  exact htv ▸ ht

/-- A large native hammock supplies a genuine good route whose interior
avoids a prescribed small set; all switching semantics stay available. -/
theorem exists_mem_avoiding {e : Option V} {extra : Occurrence Y s → Prop}
    {rho : Cardinal.{u}} {H : Set (Occurrence Y s)} {X : Set V}
    (hH : Hammock Y s e extra H) (hcard : #H = succ rho) (hX : #X ≤ rho) :
    ∃ A ∈ H, A ∈ goodRoutes Y s e extra ∧
      Disjoint (A.vertexSet \ endpoints s e) X := by
  obtain ⟨A, hA, hdisj⟩ := CarrierHammock.exists_mem_disjoint hH hcard hX
  exact ⟨A, hA, hH.1 hA, hdisj⟩

/-- The native weak-edge consequence retains the actual fixed forward
owner of the selected occurrence, not a member of an unrelated hammock. -/
theorem endpoints_same_forward_owner_of_not_large_filtered
    {W : Set Gamma.DPath} (A : CurrentSafeOccurrence W Y s)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hend : A.terminal? = some t) (hne : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    {rho : Cardinal.{u}} {X : Set V} {extra : Occurrence Y s → Prop}
    (hclosed : ClosedAt Y s (some t)
      (fun B ↦ extra B ∧ ¬B.HasFiniteSwitchedPathTo t) rho X)
    (hextra : extra (toAmbient A))
    (hcap : A.vertexSet ∩ X ⊆ {s, t}) (hout : ¬A.vertexSet ⊆ X)
    (hnotLarge : ¬HasCard Y s (some t)
      (fun B ↦ extra B ∧ ¬B.HasFiniteSwitchedPathTo t) (succ rho)) :
    ∃ q ∈ W, s ∈ q.support ∧ t ∈ q.support := by
  have hdeg := hasFiniteSwitchedPath_of_not_large_filtered hclosed
    (toAmbient_valid A hW hWfinite) (by simpa using hend) hs ht hextra
    (by simpa using hcap) (by simpa using hout) hnotLarge
  have hdegA : A.HasFiniteSwitchedPathTo t := by
    simpa only [CurrentSafeOccurrence.HasFiniteSwitchedPathTo,
      toAmbient_switchedEdges] using hdeg
  exact A.finiteDegenerate_endpoints_same_forward_owner hW hY hend hne hs ht hdegA

/-- The ordinary nondegenerate specialization retains the same owner. -/
theorem endpoints_same_forward_owner_of_not_large_nondegenerate
    {W : Set Gamma.DPath} (A : CurrentSafeOccurrence W Y s)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hend : A.terminal? = some t) (hne : s ≠ t)
    (hs : s ∉ Gamma.vertexSet Y) (ht : t ∉ Gamma.vertexSet Y)
    {rho : Cardinal.{u}} {X : Set V}
    (hclosed : ClosedAt Y s (some t) (fun B ↦ ¬B.HasFiniteSwitchedPathTo t) rho X)
    (hcap : A.vertexSet ∩ X ⊆ {s, t}) (hout : ¬A.vertexSet ⊆ X)
    (hnotLarge : ¬HasCard Y s (some t) (fun B ↦ ¬B.HasFiniteSwitchedPathTo t) (succ rho)) :
    ∃ q ∈ W, s ∈ q.support ∧ t ∈ q.support := by
  have hdeg := hasFiniteSwitchedPath_of_not_large_nondegenerate hclosed
    (toAmbient_valid A hW hWfinite) (by simpa using hend) hs ht
    (by simpa using hcap) (by simpa using hout) hnotLarge
  have hdegA : A.HasFiniteSwitchedPathTo t := by
    simpa only [CurrentSafeOccurrence.HasFiniteSwitchedPathTo,
      toAmbient_switchedEdges] using hdeg
  exact A.finiteDegenerate_endpoints_same_forward_owner hW hY hend hne hs ht hdegA

#print axioms exists_closedAt_superset
#print axioms hasCard_of_external
#print axioms hasFiniteSwitchedPath_of_not_large_nondegenerate
#print axioms exists_mem_avoiding
#print axioms endpoints_same_forward_owner_of_not_large_filtered
#print axioms endpoints_same_forward_owner_of_not_large_nondegenerate

end Erdos599.Blueprint.ColouredSafeHammock

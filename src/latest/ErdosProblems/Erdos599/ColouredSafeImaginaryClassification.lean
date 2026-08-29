/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeShortcutGraph
import ErdosProblems.Erdos599.ColouredSafeMovingLimit

/-!
# Native imaginary edges and popularity from actual closing sets

The same fixed captured-route filter is retained in the finite and infinite
branches. This does not assert a simultaneous occurrence assignment or
coerce native occurrences to the older alternating-path representation.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open ColouredSafeHammockOmegaClosure

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W Y : Set Gamma.DPath} {X persistent : Set V} {rho : Cardinal.{u}} {s t : V}

/-- The native ambient augmentation, distinct from the legacy graph. -/
def imaginaryGraph (Y : Set Gamma.DPath) (rho : Cardinal.{u}) : Digraph V where
  Adj s t := Gamma.graph.Adj s t ∨ IsImaginary Y rho s t

def IsFilteredImaginary (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (extra : ∀ s, Occurrence Y s → Prop) (s t : V) : Prop :=
  ColouredSafeHammock.HasCard Y s (some t) (extra s) (succ rho)

def IsPopular (Y : Set Gamma.DPath) (persistent : Set V)
    (rho : Cardinal.{u}) (s : V) : Prop :=
  s ∈ persistent ∨ ColouredSafeHammock.HasCard Y s none (fun _ ↦ True) (succ rho)

theorem hasCard_mono_filter
    {e : Option V} {extra extra' : Occurrence Y s → Prop}
    {card : Cardinal.{u}}
    (h : ColouredSafeHammock.HasCard Y s e extra card)
    (hfilter : ∀ A, extra A → extra' A) :
    ColouredSafeHammock.HasCard Y s e extra' card := by
  obtain ⟨H, hH, hcard⟩ := h
  refine ⟨H, ⟨?_, hH.2⟩, hcard⟩
  intro A hA
  obtain ⟨hvalid, hend, hs, ht, hExtra⟩ := hH.1 hA
  exact ⟨hvalid, hend, hs, ht, hfilter A hExtra⟩

theorem IsFilteredImaginary.isImaginary
    {extra : ∀ s, Occurrence Y s → Prop}
    (h : IsFilteredImaginary Y rho extra s t) : IsImaginary Y rho s t :=
  hasCard_mono_filter h (fun _ _ ↦ trivial)

theorem IsMarked.isFilteredImaginary
    {extra : ∀ s, Occurrence Y s → Prop}
    (h : IsMarked Y rho extra s t) : IsFilteredImaginary Y rho extra s t :=
  hasCard_mono_filter h (fun _ hA ↦ hA.1)

/-- The actual external occurrence classifies at its own optional end.
Only a finite end needs membership in the closing set. -/
theorem hasFilteredHammock_of_external_occurrence
    (A : CurrentSafeOccurrence W Y s)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    {extra : ∀ s, Occurrence Y s → Prop}
    (hclosed : FilteredOmegaClosed Y extra rho X)
    (hsX : s ∈ X) (hs : s ∉ Gamma.vertexSet Y)
    (hendX : ∀ t, A.terminal? = some t → t ∈ X)
    (hendOff : ∀ t, A.terminal? = some t → t ∉ Gamma.vertexSet Y)
    (hextra : extra s (toAmbient A))
    (hcap : A.vertexSet ∩ X ⊆ ColouredSafeHammock.endpoints s A.terminal?)
    (hout : ¬A.vertexSet ⊆ X) :
    ColouredSafeHammock.HasCard Y s A.terminal? (extra s) (succ rho) := by
  have hpair : ColouredSafeHammock.ClosedAt Y s A.terminal? (extra s) rho X := by
    cases he : A.terminal? with
    | none => exact hclosed.1 s hsX
    | some t => exact (hclosed.2 s hsX t (hendX t he)).1
  apply ColouredSafeHammock.hasCard_of_external hpair
    (A := toAmbient A) ?_ (by simpa using hcap) (by simpa using hout)
  exact ⟨toAmbient_valid A hW hfinite, by simp, hs, hendOff, hextra⟩

theorem OutsideRoute.isFilteredImaginary (R : OutsideRoute W Y X s t)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    {extra : ∀ s, Occurrence Y s → Prop}
    (hclosed : FilteredOmegaClosed Y extra rho X)
    (hextra : extra s (toAmbient R.occurrence)) :
    IsFilteredImaginary Y rho extra s t := by
  have h := hasFilteredHammock_of_external_occurrence R.occurrence hW hfinite
    hclosed R.source_mem R.source_off
    (fun v hv ↦ (Option.some.inj (R.terminal_eq.symm.trans hv)) ▸ R.terminal_mem)
    (fun v hv ↦ (Option.some.inj (R.terminal_eq.symm.trans hv)) ▸ R.terminal_off)
    hextra (by simpa only [R.terminal_eq, ColouredSafeHammock.endpoints_some]
      using R.cut_intersection) R.outside
  simpa only [R.terminal_eq, IsFilteredImaginary] using h

/-- An infinite external captured occurrence certifies native popularity;
it is not prematurely declared strong, nor assigned a finite endpoint. -/
theorem isPopular_of_external_infinite
    (A : CurrentSafeOccurrence W Y s)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    {extra : ∀ s, Occurrence Y s → Prop}
    (hclosed : FilteredOmegaClosed Y extra rho X)
    (hsX : s ∈ X) (hs : s ∉ Gamma.vertexSet Y)
    (hend : A.terminal? = none) (hextra : extra s (toAmbient A))
    (hcap : A.vertexSet ∩ X ⊆ {s}) (hout : ¬A.vertexSet ⊆ X) :
    IsPopular Y persistent rho s := by
  right
  have h := hasFilteredHammock_of_external_occurrence A hW hfinite
    hclosed hsX hs (by simp [hend]) (by simp [hend]) hextra
    (by simpa only [hend, ColouredSafeHammock.endpoints_none] using hcap) hout
  rw [hend] at h
  exact hasCard_mono_filter h (fun _ _ ↦ trivial)

/-- Every literal inside-row edge or native filtered shortcut is an edge
of the native ambient augmentation. -/
theorem adj_nativeImaginaryGraph_of_filtered_certificate
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    {extra : ∀ s, Occurrence Y s → Prop}
    (hclosed : FilteredOmegaClosed Y extra rho X)
    (h : (s, t) ∈ Alternating.familyEdges W ∨
      ∃ R : OutsideRoute W Y X s t, extra s (toAmbient R.occurrence)) :
    (imaginaryGraph Y rho).Adj s t := by
  rcases h with hrow | ⟨R, hR⟩
  · left
    simp only [Alternating.familyEdges, Set.mem_iUnion] at hrow
    obtain ⟨p, hp, he⟩ := hrow
    exact p.edgeSet_subset_adj he
  · exact Or.inr (R.isFilteredImaginary hW hfinite hclosed hR).isImaginary

#print axioms hasFilteredHammock_of_external_occurrence
#print axioms OutsideRoute.isFilteredImaginary
#print axioms isPopular_of_external_infinite
#print axioms adj_nativeImaginaryGraph_of_filtered_certificate

end Erdos599.Blueprint.ColouredSafeShortcutGraph

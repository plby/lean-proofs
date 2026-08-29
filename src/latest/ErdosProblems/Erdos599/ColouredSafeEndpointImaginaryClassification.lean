/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointHammockClosure
import ErdosProblems.Erdos599.ColouredSafeImaginaryClassification

/-!
# Classification with the explicit endpoint-pruned reference

These predicates keep the reference indexed by the displayed endpoints.
They are not identified with imaginary edges for the unchanged full warp.
An external occurrence gives the large ordinary hammock. If the finite
pair is not marked, nondegenerate closure forces its endpoints onto one
original forward owner. No simultaneous grounding is asserted here.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointHammock

open Set Cardinal Order DirectedPath
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W Y : Set Gamma.DPath} {X persistent : Set V}
variable {rho : Cardinal.{u}} {s t : V} {e : Option V}
variable {extra : ∀ s e, Route Y s e → Prop}

def IsImaginary (Y : Set Gamma.DPath) (extra : ∀ s e, Route Y s e → Prop)
    (rho : Cardinal.{u}) (s t : V) : Prop :=
  ColouredSafeHammock.HasCard (reference Y s (some t)) s (some t)
    (extra s (some t)) (succ rho)

def IsMarked (Y : Set Gamma.DPath) (extra : ∀ s e, Route Y s e → Prop)
    (rho : Cardinal.{u}) (s t : V) : Prop :=
  ColouredSafeHammock.HasCard (reference Y s (some t)) s (some t)
    (fun A ↦ extra s (some t) A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ rho)

def IsPopular (Y : Set Gamma.DPath) (extra : ∀ s e, Route Y s e → Prop)
    (persistent : Set V) (rho : Cardinal.{u}) (s : V) : Prop :=
  s ∈ persistent ∨ ColouredSafeHammock.HasCard (reference Y s none) s none
    (extra s none) (succ rho)

theorem IsMarked.isImaginary (h : IsMarked Y extra rho s t) :
    IsImaginary Y extra rho s t :=
  ColouredSafeShortcutGraph.hasCard_mono_filter h (fun _ hA ↦ hA.1)

theorem hasCard_of_external_occurrence
    (A : CurrentSafeOccurrence W (reference Y s e) s)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hclosed : Closed Y extra rho X) (hend : A.terminal? = e)
    (hends : ColouredSafeHammock.endpoints s e ⊆ X)
    (hextra : extra s e (toAmbient A))
    (hcap : A.vertexSet ∩ X ⊆ ColouredSafeHammock.endpoints s e)
    (hout : ¬A.vertexSet ⊆ X) :
    ColouredSafeHammock.HasCard (reference Y s e) s e (extra s e) (succ rho) := by
  apply ColouredSafeHammock.hasCard_of_external (hclosed s e hends).1
    (A := toAmbient A) ?_ (by simpa using hcap) (by simpa using hout)
  exact ⟨toAmbient_valid A hW hfinite, by simpa using hend,
    source_off, fun _ ht ↦ terminal_off ht, hextra⟩

/-- This conclusion refers to the actual original forward warp, even when
the displayed endpoints belong to the full reference before pruning. -/
theorem common_owner_of_not_marked
    (A : CurrentSafeOccurrence W (reference Y s e) s)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) (hY : Gamma.IsWarp Y)
    (hclosed : Closed Y extra rho X) (hend : A.terminal? = e) (he : e = some t)
    (hne : s ≠ t) (hends : ColouredSafeHammock.endpoints s e ⊆ X)
    (hextra : extra s e (toAmbient A))
    (hcap : A.vertexSet ∩ X ⊆ ColouredSafeHammock.endpoints s e)
    (hout : ¬A.vertexSet ⊆ X) (hnot : ¬IsMarked Y extra rho s t) :
    ∃ p ∈ W, s ∈ p.support ∧ t ∈ p.support := by
  subst e
  exact ColouredSafeHammock.endpoints_same_forward_owner_of_not_large_filtered
    A hW hfinite (ColouredSafeEndpointReference.isWarp hY) hend hne
    source_off (terminal_off rfl) ((hclosed s (some t) hends).2 t rfl)
    hextra (by simpa only [ColouredSafeHammock.endpoints_some] using hcap) hout hnot

#print axioms hasCard_of_external_occurrence
#print axioms common_owner_of_not_marked

end Erdos599.Blueprint.ColouredSafeEndpointHammock

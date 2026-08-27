/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleRootWeights
import ErdosProblems.Erdos207.PendingGreedySurvival

/-! # Multiplicity-preserving witnesses for local forbidden configurations -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceNibbleCodes
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ) :=
  terminalOmissionCodes W (familyExtensions F {T}) (fun E ↦ E \ {T}) (j' - j)

def sourceNibbleRemaining
    {V : Type*} [DecidableEq V] (T : TripleOn V) (x : TripleSystemOn V × TripleSystemOn V) : TripleSystemOn V :=
  (x.1 \ {T}) \ x.2

theorem sourceNibbleCode_data
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j') :
    x.1 ∈ F ∧ T ∈ x.1 ∧ x.2 ⊆ x.1 \ {T} ∧ x.2.card = j' - j ∧
      ∀ S ∈ sourceNibbleRemaining T x, W.level S = Fin.last ell := by
  have hm := mem_terminalOmissionCodes_iff.mp hx
  have he := mem_familyExtensions_iff.mp hm.1
  have ha := mem_terminalRemainderChoices_iff.mp hm.2
  exact ⟨he.1, singleton_subset_iff.mp he.2, ha.1, ha.2.1, ha.2.2⟩

theorem sourceNibbleRemaining_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hj : 4 ≤ j) (hjj : j ≤ j')
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j') :
    (sourceNibbleRemaining T x).card = j - 3 := by
  have hm := sourceNibbleCode_data hx
  unfold sourceNibbleRemaining
  rw [card_sdiff_of_subset hm.2.2.1, card_sdiff_of_subset (singleton_subset_iff.mpr hm.2.1),
    huniform x.1 hm.1, card_singleton, hm.2.2.2.1]
  omega

theorem sourceNibbleRemaining_packing
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    (hpacking : ∀ E ∈ F, IsPackingOn E)
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j') :
    IsPackingOn (sourceNibbleRemaining T x) :=
  (hpacking x.1 (sourceNibbleCode_data hx).1).mono (sdiff_subset.trans sdiff_subset)

theorem sourceNibbleRemaining_edge_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hpacking : ∀ E ∈ F, IsPackingOn E)
    (hj : 4 ≤ j) (hjj : j ≤ j')
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j') :
    ((sourceNibbleRemaining T x).biUnion tripleEdgeFinset).card = 3 * (j - 3) := by
  rw [card_biUnion_tripleEdgeFinset_of_isPackingOn (sourceNibbleRemaining_packing hpacking hx),
    sourceNibbleRemaining_card huniform hj hjj hx]

end

end Erdos207

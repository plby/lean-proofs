/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.NondegenerateHammockClosure

/-!
# Cardinal bounds for the extra nondegenerate-hammock rows

This file constructs the vertex row, not just a bound on a hypothetical
row. Every eligible pair receives an actual maximal-up-to family. Its
insertion in the causal scheduler is deliberately not asserted here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {before innerRoof outerRoof : Set V}

noncomputable def chosenNondegenerateHammock
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (q : EligiblePair before innerRoof outerRoof) : Set (AltPath Gamma.graph) :=
  Classical.choose
    (exists_nondegenerateHammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho)

theorem chosenNondegenerateHammock_spec
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (q : EligiblePair before innerRoof outerRoof) :
    NondegenerateHammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho
      (chosenNondegenerateHammock Gamma Y rho q) :=
  Classical.choose_spec
    (exists_nondegenerateHammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho)

def chosenNondegenerateHammockVertices
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (q : EligiblePair before innerRoof outerRoof) : Set V :=
  ⋃ Q : chosenNondegenerateHammock Gamma Y rho q, Q.1.vertexSet

def allNondegenerateHammockVertices
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (before innerRoof outerRoof : Set V) : Set V :=
  ⋃ q : EligiblePair before innerRoof outerRoof,
    chosenNondegenerateHammockVertices Gamma Y rho q

theorem chosenNondegenerateHammock_contained_all
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (q : EligiblePair before innerRoof outerRoof) :
    HammockContained (chosenNondegenerateHammock Gamma Y rho q)
      (allNondegenerateHammockVertices Gamma Y rho before innerRoof outerRoof) := by
  intro x hx
  simp only [hammockVertexSet, allNondegenerateHammockVertices,
    chosenNondegenerateHammockVertices, Set.mem_iUnion] at hx ⊢
  obtain ⟨Q, hQ, hxQ⟩ := hx
  exact ⟨q, ⟨Q, hQ⟩, hxQ⟩

theorem allNondegenerateHammockVertices_closed
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (before innerRoof outerRoof : Set V) :
    NondegenerateHammockClosedUpTo Gamma Y
      (allNondegenerateHammockVertices Gamma Y rho before innerRoof outerRoof)
      before innerRoof outerRoof rho := by
  intro u₀ e helig
  let q : EligiblePair before innerRoof outerRoof := ⟨(u₀, e), helig⟩
  exact ⟨chosenNondegenerateHammock Gamma Y rho q,
    chosenNondegenerateHammock_spec Gamma Y rho q,
    chosenNondegenerateHammock_contained_all Gamma Y rho q⟩

private theorem mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hf : ∀ i, #(f i) ≤ kappa) :
    #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

theorem mk_chosenNondegenerateHammockVertices_le
    (Gamma : DWeb V) (Y : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (q : EligiblePair before innerRoof outerRoof) :
    #(chosenNondegenerateHammockVertices Gamma Y rho q) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact (chosenNondegenerateHammock_spec Gamma Y rho q).card_le.trans hrho
  · intro Q
    exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa

theorem mk_allNondegenerateHammockVertices_le
    (Gamma : DWeb V) (Y : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hbefore : #before ≤ kappa) :
    #(allNondegenerateHammockVertices Gamma Y rho before innerRoof outerRoof)
      ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact mk_eligiblePair_le hkappa hbefore
  · exact mk_chosenNondegenerateHammockVertices_le Gamma Y hkappa hrho

/-- The location premise is pointwise for the actual eligible pair. It
does not incorrectly require every safe path in the whole graph to be
roofed by one fixed stage. -/
theorem allNondegenerateHammockVertices_subset
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    {Z : Set V}
    (hlocation : ∀ (q : EligiblePair before innerRoof outerRoof)
      (Q : AltPath Gamma.graph),
      IsSafe Y Q → Q.initial = q.1.1 → HasEnd Q q.1.2 →
      ¬IsDegenerate Y Q q.1.2 → Q.vertexSet ⊆ Z) :
    allNondegenerateHammockVertices Gamma Y rho before innerRoof outerRoof
      ⊆ Z := by
  intro x hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.1 hx
  have hH := (chosenNondegenerateHammock_spec Gamma Y rho q).isNondegenerateHammock
  have hQ := hH.1.1 Q.1 Q.2
  exact hlocation q Q.1 hQ.1 hQ.2.1 hQ.2.2 (hH.2 Q.1 Q.2) hxQ

#print axioms allNondegenerateHammockVertices_closed
#print axioms mk_allNondegenerateHammockVertices_le
#print axioms allNondegenerateHammockVertices_subset

end Erdos599.Blueprint

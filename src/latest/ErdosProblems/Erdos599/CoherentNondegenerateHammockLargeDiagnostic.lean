/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FilteredNondegenerateHammockLargeWitness
import ErdosProblems.Erdos599.LargeHammockMaximalCardinality
import ErdosProblems.Erdos599.CoherentNondegenerateHammockTracker

/-!
# A causal diagnostic choice of a large roof-filtered hammock

This is the successor-sized companion to the coherent capped tracker.  At a
stage it chooses an actual filtered nondegenerate hammock of cardinality
`kappa^+` when one exists, and chooses the empty family otherwise.  No bare
strong-edge predicate and no switching-safety conversion occurs here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A cardinality statement which retains the path filter on its witness. -/
def HasFilteredNondegenerateHammockCard
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (mu : Cardinal.{u}) : Prop :=
  ∃ H : Set (AltPath Gamma.graph),
    FilteredNondegenerateHammock Gamma Y u₀ e P H ∧ #H = mu

/-- Total choice: the requested filtered family when it exists, otherwise
the empty family. -/
noncomputable def chosenFilteredNondegenerateHammock
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (mu : Cardinal.{u}) :
    Set (AltPath Gamma.graph) := by
  classical
  exact if h : HasFilteredNondegenerateHammockCard Gamma Y u₀ e P mu then
    Classical.choose h
  else ∅

theorem chosenFilteredNondegenerateHammock_spec_of_exists
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (mu : Cardinal.{u})
    (h : HasFilteredNondegenerateHammockCard Gamma Y u₀ e P mu) :
    FilteredNondegenerateHammock Gamma Y u₀ e P
        (chosenFilteredNondegenerateHammock Gamma Y u₀ e P mu) ∧
      #(chosenFilteredNondegenerateHammock Gamma Y u₀ e P mu) = mu := by
  rw [chosenFilteredNondegenerateHammock, dif_pos h]
  exact Classical.choose_spec h

theorem chosenFilteredNondegenerateHammock_eq_empty_of_not_exists
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (mu : Cardinal.{u})
    (h : ¬HasFilteredNondegenerateHammockCard Gamma Y u₀ e P mu) :
    chosenFilteredNondegenerateHammock Gamma Y u₀ e P mu = ∅ := by
  rw [chosenFilteredNondegenerateHammock, dif_neg h]

theorem chosenFilteredNondegenerateHammock_card_le
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (mu : Cardinal.{u}) :
    #(chosenFilteredNondegenerateHammock Gamma Y u₀ e P mu) ≤ mu := by
  by_cases h : HasFilteredNondegenerateHammockCard Gamma Y u₀ e P mu
  · rw [(chosenFilteredNondegenerateHammock_spec_of_exists
      Gamma Y u₀ e P mu h).2]
  · rw [chosenFilteredNondegenerateHammock_eq_empty_of_not_exists
      Gamma Y u₀ e P mu h]
    simp

namespace CoherentNondegenerateHammockLargeDiagnostic

variable (Gamma : DWeb V) (kappa : Cardinal.{u})

/-- The actual stage diagnostic family.  The filter is containment in the
current roof row. -/
noncomputable def chosenAt
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    Set (AltPath Gamma.graph) :=
  chosenFilteredNondegenerateHammock Gamma (reference a) x (.vertex v)
    (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
    (succ kappa)

theorem chosenAt_spec_of_exists
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa))
    (h : HasFilteredNondegenerateHammockCard Gamma (reference a) x (.vertex v)
      (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
      (succ kappa)) :
    FilteredNondegenerateHammock Gamma (reference a) x (.vertex v)
        (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
        (chosenAt Gamma kappa reference roofAt x v a) ∧
      #(chosenAt Gamma kappa reference roofAt x v a) = succ kappa := by
  exact chosenFilteredNondegenerateHammock_spec_of_exists
    Gamma (reference a) x (.vertex v)
      (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
      (succ kappa) h

theorem chosenAt_eq_empty_of_not_exists
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa))
    (h : ¬HasFilteredNondegenerateHammockCard Gamma (reference a) x (.vertex v)
      (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
      (succ kappa)) :
    chosenAt Gamma kappa reference roofAt x v a = ∅ := by
  exact chosenFilteredNondegenerateHammock_eq_empty_of_not_exists
    Gamma (reference a) x (.vertex v)
      (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
      (succ kappa) h

theorem chosenAt_card_le
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    #(chosenAt Gamma kappa reference roofAt x v a) ≤ succ kappa :=
  chosenFilteredNondegenerateHammock_card_le
    Gamma (reference a) x (.vertex v)
      (CoherentNondegenerateHammockTracker.Roofed Gamma kappa roofAt a)
      (succ kappa)

theorem chosenAt_vertexSet_card_le
    (hkappa : aleph0 ≤ kappa)
    (reference : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    #(hammockVertexSet (chosenAt Gamma kappa reference roofAt x v a))
      ≤ succ kappa :=
  mk_hammockVertexSet_le (hkappa.trans (le_succ kappa))
    (chosenAt_card_le Gamma kappa reference roofAt x v a)

/-- The diagnostic reads only the current reference and roof.  Prefix
agreement is the convenient causal-row interface. -/
theorem chosenAt_congr_le
    (reference reference' : Ladder.Stage (succ kappa) → Set Gamma.DPath)
    (roofAt roofAt' : Ladder.Stage (succ kappa) → Set V)
    (x v : V) (a : Ladder.Stage (succ kappa))
    (href : ∀ b, b ≤ a → reference b = reference' b)
    (hroof : ∀ b, b ≤ a → roofAt b = roofAt' b) :
    chosenAt Gamma kappa reference roofAt x v a =
      chosenAt Gamma kappa reference' roofAt' x v a := by
  unfold chosenAt CoherentNondegenerateHammockTracker.Roofed
  rw [href a le_rfl, hroof a le_rfl]

#print axioms chosenFilteredNondegenerateHammock_spec_of_exists
#print axioms chosenFilteredNondegenerateHammock_card_le
#print axioms chosenAt_spec_of_exists
#print axioms chosenAt_vertexSet_card_le
#print axioms chosenAt_congr_le

end CoherentNondegenerateHammockLargeDiagnostic
end Erdos599.Blueprint

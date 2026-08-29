/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FilteredNondegenerateHammockClosure

/-!
# Retaining the filter on the large witness

The outside-insertion argument for a filtered maximal-up-to hammock already
produces a successor-sized *filtered* hammock in its large branch.  The
ordinary strong-edge conclusion forgets that filter.  This additive theorem
retains the witness needed by later roof-contained cardinal-avoidance
arguments; it does not claim that an arbitrary strong edge has such a
witness.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {u₀ : V} {e : AltEnd V} {rho : Cardinal.{u}}
variable {P : AltPath Gamma.graph → Prop}

theorem FilteredNondegenerateHammockMaximalUpTo.exists_filteredCard_succ_of_outside
    {H : Set (AltPath Gamma.graph)} {X : Set V} {Q : AltPath Gamma.graph}
    (hH : FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ e P rho H)
    (hHX : HammockContained H X)
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀) (hend : HasEnd Q e)
    (hnondeg : ¬IsDegenerate Y Q e) (hP : P Q)
    (hdisj : Disjoint (hammockInterior u₀ e Q) X)
    (houtside : ¬Q.vertexSet ⊆ X) :
    ∃ K : Set (AltPath Gamma.graph),
      FilteredNondegenerateHammock Gamma Y u₀ e P K ∧
        #K = succ rho := by
  have hinsert := hH.isFilteredNondegenerateHammock.insert
    hsafe hstart hend hnondeg hP
    (disjoint_hammockInterior_of_contained hHX hdisj)
  rcases hH with hsmall | hlarge
  · have heq : H = insert Q H :=
      hsmall.2.1.eq_of_subset hinsert (Set.subset_insert Q H)
    have hQH : Q ∈ H := heq.symm.subset (Set.mem_insert Q H)
    exact (houtside fun x hx ↦
      hHX (Set.mem_iUnion.2 ⟨Q, Set.mem_iUnion.2 ⟨hQH, hx⟩⟩)).elim
  · obtain ⟨K, hK, hKcard⟩ := hlarge.2.2
    exact ⟨K, hK, hKcard⟩

#print axioms
  FilteredNondegenerateHammockMaximalUpTo.exists_filteredCard_succ_of_outside

end Erdos599.Blueprint

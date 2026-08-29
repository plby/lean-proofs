/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FilteredNondegenerateHammockExtension

/-!
# The strong-edge consequence of roof-filtered maximality

Only maximality among paths satisfying the filter is used. Thus a tracker
restricted to the limiting roof suffices for outside intervals already
proved to be contained in that roof. The conclusion is the original strong
imaginary-edge predicate, not a weakened substitute.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {u₀ : V} {e : AltEnd V} {rho : Cardinal.{u}}
variable {P : AltPath Gamma.graph → Prop}

theorem FilteredNondegenerateHammockMaximalUpTo.hasNondegenerateHammockCard_of_outside
    {H : Set (AltPath Gamma.graph)} {X : Set V} {Q : AltPath Gamma.graph}
    (hH : FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ e P rho H)
    (hHX : HammockContained H X)
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀) (hend : HasEnd Q e)
    (hnondeg : ¬IsDegenerate Y Q e) (hP : P Q)
    (hdisj : Disjoint (hammockInterior u₀ e Q) X)
    (houtside : ¬Q.vertexSet ⊆ X) :
    HasNondegenerateHammockCard Gamma Y u₀ e (succ rho) := by
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
    exact ⟨K, hK.1, hKcard⟩

/-- This is the precise contraposition used for an actual outside interval.
The filter hypothesis remains explicit until the roof certificate is supplied. -/
theorem FilteredNondegenerateHammockMaximalUpTo.isDegenerate_of_not_strong
    {v : V} {H : Set (AltPath Gamma.graph)} {X : Set V}
    {Q : AltPath Gamma.graph}
    (hH : FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ (.vertex v) P rho H)
    (hHX : HammockContained H X)
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀)
    (hend : HasEnd Q (.vertex v)) (hP : P Q)
    (hdisj : Disjoint (hammockInterior u₀ (.vertex v) Q) X)
    (houtside : ¬Q.vertexSet ⊆ X)
    (hnot : ¬IsStrongImaginaryEdge Gamma Y rho u₀ v) :
    IsDegenerate Y Q (.vertex v) := by
  by_contra hnondeg
  exact hnot (hH.hasNondegenerateHammockCard_of_outside hHX
    hsafe hstart hend hnondeg hP hdisj houtside)

/-- The finite, distinct-endpoint closure actually needed for shortcut
edges. A root-reachable edge cannot be a loop; no assertion about
same-endpoint degeneracy or infinite nondegeneracy is bundled here. -/
def FiniteFilteredHammockClosedUpTo
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X before innerRoof outerRoof : Set V)
    (P : AltPath Gamma.graph → Prop) (rho : Cardinal.{u}) : Prop :=
  ∀ u₀ v, u₀ ≠ v → HammockEligible before innerRoof outerRoof u₀ (.vertex v) →
    ∃ H : Set (AltPath Gamma.graph),
      FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ (.vertex v) P rho H ∧
        HammockContained H X

theorem FiniteFilteredHammockClosedUpTo.isDegenerate_of_not_strong
    {X before innerRoof outerRoof : Set V} {v : V}
    {Q : AltPath Gamma.graph}
    (hclosed : FiniteFilteredHammockClosedUpTo Gamma Y
      X before innerRoof outerRoof P rho)
    (hne : u₀ ≠ v)
    (helig : HammockEligible before innerRoof outerRoof u₀ (.vertex v))
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀)
    (hend : HasEnd Q (.vertex v)) (hP : P Q)
    (hdisj : Disjoint (hammockInterior u₀ (.vertex v) Q) X)
    (houtside : ¬Q.vertexSet ⊆ X)
    (hnot : ¬IsStrongImaginaryEdge Gamma Y rho u₀ v) :
    IsDegenerate Y Q (.vertex v) := by
  obtain ⟨H, hH, hHX⟩ := hclosed u₀ v hne helig
  exact hH.isDegenerate_of_not_strong hHX hsafe hstart hend hP hdisj houtside hnot

#print axioms
  FilteredNondegenerateHammockMaximalUpTo.hasNondegenerateHammockCard_of_outside
#print axioms FilteredNondegenerateHammockMaximalUpTo.isDegenerate_of_not_strong
#print axioms FiniteFilteredHammockClosedUpTo.isDegenerate_of_not_strong

end Erdos599.Blueprint

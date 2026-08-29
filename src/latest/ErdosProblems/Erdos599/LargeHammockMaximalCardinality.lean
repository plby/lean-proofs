/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SeededHammock
import ErdosProblems.Erdos599.Blueprint931

/-!
# A small inclusion-maximal hammock excludes a successor-sized hammock

If a successor-sized hammock exists, an inclusion-maximal hammock cannot
have cardinality at most the predecessor cardinal.  We first remove the
small maximal family from the large witness.  This is important for
endpoint-only paths, whose hammock interior can be empty: selecting merely
by interior avoidance would not by itself prove that the selected path is
new.

The remaining family still has successor cardinality.  Its avoidance
selector supplies a path outside the maximal family whose interior avoids
the entire vertex carrier of that family, so adjoining it contradicts
inclusion maximality.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- The union of the countable carriers of a `kappa`-small path family is
again `kappa`-small for infinite `kappa`. -/
theorem mk_hammockVertexSet_le {H : Set (AltPath Gamma.graph)}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hHcard : #H ≤ kappa) : #(hammockVertexSet H) ≤ kappa := by
  have heq : hammockVertexSet H = ⋃ Q : H, Q.1.vertexSet := by
    ext x
    simp only [hammockVertexSet, Set.mem_iUnion]
    constructor
    · rintro ⟨Q, hQ, hxQ⟩
      exact ⟨⟨Q, hQ⟩, hxQ⟩
    · rintro ⟨Q, hxQ⟩
      exact ⟨Q.1, Q.2, hxQ⟩
  rw [heq]
  refine (Cardinal.mk_iUnion_le (fun Q : H ↦ Q.1.vertexSet)).trans ?_
  apply Cardinal.mul_le_of_le hkappa hHcard
  apply ciSup_le'
  intro Q
  exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa

/-- Removing a `kappa`-small subfamily from a `kappa⁺`-sized family leaves
cardinality `kappa⁺`. -/
private theorem mk_sdiff_eq_succ_of_card_le
    {X : Type u} {H M : Set X} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hHcard : #H = succ kappa)
    (hMcard : #M ≤ kappa) : #(H \ M : Set X) = succ kappa := by
  apply le_antisymm
  · rw [← hHcard]
    exact Cardinal.mk_subtype_mono Set.sdiff_subset
  · by_contra hnot
    have hdiffLt : #(H \ M : Set X) < succ kappa := lt_of_not_ge hnot
    have hdiffLe : #(H \ M : Set X) ≤ kappa := lt_succ_iff.mp hdiffLt
    have hsuccLe : succ kappa ≤ kappa := by
      calc
        succ kappa = #H := hHcard.symm
        _ ≤ #(H \ M : Set X) + #M := Cardinal.le_mk_sdiff_add_mk H M
        _ ≤ kappa := Cardinal.add_le_of_le hkappa hdiffLe hMcard
    exact (not_le_of_gt (lt_succ kappa)) hsuccLe

/-- A successor-sized hammock rules out an inclusion-maximal hammock of
predecessor size. -/
theorem not_hasHammockCard_succ_of_maximal_of_card_le
    {u₀ : V} {e : AltEnd V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) {M : Set (AltPath Gamma.graph)}
    (hMmax : Maximal (fun K ↦ Hammock Gamma Y u₀ e K) M)
    (hMcard : #M ≤ kappa) :
    ¬ HasHammockCard Gamma Y u₀ e (succ kappa) := by
  rintro ⟨H, hH, hHcard⟩
  let R : Set (AltPath Gamma.graph) := H \ M
  have hR : Hammock Gamma Y u₀ e R := hH.subset Set.sdiff_subset
  have hRcard : #R = succ kappa :=
    mk_sdiff_eq_succ_of_card_le hkappa hHcard hMcard
  have hVertices : #(hammockVertexSet M) ≤ kappa :=
    mk_hammockVertexSet_le hkappa hMcard
  obtain ⟨Q, hQR, hQsafe, hQinitial, hQend, hQdisjoint⟩ :=
    exists_mem_hammock_disjoint_of_mk_eq hR hRcard hVertices
  have hMcontained : HammockContained M (hammockVertexSet M) :=
    Set.Subset.rfl
  have hInsert : Hammock Gamma Y u₀ e (insert Q M) :=
    hMmax.1.insert hQsafe hQinitial hQend
      (disjoint_hammockInterior_of_contained hMcontained hQdisjoint)
  have hEq : M = insert Q M :=
    hMmax.eq_of_subset hInsert (Set.subset_insert Q M)
  have hQM : Q ∈ M := hEq.symm.subset (Set.mem_insert Q M)
  exact hQR.2 hQM

#print axioms mk_hammockVertexSet_le
#print axioms not_hasHammockCard_succ_of_maximal_of_card_le

end Blueprint
end Erdos599

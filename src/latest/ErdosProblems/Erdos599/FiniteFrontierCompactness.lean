/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Order

/-!
# Finite-path compactness at a moving frontier

Only the test set is finite.  Neither the index type nor a global reference
warp is assumed finite.  The geometric identity identifying a ladder frontier
with the difference of two unions remains explicit in the wrapper theorem.
-/

namespace Erdos599
namespace FiniteFrontierCompactness

universe u v

/-- A finite set meeting cofinally many frontiers meets the difference of
the unions, provided the discarded sets grow monotonically. -/
theorem finite_meets_limitBoundary_of_cofinal
    {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
    {F : Set V} (hF : F.Finite) (R D : I → Set V)
    (hD : Monotone D)
    (hmeet : ∀ i, ∃ j, i ≤ j ∧ (F ∩ (R j \ D j)).Nonempty) :
    (F ∩ ((⋃ i, R i) \ ⋃ i, D i)).Nonempty := by
  classical
  by_contra hnone
  have hbound : ∀ x : F, ∃ i, ∀ j, i ≤ j → x.1 ∉ R j \ D j := by
    intro x
    by_cases hxR : x.1 ∈ ⋃ i, R i
    · have hxD : x.1 ∈ ⋃ i, D i := by
        by_contra hxD
        exact hnone ⟨x.1, x.2, hxR, hxD⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxD
      exact ⟨i, fun j hij hxj ↦ hxj.2 (hD hij hxi)⟩
    · let i : I := Classical.choice inferInstance
      exact ⟨i, fun j _ hxj ↦ hxR (Set.mem_iUnion.2 ⟨j, hxj.1⟩)⟩
  let : Fintype F := hF.fintype
  choose bound hbound using hbound
  obtain ⟨i, hi⟩ := Finite.exists_le bound
  obtain ⟨j, hij, x, hxF, hxj⟩ := hmeet i
  exact hbound ⟨x, hxF⟩ j ((hi ⟨x, hxF⟩).trans hij) hxj

/-- Apply finite frontier compactness after proving the actual geometric
identity for the limiting frontier. -/
theorem finite_meets_frontier_of_cofinal
    {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
    {F T : Set V} (hF : F.Finite) (R D : I → Set V)
    (hD : Monotone D) (hT : T = (⋃ i, R i) \ ⋃ i, D i)
    (hmeet : ∀ i, ∃ j, i ≤ j ∧ (F ∩ (R j \ D j)).Nonempty) :
    (F ∩ T).Nonempty := by
  rw [hT]
  exact finite_meets_limitBoundary_of_cofinal hF R D hD hmeet

#print axioms finite_meets_limitBoundary_of_cofinal
#print axioms finite_meets_frontier_of_cofinal

end FiniteFrontierCompactness
end Erdos599

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.PolytopeCap

/-!
# Assembling polytope caps

The final combinatorial step of Pohoata--Zakharov chooses several caps, one
inside each of several clusters.  For the cap in cluster `i`, the auxiliary
polyhedron contains every other chosen cluster.  Its defining exposed-point
condition therefore exposes the same point in the union of all the caps.
-/

namespace Erdos651

open Set

noncomputable section

/-- Caps relative to polyhedra which contain all the other caps assemble to a
set in convex position.  No disjointness hypothesis is needed: membership in
more than one cap only makes the point fall under the `i = j` branch as well. -/
theorem inConvexPosition_biUnion_of_pCaps {q : ℕ}
    (P : Fin q → Set (Point 3)) (K : Fin q → Finset (Point 3))
    (hcap : ∀ i, PCap (P i) (K i))
    (hothers : ∀ i j, i ≠ j → (↑(K j) : Set (Point 3)) ⊆ P i) :
    InConvexPosition (Finset.univ.biUnion K) := by
  classical
  intro x hxU hxHull
  obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hxU
  apply (hcap i).2 x hxi
  apply convexHull_mono (s := (↑((Finset.univ.biUnion K).erase x) : Set (Point 3)))
  · intro y hy
    have hyU : y ∈ Finset.univ.biUnion K := Finset.mem_of_mem_erase hy
    obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hyU
    by_cases hij : i = j
    · right
      subst j
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hy, hyj⟩
    · left
      exact hothers i j hij hyj
  · exact hxHull

/-- The same assembly lemma with an explicit ambient-cardinality conclusion.
This is the form used after choosing equal-sized caps. -/
theorem containsConvexSubset_of_biUnion_pCaps {q n : ℕ}
    (P : Fin q → Set (Point 3)) (K : Fin q → Finset (Point 3))
    (hcap : ∀ i, PCap (P i) (K i))
    (hothers : ∀ i j, i ≠ j → (↑(K j) : Set (Point 3)) ⊆ P i)
    (hcard : n ≤ (Finset.univ.biUnion K).card) :
    ContainsConvexSubset 3 n (Finset.univ.biUnion K) := by
  let U := Finset.univ.biUnion K
  have hU : InConvexPosition U := inConvexPosition_biUnion_of_pCaps P K hcap hothers
  obtain ⟨Y, hYU, hYcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨Y, hYU, hYcard, ?_⟩
  intro x hxY hxHull
  apply hU x (hYU hxY)
  exact convexHull_mono (by
    intro y hy
    exact Finset.erase_subset_erase x hYU hy) hxHull

end

end Erdos651

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Turning disjoint short-route reservoirs into clique subdivisions. -/

import ErdosProblems.Erdos717.GreedySelection
import ErdosProblems.Erdos718.Erdos718Core

open Function Set
open SimpleGraph

namespace Erdos717

/-- A path between fixed endpoints whose interior is exactly the finite set
`A`.  Reservoir constructions can use this interface without exposing their
particular tuple representation. -/
structure ShortRoute {V : Type*} (G : SimpleGraph V) (u v : V)
    (A : Finset V) where
  path : G.Walk u v
  isPath : path.IsPath
  interior_eq : Erdos718.walkInteriorSet path = (A : Set V)

def ShortRoute.mapLe {V : Type*} {G H : SimpleGraph V} {u v : V}
    {A : Finset V} (R : ShortRoute G u v A) (h : G ≤ H) :
    ShortRoute H u v A where
  path := R.path.mapLe h
  isPath := R.isPath.mapLe h
  interior_eq := by
    simpa only [Erdos718.walkInteriorSet,
      SimpleGraph.Walk.support_mapLe_eq_support] using R.interior_eq

/-- Pairwise-disjoint reservoirs, each larger than three times the number of
missing branch pairs and consisting of routes with at most three internal
vertices, can be greedily assembled into a topological clique. -/
theorem containsCliqueSubdivision_of_short_route_reservoir
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (branch : Fin r ↪ V)
    (C : Erdos718.CliqueEdge r → Finset (Finset V))
    (hcard : ∀ e, ¬G.Adj (branch e.1.1) (branch e.1.2) →
      3 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card < (C e).card)
    (hinternal : ∀ e,
      ¬G.Adj (branch e.1.1) (branch e.1.2) →
      (C e : Set (Finset V)).Pairwise Disjoint)
    (hsmall : ∀ e A, A ∈ C e → A.card ≤ 3)
    (hroute : ∀ e, ¬G.Adj (branch e.1.1) (branch e.1.2) →
      ∀ A ∈ C e, Nonempty (ShortRoute G (branch e.1.1) (branch e.1.2) A))
    (havoid : ∀ e, ¬G.Adj (branch e.1.1) (branch e.1.2) →
      ∀ A ∈ C e, Disjoint (A : Set V) (Set.range branch)) :
    Erdos718.ContainsCliqueSubdivision G r := by
  classical
  let missing : Finset (Erdos718.CliqueEdge r) :=
    Finset.univ.filter fun e => ¬G.Adj (branch e.1.1) (branch e.1.2)
  have hmem_missing {e : Erdos718.CliqueEdge r} :
      e ∈ missing ↔ ¬G.Adj (branch e.1.1) (branch e.1.2) := by
    simp [missing]
  obtain ⟨f, hfmem, _hfsmall, hfdisj⟩ :=
    exists_pairwise_disjoint_choice missing C 3
      (by
        intro e he
        apply hcard e
        exact hmem_missing.mp he)
      (by
        intro e he
        apply hinternal e
        exact hmem_missing.mp he)
      (by
        intro e he A hA
        exact hsmall e A hA)
  let route (e : Erdos718.CliqueEdge r)
      (he : ¬G.Adj (branch e.1.1) (branch e.1.2)) :
      ShortRoute G (branch e.1.1) (branch e.1.2) (f e) :=
    Classical.choice (hroute e he (f e) (hfmem e (hmem_missing.mpr he)))
  let path (e : Erdos718.CliqueEdge r) :
      G.Walk (branch e.1.1) (branch e.1.2) :=
    if he : G.Adj (branch e.1.1) (branch e.1.2) then he.toWalk
    else (route e he).path
  refine ⟨{
    branch := branch
    path := path
    path_isPath := ?_
    interior_avoids_branch := ?_
    interior_pairwise := ?_
  }⟩
  · intro e
    by_cases he : G.Adj (branch e.1.1) (branch e.1.2)
    · simpa [path, he] using he.isPath_toWalk
    · simpa [path, he] using (route e he).isPath
  · intro e
    by_cases he : G.Adj (branch e.1.1) (branch e.1.2)
    · have hempty : Erdos718.walkInteriorSet he.toWalk = ∅ := by
        ext x
        simp only [Erdos718.walkInteriorSet, he.support_toWalk,
          List.mem_cons, List.mem_singleton, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        aesop
      rw [show path e = he.toWalk by simp [path, he], hempty]
      simp
    · rw [show path e = (route e he).path by simp [path, he],
        (route e he).interior_eq]
      exact havoid e he (f e) (hfmem e (hmem_missing.mpr he))
  · intro e q heq
    by_cases he : G.Adj (branch e.1.1) (branch e.1.2)
    · have hempty : Erdos718.walkInteriorSet he.toWalk = ∅ := by
        ext x
        simp only [Erdos718.walkInteriorSet, he.support_toWalk,
          List.mem_cons, List.mem_singleton, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        aesop
      rw [show path e = he.toWalk by simp [path, he], hempty]
      simp
    · by_cases hq : G.Adj (branch q.1.1) (branch q.1.2)
      · have hempty : Erdos718.walkInteriorSet hq.toWalk = ∅ := by
          ext x
          simp only [Erdos718.walkInteriorSet, hq.support_toWalk,
            List.mem_cons, List.mem_singleton, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false]
          aesop
        rw [show path q = hq.toWalk by simp [path, hq], hempty]
        simp
      · rw [show path e = (route e he).path by simp [path, he],
          show path q = (route q hq).path by simp [path, hq],
          (route e he).interior_eq, (route q hq).interior_eq]
        exact Finset.disjoint_coe.mpr
          (hfdisj (hmem_missing.mpr he) (hmem_missing.mpr hq) heq)

end Erdos717

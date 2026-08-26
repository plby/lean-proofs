import ErdosProblems.Erdos547.TreeConvexity
import ErdosProblems.Erdos547.FiniteTreeBoundary
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Internal vertices of a path have two neighbours on the path
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]

open scoped Classical in
theorem path_internal_degree_lower {a b u : U} (p : T.Walk a b) (hp : p.IsPath)
    (hu : u ∈ p.support) (hua : u ≠ a) (hub : u ≠ b) :
    2 ≤ degreeIn T p.support.toFinset u := by
  classical
  obtain ⟨i, hiu, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hu
  have hi0 : 0 < i := by
    by_contra hn
    have hz : i = 0 := by omega
    exact hua (hiu.symm.trans (by simp [hz]))
  have hil : i < p.length := by
    by_contra hn
    have he : i = p.length := by omega
    exact hub (hiu.symm.trans (by simp [he]))
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro he
    have hh := hp.getVert_injOn (by change i - 1 ≤ p.length; omega)
      (by change i + 1 ≤ p.length; omega) he
    omega
  have hleft : T.Adj u (p.getVert (i - 1)) := by
    have hh := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    have he : i - 1 + 1 = i := by omega
    simpa only [he, hiu] using hh
  have hright : T.Adj u (p.getVert (i + 1)) := by
    simpa only [hiu] using p.adj_getVert_succ hil
  have hsub : {p.getVert (i - 1), p.getVert (i + 1)} ⊆
      p.support.toFinset.filter (T.Adj u) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _), hleft⟩
    · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _), hright⟩
  have hh := Finset.card_le_card hsub
  simpa only [degreeIn, Finset.card_pair hne] using hh

theorem neighbour_closed_of_two_degrees {P H : Finset U} (hPH : P ⊆ H) {u : U}
    (hlo : 2 ≤ degreeIn T P u) (hhi : degreeIn T H u ≤ 2) :
    ∀ v ∈ H, T.Adj u v → v ∈ P := by
  classical
  have he : P.filter (T.Adj u) = H.filter (T.Adj u) :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ hPH) (hhi.trans hlo)
  intro v hv huv
  have hh := Finset.mem_filter.mpr ⟨hv, huv⟩
  rw [← he] at hh
  exact (Finset.mem_filter.mp hh).1

theorem forest_path_endpoints_not_adjacent (hT : T.IsAcyclic) {a b : U}
    (p : T.Walk a b) (hp : p.IsPath) (hl : 2 ≤ p.length) : ¬ T.Adj a b := by
  intro hab
  have he := (hT.subsingleton_path a b).elim ⟨p, hp⟩ (SimpleGraph.Path.singleton hab)
  have hh := congrArg (fun q : T.Path a b ↦ q.val.length) he
  have hlen : p.length = 1 := hh
  omega

end Erdos547

#print axioms Erdos547.path_internal_degree_lower

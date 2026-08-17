/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.LinearForest

/-!
# A connected linear forest is a path

This file packages the finite endpoint argument needed in the good-cut
Hamiltonicity proof.  Connectivity is required only on the support, so
isolated ambient vertices do not occur in the resulting path.
-/

open scoped SimpleGraph

namespace Erdos622
namespace LinearForest

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A walk from a vertex in `S` to a vertex outside `S` uses a first edge
which crosses from `S` to its complement. -/
private theorem exists_crossing_of_walk {P : SimpleGraph V} {S : Finset V}
    {u v : V} (q : P.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ P.Adj x y := by
  induction q with
  | nil => exact (hv hu).elim
  | @cons u w v huw q ih =>
      by_cases hw : w ∈ S
      · exact ih hw hv
      · exact ⟨u, w, hu, hw, huw⟩

/-- A finite linear forest which is connected on its non-isolated vertices
is spanned by a path.  Both endpoints of that path are leaves of the
original forest. -/
theorem exists_spanning_path_of_preconnected_support
    {P : SimpleGraph V} (hP : LinearForest P)
    (hne : P.support.Nonempty)
    (hconn : ∀ {u v}, u ∈ P.support → v ∈ P.support → P.Reachable u v) :
    ∃ a b, ∃ p : P.Walk a b, p.IsPath ∧
      p.support.toFinset = P.support.toFinset ∧
      (P.neighborSet a).ncard = 1 ∧ (P.neighborSet b).ncard = 1 := by
  classical
  letI : Nonempty V := ⟨hne.some⟩
  obtain ⟨a, b, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length P
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support P).mp hx
  have hlen : 1 ≤ p.length := by
    have hle := hmax x y hxy.toWalk (SimpleGraph.Walk.IsPath.of_adj hxy)
    simpa using hle
  have hnon : ¬p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen

  have hstart : P.neighborSet a = {p.snd} := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro haz
      have hz : z ∈ p.support := by
        by_contra hz
        have hlong : (p.cons haz.symm).IsPath := hp.cons hz
        have hle := hmax z b (p.cons haz.symm) hlong
        simp at hle
      exact hP.1.eq_snd_of_adj_start hp haz hz
    · rintro rfl
      exact p.adj_snd hnon
  have hend : P.neighborSet b = {p.penultimate} := by
    ext z
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hbz
      have hz : z ∈ p.support := by
        by_contra hz
        have hlong : (p.concat hbz).IsPath := hp.concat hz hbz
        have hle := hmax a z (p.concat hbz) hlong
        simp at hle
      exact hP.1.eq_penultimate_of_adj_end hp hbz hz
    · rintro rfl
      exact (p.adj_penultimate hnon).symm

  have hsupp : p.support.toFinset = P.support.toFinset := by
    apply Finset.Subset.antisymm
    · intro v hv
      exact Set.mem_toFinset.mpr
        (SimpleGraph.mem_support_of_mem_walk_support p hnon
          (List.mem_toFinset.mp hv))
    · intro v hv
      have hvP : v ∈ P.support := Set.mem_toFinset.mp hv
      by_contra hvp
      have hvp' : v ∉ p.support.toFinset := by simpa using hvp
      have haP : a ∈ P.support :=
        SimpleGraph.mem_support_of_mem_walk_support p hnon p.start_mem_support
      obtain ⟨q⟩ := hconn haP hvP
      obtain ⟨z, w, hz, hw, hzw⟩ :=
        exists_crossing_of_walk q
          (List.mem_toFinset.mpr p.start_mem_support) hvp'
      have hzList : z ∈ p.support := List.mem_toFinset.mp hz
      by_cases hza : z = a
      · subst z
        have hw' : w ∈ P.neighborSet a := hzw
        rw [hstart] at hw'
        exact hw (hw' ▸ List.mem_toFinset.mpr (p.getVert_mem_support 1))
      · by_cases hzb : z = b
        · subst z
          have hw' : w ∈ P.neighborSet b := hzw
          rw [hend] at hw'
          exact hw (hw' ▸ List.mem_toFinset.mpr
            (p.getVert_mem_support (p.length - 1)))
        · obtain ⟨i, hiz, hi⟩ :=
            SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzList
          have hi0 : i ≠ 0 := by
            intro hi0
            subst i
            exact hza (by simpa using hiz.symm)
          have hilt : i < p.length := by
            apply lt_of_le_of_ne hi
            intro hil
            have : z = b := by
              rw [← hiz, hil, p.getVert_length]
            exact hzb this
          have hpathCard : (p.toSubgraph.neighborSet z).ncard = 2 := by
            rw [← hiz]
            exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
          have hPCard : (P.neighborSet z).ncard ≤ 2 := by
            rw [← Set.fintypeCard_eq_ncard,
              SimpleGraph.card_neighborSet_eq_degree]
            exact hP.2 z
          have heq : p.toSubgraph.neighborSet z = P.neighborSet z := by
            apply Set.eq_of_subset_of_ncard_le
              (p.toSubgraph.neighborSet_subset z)
            omega
          have hzw' : w ∈ p.toSubgraph.neighborSet z := by
            rw [heq]
            exact hzw
          exact hw (List.mem_toFinset.mpr
            (p.mem_support_of_adj_toSubgraph hzw'.symm))

  refine ⟨a, b, p, hp, hsupp, ?_, ?_⟩
  · rw [hstart]
    simp
  · rw [hend]
    simp

end LinearForest
end Erdos622

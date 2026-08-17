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
import ErdosProblems.Erdos58.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Erdős Problem 58: the bipartite base case

This file proves the standard characterization needed when the graph has no
odd cycle lengths.  The only ingredient absent from Mathlib is the passage
from an odd closed walk to an odd simple cycle.  We prove its contrapositive:
if every simple cycle has even length, then every closed walk has even length.

The proof is by strong induction on the length of the closed walk.  If the
tail of the walk is not a path, it contains a nonempty closed subwalk.  Removing
that subwalk leaves another closed walk; both are strictly shorter, so both
have even length.  The remaining case is either a cycle or a closed walk of
length less than three.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

variable {V : Type*} {G : SimpleGraph V}

/-- If every simple cycle of `G` has even length, then every closed walk of
`G` has even length. -/
lemma even_length_of_forall_isCycle_even
    (hcycle : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) :
    ∀ (v : V) (w : G.Walk v v), Even w.length := by
  classical
  intro v w
  induction hlen : w.length using Nat.strongRec generalizing v with
  | ind n ih =>
      by_cases hwcycle : w.IsCycle
      · simpa [hlen] using hcycle v w hwcycle
      by_cases htail : w.tail.IsPath
      · have hnlt : n < 3 := by
          by_contra hn
          exact hwcycle ((SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).2
            ⟨htail, by omega⟩)
        have hn_ne_one : n ≠ 1 := by
          intro hn
          exact G.irrefl (w.adj_of_length_eq_one (hlen ▸ hn))
        have hn : n = 0 ∨ n = 2 := by omega
        rcases hn with (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact even_two
      · rw [SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil] at htail
        push Not at htail
        obtain ⟨x, q, hqsub, hq_nonempty⟩ := htail
        have hw_nonempty : ¬w.Nil := by
          intro hw
          cases hw
          have hq_zero : q.length = 0 := Nat.eq_zero_of_le_zero (by
            simpa using SimpleGraph.Walk.length_le_of_isSubwalk hqsub)
          exact hq_nonempty (SimpleGraph.Walk.length_eq_zero_iff.mp hq_zero)
        have hqsub_w : q.IsSubwalk w :=
          hqsub.trans (SimpleGraph.Walk.isSubwalk_rfl w).tail
        obtain ⟨ru, rv, hwdecomp⟩ := hqsub_w
        let r : G.Walk v v := ru.append rv
        have hq_lt : q.length < n := by
          have hq_le_tail : q.length ≤ w.tail.length :=
            SimpleGraph.Walk.length_le_of_isSubwalk hqsub
          have hq_pos : 0 < q.length :=
            SimpleGraph.Walk.not_nil_iff_lt_length.mp hq_nonempty
          calc
            q.length ≤ w.tail.length := hq_le_tail
            _ < w.length := by
              rw [← w.length_tail_add_one hw_nonempty]
              omega
            _ = n := hlen
        have hr_lt : r.length < n := by
          have hq_pos : 0 < q.length :=
            SimpleGraph.Walk.not_nil_iff_lt_length.mp hq_nonempty
          simp only [r, SimpleGraph.Walk.length_append]
          have hlength : n = ru.length + q.length + rv.length := by
            rw [← hlen, hwdecomp]
            simp [SimpleGraph.Walk.length_append]
          omega
        have hq_even : Even q.length := ih q.length hq_lt x q rfl
        have hr_even : Even r.length := ih r.length hr_lt v r rfl
        have hlength : w.length = r.length + q.length := by
          rw [hwdecomp]
          simp [r, SimpleGraph.Walk.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        rw [← hlen, hlength]
        exact hr_even.add hq_even

/-- A graph with no odd simple cycle is two-colorable. -/
theorem colorable_two_of_no_odd_isCycle
    (hodd : ∀ (v : V) (c : G.Walk v v), c.IsCycle → ¬Odd c.length) :
    G.Colorable 2 := by
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  apply even_length_of_forall_isCycle_even
  intro v c hc
  exact Nat.not_odd_iff_even.mp (hodd v c hc)

/-- Empty odd-cycle-length set is equivalent to bipartiteness in the direction
needed by Erdős Problem 58. -/
theorem colorable_two_of_oddCycleLengths_eq_empty
    (hodd : oddCycleLengths G = ∅) : G.Colorable 2 := by
  apply colorable_two_of_no_odd_isCycle
  intro v c hc hclen
  have : c.length ∈ oddCycleLengths G := ⟨hclen, v, c, hc, rfl⟩
  simpa [hodd] using this

/-- In a graph with no odd cycle lengths, the chromatic number is exactly two
precisely when the graph contains an edge, expressed canonically as a copy of
`K₂`. -/
theorem chromaticNumber_eq_two_iff_completeGraph_two_isContained
    (hodd : oddCycleLengths G = ∅) :
    G.chromaticNumber = 2 ↔
      SimpleGraph.completeGraph (Fin 2) ⊑ G := by
  have hcol : G.IsBipartite := colorable_two_of_oddCycleLengths_eq_empty hodd
  rw [SimpleGraph.chromaticNumber_eq_two_iff]
  simp only [hcol, true_and]
  simpa [SimpleGraph.cliqueFree_two] using
    (SimpleGraph.not_cliqueFree_iff_top_isContained (G := G) 2)

end Erdos58

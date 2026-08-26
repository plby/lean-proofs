/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 608.
Informal authors: Zoltán Füredi, Zeinab Maleki; construction described by
Andrzej Grzesik, Ping Hu, and Jan Volec.
Formal authors: Claude Fable 5, Emerson Hsieh.
Source: https://github.com/teorth/erdosproblems/pull/365
https://github.com/primateria/erdos608/tree/b50849234b8de6cb5c642b5cb0479cab2e9e9908
Original Lean version: 4.27.0.
Original Mathlib revision: a3a10db0e9d66acbebf76c5e6a135066525ac900 (v4.27.0).
-/
import ErdosProblems.Erdos608.Statement

open SimpleGraph

set_option linter.mathlibStandardSet false

/-
Erdős problem 608 — `OnC5` agrees with mathlib's walk-based pentagons.

`Erdos608.OnC5 G e` (five pairwise-distinct vertices in cyclic adjacency with
`e` among the five cycle edges) holds iff `e` lies on the edges of a length-5
cycle walk in the mathlib sense (`SimpleGraph.Walk.IsCycle`).
-/

namespace Erdos608

theorem onC5_iff_cycle {V : Type*} (G : SimpleGraph V) (e : Sym2 V) :
    Erdos608.OnC5 G e ↔ ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.length = 5 ∧ e ∈ w.edges := by
  constructor
  · -- Forward: build the explicit pentagon walk a → b → c → d → f → a.
    rintro ⟨a, b, c, d, f, hab, hac, had, haf, hbc, hbd, hbf, hcd, hcf, hdf,
      h1, h2, h3, h4, h5, he⟩
    refine ⟨a, .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil)))), ?_, rfl, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      constructor
      · -- The tail b → c → d → f → a is a path: its support is Nodup.
        rw [Walk.isPath_def]
        simp [hbc, hbd, hbf, hcd, hcf, hdf,
          Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm haf]
      · -- The closing edge s(a, b) is not among the tail's edges.
        simp [hab, hac, had, haf, hbf]
    · -- `e` is one of the five explicit edges.
      rcases he with rfl | rfl | rfl | rfl | rfl <;> simp
  · -- Backward: destructure the length-5 closed walk into its five steps.
    rintro ⟨u, w, hcyc, hlen, he⟩
    cases w with
    | nil => simp at hlen
    | cons h1 p1 =>
      cases p1 with
      | nil => simp at hlen
      | cons h2 p2 =>
        cases p2 with
        | nil => simp at hlen
        | cons h3 p3 =>
          cases p3 with
          | nil => simp at hlen
          | cons h4 p4 =>
            cases p4 with
            | nil => simp at hlen
            | cons h5 p5 =>
              cases p5 with
              | cons h6 p6 =>
                simp only [Walk.length_cons] at hlen
                omega
              | nil =>
                -- w = u → v1 → v2 → v3 → v4 → u; extract distinctness from
                -- Nodup of the support tail [v1, v2, v3, v4, u].
                rw [Walk.isCycle_def] at hcyc
                obtain ⟨-, -, hnodup⟩ := hcyc
                simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
                  List.nodup_cons, List.mem_cons,
                  List.not_mem_nil, or_false, List.nodup_nil, and_true,
                  not_or] at hnodup
                obtain ⟨⟨h12, h13, h14, h1u⟩, ⟨h23, h24, h2u⟩, ⟨h34, h3u⟩, h4u, -⟩ :=
                  hnodup
                simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons,
                  List.not_mem_nil, or_false] at he
                exact ⟨u, _, _, _, _,
                  Ne.symm h1u, Ne.symm h2u, Ne.symm h3u, Ne.symm h4u,
                  h12, h13, h14, h23, h24, h34,
                  h1, h2, h3, h4, h5, he⟩

end Erdos608

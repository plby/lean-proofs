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
import ErdosProblems.Erdos58.Bipartite
import ErdosProblems.Erdos58.Critical
import ErdosProblems.Erdos58.Linkage

/-!
# Assembly strategy for the structural proof of Erdős Problem 58

This file isolates the exact remaining geometric theorem and proves all of
the critical-graph assembly around it.  In particular, the interface below
does not assume the desired coloring conclusion.  Its conclusion is the
actual graph isomorphism in Gyárfás's structural theorem, and its hypotheses
are the independently proved two-connectivity, degree, and odd-cycle-length
conditions.

The geometric development should eventually prove `GyarfasStructuralAt` for
every finite graph.  Once that theorem is available,
`colorable_two_mul_add_two_of_structural` supplies the numerical upper bound,
while `critical_complete_of_structural` retains the complete critical witness
needed for the sharp equality case.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural

universe u

noncomputable section

/-! ## The one missing graph-local theorem -/

/-- The exact graph-local conclusion of Gyárfás's structural theorem.

The hypothesis uses the standard `TwoConnected` interface consumed by the
linkage layer.  The critical-subgraph file produces a slightly leaner
deletion-connectivity predicate; `twoConnected_of_vertexTwoConnected` below
bridges the two using the minimum-degree bound.
-/
def GyarfasStructuralAt {X : Type u} [Fintype X]
    (J : SimpleGraph X) [DecidableRel J.Adj] (j : ℕ) : Prop :=
  0 < j →
    TwoConnected J →
    (∀ v : X, 2 * j + 1 ≤ J.degree v) →
    (oddCycleLengths J).ncard = j →
    Nonempty (J ≃g SimpleGraph.completeGraph (Fin (2 * j + 2)))

/-- The usual low-degree-or-complete formulation follows immediately from
the minimum-degree classifier.  This is useful when comparing the Lean
interface with the statement of Gyárfás's theorem in the literature. -/
theorem low_degree_or_complete_of_structural {X : Type u}
    [Fintype X] {J : SimpleGraph X} [DecidableRel J.Adj] {j : ℕ}
    (hstruct : GyarfasStructuralAt J j) (hj : 0 < j)
    (htwo : TwoConnected J) (hcard : (oddCycleLengths J).ncard = j) :
    (∃ v : X, J.degree v ≤ 2 * j) ∨
      Nonempty (J ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
  by_cases hdegree : ∀ v : X, 2 * j + 1 ≤ J.degree v
  · exact Or.inr (hstruct hj htwo hdegree hcard)
  · push Not at hdegree
    obtain ⟨v, hv⟩ := hdegree
    exact Or.inl ⟨v, by omega⟩

/-- Convert the deletion-connectivity predicate produced by the critical
reduction into the standard finite `TwoConnected` interface used by the
linkage lemmas.  A degree lower bound of three supplies the only missing
field, namely that the graph has at least three vertices. -/
theorem twoConnected_of_vertexTwoConnected {X : Type u}
    [Fintype X] [DecidableEq X] {J : SimpleGraph X} [DecidableRel J.Adj]
    (htwo : Critical.VertexTwoConnected J)
    (hdegree : ∀ v : X, 3 ≤ J.degree v) : TwoConnected J := by
  letI : Nonempty X := htwo.1.nonempty
  let v : X := Classical.choice (inferInstance : Nonempty X)
  have hcard : 3 ≤ Fintype.card X := by
    have hlt := J.degree_lt_card_verts v
    have hdeg := hdegree v
    omega
  refine ⟨hcard, htwo.1, ?_⟩
  intro w
  let e : Critical.deleteVertex J w ≃g J.induce ({w}ᶜ : Set X) :=
    { toFun := fun x ↦ ⟨x, by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property⟩
      invFun := fun x ↦ ⟨x, by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl
      map_rel_iff' := by simp [Critical.deleteVertex] }
  exact e.connected_iff.mp (htwo.2 w)

/-! ## Nonbipartiteness of a critical graph -/

/-- A graph which is not `n`-colorable for some `n ≥ 2` has an odd simple
cycle.  This is the small bridge from the bipartite base-case file to the
positive index required by the structural theorem. -/
theorem oddCycleLengths_nonempty_of_not_colorable {X : Type u}
    [Finite X] {J : SimpleGraph X} {n : ℕ} (hn : 2 ≤ n)
    (hnot : ¬J.Colorable n) : (oddCycleLengths J).Nonempty := by
  by_contra hempty
  have hzero : oddCycleLengths J = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
  have htwo : J.Colorable 2 := colorable_two_of_oddCycleLengths_eq_empty hzero
  exact hnot (SimpleGraph.Colorable.mono hn htwo)

/-- Consequently the natural cardinality of the odd-length set of such a
finite graph is positive. -/
theorem ncard_oddCycleLengths_pos_of_not_colorable {X : Type u}
    [Finite X] {J : SimpleGraph X} {n : ℕ} (hn : 2 ≤ n)
    (hnot : ¬J.Colorable n) : 0 < (oddCycleLengths J).ncard := by
  rw [Set.ncard_pos (oddCycleLengths_finite J)]
  exact oddCycleLengths_nonempty_of_not_colorable hn hnot

/-! ## The sharp critical witness -/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The elementary degree/cardinality contradiction used after a structural
classification of a critical graph.  It is kept local here so the assembly
module depends only on the basic, bipartite, and critical layers. -/
private theorem complete_iso_impossible_of_strict_degree
    {X : Type u} [Fintype X] (J : SimpleGraph X) [DecidableRel J.Adj]
    {j k : ℕ} (hjk : j ≤ k)
    (hdegree : ∀ v : X, 2 * k + 2 ≤ J.degree v) :
    ¬Nonempty (J ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
  rintro ⟨e⟩
  let v : X := e.symm 0
  have hcard : Fintype.card X = 2 * j + 2 := by
    simpa using Fintype.card_congr e.toEquiv
  have hlt : J.degree v < Fintype.card X := J.degree_lt_card_verts v
  have := hdegree v
  omega

/-- Applying the structural theorem to a minimal non-`(2*k+1)`-colorable
induced subgraph produces precisely the complete critical witness consumed by
the sharp endgame.

This theorem performs all bookkeeping which should not be repeated in the
geometric proof: positivity of the number of odd lengths, monotonicity under
induction, comparison with `k`, weakening the critical degree bound from
`2*k+1` to `2*j+1`, and retention of the original sharp degree bound.
-/
theorem critical_complete_of_structural {k : ℕ} (hk : 0 < k)
    (hodd : (oddCycleLengths G).ncard ≤ k)
    (hstruct : ∀ {X : Type u} [Fintype X] (J : SimpleGraph X)
      [DecidableRel J.Adj] (j : ℕ),
      GyarfasStructuralAt J j)
    (hnot : ¬G.Colorable (2 * k + 1)) :
    ∃ (W : Critical.Witness G (2 * k + 1)) (j : ℕ), j ≤ k ∧
      Nonempty
        (Critical.H G W ≃g
          SimpleGraph.completeGraph (Fin (2 * j + 2))) ∧
      ∀ v : Critical.Carrier G W,
        2 * k + 1 ≤ (Critical.H G W).degree v := by
  obtain ⟨W, hdegree, htwo⟩ :=
    Critical.exists_vertexTwoConnected_witness (G := G)
      (n := 2 * k + 1) (by omega) hnot
  letI : Fintype (Critical.Carrier G W) := Critical.instSub W.S
  let J : SimpleGraph (Critical.Carrier G W) := Critical.H G W
  let j : ℕ := (oddCycleLengths J).ncard
  have hjk : j ≤ k := by
    exact (ncard_oddCycleLengths_induce_le G (fun v : V ↦ v ∈ W.S)).trans hodd
  have hjpos : 0 < j := by
    exact ncard_oddCycleLengths_pos_of_not_colorable
      (J := J) (n := 2 * k + 1) (by omega) W.not_colorable
  have hdegreej : ∀ v : Critical.Carrier G W, 2 * j + 1 ≤ J.degree v := by
    intro v
    exact (by omega : 2 * j + 1 ≤ 2 * k + 1) |>.trans (hdegree v)
  have htwostd : TwoConnected J := by
    apply twoConnected_of_vertexTwoConnected htwo
    intro v
    exact (by omega : 3 ≤ 2 * j + 1) |>.trans (hdegreej v)
  have hiso :
      Nonempty (J ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
    apply hstruct J j hjpos htwostd hdegreej
    rfl
  exact ⟨W, j, hjk, hiso, hdegree⟩

/-! ## The numerical upper bound -/

/-- The structural theorem also rules out a minimal
non-`(2*k+2)`-colorable induced subgraph.  Its critical degree lower bound is
one larger than the degree of every possible complete structural output.
-/
theorem colorable_two_mul_add_two_of_structural {k : ℕ}
    (hodd : (oddCycleLengths G).ncard ≤ k)
    (hstruct : ∀ {X : Type u} [Fintype X] (J : SimpleGraph X)
      [DecidableRel J.Adj] (j : ℕ),
      GyarfasStructuralAt J j) :
    G.Colorable (2 * k + 2) := by
  by_contra hnot
  obtain ⟨W, hdegree, htwo⟩ :=
    Critical.exists_vertexTwoConnected_witness (G := G)
      (n := 2 * k + 2) (by omega) hnot
  letI : Fintype (Critical.Carrier G W) := Critical.instSub W.S
  let J : SimpleGraph (Critical.Carrier G W) := Critical.H G W
  let j : ℕ := (oddCycleLengths J).ncard
  have hjk : j ≤ k := by
    exact (ncard_oddCycleLengths_induce_le G (fun v : V ↦ v ∈ W.S)).trans hodd
  have hjpos : 0 < j := by
    exact ncard_oddCycleLengths_pos_of_not_colorable
      (J := J) (n := 2 * k + 2) (by omega) W.not_colorable
  have hdegreej : ∀ v : Critical.Carrier G W, 2 * j + 1 ≤ J.degree v := by
    intro v
    exact (by omega : 2 * j + 1 ≤ 2 * k + 2) |>.trans (hdegree v)
  have htwostd : TwoConnected J := by
    apply twoConnected_of_vertexTwoConnected htwo
    intro v
    exact (by omega : 3 ≤ 2 * j + 1) |>.trans (hdegreej v)
  have hiso :
      Nonempty (J ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
    apply hstruct J j hjpos htwostd hdegreej
    rfl
  exact complete_iso_impossible_of_strict_degree J hjk hdegree hiso

/-- For positive `k`, the two structural reductions assemble directly into
the exact sharp colorability alternative. -/
theorem sharp_colorability_of_structural {k : ℕ} (hk : 0 < k)
    (hodd : (oddCycleLengths G).ncard ≤ k)
    (hstruct : ∀ {X : Type u} [Fintype X] (J : SimpleGraph X)
      [DecidableRel J.Adj] (j : ℕ),
      GyarfasStructuralAt J j) :
    G.Colorable (2 * k + 2) ∧
      (¬G.Colorable (2 * k + 1) ↔
        SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) := by
  refine ⟨colorable_two_mul_add_two_of_structural G hodd hstruct, ?_⟩
  constructor
  · intro hnot
    obtain ⟨W, j, hjk, ⟨e⟩, hdegree⟩ :=
      critical_complete_of_structural G hk hodd hstruct hnot
    letI : Fintype (Critical.Carrier G W) := Critical.instSub W.S
    have hkj : k ≤ j := by
      let v : Critical.Carrier G W := e.symm 0
      have hcard : Fintype.card (Critical.Carrier G W) = 2 * j + 2 := by
        simpa using Fintype.card_congr e.toEquiv
      have hlt : (Critical.H G W).degree v <
          Fintype.card (Critical.Carrier G W) :=
        (Critical.H G W).degree_lt_card_verts v
      have := hdegree v
      omega
    have hjk' : j = k := Nat.le_antisymm hjk hkj
    subst j
    exact e.isContained'.trans
      (SimpleGraph.Embedding.induce (fun v : V ↦ v ∈ W.S)).toCopy.isContained
  · intro hcopy hcolor
    have hfree := hcolor.cliqueFree (m := 2 * k + 2) (by omega)
    exact ((SimpleGraph.not_cliqueFree_iff_top_isContained (G := G)
      (2 * k + 2)).2 hcopy) hfree

end

end Erdos58.Structural

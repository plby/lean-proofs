/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 641.
https://www.erdosproblems.com/forum/thread/641

Informal authors:
- Barnabás Janzer
- Richard Steiner
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos641.md
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.JSKFreeBridge
import ErdosProblems.Erdos641.Combined

/-!
# Erdős Problem 641

Erdős and Hajnal asked whether sufficiently large chromatic number forces,
for every `r`, `r` pairwise edge-disjoint cycles on one common vertex set.
Janzer, Steiner and Sudakov disproved this already for `r = 2`: there are
finite graphs of arbitrarily large chromatic number with no nonempty
`4`-regular subgraph.

This file uses the literal common-vertex-set formulation.  A cycle is a
connected `2`-regular graph on `Fin m`; one injective graph homomorphism embeds
the union of all the cycles into the ambient graph.  Thus all cycles use the
same `m` ambient vertices, and lattice-disjointness says that their edge sets
are pairwise disjoint.
-/

open Finset Fintype Filter
open scoped BigOperators

namespace Erdos641

open SimpleGraph
open Erdos182

open scoped Classical in
/-- A finite cycle, expressed as a connected `2`-regular graph. -/
def IsCycleGraph {V : Type*} [Fintype V] (C : SimpleGraph V) : Prop :=
  C.Connected ∧ C.IsRegularOfDegree 2

/-- `G` has `r` pairwise edge-disjoint cycles on one common vertex set.

The common set is labelled by `Fin m`.  The single copy of the supremum in
`G` forces every cycle to use the same vertex injection into `G`. -/
def HasCommonVertexCycles {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    ∃ C : Fin r → SimpleGraph (Fin m),
      (∀ i, IsCycleGraph (C i)) ∧
      (∀ ⦃i j : Fin r⦄, i ≠ j → Disjoint (C i) (C j)) ∧
      Nonempty (SimpleGraph.Copy (⨆ i, C i) G)

/-- The proposed positive answer to Erdős Problem 641. -/
def ErdosHajnalProperty (F : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (F r : ℕ∞) ≤ G.chromaticNumber → HasCommonVertexCycles G r

private lemma fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

/-- Restrict a copy of an indexed supremum to the supremum of two selected
members. -/
def copySupPair {V W : Type*} {r : ℕ} {A : Fin r → SimpleGraph V}
    {G : SimpleGraph W} (i j : Fin r)
    (f : SimpleGraph.Copy (⨆ t, A t) G) :
    SimpleGraph.Copy (A i ⊔ A j) G where
  toHom :=
    { toFun := f
      map_rel' := by
        intro a b hab
        rw [SimpleGraph.sup_adj] at hab
        apply f.toHom.map_rel
        rw [SimpleGraph.iSup_adj]
        exact hab.elim (fun h ↦ ⟨i, h⟩) (fun h ↦ ⟨j, h⟩) }
  injective' := f.injective

open scoped Classical in
/-- Two edge-disjoint `2`-regular graphs on the same nonempty vertex set
have a `4`-regular union. -/
lemma isRegularOfDegree_four_sup {m : ℕ}
    {C D : SimpleGraph (Fin m)}
    (hC : C.IsRegularOfDegree 2) (hD : D.IsRegularOfDegree 2)
    (hCD : Disjoint C D) :
    (C ⊔ D).IsRegularOfDegree 4 := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_sup_of_disjoint (v := v) hCD]
  simp only [Finset.card_disjUnion, SimpleGraph.card_neighborFinset_eq_degree,
    hC v, hD v]

/-- The union of two common-support edge-disjoint cycles is a nonempty
`4`-regular subgraph of the ambient graph. -/
theorem containsRegularSubgraph_four_of_commonVertexCycles
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h : HasCommonVertexCycles G 2) :
    ContainsRegularSubgraph G 4 := by
  classical
  obtain ⟨m, hm, C, hcycle, hdis, hf⟩ := h
  obtain ⟨f⟩ := hf
  let i0 : Fin 2 := 0
  let i1 : Fin 2 := 1
  have hi : i0 ≠ i1 := by decide
  have hreg : (C i0 ⊔ C i1).IsRegularOfDegree 4 :=
    isRegularOfDegree_four_sup (hcycle i0).2 (hcycle i1).2 (hdis hi)
  have hsupp : (C i0 ⊔ C i1).support.Nonempty := by
    let v : Fin m := ⟨0, hm⟩
    refine ⟨v, ?_⟩
    rw [← SimpleGraph.degree_pos_iff_mem_support, hreg v]
    norm_num
  have hsmall : ContainsRegularSubgraph (C i0 ⊔ C i1) 4 :=
    Erdos182.BipartiteGraph.containsRegularSubgraph_of_regular_support_mono
      le_rfl hsupp
      (fun v _hv ↦ by
        rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
        exact hreg v)
  exact Erdos182.BipartiteGraph.containsRegularSubgraph_of_copy
    (copySupPair i0 i1 f) hsmall

/-- A `4`-regular-subgraph-free graph has no two edge-disjoint cycles on a
common vertex set. -/
lemma not_hasCommonVertexCycles_of_four_free
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : IsRegularSubgraphFree G 4) :
    ¬ HasCommonVertexCycles G 2 := by
  intro h
  exact hG (containsRegularSubgraph_four_of_commonVertexCycles h)

/-- JSS counterexamples have arbitrarily large chromatic number while
remaining free of nonempty `4`-regular subgraphs. -/
theorem exists_four_regular_free_high_chromatic (k : ℕ) :
    ∃ n : ℕ, ∃ ω : JSSOutcome n, ∃ hω : ω ∈ jssOutcomeSpace n,
      (k : ℕ∞) ≤ (jssGraph ω hω).chromaticNumber ∧
        IsRegularSubgraphFree (jssGraph ω hω) 4 := by
  let q := max 1 k
  have hq : 0 < q := by simp [q]
  obtain ⟨n, ω, hω, hfree, hnotColor⟩ :=
    (eventually_exists_regularFree_not_colorable q hq).exists
  have hchi : ((q + 1 : ℕ) : ℕ∞) ≤
      (jssGraph ω hω).chromaticNumber := by
    apply SimpleGraph.le_chromaticNumber_iff_coloring.mpr
    intro m C
    by_contra hm
    apply hnotColor
    have hmq : m ≤ q := by omega
    exact C.colorable.mono (by simpa using hmq)
  refine ⟨n, ω, hω, ?_, hfree⟩
  have hkq : k ≤ q + 1 := by
    dsimp [q]
    omega
  exact (by exact_mod_cast hkq : (k : ℕ∞) ≤ ((q + 1 : ℕ) : ℕ∞)).trans hchi

/-- **Negative resolution of Erdős Problem 641.**  No function can force
`r` edge-disjoint cycles on one common vertex set solely from a chromatic
number threshold; the failure already occurs for `r = 2`. -/
theorem not_erdos_641 : ¬ ∃ F : ℕ → ℕ, ErdosHajnalProperty F := by
  rintro ⟨F, hF⟩
  obtain ⟨n, ω, hω, hchrom, hfree⟩ :=
    exists_four_regular_free_high_chromatic (F 2)
  have hcycles : HasCommonVertexCycles (jssGraph ω hω) 2 :=
    hF 2 (by norm_num) (V := JSSVertex n) (jssGraph ω hω) hchrom
  exact not_hasCommonVertexCycles_of_four_free hfree hcycles

end Erdos641

#print axioms Erdos641.not_erdos_641

alias _root_.Erdos641.erdos_641 := _root_.Erdos641.not_erdos_641

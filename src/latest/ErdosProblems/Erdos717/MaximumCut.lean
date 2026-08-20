/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- A maximum-cut lemma used by the dependent-random-choice argument. -/

import ErdosProblems.Erdos718.Erdos718Core
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Function Set
open SimpleGraph
open Finset
open scoped Sym2

namespace Erdos717
namespace MaximumCut

noncomputable local instance graphEdgeFintype {V : Type*} [Finite V]
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

private def flipAt {V : Type*} [DecidableEq V]
    (u : V) (c : V → Bool) : V → Bool :=
  Function.update c u (!(c u))

private lemma flipAt_apply_self {V : Type*} [DecidableEq V]
    (u : V) (c : V → Bool) : flipAt u c u = !(c u) := by
  simp [flipAt]

private lemma flipAt_apply_of_ne {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : V → Bool) :
    flipAt u c v = c v := by
  simp [flipAt, Ne.symm huv]

private lemma flipAt_involutive {V : Type*} [DecidableEq V] (u : V) :
    Function.Involutive (flipAt u : (V → Bool) → V → Bool) := by
  intro c
  funext v
  by_cases huv : u = v
  · subst v
    simp [flipAt]
  · simp [flipAt]

private lemma flipAt_ne_iff_eq {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : V → Bool) :
    flipAt u c u ≠ flipAt u c v ↔ c u = c v := by
  rw [flipAt_apply_self, flipAt_apply_of_ne huv]
  cases c u <;> cases c v <;> decide

private lemma card_colorings_ne_eq_half {V : Type*} [Fintype V]
    [DecidableEq V] {u v : V} (huv : u ≠ v) :
    2 * #(Finset.univ.filter fun c : V → Bool => c u ≠ c v) =
      Fintype.card (V → Bool) := by
  let neColors := Finset.univ.filter fun c : V → Bool => c u ≠ c v
  let eqColors := Finset.univ.filter fun c : V → Bool => c u = c v
  have hcard : #neColors = #eqColors := by
    apply Finset.card_bij (fun c _ => flipAt u c)
    · intro c hc
      simp only [eqColors, Finset.mem_filter, Finset.mem_univ, true_and]
      apply not_ne_iff.mp
      rw [flipAt_ne_iff_eq huv]
      simpa [neColors] using hc
    · intro c₁ _ c₂ _ h
      exact (flipAt_involutive u).injective h
    · intro d hd
      refine ⟨flipAt u d, ?_, ?_⟩
      · simp only [neColors, Finset.mem_filter, Finset.mem_univ, true_and]
        have hd' : d u = d v := by simpa [eqColors] using hd
        exact (flipAt_ne_iff_eq huv _).mpr hd'
      · exact flipAt_involutive u d
  have hpartition : #neColors + #eqColors = Fintype.card (V → Bool) := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext c
      simp only [neColors, eqColors, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact iff_true_intro (ne_or_eq (c u) (c v))
    · refine Finset.disjoint_left.mpr ?_
      intro c hcne hceq
      simp only [neColors, Finset.mem_filter, Finset.mem_univ, true_and] at hcne
      simp only [eqColors, Finset.mem_filter, Finset.mem_univ, true_and] at hceq
      exact hcne hceq
  simpa [neColors, hcard, two_mul] using hpartition

private def colorSet {V : Type*} (c : V → Bool) : Set V :=
  {v | c v = true}

private def cutGraph {V : Type*} (G : SimpleGraph V)
    (c : V → Bool) : SimpleGraph V :=
  G.between (colorSet c) (colorSet c)ᶜ

private lemma mk_mem_cutGraph_edgeFinset_iff {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (c : V → Bool)
    {u v : V} (he : s(u, v) ∈ G.edgeFinset) :
    s(u, v) ∈ (cutGraph G c).edgeFinset ↔ c u ≠ c v := by
  classical
  have hadj : G.Adj u v := by simpa using he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  simp only [cutGraph, SimpleGraph.between_adj, colorSet, Set.mem_ofPred_eq,
    Set.mem_compl_iff, hadj, true_and]
  cases c u <;> cases c v <;> decide

private lemma cutGraph_edgeFinset_eq_filter {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (c : V → Bool) :
    (cutGraph G c).edgeFinset =
      G.edgeFinset.filter fun e => e ∈ (cutGraph G c).edgeFinset := by
  classical
  ext e
  simp only [Finset.mem_filter]
  constructor
  · intro he
    exact ⟨SimpleGraph.edgeFinset_mono SimpleGraph.between_le he, he⟩
  · exact And.right

private lemma card_colorings_edge_in_cut_eq_half {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    2 * #(Finset.univ.filter fun c : V → Bool =>
      e ∈ (cutGraph G c).edgeFinset) = Fintype.card (V → Bool) := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : G.Adj u v := by simpa using he
      rw [← card_colorings_ne_eq_half hadj.ne]
      congr 2
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact mk_mem_cutGraph_edgeFinset_iff G c he

private lemma sum_cutGraph_edge_card_double {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) :
    (∑ c : V → Bool, 2 * #(cutGraph G c).edgeFinset) =
      Fintype.card (V → Bool) * #G.edgeFinset := by
  classical
  calc
    (∑ c : V → Bool, 2 * #(cutGraph G c).edgeFinset) =
        ∑ c : V → Bool, ∑ e ∈ G.edgeFinset,
          if e ∈ (cutGraph G c).edgeFinset then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [cutGraph_edgeFinset_eq_filter, Finset.card_eq_sum_ones,
        Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hcut : e ∈ (cutGraph G c).edgeFinset
      · have hcut' : e ∈ (cutGraph G c).edgeSet :=
          SimpleGraph.mem_edgeFinset.mp hcut
        simp [he, hcut, hcut']
      · have hcut' : e ∉ (cutGraph G c).edgeSet := fun he' =>
          hcut (SimpleGraph.mem_edgeFinset.mpr he')
        simp [he, hcut, hcut']
    _ = ∑ e ∈ G.edgeFinset, ∑ c : V → Bool,
          if e ∈ (cutGraph G c).edgeFinset then 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e ∈ G.edgeFinset, Fintype.card (V → Bool) := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        (∑ c : V → Bool,
            if e ∈ (cutGraph G c).edgeFinset then 2 else 0) =
            2 * ∑ c : V → Bool,
              if e ∈ (cutGraph G c).edgeFinset then 1 else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          by_cases hcut : e ∈ (cutGraph G c).edgeFinset <;> simp [hcut]
        _ = 2 * #(Finset.univ.filter fun c : V → Bool =>
              e ∈ (cutGraph G c).edgeFinset) := by
          simp only [SimpleGraph.mem_edgeFinset]
          rw [Finset.sum_boole]
          simp
        _ = Fintype.card (V → Bool) :=
          card_colorings_edge_in_cut_eq_half G he
    _ = Fintype.card (V → Bool) * #G.edgeFinset := by
      simp [Nat.mul_comm]

/-- Every finite graph has a bipartite spanning subgraph containing at least
half of its edges. -/
theorem exists_bipartite_spanning_subgraph_half_edges
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧
      G.edgeSet.ncard ≤ 2 * B.edgeSet.ncard := by
  classical
  have hex : ∃ c : V → Bool,
      #G.edgeFinset ≤ 2 * #(cutGraph G c).edgeFinset := by
    by_contra! h
    have hsum_lt :
        (∑ c : V → Bool, 2 * #(cutGraph G c).edgeFinset) <
          ∑ _c : V → Bool, #G.edgeFinset := by
      apply Finset.sum_lt_sum
      · intro c _
        exact (h c).le
      · exact ⟨fun _ => false, Finset.mem_univ _, h _⟩
    rw [sum_cutGraph_edge_card_double] at hsum_lt
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_lt
    exact lt_irrefl _ hsum_lt
  obtain ⟨c, hc⟩ := hex
  refine ⟨cutGraph G c, SimpleGraph.between_le,
    SimpleGraph.between_isBipartite disjoint_compl_right, ?_⟩
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  exact hc

end MaximumCut
end Erdos717

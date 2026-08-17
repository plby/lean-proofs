/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Defs
import ErdosProblems.Erdos63.BipartiteHalf
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Erdős Problem 63: finite density reductions

This file collects the elementary finite density facts used before applying
the deep cycle theorem.  Average degree is kept in the division-free form
from `Erdos63.Defs`.  In particular, all rounding in the core and bipartite
reductions is explicit.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v

variable {V : Type u} {W : Type v}
variable {G G' : SimpleGraph V} {H : SimpleGraph W}

/-! ## Degree sums and edge counts -/

/-- The edge-count version of division-free average degree. -/
theorem avgDegreeAtLeast_iff_twice_card_edgeFinset [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    AvgDegreeAtLeast G d ↔ d * Fintype.card V ≤ 2 * G.edgeFinset.card := by
  rw [AvgDegreeAtLeast, G.sum_degrees_eq_twice_card_edges]

/-- A convenient one-way form of the degree-sum identity. -/
theorem AvgDegreeAtLeast.le_twice_card_edgeFinset [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (h : AvgDegreeAtLeast G d) :
    d * Fintype.card V ≤ 2 * G.edgeFinset.card :=
  (avgDegreeAtLeast_iff_twice_card_edgeFinset G d).mp h

/-- Average degree is invariant under a finite graph isomorphism. -/
theorem avgDegreeAtLeast_iff_of_iso [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (d : ℕ) :
    AvgDegreeAtLeast G d ↔ AvgDegreeAtLeast H d := by
  rw [avgDegreeAtLeast_iff_twice_card_edgeFinset,
    avgDegreeAtLeast_iff_twice_card_edgeFinset, e.card_eq, e.card_edgeFinset_eq]

/-- Passing to a denser spanning graph cannot decrease average degree. -/
theorem AvgDegreeAtLeast.mono_graph [Fintype V]
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    {d : ℕ} (hGG' : G ≤ G') (h : AvgDegreeAtLeast G d) :
    AvgDegreeAtLeast G' d := by
  rw [AvgDegreeAtLeast] at h ⊢
  exact h.trans <| Finset.sum_le_sum fun x _ ↦ G.degree_le_of_le hGG'

/-- A pointwise minimum-degree bound gives the corresponding average bound. -/
theorem avgDegreeAtLeast_of_le_minDegree [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (h : d ≤ G.minDegree) : AvgDegreeAtLeast G d :=
  avgDegreeAtLeast_of_forall_degree G fun v ↦ h.trans (G.minDegree_le_degree v)

/-- On a nonempty vertex type, positive average degree forces an edge. -/
theorem AvgDegreeAtLeast.edgeFinset_nonempty [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (h : AvgDegreeAtLeast G d) (hd : 0 < d) : G.edgeFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hedge
  have hc : G.edgeFinset.card = 0 := by simp [hedge]
  have hv : 0 < Fintype.card V := Fintype.card_pos
  have hdv : 0 < d * Fintype.card V := Nat.mul_pos hd hv
  have := AvgDegreeAtLeast.le_twice_card_edgeFinset G h
  rw [hc] at this
  omega

/-! ## A minimum-degree induced core -/

/-- Deleting a vertex before or after inducing gives isomorphic graphs.

The explicit isomorphism is useful because the two graphs have differently
nested subtype vertex types. -/
private noncomputable def induceEraseIso [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (v : V) (hv : v ∈ S) :
    G.induce (↑(S.erase v) : Set V) ≃g
      (G.induce (↑S : Set V)).induce ({⟨v, hv⟩}ᶜ : Set (↑S : Set V)) where
  toFun x := by
    refine ⟨⟨x, Finset.mem_of_mem_erase x.2⟩, ?_⟩
    have hxv : x.1 ≠ v := (Finset.mem_erase.mp x.2).1
    simpa using hxv
  invFun x := by
    refine ⟨x.1.1, Finset.mem_erase.mpr ⟨?_, x.1.2⟩⟩
    have hxv : x.1 ≠ (⟨v, hv⟩ : (↑S : Set V)) := by
      intro hEq
      apply x.2
      simpa using hEq
    intro h
    exact hxv (Subtype.ext h)
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext <| Subtype.ext rfl
  map_rel_iff' := Iff.rfl

/-- The induced edge count splits into the edges avoiding `v` and the edges
incident with `v`. -/
private theorem card_edgeFinset_induce_erase_add_degree [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    (G.induce (↑(S.erase v) : Set V)).edgeFinset.card +
        (G.induce (↑S : Set V)).degree ⟨v, hv⟩ =
      (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  let K : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
  let x : (↑S : Set V) := ⟨v, hv⟩
  have hdeg : K.degree x ≤ K.edgeFinset.card := K.degree_le_card_edgeFinset x
  have hcard :
      (G.induce (↑(S.erase v) : Set V)).edgeFinset.card =
        K.edgeFinset.card - K.degree x := by
    calc
      (G.induce (↑(S.erase v) : Set V)).edgeFinset.card =
          (K.induce ({x}ᶜ : Set (↑S : Set V))).edgeFinset.card :=
        (induceEraseIso G S v hv).card_edgeFinset_eq
      _ = (K.deleteIncidenceSet x).edgeFinset.card :=
        K.card_edgeFinset_induce_compl_singleton x
      _ = K.edgeFinset.card - K.degree x :=
        K.card_edgeFinset_deleteIncidenceSet x
  change (G.induce (↑(S.erase v) : Set V)).edgeFinset.card + K.degree x =
    K.edgeFinset.card
  rw [hcard, Nat.sub_add_cancel hdeg]

/-- Every nonempty finite graph of average degree at least `d` has a nonempty
induced subgraph which still has average degree at least `d` and has minimum
degree at least `d / 2`.

The proof chooses a smallest nonempty induced subgraph retaining the original
average bound.  If a vertex had degree below `d / 2`, deleting it would retain
that bound, contradicting minimality. -/
theorem exists_induced_core_avgDegreeAtLeast [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (havg : AvgDegreeAtLeast G d) :
    ∃ S : Finset V, S.Nonempty ∧
      AvgDegreeAtLeast (G.induce (↑S : Set V)) d ∧
      d / 2 ≤ (G.induce (↑S : Set V)).minDegree := by
  classical
  let good : Finset V → Prop := fun S ↦
    S.Nonempty ∧ AvgDegreeAtLeast (G.induce (↑S : Set V)) d
  let candidates : Finset (Finset V) := Finset.univ.powerset.filter good
  have hunivavg : AvgDegreeAtLeast (G.induce (Set.univ : Set V)) d :=
    (avgDegreeAtLeast_iff_of_iso (G.induce Set.univ) G
      (G.induceUnivIso) d).mpr havg
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and]
    refine ⟨Finset.univ_nonempty, ?_⟩
    let e : G.induce (↑(Finset.univ : Finset V) : Set V) ≃g G :=
      { toFun := Subtype.val
        invFun := fun x ↦ ⟨x, Finset.mem_univ x⟩
        left_inv := fun x ↦ Subtype.ext rfl
        right_inv := fun _ ↦ rfl
        map_rel_iff' := Iff.rfl }
    exact (avgDegreeAtLeast_iff_of_iso
      (G.induce (↑(Finset.univ : Finset V) : Set V)) G e d).mpr havg
  obtain ⟨S, hScandidates, hSminimal⟩ :=
    candidates.exists_min_image Finset.card hcandidates
  have hSgood : good S := (Finset.mem_filter.mp hScandidates).2
  have hSne : S.Nonempty := hSgood.1
  have hSavg : AvgDegreeAtLeast (G.induce (↑S : Set V)) d := hSgood.2
  let K : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
  have hdegree : ∀ x : (↑S : Set V), d / 2 ≤ K.degree x := by
    intro x
    by_contra hx
    have hxlt : K.degree x < d / 2 := Nat.lt_of_not_ge hx
    have herase_ne : (S.erase x.1).Nonempty := by
      by_contra herase
      have herase_eq : S.erase x.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp herase
      have hScard : S.card = 1 := by
        simpa [herase_eq] using (Finset.card_erase_add_one x.2).symm
      have hKcard : Fintype.card (↑S : Set V) = 1 := by
        simpa [hScard] using Fintype.card_coe S
      have hKedges : K.edgeFinset.card = 0 := by
        have hbottom : K = ⊥ := by
          have hle := K.card_edgeFinset_le_card_choose_two
          rw [hKcard] at hle
          simpa using hle
        simp [hbottom]
      have hbound :=
        (avgDegreeAtLeast_iff_twice_card_edgeFinset K d).mp hSavg
      rw [hKcard, hKedges] at hbound
      omega
    have herase_avg :
        AvgDegreeAtLeast (G.induce (↑(S.erase x.1) : Set V)) d := by
      rw [avgDegreeAtLeast_iff_twice_card_edgeFinset]
      have havg_edges :=
        (avgDegreeAtLeast_iff_twice_card_edgeFinset K d).mp hSavg
      have hvertex_card : Fintype.card (↑S : Set V) = S.card := Fintype.card_coe S
      rw [hvertex_card, ← Finset.card_erase_add_one x.2] at havg_edges
      simp only [Nat.mul_add] at havg_edges
      have hedge_split := card_edgeFinset_induce_erase_add_degree G S x.1 x.2
      change (G.induce (↑(S.erase x.1) : Set V)).edgeFinset.card + K.degree x =
        K.edgeFinset.card at hedge_split
      rw [← hedge_split] at havg_edges
      simp only [Nat.mul_add] at havg_edges
      have htwodeg : 2 * K.degree x ≤ d := by omega
      have hcard_erase :
          Fintype.card (↑(S.erase x.1) : Set V) = (S.erase x.1).card :=
        Fintype.card_coe (S.erase x.1)
      rw [hcard_erase]
      omega
    have herase_candidate : S.erase x.1 ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨(S.erase_subset x.1).trans (Finset.subset_univ S),
        ⟨herase_ne, herase_avg⟩⟩
    have hminimal := hSminimal (S.erase x.1) herase_candidate
    have hcard := Finset.card_erase_add_one x.2
    omega
  refine ⟨S, hSne, hSavg, ?_⟩
  letI : Nonempty (↑S : Set V) :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  exact K.le_minDegree_of_forall_le_degree (d / 2) hdegree

/-! ## Retaining density in a bipartite graph -/

/-- Restricting a bipartite graph to an induced subgraph preserves
bipartiteness. -/
theorem SimpleGraph.IsBipartite.induce {G : SimpleGraph V}
    (h : G.IsBipartite) (S : Set V) : (G.induce S).IsBipartite := by
  obtain ⟨C⟩ := h
  let f : G.induce S →g G :=
    { toFun := Subtype.val
      map_rel' := fun hadj ↦ hadj }
  exact ⟨C.comp f⟩

/-- Exact, unrounded form of the bipartite half-density reduction.  The
right-hand side is twice the degree sum of the retained bipartite graph, so
this says that its average degree is at least one half of the original lower
bound. -/
theorem exists_bipartite_subgraph_twice_average_bound [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (havg : AvgDegreeAtLeast G d) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      d * Fintype.card V ≤ 2 * (∑ x : V, H.degree x) := by
  classical
  obtain ⟨H, hHG, hbip, hhalf⟩ := exists_bipartite_subgraph_half G
  refine ⟨H, hHG, hbip, ?_⟩
  have hGedges := AvgDegreeAtLeast.le_twice_card_edgeFinset G havg
  rw [H.sum_degrees_eq_twice_card_edges]
  exact hGedges.trans <| by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hhalf

/-- A finite graph has a spanning bipartite subgraph whose average degree is
at least half the original integer lower bound (rounded down). -/
theorem exists_bipartite_subgraph_avgDegreeAtLeast_half [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (havg : AvgDegreeAtLeast G d) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧ AvgDegreeAtLeast H (d / 2) := by
  classical
  obtain ⟨H, hHG, hbip, hstrong⟩ :=
    exists_bipartite_subgraph_twice_average_bound G havg
  refine ⟨H, hHG, hbip, ?_⟩
  rw [AvgDegreeAtLeast]
  have hfloor : 2 * (d / 2) ≤ d := Nat.mul_div_le d 2
  have hscaled :
      2 * ((d / 2) * Fintype.card V) ≤ d * Fintype.card V := by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (Fintype.card V) hfloor
  have htwo :
      2 * ((d / 2) * Fintype.card V) ≤
        2 * (∑ x : V, H.degree x) := hscaled.trans hstrong
  exact (Nat.mul_le_mul_left_iff (by omega : 0 < 2)).mp htwo

/-- Combining the half-edge bipartite reduction with the induced-core lemma
gives a nonempty bipartite model retaining the half-average bound and having
minimum degree at least one further factor of two (with explicit rounding). -/
theorem exists_bipartite_induced_core [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (havg : AvgDegreeAtLeast G d) :
    ∃ (H : SimpleGraph V) (S : Finset V),
      H ≤ G ∧ H.IsBipartite ∧ S.Nonempty ∧
      AvgDegreeAtLeast (H.induce (↑S : Set V)) (d / 2) ∧
      d / 4 ≤ (H.induce (↑S : Set V)).minDegree ∧
      (H.induce (↑S : Set V)).IsBipartite := by
  classical
  obtain ⟨H, hHG, hbip, hHavg⟩ :=
    exists_bipartite_subgraph_avgDegreeAtLeast_half G havg
  obtain ⟨S, hSne, hSavg, hSmin⟩ :=
    exists_induced_core_avgDegreeAtLeast H hHavg
  have hSmin' : d / 4 ≤ (H.induce (↑S : Set V)).minDegree := by
    norm_num [Nat.div_div_eq_div_mul] at hSmin ⊢
    exact hSmin
  exact ⟨H, S, hHG, hbip, hSne, hSavg, hSmin',
    SimpleGraph.IsBipartite.induce hbip (↑S : Set V)⟩

end Erdos63

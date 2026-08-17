/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.Covers
import ErdosProblems.Erdos622.GoodCut
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Bounded-degree internal graphs for the almost-bipartite case

This file formalizes the finite edge-truncation and regularity counts behind
equation (4.1) of Draganić--Keevash--Müyesser.  The main theorem gives the
two bounded-degree subgraphs in either orientation of the balanced cut.
-/

namespace Erdos622.BoundedInternal

open Finset
open scoped SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A finite degree truncation -/

private theorem degree_sub_le_card_incidenceFinset
    (H : SimpleGraph V) (d : ℕ) (v : V) :
    H.degree v - d ≤ (H.incidenceFinset v).card := by
  rw [H.card_incidenceFinset_eq_degree]
  exact Nat.sub_le _ _

/-- An arbitrary set of exactly the excess edges incident with `v`. -/
noncomputable def excessEdges (H : SimpleGraph V) (d : ℕ) (v : V) :
    Finset (Sym2 V) :=
  (Finset.exists_subset_card_eq (degree_sub_le_card_incidenceFinset H d v)
    (s := H.incidenceFinset v)).choose

theorem excessEdges_subset (H : SimpleGraph V) (d : ℕ) (v : V) :
    excessEdges H d v ⊆ H.incidenceFinset v :=
  (Finset.exists_subset_card_eq (degree_sub_le_card_incidenceFinset H d v)
    (s := H.incidenceFinset v)).choose_spec.1

@[simp]
theorem card_excessEdges (H : SimpleGraph V) (d : ℕ) (v : V) :
    (excessEdges H d v).card = H.degree v - d :=
  (Finset.exists_subset_card_eq (degree_sub_le_card_incidenceFinset H d v)
    (s := H.incidenceFinset v)).choose_spec.2

/-- Delete, simultaneously, the chosen excess set at every vertex. -/
noncomputable def deletionSet (H : SimpleGraph V) (d : ℕ) :
    Finset (Sym2 V) :=
  Finset.univ.biUnion (excessEdges H d)

/-- The spanning subgraph obtained by the simultaneous degree truncation. -/
noncomputable def truncateDegree (H : SimpleGraph V) (d : ℕ) :
    SimpleGraph V :=
  H.deleteEdges (deletionSet H d : Set (Sym2 V))

theorem deletionSet_subset_edgeFinset (H : SimpleGraph V) (d : ℕ) :
    deletionSet H d ⊆ H.edgeFinset := by
  intro e he
  obtain ⟨v, _hv, hev⟩ := Finset.mem_biUnion.mp he
  exact (H.incidenceFinset_subset v) (excessEdges_subset H d v hev)

theorem card_deletionSet_le_sum_excess (H : SimpleGraph V) (d : ℕ) :
    (deletionSet H d).card ≤ ∑ v : V, (H.degree v - d) := by
  calc
    (deletionSet H d).card ≤
        ∑ v ∈ (Finset.univ : Finset V), (excessEdges H d v).card :=
      Finset.card_biUnion_le
    _ = ∑ v : V, (H.degree v - d) := by simp

theorem truncateDegree_le (H : SimpleGraph V) (d : ℕ) :
    truncateDegree H d ≤ H :=
  SimpleGraph.deleteEdges_le _

theorem truncateDegree_degree_le (H : SimpleGraph V) (d : ℕ) (v : V) :
    (truncateDegree H d).degree v ≤ d := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  have hsub :
      (truncateDegree H d).incidenceFinset v ⊆
        H.incidenceFinset v \ excessEdges H d v := by
    intro e he
    rw [SimpleGraph.incidenceFinset_eq_filter] at he ⊢
    simp only [Finset.mem_filter, Finset.mem_sdiff] at he ⊢
    refine ⟨⟨?_, he.2⟩, ?_⟩
    · exact SimpleGraph.edgeFinset_mono (truncateDegree_le H d) he.1
    · intro hex
      have hdel : e ∈ deletionSet H d := by
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hex⟩
      have heedge : e ∈ (truncateDegree H d).edgeFinset := he.1
      have hedge :
          (truncateDegree H d).edgeFinset =
            H.edgeFinset \ deletionSet H d := by
        apply Finset.coe_injective
        rw [SimpleGraph.coe_edgeFinset, Finset.coe_sdiff,
          SimpleGraph.coe_edgeFinset]
        exact SimpleGraph.edgeSet_deleteEdges _
      rw [hedge] at heedge
      exact (Finset.mem_sdiff.mp heedge).2 hdel
  calc
    ((truncateDegree H d).incidenceFinset v).card ≤
        (H.incidenceFinset v \ excessEdges H d v).card :=
      Finset.card_le_card hsub
    _ = (H.incidenceFinset v).card - (excessEdges H d v).card :=
      Finset.card_sdiff_of_subset (excessEdges_subset H d v)
    _ = H.degree v - (H.degree v - d) := by simp
    _ ≤ d := by omega

theorem truncateDegree_edge_bound (H : SimpleGraph V) (d : ℕ) :
    H.edgeFinset.card ≤
      (truncateDegree H d).edgeFinset.card +
        ∑ v : V, (H.degree v - d) := by
  have hdel := deletionSet_subset_edgeFinset H d
  have hcard := card_deletionSet_le_sum_excess H d
  have hedge :
      (truncateDegree H d).edgeFinset =
        H.edgeFinset \ deletionSet H d := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, Finset.coe_sdiff,
      SimpleGraph.coe_edgeFinset]
    exact SimpleGraph.edgeSet_deleteEdges _
  rw [hedge, Finset.card_sdiff_of_subset hdel]
  omega

/-- A budgeted version of simultaneous degree truncation. -/
theorem exists_bounded_subgraph_of_degree_le_add
    (H : SimpleGraph V) (d : ℕ) (budget : V → ℕ)
    (hdegree : ∀ v, H.degree v ≤ d + budget v) :
    ∃ J : SimpleGraph V,
      J ≤ H ∧ (∀ v, J.degree v ≤ d) ∧
        H.edgeFinset.card ≤ J.edgeFinset.card + ∑ v, budget v := by
  refine ⟨truncateDegree H d, truncateDegree_le H d,
    truncateDegree_degree_le H d, ?_⟩
  refine (truncateDegree_edge_bound H d).trans ?_
  gcongr with v
  exact Nat.sub_le_of_le_add (by simpa [Nat.add_comm] using hdegree v)

/-! ## The bipartite graph between two finite vertex sets -/

/-- The subgraph of `G` consisting of its edges between `P` and `Q`. -/
def betweenGraph (G : SimpleGraph V) (P Q : Finset V) : SimpleGraph V :=
  G ⊓ SimpleGraph.fromRel (fun u v ↦ u ∈ P ∧ v ∈ Q)

@[simp]
theorem betweenGraph_adj (G : SimpleGraph V) (P Q : Finset V) (u v : V) :
    (betweenGraph G P Q).Adj u v ↔
      G.Adj u v ∧
        ((u ∈ P ∧ v ∈ Q) ∨ (v ∈ P ∧ u ∈ Q)) := by
  rw [betweenGraph]
  simp only [SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, _hne, hmem⟩
    exact ⟨huv, hmem⟩
  · rintro ⟨huv, hmem⟩
    exact ⟨huv, huv.ne, hmem⟩

theorem betweenGraph_le (G : SimpleGraph V) (P Q : Finset V) :
    betweenGraph G P Q ≤ G :=
  inf_le_left

theorem betweenGraph_isBipartiteWith (G : SimpleGraph V)
    {P Q : Finset V} (hPQ : Disjoint P Q) :
    (betweenGraph G P Q).IsBipartiteWith (P : Set V) (Q : Set V) := by
  refine ⟨by simpa using hPQ, ?_⟩
  intro u v huv
  rcases (betweenGraph_adj G P Q u v).mp huv |>.2 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

theorem betweenGraph_degree_eq_degreeInto_left (G : SimpleGraph V)
    {P Q : Finset V} (hPQ : Disjoint P Q) {v : V} (hv : v ∈ P) :
    (betweenGraph G P Q).degree v = degreeInto G v Q := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degreeInto
  congr 1
  ext w
  have hvQ : v ∉ Q := Finset.disjoint_left.mp hPQ hv
  simp [betweenGraph_adj, hv, hvQ, and_comm]

theorem betweenGraph_degree_eq_degreeInto_right (G : SimpleGraph V)
    {P Q : Finset V} (hPQ : Disjoint P Q) {v : V} (hv : v ∈ Q) :
    (betweenGraph G P Q).degree v = degreeInto G v P := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degreeInto
  congr 1
  ext w
  have hvP : v ∉ P := Finset.disjoint_right.mp hPQ hv
  simp [betweenGraph_adj, hv, hvP, and_comm]

theorem card_betweenGraph (G : SimpleGraph V)
    {P Q : Finset V} (hPQ : Disjoint P Q) :
    (betweenGraph G P Q).edgeFinset.card = edgesBetween G P Q := by
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (betweenGraph_isBipartiteWith G hPQ)]
  rw [edgesBetween_eq_sum_degreeInto]
  apply Finset.sum_congr rfl
  intro v hv
  exact betweenGraph_degree_eq_degreeInto_left G hPQ hv

/-! ## Regularity identities on a balanced cut -/

theorem degreeInto_add_compl_of_not_mem (G : SimpleGraph V)
    (v : V) (S : Finset V) (hv : v ∉ S) :
    degreeInto G v S + degreeInto Gᶜ v S = S.card := by
  unfold degreeInto
  have hdisj : Disjoint (G.neighborFinset v ∩ S) (Gᶜ.neighborFinset v ∩ S) := by
    rw [Finset.disjoint_left]
    intro w hwG hwGc
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hwG hwGc
    exact hwGc.1.2 hwG.1
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext w
  constructor
  · simp only [Finset.mem_union, Finset.mem_inter]
    rintro (⟨_, hwS⟩ | ⟨_, hwS⟩) <;> exact hwS
  · intro hwS
    have hvw : v ≠ w := by
      intro hvw
      subst w
      exact hv hwS
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
    by_cases hadj : G.Adj v w
    · exact Or.inl ⟨(G.mem_neighborFinset v w).mpr hadj, hwS⟩
    · exact Or.inr ⟨((Gᶜ).mem_neighborFinset v w).mpr ⟨hvw, hadj⟩, hwS⟩

theorem degreeInto_internal_eq_succ_compl_other
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B : Finset (Fin (2 * n))} (hcut : IsCut A B)
    (hBcard : B.card = n) {v : Fin (2 * n)} (hvA : v ∈ A) :
    degreeInto G v A = degreeInto Gᶜ v B + 1 := by
  have hvB : v ∉ B := Finset.disjoint_left.mp hcut.1 hvA
  have hpartition := degreeInto_union_of_disjoint G v hcut.1
  rw [hcut.2, degreeInto_univ, hreg.degree_eq] at hpartition
  have hfill := degreeInto_add_compl_of_not_mem G v B hvB
  rw [hBcard] at hfill
  omega

theorem degree_between_le_cap_add_budget
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hBcard : B.card = n)
    (hCA : C ⊆ A) (hDB : D ⊆ B)
    (v : Fin (2 * n)) :
    (betweenGraph G C (A \ C)).degree v ≤
      (D.card + 1) + if v ∈ A then degreeInto Gᶜ v (B \ D) else 0 := by
  have hCX : Disjoint C (A \ C) := Finset.disjoint_sdiff
  by_cases hvC : v ∈ C
  · have hvA : v ∈ A := hCA hvC
    rw [betweenGraph_degree_eq_degreeInto_left G hCX hvC, if_pos hvA]
    have hmono : degreeInto G v (A \ C) ≤ degreeInto G v A :=
      degreeInto_mono G v Finset.sdiff_subset
    have hint := degreeInto_internal_eq_succ_compl_other G hreg hcut hBcard hvA
    have hsplit := degreeInto_union_of_disjoint Gᶜ v
      (Finset.disjoint_sdiff : Disjoint D (B \ D))
    rw [Finset.union_sdiff_of_subset hDB] at hsplit
    have hDle := degreeInto_le_card Gᶜ v D
    omega
  · by_cases hvX : v ∈ A \ C
    · have hvA : v ∈ A := (Finset.mem_sdiff.mp hvX).1
      rw [betweenGraph_degree_eq_degreeInto_right G hCX hvX, if_pos hvA]
      have hmono : degreeInto G v C ≤ degreeInto G v A :=
        degreeInto_mono G v hCA
      have hint := degreeInto_internal_eq_succ_compl_other G hreg hcut hBcard hvA
      have hsplit := degreeInto_union_of_disjoint Gᶜ v
        (Finset.disjoint_sdiff : Disjoint D (B \ D))
      rw [Finset.union_sdiff_of_subset hDB] at hsplit
      have hDle := degreeInto_le_card Gᶜ v D
      omega
    · have hzero : (betweenGraph G C (A \ C)).degree v = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,
          Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        rw [SimpleGraph.mem_neighborFinset, betweenGraph_adj] at hw
        rcases hw.2 with h | h
        · exact hvC h.1
        · exact hvX h.2
      rw [hzero]
      exact Nat.zero_le _

/-- Exact edge count between a minimum cover and its independent complement. -/
theorem card_between_cover_complement
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hAcard : A.card = n) (hBcard : B.card = n)
    (hC : IsVertexCoverOn G A C) (hDB : D ⊆ B) :
    (betweenGraph G C (A \ C)).edgeFinset.card + C.card =
      n + edgesBetween Gᶜ (A \ C) D +
        edgesBetween Gᶜ (A \ C) (B \ D) := by
  have hCX : Disjoint C (A \ C) := Finset.disjoint_sdiff
  have hXA : A \ C ⊆ A := Finset.sdiff_subset
  have hXcard : (A \ C).card + C.card = n := by
    rw [Finset.card_sdiff_of_subset hC.1, hAcard]
    have hle := Finset.card_le_card hC.1
    omega
  have hpoint : ∀ v ∈ A \ C,
      degreeInto G v C =
        1 + degreeInto Gᶜ v D + degreeInto Gᶜ v (B \ D) := by
    intro v hvX
    have hvA : v ∈ A := hXA hvX
    have hzero : degreeInto G v (A \ C) = 0 :=
      degreeInto_sdiff_eq_zero G hC hvX
    have hsplitA := degreeInto_union_of_disjoint G v
      (Finset.disjoint_sdiff : Disjoint C (A \ C))
    rw [Finset.union_sdiff_of_subset hC.1] at hsplitA
    have hint := degreeInto_internal_eq_succ_compl_other G hreg hcut hBcard hvA
    have hsplitB := degreeInto_union_of_disjoint Gᶜ v
      (Finset.disjoint_sdiff : Disjoint D (B \ D))
    rw [Finset.union_sdiff_of_subset hDB] at hsplitB
    omega
  rw [card_betweenGraph G hCX, edgesBetween_comm G C,
    edgesBetween_eq_sum_degreeInto]
  calc
    (∑ v ∈ A \ C, degreeInto G v C) + C.card =
        (∑ v ∈ A \ C,
          (1 + degreeInto Gᶜ v D + degreeInto Gᶜ v (B \ D))) + C.card := by
      congr 1
      apply Finset.sum_congr rfl
      exact hpoint
    _ = n + edgesBetween Gᶜ (A \ C) D +
          edgesBetween Gᶜ (A \ C) (B \ D) := by
      rw [edgesBetween_eq_sum_degreeInto, edgesBetween_eq_sum_degreeInto]
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const_zero, Nat.zero_add, Finset.sum_const,
        Nat.nsmul_eq_mul, one_mul]
      omega

/-- The second regularity count in the oriented setup. -/
theorem complement_cross_lower_bound
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hAcard : A.card = n) (hBcard : B.card = n)
    (hC : IsVertexCoverOn G A C) (hD : IsVertexCoverOn G B D) :
    n + edgesBetween Gᶜ C (B \ D) + edgesBetween Gᶜ (A \ C) (B \ D) ≤
      C.card * D.card + 2 * D.card + edgesBetween Gᶜ D (A \ C) := by
  have hDY : Disjoint D (B \ D) := Finset.disjoint_sdiff
  have hbase := card_between_cover_complement G hreg hcut.symm
    hBcard hAcard hD hC.1
  have hbase' :
      (betweenGraph G D (B \ D)).edgeFinset.card + D.card =
        n + edgesBetween Gᶜ C (B \ D) +
          edgesBetween Gᶜ (A \ C) (B \ D) := by
    simpa only [edgesBetween_comm Gᶜ] using hbase
  have hcapPoint : ∀ v ∈ D,
      degreeInto G v (B \ D) ≤
        (C.card + 1) + degreeInto Gᶜ v (A \ C) := by
    intro v hvD
    have hdeg := degree_between_le_cap_add_budget G hreg hcut.symm
      hAcard hD.1 hC.1 v
    rw [betweenGraph_degree_eq_degreeInto_left G hDY hvD,
      if_pos (hD.1 hvD)] at hdeg
    exact hdeg
  have hcap :
      (betweenGraph G D (B \ D)).edgeFinset.card ≤
        D.card * (C.card + 1) + edgesBetween Gᶜ D (A \ C) := by
    rw [card_betweenGraph G hDY, edgesBetween_eq_sum_degreeInto,
      edgesBetween_eq_sum_degreeInto]
    calc
      ∑ v ∈ D, degreeInto G v (B \ D) ≤
          ∑ v ∈ D, ((C.card + 1) + degreeInto Gᶜ v (A \ C)) :=
        Finset.sum_le_sum hcapPoint
      _ = D.card * (C.card + 1) +
          ∑ v ∈ D, degreeInto Gᶜ v (A \ C) := by
        simp_rw [Finset.sum_add_distrib]
        simp [Nat.mul_add, Nat.mul_comm]
  have hcapAdd :
      (betweenGraph G D (B \ D)).edgeFinset.card + D.card ≤
        C.card * D.card + 2 * D.card + edgesBetween Gᶜ D (A \ C) := by
    rw [Nat.mul_add, Nat.mul_one] at hcap
    rw [Nat.mul_comm D.card C.card] at hcap
    omega
  rw [hbase'] at hcapAdd
  exact hcapAdd

/-- The concrete finite conclusion of DKM (4.1) in one orientation. -/
def OrientedBoundedInternal
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (A B C D : Finset (Fin (2 * n))) : Prop :=
  ∃ JA JB : SimpleGraph (Fin (2 * n)),
    JA ≤ G ∧ JB ≤ G ∧
    JA.support ⊆ (A : Set (Fin (2 * n))) ∧
    JB.support ⊆ (B : Set (Fin (2 * n))) ∧
    JA.IsBipartiteWith (C : Set (Fin (2 * n)))
      (↑(A \ C) : Set (Fin (2 * n))) ∧
    JB.IsBipartiteWith (D : Set (Fin (2 * n)))
      (↑(B \ D) : Set (Fin (2 * n))) ∧
    (∀ v, JA.degree v ≤ D.card + 1) ∧
    (∀ v, JB.degree v ≤ C.card + 1) ∧
    2 * n ≤ JA.edgeFinset.card + C.card * D.card + C.card + 2 * D.card ∧
    n ≤ JB.edgeFinset.card + D.card

private theorem support_between_subset
    (G : SimpleGraph V) {A P Q : Finset V}
    (hPA : P ⊆ A) (hQA : Q ⊆ A) :
    (betweenGraph G P Q).support ⊆ (A : Set V) := by
  intro v hv
  obtain ⟨w, hvw⟩ := hv
  rcases (betweenGraph_adj G P Q v w).mp hvw |>.2 with h | h
  · exact hPA h.1
  · exact hQA h.2

private theorem isBipartiteWith_of_le_between
    {G J : SimpleGraph V} {P Q : Finset V} (hPQ : Disjoint P Q)
    (hJ : J ≤ betweenGraph G P Q) :
    J.IsBipartiteWith (P : Set V) (Q : Set V) := by
  refine ⟨by simpa using hPQ, ?_⟩
  intro v w hvw
  exact (betweenGraph_isBipartiteWith G hPQ).mem_of_adj (hJ hvw)

/-- Edge truncation realizes the two bounded internal graphs in the
orientation where `ē(D,A\C) ≤ ē(C,B\D)`. -/
theorem exists_orientedBoundedInternal
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hAcard : A.card = n) (hBcard : B.card = n)
    (hC : IsVertexCoverOn G A C) (hD : IsVertexCoverOn G B D)
    (horient : edgesBetween Gᶜ D (A \ C) ≤ edgesBetween Gᶜ C (B \ D)) :
    OrientedBoundedInternal G A B C D := by
  let HA := betweenGraph G C (A \ C)
  let HB := betweenGraph G D (B \ D)
  let budgetA : Fin (2 * n) → ℕ :=
    fun v ↦ if v ∈ A then degreeInto Gᶜ v (B \ D) else 0
  let budgetB : Fin (2 * n) → ℕ :=
    fun v ↦ if v ∈ B then degreeInto Gᶜ v (A \ C) else 0
  have hdegA : ∀ v, HA.degree v ≤ (D.card + 1) + budgetA v := by
    intro v
    exact degree_between_le_cap_add_budget G hreg hcut hBcard hC.1 hD.1 v
  have hdegB : ∀ v, HB.degree v ≤ (C.card + 1) + budgetB v := by
    intro v
    exact degree_between_le_cap_add_budget G hreg hcut.symm hAcard hD.1 hC.1 v
  obtain ⟨JA, hJAHA, hJAdeg, hJAedge⟩ :=
    exists_bounded_subgraph_of_degree_le_add HA (D.card + 1) budgetA hdegA
  obtain ⟨JB, hJBHB, hJBdeg, hJBedge⟩ :=
    exists_bounded_subgraph_of_degree_le_add HB (C.card + 1) budgetB hdegB
  have hCX : Disjoint C (A \ C) := Finset.disjoint_sdiff
  have hDY : Disjoint D (B \ D) := Finset.disjoint_sdiff
  have hbudgetA : ∑ v, budgetA v =
      edgesBetween Gᶜ C (B \ D) + edgesBetween Gᶜ (A \ C) (B \ D) := by
    have hsum : ∑ v, budgetA v = edgesBetween Gᶜ A (B \ D) := by
      rw [edgesBetween_eq_sum_degreeInto]
      simp [budgetA]
    have hAunion : C ∪ (A \ C) = A := Finset.union_sdiff_of_subset hC.1
    calc
      ∑ v, budgetA v = edgesBetween Gᶜ A (B \ D) := hsum
      _ = edgesBetween Gᶜ (C ∪ (A \ C)) (B \ D) := by rw [hAunion]
      _ = _ := by
        rw [edgesBetween_comm Gᶜ,
          edgesBetween_union_right_of_disjoint Gᶜ _ hCX,
          edgesBetween_comm Gᶜ (B \ D) C,
          edgesBetween_comm Gᶜ (B \ D) (A \ C)]
  have hbudgetB : ∑ v, budgetB v =
      edgesBetween Gᶜ D (A \ C) + edgesBetween Gᶜ (A \ C) (B \ D) := by
    have hsum : ∑ v, budgetB v = edgesBetween Gᶜ B (A \ C) := by
      rw [edgesBetween_eq_sum_degreeInto]
      simp [budgetB]
    have hBunion : D ∪ (B \ D) = B := Finset.union_sdiff_of_subset hD.1
    calc
      ∑ v, budgetB v = edgesBetween Gᶜ B (A \ C) := hsum
      _ = edgesBetween Gᶜ (D ∪ (B \ D)) (A \ C) := by rw [hBunion]
      _ = _ := by
        rw [edgesBetween_comm Gᶜ,
          edgesBetween_union_right_of_disjoint Gᶜ _ hDY,
          edgesBetween_comm Gᶜ (A \ C) D]
  have hbaseA := card_between_cover_complement G hreg hcut
    hAcard hBcard hC hD.1
  have hbaseB := card_between_cover_complement G hreg hcut.symm
    hBcard hAcard hD hC.1
  have hcross := complement_cross_lower_bound G hreg hcut hAcard hBcard hC hD
  have hJAedge' : HA.edgeFinset.card ≤ JA.edgeFinset.card +
      (edgesBetween Gᶜ C (B \ D) + edgesBetween Gᶜ (A \ C) (B \ D)) := by
    simpa [hbudgetA] using hJAedge
  have hJBedge' : HB.edgeFinset.card ≤ JB.edgeFinset.card +
      (edgesBetween Gᶜ D (A \ C) + edgesBetween Gᶜ (A \ C) (B \ D)) := by
    simpa [hbudgetB] using hJBedge
  have hlargeA :
      2 * n ≤ JA.edgeFinset.card + C.card * D.card + C.card + 2 * D.card := by
    have hbaseA' : HA.edgeFinset.card + C.card =
        n + edgesBetween Gᶜ D (A \ C) +
          edgesBetween Gᶜ (A \ C) (B \ D) := by
      change HA.edgeFinset.card + C.card = _ at hbaseA
      simpa only [edgesBetween_comm Gᶜ (A \ C) D] using hbaseA
    omega
  have hlargeB : n ≤ JB.edgeFinset.card + D.card := by
    change HB.edgeFinset.card + D.card = _ at hbaseB
    have hbaseB' : HB.edgeFinset.card + D.card =
        n + edgesBetween Gᶜ C (B \ D) +
          edgesBetween Gᶜ (A \ C) (B \ D) := by
      simpa only [edgesBetween_comm Gᶜ] using hbaseB
    omega
  refine ⟨JA, JB,
    hJAHA.trans (betweenGraph_le G C (A \ C)),
    hJBHB.trans (betweenGraph_le G D (B \ D)),
    (SimpleGraph.support_mono hJAHA).trans
      (support_between_subset G hC.1 Finset.sdiff_subset),
    (SimpleGraph.support_mono hJBHB).trans
      (support_between_subset G hD.1 Finset.sdiff_subset),
    isBipartiteWith_of_le_between hCX hJAHA,
    isBipartiteWith_of_le_between hDY hJBHB,
    hJAdeg, hJBdeg, hlargeA, hlargeB⟩

/-- The orientation-free form: one of the two orders of the cut satisfies
the strong `2n` bound. -/
theorem exists_boundedInternal_either_orientation
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hAcard : A.card = n) (hBcard : B.card = n)
    (hC : IsVertexCoverOn G A C) (hD : IsVertexCoverOn G B D) :
    OrientedBoundedInternal G A B C D ∨
      OrientedBoundedInternal G B A D C := by
  rcases le_total (edgesBetween Gᶜ D (A \ C))
      (edgesBetween Gᶜ C (B \ D)) with h | h
  · exact Or.inl (exists_orientedBoundedInternal G hreg hcut hAcard hBcard hC hD h)
  · exact Or.inr (exists_orientedBoundedInternal G hreg hcut.symm
      hBcard hAcard hD hC h)

end Erdos622.BoundedInternal

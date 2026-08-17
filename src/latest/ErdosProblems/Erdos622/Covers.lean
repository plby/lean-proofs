/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 622: finite cut and cover lemmas

This file contains the elementary deterministic counting facts used in the
almost-bipartite part of Draganić--Keevash--Müyesser's proof.
-/

namespace Erdos622

open Finset
open scoped SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of neighbours of `v` which lie in `S`. -/
def degreeInto (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : ℕ :=
  (G.neighborFinset v ∩ S).card

lemma degreeInto_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    degreeInto G v S = ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
  have heq : G.neighborFinset v ∩ S = S.filter fun w ↦ G.Adj v w := by
    ext w
    simp [and_comm]
  rw [degreeInto, heq]
  simpa using (Finset.sum_boole (fun w ↦ G.Adj v w) S).symm

lemma degreeInto_union_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : Disjoint S T) :
    degreeInto G v (S ∪ T) = degreeInto G v S + degreeInto G v T := by
  rw [degreeInto, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right
      Finset.inter_subset_right (Finset.disjoint_of_subset_left
        Finset.inter_subset_right hST))]
  rfl

lemma degreeInto_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeInto G v Finset.univ = G.degree v := by
  simp [degreeInto, G.card_neighborFinset_eq_degree]

lemma degreeInto_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : S ⊆ T) :
    degreeInto G v S ≤ degreeInto G v T := by
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
    hST (Finset.mem_inter.mp hw).2⟩

lemma degreeInto_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    degreeInto G v S ≤ S.card := by
  exact Finset.card_le_card Finset.inter_subset_right

/-- The number of ordered adjacent pairs whose first endpoint lies in `S`
and whose second endpoint lies in `T`.  For disjoint sets this is the usual
number of graph edges across the cut. -/
def edgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) : ℕ :=
  ∑ v ∈ S, ∑ w ∈ T, if G.Adj v w then 1 else 0

lemma edgesBetween_eq_sum_degreeInto (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    edgesBetween G S T = ∑ v ∈ S, degreeInto G v T := by
  apply Finset.sum_congr rfl
  intro v hv
  exact (degreeInto_eq_sum G v T).symm

lemma edgesBetween_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    edgesBetween G S T = edgesBetween G T S := by
  rw [edgesBetween, edgesBetween, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

lemma edgesBetween_le_card_mul_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    edgesBetween G S T ≤ S.card * T.card := by
  rw [edgesBetween_eq_sum_degreeInto]
  calc
    (∑ v ∈ S, degreeInto G v T) ≤ ∑ _v ∈ S, T.card := by
      exact Finset.sum_le_sum fun v hv ↦ degreeInto_le_card G v T
    _ = S.card * T.card := by simp

/-- A finite set meeting both endpoints of every edge induced by `S`. -/
def IsVertexCoverOn (G : SimpleGraph V) (S C : Finset V) : Prop :=
  C ⊆ S ∧
    ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → G.Adj u v → u ∈ C ∨ v ∈ C

lemma degreeInto_sdiff_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    {S C : Finset V} (hC : IsVertexCoverOn G S C)
    {v : V} (hv : v ∈ S \ C) :
    degreeInto G v (S \ C) = 0 := by
  rw [degreeInto, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwn := Finset.mem_inter.mp hw
  have hv' := Finset.mem_sdiff.mp hv
  have hw' := Finset.mem_sdiff.mp hwn.2
  rcases hC.2 hv'.1 hw'.1 ((G.mem_neighborFinset v w).mp hwn.1) with h | h
  · exact hv'.2 h
  · exact hw'.2 h

lemma edgesBetween_sdiff_self_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    {S C : Finset V} (hC : IsVertexCoverOn G S C) :
    edgesBetween G (S \ C) (S \ C) = 0 := by
  rw [edgesBetween_eq_sum_degreeInto]
  exact Finset.sum_eq_zero fun v hv ↦ degreeInto_sdiff_eq_zero G hC hv

lemma edgesBetween_union_right_of_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {T U : Finset V} (hTU : Disjoint T U) :
    edgesBetween G S (T ∪ U) =
      edgesBetween G S T + edgesBetween G S U := by
  simp_rw [edgesBetween_eq_sum_degreeInto,
    degreeInto_union_of_disjoint G _ hTU, Finset.sum_add_distrib]

lemma sum_degree_eq_edgesBetween_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {A B : Finset V}
    (hAB : Disjoint A B) (hpart : A ∪ B = Finset.univ) :
    (∑ v ∈ S, G.degree v) =
      edgesBetween G S A + edgesBetween G S B := by
  rw [edgesBetween_eq_sum_degreeInto, edgesBetween_eq_sum_degreeInto,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← degreeInto_union_of_disjoint G v hAB, hpart, degreeInto_univ]

lemma edgesBetween_add_le_sum_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {T U : Finset V} (hTU : Disjoint T U) :
    edgesBetween G S T + edgesBetween G S U ≤ ∑ v ∈ S, G.degree v := by
  rw [← edgesBetween_union_right_of_disjoint G S hTU,
    edgesBetween_eq_sum_degreeInto]
  exact Finset.sum_le_sum fun v hv ↦
    (degreeInto_mono G v (Finset.subset_univ (T ∪ U))).trans_eq
      (degreeInto_univ G v)

lemma sum_degree_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hreg : G.IsRegularOfDegree r) (S : Finset V) :
    (∑ v ∈ S, G.degree v) = S.card * r := by
  simp [hreg.degree_eq]

/-- A vertex cover of size `c` in a graph of maximum degree at most `D`
covers at most `cD` edges. -/
theorem card_edgeFinset_le_card_mul_of_vertexCover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (D : ℕ)
    (hcover : G.IsVertexCover (C : Set V))
    (hdegree : ∀ v ∈ C, G.degree v ≤ D) :
    G.edgeFinset.card ≤ C.card * D := by
  have hsub : G.edgeFinset ⊆ C.biUnion (fun v ↦ G.incidenceFinset v) := by
    intro e he
    obtain ⟨u, v⟩ := e
    have huv : G.Adj u v := by
      simpa using SimpleGraph.mem_edgeFinset.mp he
    rcases hcover huv with hu | hv
    · rw [Finset.mem_biUnion]
      refine ⟨u, hu, ?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_left u v⟩
    · rw [Finset.mem_biUnion]
      refine ⟨v, hv, ?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_right u v⟩
  calc
    G.edgeFinset.card ≤ (C.biUnion (fun v ↦ G.incidenceFinset v)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ C, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ C, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact G.card_incidenceFinset_eq_degree v
    _ ≤ ∑ _v ∈ C, D := Finset.sum_le_sum fun v hv ↦ hdegree v hv
    _ = C.card * D := by simp

theorem card_edgeFinset_le_card_mul_maxDegree_of_vertexCover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hcover : G.IsVertexCover (C : Set V)) :
    G.edgeFinset.card ≤ C.card * G.maxDegree :=
  card_edgeFinset_le_card_mul_of_vertexCover G C G.maxDegree hcover
    (fun v hv ↦ G.degree_le_maxDegree v)

/-- The cover-product inequality forced by degree `n+1` across a balanced
cut of a graph on `2n` vertices. -/
theorem balancedCut_cover_product
    (n : ℕ) (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B A' B' : Finset (Fin (2 * n))}
    (hAB : Disjoint A B) (hpart : A ∪ B = Finset.univ)
    (hAcard : A.card = n) (hBcard : B.card = n)
    (hAcover : IsVertexCoverOn G A A')
    (hBcover : IsVertexCoverOn G B B') :
    n + 1 ≤ (A'.card + 1) * (B'.card + 1) := by
  let X := A \ A'
  let Y := B \ B'
  have hAX : Disjoint X A' := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvA'
    exact (Finset.mem_sdiff.mp hvX).2 hvA'
  have hBY : Disjoint B' Y := by
    apply Finset.disjoint_left.mpr
    intro v hvB' hvY
    exact (Finset.mem_sdiff.mp hvY).2 hvB'
  have hXY : Disjoint X Y := by
    exact hAB.mono Finset.sdiff_subset Finset.sdiff_subset
  have hXcard : X.card + A'.card = n := by
    have hle : A'.card ≤ n :=
      (Finset.card_le_card hAcover.1).trans_eq hAcard
    dsimp [X]
    rw [Finset.card_sdiff_of_subset hAcover.1, hAcard]
    omega
  have hYcard : Y.card + B'.card = n := by
    have hle : B'.card ≤ n :=
      (Finset.card_le_card hBcover.1).trans_eq hBcard
    dsimp [Y]
    rw [Finset.card_sdiff_of_subset hBcover.1, hBcard]
    omega
  have hYzero : edgesBetween G Y Y = 0 := by
    exact edgesBetween_sdiff_self_eq_zero G hBcover
  have hXzero : edgesBetween G X X = 0 := by
    exact edgesBetween_sdiff_self_eq_zero G hAcover
  have hsumY :
      (n + 1) * Y.card =
        edgesBetween G Y X + edgesBetween G Y A' +
          edgesBetween G Y B' + edgesBetween G Y Y := by
    have hdeg := sum_degree_eq_edgesBetween_partition G Y hAB hpart
    rw [← Finset.sdiff_union_of_subset hAcover.1,
      edgesBetween_union_right_of_disjoint G Y hAX,
      ← Finset.union_sdiff_of_subset hBcover.1,
      edgesBetween_union_right_of_disjoint G Y hBY] at hdeg
    rw [sum_degree_regular G hreg Y] at hdeg
    simpa [Nat.mul_comm, Nat.add_assoc] using hdeg
  have hsumX :
      (n + 1) * X.card =
        edgesBetween G X X + edgesBetween G X A' +
          edgesBetween G X B' + edgesBetween G X Y := by
    have hdeg := sum_degree_eq_edgesBetween_partition G X hAB hpart
    rw [← Finset.sdiff_union_of_subset hAcover.1,
      edgesBetween_union_right_of_disjoint G X hAX,
      ← Finset.union_sdiff_of_subset hBcover.1,
      edgesBetween_union_right_of_disjoint G X hBY] at hdeg
    rw [sum_degree_regular G hreg X] at hdeg
    simpa [Nat.mul_comm, Nat.add_assoc] using hdeg
  have hcapA :
      edgesBetween G A' Y + edgesBetween G A' X ≤
        A'.card * (n + 1) := by
    calc
      edgesBetween G A' Y + edgesBetween G A' X ≤
          ∑ v ∈ A', G.degree v :=
        edgesBetween_add_le_sum_degree G A' hXY.symm
      _ = A'.card * (n + 1) := sum_degree_regular G hreg A'
  have hcapB :
      edgesBetween G B' X + edgesBetween G B' Y ≤
        B'.card * (n + 1) := by
    calc
      edgesBetween G B' X + edgesBetween G B' Y ≤
          ∑ v ∈ B', G.degree v :=
        edgesBetween_add_le_sum_degree G B' hXY
      _ = B'.card * (n + 1) := sum_degree_regular G hreg B'
  have hYX : edgesBetween G Y X ≤ Y.card * X.card :=
    edgesBetween_le_card_mul_card G Y X
  have hYX' : edgesBetween G Y X ≤ X.card * Y.card := by
    simpa [Nat.mul_comm] using hYX
  have hXY' : edgesBetween G X Y ≤ X.card * Y.card :=
    edgesBetween_le_card_mul_card G X Y
  have hmain :
      (n + 1) * Y.card ≤ X.card * Y.card + A'.card * (n + 1) := by
    rcases le_total (edgesBetween G B' Y) (edgesBetween G A' X) with hpq | hqp
    · rw [edgesBetween_comm G Y B', edgesBetween_comm G Y A', hYzero] at hsumY
      omega
    · rw [edgesBetween_comm G X A', edgesBetween_comm G X B', hXzero] at hsumX
      have hmainX :
          (n + 1) * X.card ≤ X.card * Y.card + B'.card * (n + 1) := by
        omega
      have hmainXz :
          ((n + 1) * X.card : ℤ) ≤
            (X.card * Y.card : ℕ) + B'.card * (n + 1) := by
        exact_mod_cast hmainX
      have hXcardz : (X.card : ℤ) + A'.card = n := by
        exact_mod_cast hXcard
      have hYcardz : (Y.card : ℤ) + B'.card = n := by
        exact_mod_cast hYcard
      have htargetz :
          ((n + 1) * Y.card : ℕ) ≤
            X.card * Y.card + A'.card * (n + 1) := by
        exact_mod_cast (show
          ((n + 1 : ℕ) * Y.card : ℤ) ≤
            (X.card * Y.card : ℕ) + A'.card * (n + 1) by
          push_cast
          nlinarith)
      exact htargetz
  have hmainz :
      ((n + 1) * Y.card : ℤ) ≤
        (X.card * Y.card : ℕ) + A'.card * (n + 1) := by
    exact_mod_cast hmain
  have hXcardz : (X.card : ℤ) + A'.card = n := by
    exact_mod_cast hXcard
  have hYcardz : (Y.card : ℤ) + B'.card = n := by
    exact_mod_cast hYcard
  have hresultz :
      (n + 1 : ℤ) ≤ (A'.card + 1 : ℕ) * (B'.card + 1) := by
    push_cast
    nlinarith
  exact_mod_cast hresultz

end Erdos622

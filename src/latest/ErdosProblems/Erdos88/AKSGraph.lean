/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import Mathlib
import ErdosProblems.Erdos88.FiniteES
import ErdosProblems.Erdos88.AKSFamily
import ErdosProblems.Erdos88.Richness

/-!
# Erdős Problem 88: graph-theoretic AKS lemmas

This file contains the finite graph bookkeeping used in the
Alon--Krivelevich--Sudakov small-count argument.  In particular it fixes the
meaning of a balanced graph, proves the degree-averaging step underlying AKS
Lemma 3.1, and proves two exact discrete interpolation lemmas used after the
AKS block construction.
-/

open SimpleGraph

namespace Erdos88
namespace AKSGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable local instance graphAdjDecidable (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

/-- The number of edges of `G` having both endpoints in `S`.  This local
definition keeps the AKS graph module independently checkable; the root
Problem 88 module identifies it with its public induced-edge count. -/
noncomputable def edgeCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card

@[simp] lemma edgeCount_univ (G : SimpleGraph V) :
    edgeCount G Finset.univ = G.edgeFinset.card := by
  simp [edgeCount]

/-- The degree of `v` into a finite set of vertices. -/
noncomputable def degreeInto (G : SimpleGraph V) (v : V) (S : Finset V) : ℕ :=
  (G.neighborFinset v ∩ S).card

lemma edgeCount_mono (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    edgeCount G S ≤ edgeCount G T := by
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2.trans hST⟩

lemma edgeCount_le_choose (G : SimpleGraph V) (S : Finset V) :
    edgeCount G S ≤ S.card.choose 2 := by
  have hbound :=
    (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
  rw [← G.card_filter_edgeFinset_toFinset_subset S] at hbound
  simpa [edgeCount] using hbound

lemma edgeCount_eq_zero_of_card_le_one (G : SimpleGraph V) {S : Finset V}
    (hS : S.card ≤ 1) : edgeCount G S = 0 := by
  have hbound := edgeCount_le_choose G S
  have hchoose : S.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  omega

@[simp] lemma degreeInto_empty (G : SimpleGraph V) (v : V) :
    degreeInto G v ∅ = 0 := by
  simp [degreeInto]

lemma degreeInto_le_card (G : SimpleGraph V) (v : V) (S : Finset V) :
    degreeInto G v S ≤ S.card := by
  exact Finset.card_le_card Finset.inter_subset_right

lemma degreeInto_mono (G : SimpleGraph V) (v : V) {S T : Finset V}
    (hST : S ⊆ T) : degreeInto G v S ≤ degreeInto G v T := by
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_inter] at hw ⊢
  exact ⟨hw.1, hST hw.2⟩

lemma degreeInto_union_le (G : SimpleGraph V) (v : V) (S T : Finset V) :
    degreeInto G v (S ∪ T) ≤ degreeInto G v S + degreeInto G v T := by
  rw [degreeInto, degreeInto, degreeInto]
  have hEq : G.neighborFinset v ∩ (S ∪ T) =
      (G.neighborFinset v ∩ S) ∪ (G.neighborFinset v ∩ T) := by
    ext x
    simp [and_or_left]
  rw [hEq]
  exact Finset.card_union_le _ _

lemma degreeInto_le_sdiff_add_card (G : SimpleGraph V) (v : V)
    (S T : Finset V) :
    degreeInto G v S ≤ degreeInto G v (S \ T) + T.card := by
  calc
    degreeInto G v S ≤ degreeInto G v ((S \ T) ∪ T) :=
      degreeInto_mono G v (by intro x hx; simp [hx])
    _ ≤ degreeInto G v (S \ T) + degreeInto G v T :=
      degreeInto_union_le G v (S \ T) T
    _ ≤ degreeInto G v (S \ T) + T.card :=
      Nat.add_le_add_left (degreeInto_le_card G v T) _

/-- Inside a set containing `v`, the degrees in a graph and its complement
partition all other vertices. -/
lemma degreeInto_add_degreeInto_compl (G : SimpleGraph V) (v : V)
    (C : Finset V) (hv : v ∈ C) :
    degreeInto G v C + degreeInto Gᶜ v C = C.card - 1 := by
  let A := G.neighborFinset v ∩ C
  let B := Gᶜ.neighborFinset v ∩ C
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hadj : G.Adj v x := by
      simpa [A] using (Finset.mem_inter.mp hxA).1
    have hnadj : ¬G.Adj v x := by
      have := (Finset.mem_inter.mp hxB).1
      have h' : v ≠ x ∧ ¬G.Adj v x := by simpa using this
      exact h'.2
    exact hnadj hadj
  have hunion : A ∪ B = C.erase v := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · have hxA' := Finset.mem_inter.mp hxA
        exact Finset.mem_erase.mpr ⟨by
          intro hxv
          subst x
          exact G.loopless.irrefl v (by simpa using hxA'.1), hxA'.2⟩
      · have hxB' := Finset.mem_inter.mp hxB
        exact Finset.mem_erase.mpr ⟨by
          intro hxv
          subst x
          exact Gᶜ.loopless.irrefl v (by simpa using hxB'.1), hxB'.2⟩
    · intro hx
      have hx' := Finset.mem_erase.mp hx
      by_cases hadj : G.Adj v x
      · apply Finset.mem_union.mpr
        left
        exact Finset.mem_inter.mpr ⟨by simpa using hadj, hx'.2⟩
      · apply Finset.mem_union.mpr
        right
        have hcomp : x ∈ Gᶜ.neighborFinset v := by
          simp [hadj, Ne.symm hx'.1]
        exact Finset.mem_inter.mpr ⟨hcomp, hx'.2⟩
  have hcard : A.card + B.card = C.card - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem hv]
  have hA : degreeInto G v C = A.card := by
    rw [degreeInto]
  have hB : degreeInto Gᶜ v C = B.card := by
    rw [degreeInto]
    apply congrArg Finset.card
    ext x
    simp [B]
  rw [hA, hB]
  exact hcard

/-- Vertices of `C` having at most half the possible degree into `C`. -/
noncomputable def lowDegreeSide (G : SimpleGraph V) (C : Finset V) : Finset V :=
  C.filter fun v ↦ degreeInto G v C ≤ (C.card - 1) / 2

lemma lowDegreeSide_subset (G : SimpleGraph V) (C : Finset V) :
    lowDegreeSide G C ⊆ C := Finset.filter_subset _ _

/-- In one of `G` and `Gᶜ`, at least half of `C` has degree at most half
the possible degree.  Keeping this orientation is essential for the strong
AKS common-neighbor/common-nonneighbor product. -/
lemma exists_large_lowDegreeSide (G : SimpleGraph V) (C : Finset V) :
    (C.card / 2 ≤ (lowDegreeSide G C).card) ∨
      (C.card / 2 ≤ (lowDegreeSide Gᶜ C).card) := by
  have hcover : C ⊆ lowDegreeSide G C ∪ lowDegreeSide Gᶜ C := by
    intro v hv
    have hsum := degreeInto_add_degreeInto_compl G v C hv
    by_cases hlow : degreeInto G v C ≤ (C.card - 1) / 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hlow⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, by omega⟩)
  have hcard : C.card ≤
      (lowDegreeSide G C).card + (lowDegreeSide Gᶜ C).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  by_cases hG : C.card / 2 ≤ (lowDegreeSide G C).card
  · exact Or.inl hG
  · right
    omega

lemma degreeInto_erase_le_add_one (G : SimpleGraph V) (u v : V) (S : Finset V) :
    degreeInto G u S ≤ degreeInto G u (S.erase v) + 1 := by
  let A := G.neighborFinset u ∩ S
  have hcard : A.card ≤ (A.erase v).card + 1 := by
    by_cases hv : v ∈ A
    · rw [← A.card_erase_add_one hv]
    · simp [Finset.erase_eq_of_notMem hv]
  have herase : A.erase v = G.neighborFinset u ∩ S.erase v := by
    ext w
    simp [A, and_assoc, and_left_comm, and_comm]
  simpa [degreeInto, A, herase] using hcard

lemma degreeInto_erase_self (G : SimpleGraph V) (v : V) (S : Finset V) :
    degreeInto G v (S.erase v) = degreeInto G v S := by
  apply le_antisymm
  · exact degreeInto_mono G v (Finset.erase_subset _ _)
  · rw [degreeInto]
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_inter] at hw ⊢
    have hwv : w ≠ v := by
      intro h
      subst w
      simpa using hw.1
    exact ⟨hw.1, Finset.mem_erase.mpr ⟨hwv, hw.2⟩⟩

lemma degreeInto_eq_sum (G : SimpleGraph V) (v : V) (S : Finset V) :
    degreeInto G v S = ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
  have heq : G.neighborFinset v ∩ S = S.filter fun w ↦ G.Adj v w := by
    ext w
    simp [and_comm]
  rw [degreeInto, heq]
  simpa using (Finset.sum_boole (fun w ↦ G.Adj v w) S).symm

lemma degreeInto_insert (G : SimpleGraph V) (u v : V) (S : Finset V)
    (hv : v ∉ S) :
    degreeInto G u (insert v S) =
      degreeInto G u S + if G.Adj u v then 1 else 0 := by
  by_cases huv : G.Adj u v
  · have hvN : v ∈ G.neighborFinset u := by simpa
    have hvNS : v ∉ G.neighborFinset u ∩ S := by simp [hv]
    rw [degreeInto, degreeInto]
    have hinter : G.neighborFinset u ∩ insert v S =
        insert v (G.neighborFinset u ∩ S) := by
      ext w
      simp [huv, and_or_left, and_comm, and_left_comm]
    rw [hinter, Finset.card_insert_of_notMem hvNS]
    simp [huv]
  · have hvN : v ∉ G.neighborFinset u := by simpa
    rw [degreeInto, degreeInto]
    have hinter : G.neighborFinset u ∩ insert v S =
        G.neighborFinset u ∩ S := by
      ext w
      simp [huv, and_or_left, and_comm, and_left_comm]
    rw [hinter]
    simp [huv]

/-- The degree sum inside a vertex set is twice its induced edge count. -/
lemma sum_degreeInto (G : SimpleGraph V) (S : Finset V) :
    ∑ v ∈ S, degreeInto G v S = 2 * edgeCount G S := by
  let K : SimpleGraph V := (G.induce (↑S : Set V)).spanningCoe
  letI : DecidableRel K.Adj := Classical.decRel _
  have hneighbor (v : V) : K.neighborFinset v =
      if v ∈ S then G.neighborFinset v ∩ S else ∅ := by
    ext w
    by_cases hv : v ∈ S <;> simp [K, hv]
  have hdegree (v : V) : K.degree v =
      if v ∈ S then degreeInto G v S else 0 := by
    rw [← K.card_neighborFinset_eq_degree, hneighbor]
    by_cases hv : v ∈ S <;> simp [hv, degreeInto]
  have hedge : K.edgeFinset =
      G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S := by
    ext e
    obtain ⟨x, y⟩ := e
    simp [K, Sym2.toFinset_mk_eq, Finset.insert_subset_iff]
  have hsum : (∑ v : V, K.degree v) = ∑ v ∈ S, degreeInto G v S := by
    calc
      _ = ∑ v : V, if v ∈ S then degreeInto G v S else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hdegree v
      _ = _ := by
        rw [← Finset.sum_filter]
        simp
  calc
    _ = ∑ v : V, K.degree v := hsum.symm
    _ = 2 * K.edgeFinset.card := K.sum_degrees_eq_twice_card_edges
    _ = 2 * edgeCount G S := by
      rw [hedge]
      rfl

/-- Adding one new vertex creates exactly its edges into the old set. -/
lemma edgeCount_insert (G : SimpleGraph V) (v : V) (S : Finset V)
    (hv : v ∉ S) :
    edgeCount G (insert v S) = edgeCount G S + degreeInto G v S := by
  have hnew := sum_degreeInto G (insert v S)
  have hold := sum_degreeInto G S
  rw [Finset.sum_insert hv] at hnew
  rw [degreeInto_insert G v v S hv] at hnew
  have hloop : ¬G.Adj v v := G.loopless.irrefl v
  simp [hloop] at hnew
  have hterms :
      (∑ x ∈ S, degreeInto G x (insert v S)) =
        (∑ x ∈ S, degreeInto G x S) + degreeInto G v S := by
    calc
      _ = ∑ x ∈ S, (degreeInto G x S + if G.Adj x v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact degreeInto_insert G x v S hv
      _ = (∑ x ∈ S, degreeInto G x S) +
          ∑ x ∈ S, (if G.Adj x v then 1 else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ x ∈ S, degreeInto G x S) + degreeInto G v S := by
        congr 1
        rw [degreeInto_eq_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [adj_comm]
  rw [hterms, hold] at hnew
  omega

/-- Exact edge increment when the two vertices of one AKS correction block
are both added.  The final Boolean term is the possible edge internal to
that two-vertex block. -/
lemma edgeCount_insert_pair (G : SimpleGraph V) (A : Finset V) (p q : V)
    (hpA : p ∉ A) (hqA : q ∉ A) (hpq : p ≠ q) :
    edgeCount G (insert q (insert p A)) =
      edgeCount G A + degreeInto G p A + degreeInto G q A +
        (if G.Adj q p then 1 else 0) := by
  have hqInsert : q ∉ insert p A := by simp [hqA, hpq.symm]
  rw [edgeCount_insert G q (insert p A) hqInsert,
    edgeCount_insert G p A hpA, degreeInto_insert G q p A hpA]
  omega

/-- Double-counting identity for induced edges in all fixed-cardinality
subsets.  Every edge of `S` occurs in exactly
`choose (|S|-2) (k-2)` of its `k`-subsets. -/
lemma sum_edgeCount_powersetCard (G : SimpleGraph V) (S : Finset V)
    {k : ℕ} (hkTwo : 2 ≤ k) (hkS : k ≤ S.card) :
    ∑ A ∈ S.powersetCard k, edgeCount G A =
      edgeCount G S * (S.card - 2).choose (k - 2) := by
  let E := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S
  have hcount (A : Finset V) (hA : A ∈ S.powersetCard k) :
      edgeCount G A =
        ∑ e ∈ E, if e.toFinset ⊆ A then 1 else 0 := by
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hfilter :
        G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ A) =
          E.filter (fun e ↦ e.toFinset ⊆ A) := by
      ext e
      simp only [E, Finset.mem_filter]
      constructor
      · rintro ⟨he, heA⟩
        exact ⟨⟨he, heA.trans hAS⟩, heA⟩
      · rintro ⟨⟨he, _heS⟩, heA⟩
        exact ⟨he, heA⟩
    rw [edgeCount, hfilter]
    symm
    simpa using
      (Finset.sum_boole (R := ℕ) (fun e ↦ e.toFinset ⊆ A) E)
  calc
    ∑ A ∈ S.powersetCard k, edgeCount G A =
        ∑ A ∈ S.powersetCard k,
          ∑ e ∈ E, if e.toFinset ⊆ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hcount A hA
    _ = ∑ e ∈ E, ∑ A ∈ S.powersetCard k,
          if e.toFinset ⊆ A then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e ∈ E, (S.card - 2).choose (k - 2) := by
      apply Finset.sum_congr rfl
      intro e he
      have heEdge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
      have heS : e.toFinset ⊆ S := (Finset.mem_filter.mp he).2
      have heCard : e.toFinset.card = 2 := by
        exact G.card_toFinset_mem_edgeFinset ⟨e, heEdge⟩
      rw [Finset.sum_boole]
      simpa [heCard] using
        Finset.card_filter_powersetCard_subset e.toFinset S k heS (by omega)
    _ = E.card * (S.card - 2).choose (k - 2) := by simp
    _ = edgeCount G S * (S.card - 2).choose (k - 2) := by rfl

/-- A fixed-size subset has at least the ambient induced-edge density.  This
is the averaging step used to choose every dense `A_i` in AKS Lemma 3.2. -/
lemma exists_dense_subset (G : SimpleGraph V) (S : Finset V) (γ : ℝ)
    {k : ℕ} (hkTwo : 2 ≤ k) (hkS : k ≤ S.card)
    (hdense : γ * (S.card.choose 2 : ℝ) ≤ (edgeCount G S : ℝ)) :
    ∃ A ⊆ S, A.card = k ∧
      γ * (k.choose 2 : ℝ) ≤ (edgeCount G A : ℝ) := by
  have hpowerset : (S.powersetCard k).Nonempty := by
    simpa only [Finset.powersetCard_nonempty] using hkS
  have hchoose :
      S.card.choose k * k.choose 2 =
        S.card.choose 2 * (S.card - 2).choose (k - 2) :=
    Nat.choose_mul hkTwo
  have hsumCount := sum_edgeCount_powersetCard G S hkTwo hkS
  have hsumCast :
      (∑ A ∈ S.powersetCard k, (edgeCount G A : ℝ)) =
        (edgeCount G S : ℝ) * ((S.card - 2).choose (k - 2) : ℝ) := by
    exact_mod_cast hsumCount
  have hsumLower :
      ∑ _A ∈ S.powersetCard k, γ * (k.choose 2 : ℝ) ≤
        ∑ A ∈ S.powersetCard k, (edgeCount G A : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, hsumCast]
    have hfactor : (0 : ℝ) ≤ ((S.card - 2).choose (k - 2) : ℝ) := by positivity
    have hdenseMul := mul_le_mul_of_nonneg_right hdense hfactor
    have hchooseReal :
        (S.card.choose k : ℝ) * (k.choose 2 : ℝ) =
          (S.card.choose 2 : ℝ) * ((S.card - 2).choose (k - 2) : ℝ) := by
      exact_mod_cast hchoose
    calc
      (S.card.choose k : ℝ) * (γ * (k.choose 2 : ℝ)) =
          γ * ((S.card.choose k : ℝ) * (k.choose 2 : ℝ)) := by ring
      _ = γ * ((S.card.choose 2 : ℝ) *
          ((S.card - 2).choose (k - 2) : ℝ)) := by rw [hchooseReal]
      _ = (γ * (S.card.choose 2 : ℝ)) *
          ((S.card - 2).choose (k - 2) : ℝ) := by ring
      _ ≤ (edgeCount G S : ℝ) *
          ((S.card - 2).choose (k - 2) : ℝ) := hdenseMul
  obtain ⟨A, hA, hAedge⟩ :=
    Finset.exists_le_of_sum_le hpowerset hsumLower
  exact ⟨A, (Finset.mem_powersetCard.mp hA).1,
    (Finset.mem_powersetCard.mp hA).2, hAedge⟩

lemma degreeInto_union_eq_left_of_indep (G : SimpleGraph V)
    {A B D : Finset V} {v : V} (hBD : B ⊆ D) (hvD : v ∈ D)
    (hD : G.IsIndepSet (D : Set V)) :
    degreeInto G v (A ∪ B) = degreeInto G v A := by
  rw [degreeInto, degreeInto]
  congr 1
  ext w
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hvw, hwA | hwB⟩
    · exact ⟨hvw, hwA⟩
    · exfalso
      have hadj : G.Adj v w := by simpa using hvw
      by_cases heq : v = w
      · subst w
        exact G.loopless.irrefl v hadj
      · exact (hD hvD (hBD hwB) heq) hadj
  · rintro ⟨hvw, hwA⟩
    exact ⟨hvw, Or.inl hwA⟩

/-- If `b` has no neighbors in `C`, adjoining `C` does not change its
degree into the base set.  Unlike `degreeInto_union_eq_left_of_indep`, this
does not require the vertices of `C` to be mutually nonadjacent. -/
lemma degreeInto_union_eq_left_of_anticomplete (G : SimpleGraph V)
    {X C : Finset V} {b : V}
    (hanti : ∀ c ∈ C, ¬G.Adj b c) :
    degreeInto G b (X ∪ C) = degreeInto G b X := by
  rw [degreeInto, degreeInto]
  congr 1
  ext c
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hbc, hcX | hcC⟩
    · exact ⟨hbc, hcX⟩
    · exfalso
      exact (hanti c hcC) (by simpa using hbc)
  · rintro ⟨hbc, hcX⟩
    exact ⟨hbc, Or.inl hcX⟩

/-- Every vertex of `S` is adjacent to every vertex of `T`. -/
def CompleteTo (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → G.Adj s t

/-- No vertex of `S` is adjacent to a vertex of `T`. -/
def AnticompleteTo (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → ¬G.Adj s t

/-- Common neighbors of every vertex of `B`, restricted to a reservoir
`M`. -/
noncomputable def commonNeighbors (G : SimpleGraph V) (M B : Finset V) : Finset V :=
  M.filter fun x ↦ ∀ b ∈ B, G.Adj b x

/-- Common nonneighbors of every vertex of `B`, restricted to `M`. -/
noncomputable def commonNonneighbors (G : SimpleGraph V) (M B : Finset V) : Finset V :=
  M.filter fun x ↦ ∀ b ∈ B, ¬G.Adj b x

@[simp] lemma mem_commonNeighbors {G : SimpleGraph V} {M B : Finset V} {x : V} :
    x ∈ commonNeighbors G M B ↔ x ∈ M ∧ ∀ b ∈ B, G.Adj b x := by
  simp [commonNeighbors]

@[simp] lemma mem_commonNonneighbors {G : SimpleGraph V}
    {M B : Finset V} {x : V} :
    x ∈ commonNonneighbors G M B ↔ x ∈ M ∧ ∀ b ∈ B, ¬G.Adj b x := by
  simp [commonNonneighbors]

/-- The union of the correction blocks with indices at most `d`. -/
def BThrough (B : ℕ → Finset V) (d : ℕ) : Finset V :=
  (Finset.range (d + 1)).biUnion B

lemma BThrough_mono (B : ℕ → Finset V) {d e : ℕ} (hde : d ≤ e) :
    BThrough B d ⊆ BThrough B e := by
  intro v hv
  simp only [BThrough, Finset.mem_biUnion] at hv ⊢
  obtain ⟨i, hi, hvi⟩ := hv
  exact ⟨i, Finset.mem_range.mpr
    ((Finset.mem_range.mp hi).trans_le (Nat.add_le_add_right hde 1)), hvi⟩

lemma subset_BThrough (B : ℕ → Finset V) {i d : ℕ} (hid : i ≤ d) :
    B i ⊆ BThrough B d := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hid), hv⟩

/-- Graph form of the two-set specialization of the AKS indexed-family
selection lemma.  The hypotheses deliberately retain the exact integral
counting inequality, so all later rounding is visible. -/
theorem exists_pair_with_large_common_parts (G : SimpleGraph V)
    (M U : Finset V) (d r q : ℕ)
    (hr : ∀ u ∈ U, r ≤ degreeInto G u M)
    (hq : ∀ u ∈ U, q ≤ (M \ G.neighborFinset u).card)
    (hnumeric :
      M.card ^ 4 + U.card.choose 2 * (d ^ 2 * M.card ^ 2) <
        U.card * (r ^ 2 * q ^ 2)) :
    ∃ B ⊆ U, B.card = 2 ∧
      d < (commonNeighbors G M B).card ∧
      d < (commonNonneighbors G M B).card := by
  let F : (↥U) → Finset V := fun u ↦ G.neighborFinset u.1 ∩ M
  have hFM : ∀ u, F u ⊆ M := fun _ ↦ Finset.inter_subset_right
  have hr' : ∀ u, r ≤ (F u).card := by
    intro u
    simpa [F, degreeInto] using hr u.1 u.2
  have hq' : ∀ u, q ≤ (M \ F u).card := by
    intro u
    have heq : M \ F u = M \ G.neighborFinset u.1 := by
      ext x
      simp [F, and_assoc]
    rw [heq]
    exact hq u.1 u.2
  have hnumeric' :
      M.card ^ 4 + (Fintype.card (↥U)).choose 2 *
          (d ^ 2 * M.card ^ 2) <
        Fintype.card (↥U) * (r ^ 2 * q ^ 2) := by
    simpa using hnumeric
  obtain ⟨J, hJcard, hJgood⟩ :=
    AKSFamily.pairSelection M F hFM d r q hr' hq' hnumeric'
  let B : Finset V := J.image Subtype.val
  have hBU : B ⊆ U := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    exact u.2
  have hBcard : B.card = 2 := by
    change (J.image Subtype.val).card = 2
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hJcard]
  have hJmem : J ∈ J.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, hJcard⟩
  have hparts := hJgood J hJmem
  have hcommon : AKSFamily.commonPart M F J = commonNeighbors G M B := by
    ext x
    simp only [AKSFamily.mem_commonPart, mem_commonNeighbors]
    constructor
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
      have hxu := hx u hu
      have hxu' : G.Adj (u : V) x ∧ x ∈ M := by
        simpa [F] using hxu
      exact hxu'.1
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro u hu
      have hub : u.1 ∈ B := Finset.mem_image.mpr ⟨u, hu, rfl⟩
      have := hx u.1 hub
      simp [F, hxM, this]
  have houtside : AKSFamily.commonOutside M F J = commonNonneighbors G M B := by
    ext x
    simp only [AKSFamily.mem_commonOutside, mem_commonNonneighbors]
    constructor
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
      have hxu := hx u hu
      simpa [F, hxM] using hxu
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro u hu
      have hub : u.1 ∈ B := Finset.mem_image.mpr ⟨u, hu, rfl⟩
      have := hx u.1 hub
      simpa [F, hxM] using this
  exact ⟨B, hBU, hBcard, by simpa [hcommon] using hparts.1,
    by simpa [houtside] using hparts.2⟩

/-- A reusable exact arithmetic criterion for the AKS pair-family inequality.
The hypotheses `w ≤ Qℓ` and `w ≤ 3q` make the main right-hand side at
least twice `w⁴`; `hbad` reserves less than the remaining copy for bad
pairs. -/
lemma pairSelection_numeric_of_ratio {w u ℓ q d Q : ℕ}
    (hu : 18 * Q ^ 2 ≤ u)
    (hwℓ : w ≤ Q * ℓ) (hwq : w ≤ 3 * q)
    (hbad : u.choose 2 * (d ^ 2 * w ^ 2) < w ^ 4) :
    w ^ 4 + u.choose 2 * (d ^ 2 * w ^ 2) <
      u * (ℓ ^ 2 * q ^ 2) := by
  have hwℓ2 := Nat.pow_le_pow_left hwℓ 2
  have hwq2 := Nat.pow_le_pow_left hwq 2
  have hratioRaw := Nat.mul_le_mul hwℓ2 hwq2
  have hratio : w ^ 4 ≤ 9 * Q ^ 2 * (ℓ ^ 2 * q ^ 2) := by
    nlinarith
  have hmul := Nat.mul_le_mul_right (ℓ ^ 2 * q ^ 2) hu
  have htwice : 2 * w ^ 4 ≤ u * (ℓ ^ 2 * q ^ 2) := by
    nlinarith
  omega

/-- The rounded quotient loses a full positive copy of `u`, hence its
product is strictly smaller than the original numerator. -/
lemma mul_div_sub_one_lt {w u : ℕ} (hw : 0 < w) (hu : 0 < u) :
    u * (w / u - 1) < w := by
  have hdiv := Nat.div_mul_le_self w u
  rw [Nat.mul_comm] at hdiv
  by_cases hq : w / u = 0
  · simp [hq, hw]
  · have hqpos : 0 < w / u := Nat.pos_of_ne_zero hq
    have hqone : 1 ≤ w / u := hqpos
    have hstep : u * (w / u - 1) + u = u * (w / u) := by
      calc
        u * (w / u - 1) + u = u * (w / u - 1) + u * 1 := by simp
        _ = u * ((w / u - 1) + 1) := (Nat.mul_add _ _ _).symm
        _ = u * (w / u) := by rw [Nat.sub_add_cancel hqone]
    have hlt : u * (w / u - 1) < u * (w / u - 1) + u :=
      Nat.lt_add_of_pos_right hu
    rw [hstep] at hlt
    exact hlt.trans_le hdiv

/-- If `u d < w`, even the crude bound `choose(u,2) ≤ u²` makes the
bad-pair contribution strictly smaller than `w⁴`. -/
lemma pair_bad_budget_of_mul_lt {w u d : ℕ} (hw : 0 < w)
    (hud : u * d < w) :
    u.choose 2 * (d ^ 2 * w ^ 2) < w ^ 4 := by
  have hchoose := Nat.choose_le_pow u 2
  have hudPow := Nat.pow_lt_pow_left hud (by decide : 2 ≠ 0)
  have hwPow : 0 < w ^ 2 := pow_pos hw 2
  have hstrict := Nat.mul_lt_mul_of_pos_right hudPow hwPow
  calc
    u.choose 2 * (d ^ 2 * w ^ 2) ≤
        u ^ 2 * (d ^ 2 * w ^ 2) := Nat.mul_le_mul_right _ hchoose
    _ = (u * d) ^ 2 * w ^ 2 := by ring
    _ < w ^ 2 * w ^ 2 := hstrict
    _ = w ^ 4 := by ring

/-- The explicit uniform pair-stage schedule from the AKS proof.  Taking
`u = 18Q²` selected vertices and `d = ⌊w/u⌋-1` satisfies the exact
family-selection inequality whenever the two oriented degree ratios hold. -/
lemma pairSelection_numeric_divSchedule {w ℓ q Q : ℕ}
    (hw : 0 < w) (hQ : 0 < Q)
    (hwℓ : w ≤ Q * ℓ) (hwq : w ≤ 3 * q) :
    let u := 18 * Q ^ 2
    let d := w / u - 1
    w ^ 4 + u.choose 2 * (d ^ 2 * w ^ 2) <
      u * (ℓ ^ 2 * q ^ 2) := by
  dsimp only
  apply pairSelection_numeric_of_ratio le_rfl hwℓ hwq
  apply pair_bad_budget_of_mul_lt hw
  exact mul_div_sub_one_lt hw (by positivity)

/-- Graph form of the triple specialization of the AKS indexed-family
selection lemma.  Every triple in the returned vertex family has large
common-neighbor and common-nonneighbor parts inside `M`. -/
theorem exists_family_with_good_triples (G : SimpleGraph V)
    (M U : Finset V) (b d r q : ℕ) (hb : 0 < b)
    (hr : ∀ u ∈ U, r ≤ degreeInto G u M)
    (hq : ∀ u ∈ U, q ≤ (M \ G.neighborFinset u).card)
    (hnumeric :
      (b - 1) * M.card ^ 8 + U.card.choose 3 *
          (d ^ 4 * M.card ^ 4) <
        U.card * (r ^ 4 * q ^ 4)) :
    ∃ J ⊆ U, J.card = b ∧
      ∀ B ∈ J.powersetCard 3,
        d < (commonNeighbors G M B).card ∧
        d < (commonNonneighbors G M B).card := by
  let F : (↑U) → Finset V := fun u ↦ G.neighborFinset u.1 ∩ M
  have hFM : ∀ u, F u ⊆ M := fun _ ↦ Finset.inter_subset_right
  have hr' : ∀ u, r ≤ (F u).card := by
    intro u
    simpa [F, degreeInto] using hr u.1 u.2
  have hq' : ∀ u, q ≤ (M \ F u).card := by
    intro u
    have heq : M \ F u = M \ G.neighborFinset u.1 := by
      ext x
      simp [F, and_assoc]
    rw [heq]
    exact hq u.1 u.2
  have hnumeric' :
      (b - 1) * M.card ^ 8 + (Fintype.card (↑U)).choose 3 *
          (d ^ 4 * M.card ^ 4) <
        Fintype.card (↑U) * (r ^ 4 * q ^ 4) := by
    simpa using hnumeric
  obtain ⟨J, hJcard, hJgood⟩ :=
    AKSFamily.tripleSelection M F hFM b d r q hb hr' hq' hnumeric'
  let Jv : Finset V := J.image Subtype.val
  have hJvU : Jv ⊆ U := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact u.2
  have hJvcard : Jv.card = b := by
    change (J.image Subtype.val).card = b
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hJcard]
  refine ⟨Jv, hJvU, hJvcard, ?_⟩
  intro B hB
  have hBJv : B ⊆ Jv := (Finset.mem_powersetCard.mp hB).1
  have hBcard : B.card = 3 := (Finset.mem_powersetCard.mp hB).2
  let T : Finset (↑U) := J.filter fun u ↦ u.1 ∈ B
  have hTJ : T ⊆ J := Finset.filter_subset _ _
  have hTimage : T.image Subtype.val = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
      subst x
      exact (Finset.mem_filter.mp hu).2
    · intro hx
      have hxJv := hBJv hx
      obtain ⟨u, huJ, hux⟩ := Finset.mem_image.mp hxJv
      exact Finset.mem_image.mpr ⟨u,
        Finset.mem_filter.mpr ⟨huJ, by simpa [hux] using hx⟩, hux⟩
  have hTcard : T.card = 3 := by
    rw [← hBcard, ← hTimage,
      Finset.card_image_of_injective _ Subtype.val_injective]
  have hTpower : T ∈ J.powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hTJ, hTcard⟩
  have hparts := hJgood T hTpower
  have hcommon : AKSFamily.commonPart M F T = commonNeighbors G M B := by
    ext x
    simp only [AKSFamily.mem_commonPart, mem_commonNeighbors]
    constructor
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro v hv
      rw [← hTimage] at hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      have hxu := hx u hu
      have hxu' : G.Adj (u : V) x ∧ x ∈ M := by simpa [F] using hxu
      exact hxu'.1
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro u hu
      have huv : u.1 ∈ B := by
        rw [← hTimage]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      simp [F, hxM, hx u.1 huv]
  have houtside : AKSFamily.commonOutside M F T =
      commonNonneighbors G M B := by
    ext x
    simp only [AKSFamily.mem_commonOutside, mem_commonNonneighbors]
    constructor
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro v hv
      rw [← hTimage] at hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      have hxu := hx u hu
      simpa [F, hxM] using hxu
    · rintro ⟨hxM, hx⟩
      refine ⟨hxM, ?_⟩
      intro u hu
      have huv : u.1 ∈ B := by
        rw [← hTimage]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      simpa [F, hxM] using hx u.1 huv
  exact ⟨by simpa [hcommon] using hparts.1,
    by simpa [houtside] using hparts.2⟩

/-- Every unordered pair inside `S` is an edge of exactly one of `G` and
`Gᶜ`. -/
lemma edgeCount_add_edgeCount_compl (G : SimpleGraph V) (S : Finset V) :
    edgeCount G S + edgeCount Gᶜ S = S.card.choose 2 := by
  have hG : edgeCount G S = (G.induce (↑S : Set V)).edgeFinset.card := by
    simpa only [edgeCount] using G.card_filter_edgeFinset_toFinset_subset S
  have hGc : edgeCount Gᶜ S = (Gᶜ.induce (↑S : Set V)).edgeFinset.card := by
    unfold edgeCount
    refine Eq.trans ?_ (Gᶜ.card_filter_edgeFinset_toFinset_subset S)
    apply congrArg Finset.card
    ext e
    simp
  rw [hG, hGc]
  let H : SimpleGraph (↑(↑S : Set V)) := G.induce (↑S : Set V)
  have hcomplEdges : (Gᶜ.induce (↑S : Set V)).edgeFinset = Hᶜ.edgeFinset := by
    ext e
    simp [H]
  rw [congrArg Finset.card hcomplEdges]
  change H.edgeFinset.card + Hᶜ.edgeFinset.card = S.card.choose 2
  have hsub : H.edgeFinset ⊆ (⊤ : SimpleGraph (↑(↑S : Set V))).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hsdiffEdges : Hᶜ.edgeFinset =
      (⊤ : SimpleGraph (↑(↑S : Set V))).edgeFinset \ H.edgeFinset := by
    ext e
    obtain ⟨x, y⟩ := e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff,
      SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
  have hle' : H.edgeFinset.card ≤ S.card.choose 2 := by
    calc
      H.edgeFinset.card ≤
          (⊤ : SimpleGraph (↑(↑S : Set V))).edgeFinset.card :=
        Finset.card_le_card hsub
      _ = (Fintype.card (↑(↑S : Set V))).choose 2 :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
      _ = S.card.choose 2 := by simp
  rw [hsdiffEdges, Finset.card_sdiff_of_subset hsub,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simpa using Nat.add_sub_of_le hle'

/-- Adding an independent correction set to a disjoint base adds the sum of
the correction vertices' degrees into the base. -/
lemma edgeCount_union_independent (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hB : G.IsIndepSet (B : Set V)) :
    edgeCount G (A ∪ B) =
      edgeCount G A + ∑ v ∈ B, degreeInto G v A := by
  revert hAB hB
  induction B using Finset.induction_on with
  | empty =>
      intro hAB hB
      simp [edgeCount]
  | @insert v B hv ih =>
      intro hAB hB
      have hvA : v ∉ A := by
        intro hvA
        exact (Finset.disjoint_left.mp hAB hvA) (by simp)
      have hAB' : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        exact Finset.disjoint_left.mp hAB hxA (by simp [hxB])
      have hB' : G.IsIndepSet (B : Set V) := by
        intro x hx y hy hxy
        exact hB (by simp [hx]) (by simp [hy]) hxy
      have hvUnion : v ∉ A ∪ B := by simp [hv, hvA]
      have hdeg : degreeInto G v (A ∪ B) = degreeInto G v A :=
        degreeInto_union_eq_left_of_indep G (A := A) (B := B)
          (D := insert v B) (v := v) (Finset.subset_insert v B)
          (Finset.mem_insert_self v B) hB
      calc
        edgeCount G (A ∪ insert v B) = edgeCount G (insert v (A ∪ B)) := by
          congr 2
          ext x
          simp [or_assoc, or_left_comm, or_comm]
        _ = edgeCount G (A ∪ B) + degreeInto G v (A ∪ B) :=
          edgeCount_insert G v (A ∪ B) hvUnion
        _ = (edgeCount G A + ∑ x ∈ B, degreeInto G x A) +
            degreeInto G v A := by rw [ih hAB' hB', hdeg]
        _ = edgeCount G A + ∑ x ∈ insert v B, degreeInto G x A := by
          rw [Finset.sum_insert hv]
          omega

/-- Every sufficiently large induced subgraph has edge density in
`[γ, 1-γ]`.  This is the exact balancedness condition used by AKS. -/
def IsBalanced (G : SimpleGraph V) (γ : ℝ) (t₀ : ℕ) : Prop :=
  ∀ S : Finset V, t₀ ≤ S.card →
    γ * (S.card.choose 2 : ℝ) ≤ (edgeCount G S : ℝ) ∧
      (edgeCount G S : ℝ) ≤ (1 - γ) * (S.card.choose 2 : ℝ)

/-- Lower density for a graph and its complement is exactly the input
needed for the two-sided balancedness interval. -/
lemma isBalanced_of_lower_and_compl_lower (G : SimpleGraph V) (γ : ℝ) (t₀ : ℕ)
    (hG : ∀ S : Finset V, t₀ ≤ S.card →
      γ * (S.card.choose 2 : ℝ) ≤ (edgeCount G S : ℝ))
    (hGc : ∀ S : Finset V, t₀ ≤ S.card →
      γ * (S.card.choose 2 : ℝ) ≤ (edgeCount Gᶜ S : ℝ)) :
    IsBalanced G γ t₀ := by
  intro S hS
  refine ⟨hG S hS, ?_⟩
  have hpartition :
      (edgeCount G S : ℝ) + (edgeCount Gᶜ S : ℝ) =
        (S.card.choose 2 : ℝ) := by
    exact_mod_cast edgeCount_add_edgeCount_compl G S
  nlinarith [hGc S hS]

/-- The unconditional finite Erdős--Szemerédi theorem, translated to
this module's induced-edge-count convention on the whole vertex set. -/
theorem ramseyFree_eventually_whole_density_lower (C : ℝ) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        a * (n : ℝ) ^ 2 ≤ (edgeCount G Finset.univ : ℝ) := by
  obtain ⟨a, ha, N, hN⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower C hC
  refine ⟨a, ha, N, ?_⟩
  intro n hn G hG
  simpa [FiniteES.edgeCount] using hN n hn G hG

/-- A globally `C`-Ramsey graph is `2C`-Ramsey on every induced vertex set
of cardinality at least `√n`.  This is the exact logarithmic threshold
conversion used by the AKS construction: the loss of a factor two is paid
for by passing from `n` to `√n`. -/
lemma ramseyFree_induce_overFin_of_sqrt {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) {C : ℝ}
    (hC : 0 < C) (hn : 1 ≤ n) (hG : RamseyFree C G)
    (hS : Real.sqrt n ≤ (S.card : ℝ)) :
    RamseyFree (2 * C)
      ((G.induce (S : Set (Fin n))).overFin (card_subtype_coe_finset S)) := by
  apply ramseyFree_induce_overFin G S hG
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hlogMono :
      Real.logb 2 (Real.sqrt n) ≤ Real.logb 2 (S.card : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hsqrtPos hS
  have hlogSqrt :
      Real.logb 2 (Real.sqrt n) = (1 / 2 : ℝ) * Real.logb 2 n := by
    rw [Real.logb, Real.logb, Real.log_sqrt hnpos.le]
    ring
  rw [hlogSqrt] at hlogMono
  nlinarith

/-- Ramsey-freeness supplies a uniform two-sided density constant on every
induced set of size at least `√n` (and above the finite density threshold).
This is the unconditional balancedness input to all later AKS stages. -/
theorem ramseyFree_eventually_balanced (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 12 ∧ ∃ N : ℕ,
      ∀ {n : ℕ}, 1 ≤ n → ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
        ∀ {t : ℕ}, N ≤ t → Real.sqrt n ≤ (t : ℝ) →
          IsBalanced G γ t ∧ IsBalanced Gᶜ γ t := by
  obtain ⟨a, ha, N, hDensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower (2 * C) (mul_pos (by norm_num) hC)
  let γ : ℝ := min a (1 / 12)
  have hγ : 0 < γ := by
    dsimp only [γ]
    exact lt_min ha (by norm_num)
  have hγa : γ ≤ a := by exact min_le_left _ _
  have hγsmall : γ ≤ 1 / 12 := by exact min_le_right _ _
  refine ⟨γ, hγ, hγsmall, N, ?_⟩
  intro n hn G hG t hNt hsqrt
  have hLower (H : SimpleGraph (Fin n)) (hHG : RamseyFree C H) :
      ∀ S : Finset (Fin n), t ≤ S.card →
        γ * (S.card.choose 2 : ℝ) ≤ (edgeCount H S : ℝ) := by
    intro S htS
    let HI := (H.induce (S : Set (Fin n))).overFin
      (card_subtype_coe_finset S)
    have hNS : N ≤ S.card := hNt.trans htS
    have hsqrtS : Real.sqrt n ≤ (S.card : ℝ) := by
      exact hsqrt.trans (by exact_mod_cast htS)
    have hRamsey : RamseyFree (2 * C) HI := by
      exact ramseyFree_induce_overFin_of_sqrt H S hC hn hHG hsqrtS
    have hDense := hDensity S.card hNS HI hRamsey
    have hEdge : FiniteES.edgeCount HI = edgeCount H S := by
      calc
        FiniteES.edgeCount HI =
            FiniteES.edgeCount (H.induce (S : Set (Fin n))) :=
          edgeCount_overFin _ (card_subtype_coe_finset S)
        _ = (H.induce (S : Set (Fin n))).edgeFinset.card := rfl
        _ = edgeCount H S := by
          symm
          simpa only [edgeCount] using
            H.card_filter_edgeFinset_toFinset_subset S
    rw [hEdge] at hDense
    have hchooseSq :
        (S.card.choose 2 : ℝ) ≤ (S.card : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow S.card 2
    calc
      γ * (S.card.choose 2 : ℝ) ≤
          a * (S.card.choose 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hγa (by positivity)
      _ ≤ a * (S.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hchooseSq ha.le
      _ ≤ (edgeCount H S : ℝ) := hDense
  have hLowerG := hLower G hG
  have hLowerGc := hLower Gᶜ ((ramseyFree_compl G).2 hG)
  constructor
  · exact isBalanced_of_lower_and_compl_lower G γ t hLowerG hLowerGc
  · apply isBalanced_of_lower_and_compl_lower Gᶜ γ t hLowerGc
    simpa using hLowerG

lemma IsBalanced.lower {G : SimpleGraph V} {γ : ℝ} {t₀ : ℕ}
    (hG : IsBalanced G γ t₀) {S : Finset V} (hS : t₀ ≤ S.card) :
    γ * (S.card.choose 2 : ℝ) ≤ (edgeCount G S : ℝ) :=
  (hG S hS).1

lemma IsBalanced.upper {G : SimpleGraph V} {γ : ℝ} {t₀ : ℕ}
    (hG : IsBalanced G γ t₀) {S : Finset V} (hS : t₀ ≤ S.card) :
    (edgeCount G S : ℝ) ≤ (1 - γ) * (S.card.choose 2 : ℝ) :=
  (hG S hS).2

lemma IsBalanced.mono_threshold {G : SimpleGraph V} {γ : ℝ} {s t : ℕ}
    (hG : IsBalanced G γ s) (hst : s ≤ t) : IsBalanced G γ t := by
  intro S hS
  exact hG S (hst.trans hS)

/-- Degree averaging: a lower edge-density bound produces a vertex whose
degree into the current set is at least the corresponding average degree.
This is the selection step used at every stage of AKS Lemma 3.1. -/
lemma exists_degree_ge_of_lower_density (G : SimpleGraph V) (S : Finset V)
    (γ : ℝ) (hS : S.Nonempty)
    (hdense : γ * (S.card.choose 2 : ℝ) ≤ (edgeCount G S : ℝ)) :
    ∃ v ∈ S, γ * ((S.card : ℝ) - 1) ≤ degreeInto G v S := by
  have hchoose : (S.card.choose 2 : ℝ) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two (K := ℝ) S.card)
  have hhand : (∑ v ∈ S, (degreeInto G v S : ℝ)) =
      2 * (edgeCount G S : ℝ) := by
    exact_mod_cast sum_degreeInto G S
  have hsum :
      ∑ _v ∈ S, γ * ((S.card : ℝ) - 1) ≤
        ∑ v ∈ S, (degreeInto G v S : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hhand]
    rw [hchoose] at hdense
    have htwo : (0 : ℝ) < 2 := by norm_num
    nlinarith
  obtain ⟨v, hv, hdeg⟩ :=
    Finset.exists_le_of_sum_le hS hsum
  exact ⟨v, hv, by simpa using hdeg⟩

/-- The upper-density counterpart of `exists_degree_ge_of_lower_density`. -/
lemma exists_degree_le_of_upper_density (G : SimpleGraph V) (S : Finset V)
    (γ : ℝ) (hS : S.Nonempty)
    (hdense : (edgeCount G S : ℝ) ≤
      (1 - γ) * (S.card.choose 2 : ℝ)) :
    ∃ v ∈ S, degreeInto G v S ≤ (1 - γ) * ((S.card : ℝ) - 1) := by
  have hchoose : (S.card.choose 2 : ℝ) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two (K := ℝ) S.card)
  have hhand : (∑ v ∈ S, (degreeInto G v S : ℝ)) =
      2 * (edgeCount G S : ℝ) := by
    exact_mod_cast sum_degreeInto G S
  have hsum :
      ∑ v ∈ S, (degreeInto G v S : ℝ) ≤
        ∑ _v ∈ S, (1 - γ) * ((S.card : ℝ) - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, hhand]
    rw [hchoose] at hdense
    nlinarith
  obtain ⟨v, hv, hdeg⟩ :=
    Finset.exists_le_of_sum_le hS hsum
  exact ⟨v, hv, by simpa using hdeg⟩

/-- A balanced set large enough compared with its threshold contains an
independent triple.  The proof first chooses a low-degree vertex, then finds
a nonedge among its many nonneighbors using the balanced upper-density
bound a second time. -/
theorem IsBalanced.exists_independent_triple
    {G : SimpleGraph V} {γ : ℝ} {t : ℕ}
    (hbal : IsBalanced G γ t) (hγ : 0 < γ) (ht : 2 ≤ t)
    (J : Finset V) (htJ : t ≤ J.card)
    (hlarge : (t : ℝ) ≤ γ * ((J.card : ℝ) - 1)) :
    ∃ B ⊆ J, B.card = 3 ∧ G.IsIndepSet (B : Set V) := by
  have hJ : J.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  obtain ⟨v, hvJ, hvdeg⟩ :=
    exists_degree_le_of_upper_density G J γ hJ (hbal.upper htJ)
  let N := Gᶜ.neighborFinset v ∩ J
  have hNcard : N.card = degreeInto Gᶜ v J := by
    unfold degreeInto
    apply congrArg Finset.card
    ext x
    simp only [N, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  have hsum := degreeInto_add_degreeInto_compl G v J hvJ
  have htN : t ≤ N.card := by
    rw [hNcard]
    have hsumReal :
        (degreeInto G v J : ℝ) + (degreeInto Gᶜ v J : ℝ) =
          (J.card - 1 : ℕ) := by
      exact_mod_cast hsum
    have hcardCast : ((J.card - 1 : ℕ) : ℝ) = (J.card : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcardCast] at hsumReal
    have htReal : (t : ℝ) ≤ (degreeInto Gᶜ v J : ℝ) := by
      nlinarith
    exact_mod_cast htReal
  have hupper := hbal.upper htN
  have hpartition := edgeCount_add_edgeCount_compl G N
  have hcompPos : 0 < edgeCount Gᶜ N := by
    have hchoosePos : 0 < N.card.choose 2 := by
      exact Nat.choose_pos (by omega)
    have hpartitionReal :
        (edgeCount G N : ℝ) + (edgeCount Gᶜ N : ℝ) =
          (N.card.choose 2 : ℝ) := by
      exact_mod_cast hpartition
    have hchooseReal : (0 : ℝ) < (N.card.choose 2 : ℝ) := by
      exact_mod_cast hchoosePos
    have hcompReal : (0 : ℝ) < (edgeCount Gᶜ N : ℝ) := by
      nlinarith
    exact_mod_cast hcompReal
  rw [edgeCount] at hcompPos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcompPos
  obtain ⟨x, y⟩ := e
  have he' := Finset.mem_filter.mp he
  have hxyComp : Gᶜ.Adj x y := by
    simpa using he'.1
  have hxy' : x ≠ y ∧ ¬G.Adj x y := by simpa using hxyComp
  have hxN : x ∈ N := by
    apply he'.2
    simp [Sym2.toFinset_mk_eq]
  have hyN : y ∈ N := by
    apply he'.2
    simp [Sym2.toFinset_mk_eq]
  have hxComp : Gᶜ.Adj v x := by
    simpa [N] using (Finset.mem_inter.mp hxN).1
  have hyComp : Gᶜ.Adj v y := by
    simpa [N] using (Finset.mem_inter.mp hyN).1
  have hvx' : v ≠ x ∧ ¬G.Adj v x := by simpa using hxComp
  have hvy' : v ≠ y ∧ ¬G.Adj v y := by simpa using hyComp
  let B : Finset V := {v, x, y}
  have hBJ : B ⊆ J := by
    intro z hz
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hvJ
    · exact (Finset.mem_inter.mp hxN).2
    · exact (Finset.mem_inter.mp hyN).2
  have hBcard : B.card = 3 := by
    simp [B, hvx'.1, hvy'.1, hxy'.1]
  have hBindep : G.IsIndepSet (B : Set V) := by
    intro a ha b hb hab
    simp only [B, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl
    all_goals try { exact (hab rfl).elim }
    · exact hvx'.2
    · exact hvy'.2
    · simpa only [G.adj_comm] using hvx'.2
    · exact hxy'.2
    · simpa only [G.adj_comm] using hvy'.2
    · simpa only [G.adj_comm] using hxy'.2
  exact ⟨B, hBJ, hBcard, hBindep⟩

/-- The one-step graph form of AKS Lemma 3.1.  Balancedness supplies both a
large-degree choice and a small-degree choice in every eligible remainder.
The two choices need not be the same vertex; AKS applies the lower statement
inside a preselected low-degree reservoir. -/
lemma balanced_degree_selection {G : SimpleGraph V} {γ : ℝ} {t₀ : ℕ}
    (hG : IsBalanced G γ t₀) {S : Finset V}
    (hcard : t₀ ≤ S.card) (hS : S.Nonempty) :
    (∃ v ∈ S, γ * ((S.card : ℝ) - 1) ≤ degreeInto G v S) ∧
      (∃ v ∈ S, degreeInto G v S ≤
        (1 - γ) * ((S.card : ℝ) - 1)) := by
  exact ⟨exists_degree_ge_of_lower_density G S γ hS (hG.lower hcard),
    exists_degree_le_of_upper_density G S γ hS (hG.upper hcard)⟩

/-- A certificate for repeatedly peeling a vertex whose degree is at least
the current density average.  The remainder in the recursive certificate is
literally the preceding set with the selected vertex erased, so distinctness
and all floor/cardinality bookkeeping are explicit. -/
inductive LowerDegreePeeling (G : SimpleGraph V) (γ : ℝ) :
    Finset V → ℕ → Prop
  | nil (S : Finset V) : LowerDegreePeeling G γ S 0
  | cons {S : Finset V} {k : ℕ} (v : V) (hv : v ∈ S)
      (hdeg : γ * ((S.card : ℝ) - 1) ≤ degreeInto G v S)
      (tail : LowerDegreePeeling G γ (S.erase v) k) :
      LowerDegreePeeling G γ S (k + 1)

/-- Iterated AKS degree selection.  A balanced graph can peel any `k`
vertices while the remainder stays above the balancedness threshold. -/
lemma IsBalanced.exists_lowerDegreePeeling {G : SimpleGraph V}
    {γ : ℝ} {t₀ : ℕ} (hG : IsBalanced G γ t₀) :
    ∀ {S : Finset V} {k : ℕ}, t₀ + k ≤ S.card →
      LowerDegreePeeling G γ S k := by
  intro S k
  induction k generalizing S with
  | zero =>
      intro hcard
      exact LowerDegreePeeling.nil S
  | succ k ih =>
      intro hcard
      have ht : t₀ ≤ S.card := by omega
      have hS : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hzero
        subst S
        simp at hcard
      obtain ⟨v, hv, hdeg⟩ :=
        exists_degree_ge_of_lower_density G S γ hS (hG.lower ht)
      have htail : t₀ + k ≤ (S.erase v).card := by
        rw [Finset.card_erase_of_mem hv]
        omega
      exact LowerDegreePeeling.cons v hv hdeg (ih htail)

namespace LowerDegreePeeling

/-- Extract the selected vertices from a peeling certificate.  Every
selected vertex retains its original density lower bound, up to the number
of selected vertices that were deleted. -/
lemma exists_selected {G : SimpleGraph V} {γ : ℝ} {S : Finset V} {k : ℕ}
    (h : LowerDegreePeeling G γ S k) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ U ⊆ S, U.card = k ∧ ∀ v ∈ U,
      γ * ((S.card : ℝ) - 1) - (k : ℝ) ≤
        (degreeInto G v (S \ U) : ℝ) := by
  induction h with
  | nil S =>
      refine ⟨∅, Finset.empty_subset S, by simp, ?_⟩
      simp
  | @cons S k v hv hdeg tail ih =>
      obtain ⟨U, hUS, hUcard, hUdeg⟩ := ih
      have hvU : v ∉ U := by
        intro hvU
        exact (Finset.mem_erase.mp (hUS hvU)).1 rfl
      let U' := insert v U
      have hU'S : U' ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv
        · exact Finset.erase_subset v S (hUS hx)
      have hU'card : U'.card = k + 1 := by
        simp [U', Finset.card_insert_of_notMem hvU, hUcard]
      refine ⟨U', hU'S, hU'card, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxU
      · have hloss := degreeInto_le_sdiff_add_card G x S U'
        have hlossReal :
            (degreeInto G x S : ℝ) ≤
              (degreeInto G x (S \ U') : ℝ) + U'.card := by
          exact_mod_cast hloss
        rw [hU'card] at hlossReal
        linarith
      · have hxTail := hUdeg x hxU
        have hsets : (S.erase v) \ U = S \ U' := by
          ext z
          simp [U', and_assoc, and_left_comm, and_comm]
        rw [hsets] at hxTail
        have hcardPos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
        have hcardErase : ((S.erase v).card : ℝ) = (S.card : ℝ) - 1 := by
          rw [Finset.card_erase_of_mem hv]
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [hcardErase] at hxTail
        have hkcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
        rw [hkcast]
        nlinarith [hxTail, hγ1, hγ0]

end LowerDegreePeeling

/-- A low-degree orientation together with a peeled set of `u` moderate-degree
vertices.  The graph `H` records whether the low-degree side was found in
`G` or in its complement; retaining that orientation is what later gives
simultaneously large common-neighbor and common-nonneighbor reservoirs. -/
structure OrientedModerateSplit (G : SimpleGraph V) (C : Finset V)
    (u ℓ : ℕ) where
  H : SimpleGraph V
  H_eq : H = G ∨ H = Gᶜ
  U : Finset V
  W : Finset V
  U_sub : U ⊆ C
  W_eq : W = C \ U
  card_U : U.card = u
  low : ∀ v ∈ U, ℓ ≤ degreeInto H v W
  high : ∀ v ∈ U, degreeInto H v W ≤ (C.card - 1) / 2

/-- Construct an oriented moderate-degree split from a specified large
low-degree side.  This isolates the quantitative part of AKS Lemma 3.1 from
the elementary majority argument choosing between `G` and `Gᶜ`. -/
private lemma exists_orientedModerateSplit_of_side
    {G H : SimpleGraph V} {γ : ℝ} {t : ℕ} {C : Finset V} {u ℓ : ℕ}
    (hHG : H = G ∨ H = Gᶜ) (hH : IsBalanced H γ t)
    (hlarge : C.card / 2 ≤ (lowDegreeSide H C).card)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (htu : t + u ≤ C.card / 2)
    (hlow : (ℓ : ℝ) ≤
      γ * (((C.card / 2 : ℕ) : ℝ) - 1) - (u : ℝ)) :
    Nonempty (OrientedModerateSplit G C u ℓ) := by
  obtain ⟨R, hRlow, hRcard⟩ := Finset.exists_subset_card_eq hlarge
  have hRC : R ⊆ C := hRlow.trans (lowDegreeSide_subset H C)
  have hpeel : LowerDegreePeeling H γ R u := by
    apply hH.exists_lowerDegreePeeling
    simpa [hRcard] using htu
  obtain ⟨U, hUR, hUcard, hUdeg⟩ :=
    hpeel.exists_selected hγ0 hγ1
  let W := C \ U
  have hUC : U ⊆ C := hUR.trans hRC
  have hRUW : R \ U ⊆ W := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hRC hx'.1, hx'.2⟩
  refine ⟨{
    H := H
    H_eq := hHG
    U := U
    W := W
    U_sub := hUC
    W_eq := rfl
    card_U := hUcard
    low := ?_
    high := ?_
  }⟩
  · intro v hv
    have hmono := degreeInto_mono H v hRUW
    have hmonoReal :
        (degreeInto H v (R \ U) : ℝ) ≤ (degreeInto H v W : ℝ) := by
      exact_mod_cast hmono
    have hvdeg := hUdeg v hv
    have hreal : (ℓ : ℝ) ≤ (degreeInto H v W : ℝ) := by
      rw [hRcard] at hvdeg
      exact hlow.trans (hvdeg.trans hmonoReal)
    exact_mod_cast hreal
  · intro v hv
    have hvR : v ∈ R := hUR hv
    have hvLow : v ∈ lowDegreeSide H C := hRlow hvR
    have hvBound : degreeInto H v C ≤ (C.card - 1) / 2 :=
      (Finset.mem_filter.mp hvLow).2
    exact (degreeInto_mono H v Finset.sdiff_subset).trans hvBound

/-- AKS Lemma 3.1 in oriented finite form.  At least half the vertices lie
on a low-degree side of either `G` or `Gᶜ`; balanced peeling then selects
`u` vertices whose degrees into the untouched reservoir have the displayed
moderate lower and upper bounds. -/
theorem IsBalanced.exists_orientedModerateSplit
    {G : SimpleGraph V} {γ : ℝ} {t : ℕ} {C : Finset V} {u ℓ : ℕ}
    (hG : IsBalanced G γ t) (hGc : IsBalanced Gᶜ γ t)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (htu : t + u ≤ C.card / 2)
    (hlow : (ℓ : ℝ) ≤
      γ * (((C.card / 2 : ℕ) : ℝ) - 1) - (u : ℝ)) :
    Nonempty (OrientedModerateSplit G C u ℓ) := by
  rcases exists_large_lowDegreeSide G C with hlarge | hlarge
  · exact exists_orientedModerateSplit_of_side (Or.inl rfl) hG hlarge
      hγ0 hγ1 htu hlow
  · exact exists_orientedModerateSplit_of_side (Or.inr rfl) hGc hlarge
      hγ0 hγ1 htu hlow

/-- A reservoir splits into the neighbors and nonneighbors of a vertex. -/
lemma card_sdiff_neighborFinset_add_degreeInto (G : SimpleGraph V) (v : V)
    (W : Finset V) :
    (W \ G.neighborFinset v).card + degreeInto G v W = W.card := by
  have hsplit := Finset.card_sdiff_add_card_inter W (G.neighborFinset v)
  simpa [degreeInto, Finset.inter_comm] using hsplit

/-- The output of one positive-index AKS block step.  Besides the diagonal
complete pair and its dense dyadic block, the structure records a large
reservoir anticomplete to the pair, ready for the next step. -/
structure PairBlockStep (G : SimpleGraph V) (ε : ℝ) (i d : ℕ)
    (U W : Finset V) where
  A : Finset V
  B : Finset V
  Cnext : Finset V
  A_sub : A ⊆ W
  B_sub : B ⊆ U
  Cnext_sub : Cnext ⊆ W
  card_A : A.card = 2 ^ i
  card_B : B.card = 2
  next_large : d < Cnext.card
  complete : CompleteTo G B A
  anti_next : AnticompleteTo G B Cnext
  disjoint_AB : Disjoint A B
  disjoint_ACnext : Disjoint A Cnext
  disjoint_BCnext : Disjoint B Cnext
  dense_A : 6 * ε * ((2 ^ i).choose 2 : ℝ) ≤ (edgeCount G A : ℝ)

/-- One exact pair-block extension of the AKS construction.  The numerical
hypothesis is precisely the pair-family counting inequality.  The orientation
stored by `split` determines which common part supplies `A` and which supplies
the next anticomplete reservoir. -/
theorem OrientedModerateSplit.exists_pairBlockStep
    {G : SimpleGraph V} {ε : ℝ} {t i d q : ℕ} {C : Finset V}
    {u ℓ : ℕ} (split : OrientedModerateSplit G C u ℓ)
    (hbal : IsBalanced G (6 * ε) t) (hi : 1 ≤ i)
    (hq : q + (C.card - 1) / 2 ≤ split.W.card)
    (hsize : max t (2 ^ i) ≤ d + 1)
    (hnumeric :
      split.W.card ^ 4 + split.U.card.choose 2 *
          (d ^ 2 * split.W.card ^ 2) <
        split.U.card * (ℓ ^ 2 * q ^ 2)) :
    Nonempty (PairBlockStep G ε i d split.U split.W) := by
  have hnonneighbor : ∀ v ∈ split.U,
      q ≤ (split.W \ split.H.neighborFinset v).card := by
    intro v hv
    have hpartition :=
      card_sdiff_neighborFinset_add_degreeInto split.H v split.W
    have hhigh := split.high v hv
    omega
  obtain ⟨B, hBU, hBcard, hneighbors, hnonneighbors⟩ :=
    exists_pair_with_large_common_parts split.H split.W split.U d ℓ q
      split.low hnonneighbor hnumeric
  let N := commonNeighbors split.H split.W B
  let O := commonNonneighbors split.H split.W B
  have hNW : N ⊆ split.W := by
    intro x hx
    exact (mem_commonNeighbors.mp hx).1
  have hOW : O ⊆ split.W := by
    intro x hx
    exact (mem_commonNonneighbors.mp hx).1
  have hNO : Disjoint N O := by
    rw [Finset.disjoint_left]
    intro x hxN hxO
    have hn := (mem_commonNeighbors.mp hxN).2
    have ho := (mem_commonNonneighbors.mp hxO).2
    obtain ⟨b, hb⟩ : B.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hB
      subst B
      simp at hBcard
    exact (ho b hb) (hn b hb)
  have hWU : Disjoint split.W split.U := by
    rw [Finset.disjoint_left]
    intro x hxW hxU
    rw [split.W_eq] at hxW
    exact (Finset.mem_sdiff.mp hxW).2 hxU
  have hpow : 2 ≤ 2 ^ i := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hi
    simpa using this
  have denseChoice : ∀ {R : Finset V}, d < R.card →
      ∃ A ⊆ R, A.card = 2 ^ i ∧
        6 * ε * ((2 ^ i).choose 2 : ℝ) ≤ (edgeCount G A : ℝ) := by
    intro R hdR
    have hcard : d + 1 ≤ R.card := by omega
    have htR : t ≤ R.card :=
      (le_max_left t (2 ^ i)).trans (hsize.trans hcard)
    have hkR : 2 ^ i ≤ R.card :=
      (le_max_right t (2 ^ i)).trans (hsize.trans hcard)
    exact exists_dense_subset G R (6 * ε) hpow hkR (hbal.lower htR)
  rcases split.H_eq with hHG | hHGc
  · obtain ⟨A, hAN, hAcard, hAdense⟩ := denseChoice (by simpa [N] using hneighbors)
    refine ⟨{
      A := A
      B := B
      Cnext := O
      A_sub := hAN.trans hNW
      B_sub := hBU
      Cnext_sub := hOW
      card_A := hAcard
      card_B := hBcard
      next_large := by simpa [O] using hnonneighbors
      complete := ?_
      anti_next := ?_
      disjoint_AB := hWU.mono (hAN.trans hNW) hBU
      disjoint_ACnext := hNO.mono_left hAN
      disjoint_BCnext := hWU.symm.mono hBU hOW
      dense_A := hAdense
    }⟩
    · intro b hb a ha
      have hadj := (mem_commonNeighbors.mp (hAN ha)).2 b hb
      simpa [hHG] using hadj
    · intro b hb x hx
      have hnadj := (mem_commonNonneighbors.mp hx).2 b hb
      simpa [hHG] using hnadj
  · obtain ⟨A, hAO, hAcard, hAdense⟩ :=
      denseChoice (by simpa [O] using hnonneighbors)
    refine ⟨{
      A := A
      B := B
      Cnext := N
      A_sub := hAO.trans hOW
      B_sub := hBU
      Cnext_sub := hNW
      card_A := hAcard
      card_B := hBcard
      next_large := by simpa [N] using hneighbors
      complete := ?_
      anti_next := ?_
      disjoint_AB := hWU.mono (hAO.trans hOW) hBU
      disjoint_ACnext := hNO.mono_right hAO |>.symm
      disjoint_BCnext := hWU.symm.mono hBU hNW
      dense_A := hAdense
    }⟩
    · intro b hb a ha
      have hnotComp := (mem_commonNonneighbors.mp (hAO ha)).2 b hb
      have hba : b ≠ a := by
        intro hba
        subst a
        exact Finset.disjoint_left.mp hWU (hOW (hAO ha)) (hBU hb)
      by_contra hnot
      apply hnotComp
      rw [hHGc]
      simp [hba, hnot]
    · intro b hb x hx
      have hcomp := (mem_commonNeighbors.mp hx).2 b hb
      rw [hHGc] at hcomp
      have hcomp' : b ≠ x ∧ ¬G.Adj b x := by simpa using hcomp
      exact hcomp'.2

/-- The zero-index block produced by the initial triple-family step.  Its
residual `Cnext` is the source reservoir for all positive pair blocks. -/
structure InitialTripleBlock (G : SimpleGraph V)
    (A0 B0 Cnext : Finset V) : Prop where
  card_A : A0.card = 1
  card_B : B0.card = 3
  indep_B : G.IsIndepSet (B0 : Set V)
  complete : CompleteTo G B0 A0
  anti_next : AnticompleteTo G B0 Cnext
  disjoint_AB : Disjoint A0 B0
  disjoint_A_next : Disjoint A0 Cnext
  disjoint_B_next : Disjoint B0 Cnext

/-- The completed zero-index AKS step together with a quantitative lower
bound on the residual reservoir. -/
structure InitialTripleExtension (G : SimpleGraph V) (d : ℕ)
    (C : Finset V) where
  A0 : Finset V
  B0 : Finset V
  Cnext : Finset V
  initial : InitialTripleBlock G A0 B0 Cnext
  next_large : d < Cnext.card
  next_subset : Cnext ⊆ C

/-- Construct the initial AKS triple block from an oriented moderate split
and the exact triple-family counting inequality. -/
theorem OrientedModerateSplit.exists_initialTripleExtension
    {G : SimpleGraph V} {γ : ℝ} {t b d q : ℕ} {C : Finset V}
    {u ℓ : ℕ} (split : OrientedModerateSplit G C u ℓ)
    (hbal : IsBalanced G γ t) (hγ : 0 < γ) (ht : 2 ≤ t)
    (htb : t ≤ b) (hlarge : (t : ℝ) ≤ γ * ((b : ℝ) - 1))
    (hb : 0 < b)
    (hq : q + (C.card - 1) / 2 ≤ split.W.card)
    (hnumeric :
      (b - 1) * split.W.card ^ 8 + split.U.card.choose 3 *
          (d ^ 4 * split.W.card ^ 4) <
        split.U.card * (ℓ ^ 4 * q ^ 4)) :
    Nonempty (InitialTripleExtension G d C) := by
  have hnonneighbor : ∀ v ∈ split.U,
      q ≤ (split.W \ split.H.neighborFinset v).card := by
    intro v hv
    have hpartition :=
      card_sdiff_neighborFinset_add_degreeInto split.H v split.W
    have hhigh := split.high v hv
    omega
  obtain ⟨J, hJU, hJcard, hgood⟩ :=
    exists_family_with_good_triples split.H split.W split.U b d ℓ q hb
      split.low hnonneighbor hnumeric
  obtain ⟨B0, hB0J, hB0card, hB0indep⟩ :=
    hbal.exists_independent_triple hγ ht J (by simpa [hJcard] using htb)
      (by simpa [hJcard] using hlarge)
  have hB0U : B0 ⊆ split.U := hB0J.trans hJU
  have hB0power : B0 ∈ J.powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hB0J, hB0card⟩
  have hparts := hgood B0 hB0power
  let N := commonNeighbors split.H split.W B0
  let O := commonNonneighbors split.H split.W B0
  have hNW : N ⊆ split.W := by
    intro x hx
    exact (mem_commonNeighbors.mp hx).1
  have hOW : O ⊆ split.W := by
    intro x hx
    exact (mem_commonNonneighbors.mp hx).1
  have hNO : Disjoint N O := by
    rw [Finset.disjoint_left]
    intro x hxN hxO
    have hn := (mem_commonNeighbors.mp hxN).2
    have ho := (mem_commonNonneighbors.mp hxO).2
    obtain ⟨v, hv⟩ : B0.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hzero
      subst B0
      simp at hB0card
    exact (ho v hv) (hn v hv)
  have hWU : Disjoint split.W split.U := by
    rw [Finset.disjoint_left]
    intro x hxW hxU
    rw [split.W_eq] at hxW
    exact (Finset.mem_sdiff.mp hxW).2 hxU
  have hWC : split.W ⊆ C := by
    rw [split.W_eq]
    exact Finset.sdiff_subset
  rcases split.H_eq with hHG | hHGc
  · have hNnonempty : N.Nonempty := Finset.card_pos.mp (by
      have : d < N.card := by simpa [N] using hparts.1
      omega)
    obtain ⟨a, haN⟩ := hNnonempty
    let A0 : Finset V := {a}
    have hA0N : A0 ⊆ N := by simpa [A0] using haN
    refine ⟨{
      A0 := A0
      B0 := B0
      Cnext := O
      initial := {
        card_A := by simp [A0]
        card_B := hB0card
        indep_B := hB0indep
        complete := ?_
        anti_next := ?_
        disjoint_AB := hWU.mono (hA0N.trans hNW) hB0U
        disjoint_A_next := hNO.mono_left hA0N
        disjoint_B_next := hWU.symm.mono hB0U hOW
      }
      next_large := by simpa [O] using hparts.2
      next_subset := hOW.trans hWC
    }⟩
    · intro v hv x hx
      have hadj := (mem_commonNeighbors.mp (hA0N hx)).2 v hv
      simpa [hHG] using hadj
    · intro v hv x hx
      have hnadj := (mem_commonNonneighbors.mp hx).2 v hv
      simpa [hHG] using hnadj
  · have hOnonempty : O.Nonempty := Finset.card_pos.mp (by
      have : d < O.card := by simpa [O] using hparts.2
      omega)
    obtain ⟨a, haO⟩ := hOnonempty
    let A0 : Finset V := {a}
    have hA0O : A0 ⊆ O := by simpa [A0] using haO
    refine ⟨{
      A0 := A0
      B0 := B0
      Cnext := N
      initial := {
        card_A := by simp [A0]
        card_B := hB0card
        indep_B := hB0indep
        complete := ?_
        anti_next := ?_
        disjoint_AB := hWU.mono (hA0O.trans hOW) hB0U
        disjoint_A_next := hNO.mono_right hA0O |>.symm
        disjoint_B_next := hWU.symm.mono hB0U hNW
      }
      next_large := by simpa [N] using hparts.1
      next_subset := hNW.trans hWC
    }⟩
    · intro v hv x hx
      have hnotComp := (mem_commonNonneighbors.mp (hA0O hx)).2 v hv
      have hvx : v ≠ x := by
        intro hvx
        subst x
        exact Finset.disjoint_left.mp hWU (hOW (hA0O hx)) (hB0U hv)
      by_contra hnot
      apply hnotComp
      rw [hHGc]
      simp [hvx, hnot]
    · intro v hv x hx
      have hcomp := (mem_commonNeighbors.mp hx).2 v hv
      rw [hHGc] at hcomp
      have hcomp' : v ≠ x ∧ ¬G.Adj v x := by simpa using hcomp
      exact hcomp'.2

structure PairExtension (G : SimpleGraph V) (ε : ℝ) (i : ℕ)
    (C : Finset V) where
  u : ℕ
  ℓ : ℕ
  d : ℕ
  q : ℕ
  split : OrientedModerateSplit G C u ℓ
  block : PairBlockStep G ε i d split.U split.W

namespace PairExtension

lemma A_subset_source {G : SimpleGraph V} {ε : ℝ} {i : ℕ}
    {C : Finset V} (step : PairExtension G ε i C) :
    step.block.A ⊆ C := by
  exact step.block.A_sub.trans (by
    rw [step.split.W_eq]
    exact Finset.sdiff_subset)

lemma B_subset_source {G : SimpleGraph V} {ε : ℝ} {i : ℕ}
    {C : Finset V} (step : PairExtension G ε i C) :
    step.block.B ⊆ C :=
  step.block.B_sub.trans step.split.U_sub

lemma next_subset_source {G : SimpleGraph V} {ε : ℝ} {i : ℕ}
    {C : Finset V} (step : PairExtension G ε i C) :
    step.block.Cnext ⊆ C := by
  exact step.block.Cnext_sub.trans (by
    rw [step.split.W_eq]
    exact Finset.sdiff_subset)

lemma disjoint_A_next {G : SimpleGraph V} {ε : ℝ} {i : ℕ}
    {C : Finset V} (step : PairExtension G ε i C) :
    Disjoint step.block.A step.block.Cnext :=
  step.block.disjoint_ACnext

lemma disjoint_B_next {G : SimpleGraph V} {ε : ℝ} {i : ℕ}
    {C : Finset V} (step : PairExtension G ε i C) :
    Disjoint step.block.B step.block.Cnext :=
  step.block.disjoint_BCnext

end PairExtension

/-- Package the checked one-step construction as a recursive extension. -/
theorem OrientedModerateSplit.exists_pairExtension
    {G : SimpleGraph V} {ε : ℝ} {t i d q : ℕ} {C : Finset V}
    {u ℓ : ℕ} (split : OrientedModerateSplit G C u ℓ)
    (hbal : IsBalanced G (6 * ε) t) (hi : 1 ≤ i)
    (hq : q + (C.card - 1) / 2 ≤ split.W.card)
    (hsize : max t (2 ^ i) ≤ d + 1)
    (hnumeric :
      split.W.card ^ 4 + split.U.card.choose 2 *
          (d ^ 2 * split.W.card ^ 2) <
        split.U.card * (ℓ ^ 2 * q ^ 2)) :
    Nonempty (PairExtension G ε i C) := by
  obtain ⟨block⟩ := split.exists_pairBlockStep hbal hi hq hsize hnumeric
  exact ⟨{
    u := u
    ℓ := ℓ
    d := d
    q := q
    split := split
    block := block
  }⟩

/-- A pair extension that also certifies the minimum size needed by the next
stage of a recursive construction. -/
structure SizedPairExtension (G : SimpleGraph V) (ε : ℝ) (i nextMin : ℕ)
    (C : Finset V) where
  extension : PairExtension G ε i C
  next_card : nextMin ≤ extension.block.Cnext.card

/-- Balancedness and the displayed exact finite inequalities produce one
sized recursive pair extension. -/
theorem exists_sizedPairExtension_of_balanced
    {G : SimpleGraph V} {ε : ℝ} {t i u ℓ d q nextMin : ℕ}
    {C : Finset V}
    (hbal : IsBalanced G (6 * ε) t)
    (hbalc : IsBalanced Gᶜ (6 * ε) t)
    (hγ0 : 0 ≤ 6 * ε) (hγ1 : 6 * ε ≤ 1)
    (htu : t + u ≤ C.card / 2)
    (hlow : (ℓ : ℝ) ≤
      (6 * ε) * (((C.card / 2 : ℕ) : ℝ) - 1) - (u : ℝ))
    (hi : 1 ≤ i)
    (hq : ∀ split : OrientedModerateSplit G C u ℓ,
      q + (C.card - 1) / 2 ≤ split.W.card)
    (hsize : max t (2 ^ i) ≤ d + 1)
    (hnumeric : ∀ split : OrientedModerateSplit G C u ℓ,
      split.W.card ^ 4 + split.U.card.choose 2 *
          (d ^ 2 * split.W.card ^ 2) <
        split.U.card * (ℓ ^ 2 * q ^ 2))
    (hnext : nextMin ≤ d + 1) :
    Nonempty (SizedPairExtension G ε i nextMin C) := by
  obtain ⟨split⟩ := hbal.exists_orientedModerateSplit hbalc hγ0 hγ1 htu hlow
  obtain ⟨block⟩ := split.exists_pairBlockStep hbal hi (hq split)
    hsize (hnumeric split)
  let extension : PairExtension G ε i C := {
    u := u
    ℓ := ℓ
    d := d
    q := q
    split := split
    block := block
  }
  refine ⟨{ extension := extension, next_card := ?_ }⟩
  have hlarge := block.next_large
  change nextMin ≤ block.Cnext.card
  omega

/-- A recursive chain of positive AKS blocks.  The tail is constructed inside
the preceding block's anticomplete reservoir, so cross-block disjointness and
anticompleteness follow by monotonicity rather than being extra assumptions. -/
inductive PairBlockChain (G : SimpleGraph V) (ε : ℝ) :
    ℕ → ℕ → Finset V → Type u
  | nil (i : ℕ) (C : Finset V) : PairBlockChain G ε i 0 C
  | cons {i k : ℕ} {C : Finset V}
      (head : PairExtension G ε i C)
      (tail : PairBlockChain G ε (i + 1) k head.block.Cnext) :
      PairBlockChain G ε i (k + 1) C

namespace PairBlockChain

/-- Any finite indexed supply of source-reservoir extensions assembles into
a chain.  At the recursive call the source is definitionally the preceding
extension's `Cnext`, which is the key invariant needed by the block-system
conversion. -/
theorem exists_of_supply {G : SimpleGraph V} {ε : ℝ} :
    ∀ {i L : ℕ} {C : Finset V},
      (∀ j, j < L → ∀ R : Finset V,
        Nonempty (PairExtension G ε (i + j) R)) →
      Nonempty (PairBlockChain G ε i L C) := by
  intro i L
  induction L generalizing i with
  | zero =>
      intro C hsupply
      exact ⟨PairBlockChain.nil i C⟩
  | succ k ih =>
      intro C hsupply
      obtain ⟨head⟩ := hsupply 0 (by omega) C
      have htailSupply : ∀ j, j < k → ∀ R : Finset V,
          Nonempty (PairExtension G ε ((i + 1) + j) R) := by
        intro j hj R
        have h := hsupply (j + 1) (by omega) R
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      obtain ⟨tail⟩ := ih (C := head.block.Cnext) htailSupply
      exact ⟨PairBlockChain.cons head tail⟩

/-- Assemble a chain from a size-indexed supply.  Unlike `exists_of_supply`,
this version is directly usable with graph estimates: the certificate at one
stage proves the size hypothesis required at the next stage. -/
theorem exists_of_sized_supply {G : SimpleGraph V} {ε : ℝ} (minSize : ℕ → ℕ) :
    ∀ {i L : ℕ} {C : Finset V}, minSize i ≤ C.card →
      (∀ j, i ≤ j → j < i + L → ∀ R : Finset V,
        minSize j ≤ R.card →
          Nonempty (SizedPairExtension G ε j (minSize (j + 1)) R)) →
      Nonempty (PairBlockChain G ε i L C) := by
  intro i L
  induction L generalizing i with
  | zero =>
      intro C hC hsupply
      exact ⟨PairBlockChain.nil i C⟩
  | succ k ih =>
      intro C hC hsupply
      obtain ⟨head⟩ := hsupply i le_rfl (by omega) C hC
      have htailSupply : ∀ j, i + 1 ≤ j → j < (i + 1) + k →
          ∀ R : Finset V, minSize j ≤ R.card →
            Nonempty (SizedPairExtension G ε j (minSize (j + 1)) R) := by
        intro j hij hj R hR
        exact hsupply j (by omega) (by omega) R hR
      obtain ⟨tail⟩ := ih (i := i + 1) (C := head.extension.block.Cnext)
        head.next_card htailSupply
      exact ⟨PairBlockChain.cons head.extension tail⟩

/-- The `j`-th dense block in a pair chain. -/
def blockA {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V} :
    PairBlockChain G ε i k C → Fin k → Finset V
  | .nil _ _, j => Fin.elim0 j
  | .cons head tail, j =>
      Fin.cases head.block.A (fun r ↦ blockA tail r) j

/-- The `j`-th correcting pair in a pair chain. -/
def blockB {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V} :
    PairBlockChain G ε i k C → Fin k → Finset V
  | .nil _ _, j => Fin.elim0 j
  | .cons head tail, j =>
      Fin.cases head.block.B (fun r ↦ blockB tail r) j

@[simp] lemma blockA_zero {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (head : PairExtension G ε i C)
    (tail : PairBlockChain G ε (i + 1) k head.block.Cnext) :
    blockA (.cons head tail) 0 = head.block.A := rfl

@[simp] lemma blockA_succ {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (head : PairExtension G ε i C)
    (tail : PairBlockChain G ε (i + 1) k head.block.Cnext)
    (j : Fin k) :
    blockA (.cons head tail) j.succ = blockA tail j := rfl

@[simp] lemma blockB_zero {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (head : PairExtension G ε i C)
    (tail : PairBlockChain G ε (i + 1) k head.block.Cnext) :
    blockB (.cons head tail) 0 = head.block.B := rfl

@[simp] lemma blockB_succ {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (head : PairExtension G ε i C)
    (tail : PairBlockChain G ε (i + 1) k head.block.Cnext)
    (j : Fin k) :
    blockB (.cons head tail) j.succ = blockB tail j := rfl

lemma card_blockA {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (chain : PairBlockChain G ε i k C) (j : Fin k) :
    (chain.blockA j).card = 2 ^ (i + j) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      refine Fin.cases ?_ (fun r ↦ ?_) j
      · simpa using head.block.card_A
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih r

lemma card_blockB {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (chain : PairBlockChain G ε i k C) (j : Fin k) :
    (chain.blockB j).card = 2 := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      refine Fin.cases ?_ (fun r ↦ ?_) j
      · simpa using head.block.card_B
      · simpa using ih r

lemma blockA_subset_source {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (chain : PairBlockChain G ε i k C) (j : Fin k) :
    chain.blockA j ⊆ C := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      refine Fin.cases ?_ (fun r ↦ ?_) j
      · simpa using head.A_subset_source
      · simpa using (ih r).trans head.next_subset_source

lemma blockB_subset_source {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (chain : PairBlockChain G ε i k C) (j : Fin k) :
    chain.blockB j ⊆ C := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      refine Fin.cases ?_ (fun r ↦ ?_) j
      · simpa using head.B_subset_source
      · simpa using (ih r).trans head.next_subset_source

lemma complete_block {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (chain : PairBlockChain G ε i k C) (j : Fin k) :
    CompleteTo G (chain.blockB j) (chain.blockA j) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      refine Fin.cases ?_ (fun r ↦ ?_) j
      · simpa using head.block.complete
      · simpa using ih r

lemma dense_blockA {G : SimpleGraph V} {ε : ℝ} {i k : ℕ}
    {C : Finset V} (chain : PairBlockChain G ε i k C) (j : Fin k) :
    6 * ε * ((2 ^ (i + j)).choose 2 : ℝ) ≤
      (edgeCount G (chain.blockA j) : ℝ) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      refine Fin.cases ?_ (fun r ↦ ?_) j
      · simpa using head.block.dense_A
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih r

/-- An earlier correcting pair is anticomplete to every later dense block. -/
lemma anticomplete_blockB_blockA_of_lt
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) {j ℓ : Fin k} (hjℓ : j < ℓ) :
    AnticompleteTo G (chain.blockB j) (chain.blockA ℓ) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      cases j using Fin.cases with
      | zero =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockB_zero, blockA_succ] using
                (show AnticompleteTo G head.block.B (tail.blockA s) from by
                  intro b hb a ha
                  exact head.block.anti_next hb
                    (tail.blockA_subset_source s ha))
      | succ r =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockB_succ, blockA_succ] using
                ih (by simpa using hjℓ : r < s)

/-- An earlier correcting pair is anticomplete to every later correcting
pair. -/
lemma anticomplete_blockB_blockB_of_lt
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) {j ℓ : Fin k} (hjℓ : j < ℓ) :
    AnticompleteTo G (chain.blockB j) (chain.blockB ℓ) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      cases j using Fin.cases with
      | zero =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockB_zero, blockB_succ] using
                (show AnticompleteTo G head.block.B (tail.blockB s) from by
                  intro b hb x hx
                  exact head.block.anti_next hb
                    (tail.blockB_subset_source s hx))
      | succ r =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockB_succ] using
                ih (by simpa using hjℓ : r < s)

/-- Dense blocks at distinct chain positions are disjoint. -/
lemma disjoint_blockA_of_lt
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) {j ℓ : Fin k} (hjℓ : j < ℓ) :
    Disjoint (chain.blockA j) (chain.blockA ℓ) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      cases j using Fin.cases with
      | zero =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockA_zero, blockA_succ] using
                head.disjoint_A_next.mono_right
                  (tail.blockA_subset_source s)
      | succ r =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockA_succ] using
                ih (by simpa using hjℓ : r < s)

/-- Correcting pairs at distinct chain positions are disjoint. -/
lemma disjoint_blockB_of_lt
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) {j ℓ : Fin k} (hjℓ : j < ℓ) :
    Disjoint (chain.blockB j) (chain.blockB ℓ) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      cases j using Fin.cases with
      | zero =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockB_zero, blockB_succ] using
                head.disjoint_B_next.mono_right
                  (tail.blockB_subset_source s)
      | succ r =>
          cases ℓ using Fin.cases with
          | zero => simp at hjℓ
          | succ s =>
              simpa only [blockB_succ] using
                ih (by simpa using hjℓ : r < s)

lemma disjoint_blockA_of_ne
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) {j ℓ : Fin k} (hjℓ : j ≠ ℓ) :
    Disjoint (chain.blockA j) (chain.blockA ℓ) := by
  rcases lt_or_gt_of_ne hjℓ with hjℓ | hℓj
  · exact chain.disjoint_blockA_of_lt hjℓ
  · exact (chain.disjoint_blockA_of_lt hℓj).symm

lemma disjoint_blockB_of_ne
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) {j ℓ : Fin k} (hjℓ : j ≠ ℓ) :
    Disjoint (chain.blockB j) (chain.blockB ℓ) := by
  rcases lt_or_gt_of_ne hjℓ with hjℓ | hℓj
  · exact chain.disjoint_blockB_of_lt hjℓ
  · exact (chain.disjoint_blockB_of_lt hℓj).symm

/-- Every dense block is disjoint from every correcting pair, including at
the same chain position. -/
lemma disjoint_blockA_blockB
    {G : SimpleGraph V} {ε : ℝ} {i k : ℕ} {C : Finset V}
    (chain : PairBlockChain G ε i k C) (j ℓ : Fin k) :
    Disjoint (chain.blockA j) (chain.blockB ℓ) := by
  induction chain with
  | nil => exact Fin.elim0 j
  | @cons i k C head tail ih =>
      cases j using Fin.cases with
      | zero =>
          cases ℓ using Fin.cases with
          | zero =>
              simpa only [blockA_zero, blockB_zero] using
                head.block.disjoint_AB
          | succ s =>
              simpa only [blockA_zero, blockB_succ] using
                head.disjoint_A_next.mono_right
                  (tail.blockB_subset_source s)
      | succ r =>
          cases ℓ using Fin.cases with
          | zero =>
              simpa only [blockA_succ, blockB_zero] using
                (head.disjoint_B_next.mono_right
                  (tail.blockA_subset_source r)).symm
          | succ s =>
              simpa only [blockA_succ, blockB_succ] using ih r s

end PairBlockChain

section DiscreteInterpolation

/-- If an integer process starts below `y`, ends above `y`, and has
increments at most `i` at step `i`, then some value lies below `y`
with deficit strictly less than its next step index.  This is the precise
"longest blockwise prefix" argument in the AKS construction. -/
lemma exists_prefix_with_small_deficit {N y : ℕ} (f : ℕ → ℕ)
    (hzero : f 0 = 0)
    (hstep : ∀ i < N, f (i + 1) ≤ f i + i)
    (hy : y ≤ f N) :
    ∃ i ≤ N, f i ≤ y ∧ (f i = y ∨ y - f i < i) := by
  let good : Finset ℕ := (Finset.range (N + 1)).filter fun i ↦ f i ≤ y
  have hgood : good.Nonempty := by
    refine ⟨0, ?_⟩
    simp [good, hzero]
  let i := good.max' hgood
  have hi_good : i ∈ good := Finset.max'_mem good hgood
  have hiN : i ≤ N := by
    have : i < N + 1 := (Finset.mem_filter.mp hi_good).1 |> Finset.mem_range.mp
    omega
  have hfiy : f i ≤ y := (Finset.mem_filter.mp hi_good).2
  refine ⟨i, hiN, hfiy, ?_⟩
  by_cases hi : i = N
  · left
    exact le_antisymm hfiy (by simpa [hi] using hy)
  · right
    have hi_lt : i < N := lt_of_le_of_ne hiN hi
    have hnext_not : ¬f (i + 1) ≤ y := by
      intro hnext
      have hmem : i + 1 ∈ good := by
        simp [good, hnext, hi_lt]
      have hle := Finset.le_max' good (i + 1) hmem
      omega
    have hy_next : y < f (i + 1) := Nat.lt_of_not_ge hnext_not
    have hgap := hstep i hi_lt
    omega

/-- Shifted longest-prefix interpolation.  Here `q` is the number of
vertices already present before an ordered block is exposed, so the
`i`-th vertex can create at most `q+i` new edges. -/
lemma exists_prefix_with_small_deficit_from {N y q : ℕ} (f : ℕ → ℕ)
    (hzero : f 0 ≤ y)
    (hstep : ∀ i < N, f (i + 1) ≤ f i + q + i)
    (hy : y ≤ f N) :
    ∃ i ≤ N, f i ≤ y ∧ (f i = y ∨ y - f i < q + i) := by
  let good : Finset ℕ := (Finset.range (N + 1)).filter fun i ↦ f i ≤ y
  have hgood : good.Nonempty := by
    refine ⟨0, ?_⟩
    simp [good, hzero]
  let i := good.max' hgood
  have hi_good : i ∈ good := Finset.max'_mem good hgood
  have hiN : i ≤ N := by
    have hi : i < N + 1 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hi_good).1
    omega
  have hfiy : f i ≤ y := (Finset.mem_filter.mp hi_good).2
  refine ⟨i, hiN, hfiy, ?_⟩
  by_cases hi : i = N
  · left
    exact le_antisymm hfiy (by simpa [hi] using hy)
  · right
    have hi_lt : i < N := lt_of_le_of_ne hiN hi
    have hnext_not : ¬f (i + 1) ≤ y := by
      intro hnext
      have hmem : i + 1 ∈ good := by
        simp [good, hnext, hi_lt]
      have hle := Finset.le_max' good (i + 1) hmem
      omega
    have hy_next : y < f (i + 1) := Nat.lt_of_not_ge hnext_not
    have hgap := hstep i hi_lt
    omega

/-- Order-free form of the longest-prefix argument.  Among the subsets of
`A` whose union with `Q` stays below the target, choose one of maximum
cardinality.  If it is not already exact, inserting any missing vertex
overshoots, so the remaining deficit is smaller than `|Q|+|A|`. -/
lemma exists_subset_with_small_deficit (G : SimpleGraph V)
    (Q A : Finset V) (hQA : Disjoint Q A) (y : ℕ)
    (hQ : edgeCount G Q ≤ y) (hy : y ≤ edgeCount G (Q ∪ A)) :
    ∃ P ⊆ A, edgeCount G (Q ∪ P) ≤ y ∧
      (edgeCount G (Q ∪ P) = y ∨
        y - edgeCount G (Q ∪ P) < Q.card + A.card) := by
  let good : Finset (Finset V) :=
    A.powerset.filter fun P ↦ edgeCount G (Q ∪ P) ≤ y
  have hgood : good.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [good, hQ]
  obtain ⟨P, hPgood, hmax⟩ := good.exists_max_image Finset.card hgood
  have hPA : P ⊆ A := (Finset.mem_powerset.mp (Finset.mem_filter.mp hPgood).1)
  have hPy : edgeCount G (Q ∪ P) ≤ y := (Finset.mem_filter.mp hPgood).2
  refine ⟨P, hPA, hPy, ?_⟩
  by_cases heq : edgeCount G (Q ∪ P) = y
  · exact Or.inl heq
  · right
    have hlt : edgeCount G (Q ∪ P) < y := lt_of_le_of_ne hPy heq
    have hPne : P ≠ A := by
      intro hEq
      subst P
      omega
    have hnotAP : ¬A ⊆ P := by
      intro hAP
      exact hPne (Finset.Subset.antisymm hPA hAP)
    obtain ⟨v, hv⟩ := Finset.sdiff_nonempty.mpr hnotAP
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have hvP : v ∉ P := (Finset.mem_sdiff.mp hv).2
    have hvQ : v ∉ Q := by
      intro hv
      exact Finset.disjoint_left.mp hQA hv hvA
    have hvQP : v ∉ Q ∪ P := by simp [hvQ, hvP]
    have hinsertA : insert v P ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hvA
      · exact hPA hx
    have hover : y < edgeCount G (Q ∪ insert v P) := by
      apply Nat.lt_of_not_ge
      intro hle
      have hmem : insert v P ∈ good := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hinsertA, hle⟩
      have hcardMax := hmax (insert v P) hmem
      rw [Finset.card_insert_of_notMem hvP] at hcardMax
      omega
    have hincr : edgeCount G (Q ∪ insert v P) =
        edgeCount G (Q ∪ P) + degreeInto G v (Q ∪ P) := by
      rw [show Q ∪ insert v P = insert v (Q ∪ P) by
        ext x
        simp [or_assoc, or_left_comm, or_comm]]
      exact edgeCount_insert G v (Q ∪ P) hvQP
    have hdeg : degreeInto G v (Q ∪ P) ≤ Q.card + A.card := by
      exact (degreeInto_le_card G v (Q ∪ P)).trans <|
        (Finset.card_union_le Q P).trans (Nat.add_le_add_left
          (Finset.card_le_card hPA) Q.card)
    rw [hincr] at hover
    omega

/-- AKS Proposition 3.1, with the possible edge inside the two-vertex block
recorded by `e ≤ 1`.  After adding the first correction vertex, either the
deficit has entered the next dyadic band, or adding the second vertex does
so without overshooting. -/
lemma dyadic_pair_reduction (i D x₁ x₂ e : ℕ)
    (hDlow : 2 ^ (i + 1) ≤ D) (hDhigh : D < 2 ^ (i + 2))
    (hx₁low : 2 ^ i ≤ x₁) (hx₁high : x₁ < 2 ^ (i + 1))
    (hx₂low : 2 ^ i ≤ x₂) (hx₂high : x₂ < 2 ^ (i + 1))
    (he : e ≤ 1) :
    D - x₁ < 2 ^ (i + 1) ∨
      (x₂ + e ≤ D - x₁ ∧ (D - x₁) - (x₂ + e) < 2 ^ (i + 1)) := by
  have hp₁ : 2 ^ (i + 1) = 2 ^ i * 2 := by
    rw [Nat.pow_succ]
  have hp₂ : 2 ^ (i + 2) = 2 ^ (i + 1) * 2 := by
    rw [Nat.pow_succ]
  by_cases hfirst : D - x₁ < 2 ^ (i + 1)
  · exact Or.inl hfirst
  · right
    have hremain : 2 ^ (i + 1) ≤ D - x₁ := Nat.le_of_not_gt hfirst
    constructor
    · omega
    · omega

/-- Graph form of AKS Proposition 3.1.  A two-vertex correction block lowers
the deficit into the next dyadic band, while the equality records exactly
the edges already added. -/
lemma exists_pair_correction (G : SimpleGraph V) (X : Finset V)
    (p q : V) (i D : ℕ)
    (hpX : p ∉ X) (hqX : q ∉ X) (hpq : p ≠ q)
    (hpLow : 2 ^ i ≤ degreeInto G p X)
    (hpHigh : degreeInto G p X < 2 ^ (i + 1))
    (hqLow : 2 ^ i ≤ degreeInto G q X)
    (hqHigh : degreeInto G q X < 2 ^ (i + 1))
    (hDLow : 2 ^ (i + 1) ≤ D) (hDHigh : D < 2 ^ (i + 2)) :
    ∃ C ⊆ ({p, q} : Finset V), ∃ D' < 2 ^ (i + 1),
      edgeCount G (X ∪ C) + D' = edgeCount G X + D := by
  let e : ℕ := if G.Adj q p then 1 else 0
  have he : e ≤ 1 := by
    dsimp [e]
    split <;> omega
  obtain hfirst | hsecond :=
    dyadic_pair_reduction i D (degreeInto G p X) (degreeInto G q X) e
      hDLow hDHigh hpLow hpHigh hqLow hqHigh he
  · refine ⟨{p}, by simp, D - degreeInto G p X, hfirst, ?_⟩
    have hcount : edgeCount G (X ∪ {p}) =
        edgeCount G X + degreeInto G p X := by
      simpa [Finset.union_comm] using edgeCount_insert G p X hpX
    rw [hcount]
    omega

  · refine ⟨{p, q}, Finset.Subset.rfl,
      (D - degreeInto G p X) - (degreeInto G q X + e), hsecond.2, ?_⟩
    have hcount : edgeCount G (X ∪ {p, q}) =
        edgeCount G X + degreeInto G p X + degreeInto G q X + e := by
      simpa [e, Finset.union_comm, Finset.insert_comm] using
        edgeCount_insert_pair G X p q hpX hqX hpq
    rw [hcount]
    omega

/-- The exact correction data extracted from the AKS block construction at
one longest prefix.  Only `B 0` is required to be independent.  A positive
block can contain its one possible internal edge, while distinct blocks are
pairwise anticomplete. -/
structure CorrectionTower (G : SimpleGraph V) (X : Finset V)
    (B : ℕ → Finset V) (d : ℕ) : Prop where
  disjoint_base : Disjoint X (BThrough B d)
  card_zero : (B 0).card = 3
  indep_zero : G.IsIndepSet ((B 0 : Finset V) : Set V)
  degree_zero : ∀ b ∈ B 0, degreeInto G b X = 1
  card_pos : ∀ i, 1 ≤ i → i ≤ d → (B i).card = 2
  degree_pos : ∀ i, 1 ≤ i → i ≤ d → ∀ b ∈ B i,
    2 ^ i ≤ degreeInto G b X ∧ degreeInto G b X < 2 ^ (i + 1)
  disjoint_blocks : ∀ i j, i ≤ d → j ≤ d → i ≠ j →
    Disjoint (B i) (B j)
  anticomplete_blocks : ∀ i j, i ≤ d → j ≤ d → i ≠ j →
    AnticompleteTo G (B i) (B j)

namespace CorrectionTower

lemma restrict {G : SimpleGraph V} {X : Finset V} {B : ℕ → Finset V}
    {d e : ℕ} (h : CorrectionTower G X B e) (hde : d ≤ e) :
    CorrectionTower G X B d where
  disjoint_base := h.disjoint_base.mono_right (BThrough_mono B hde)
  card_zero := h.card_zero
  indep_zero := h.indep_zero
  degree_zero := h.degree_zero
  card_pos i hi hid := h.card_pos i hi (hid.trans hde)
  degree_pos i hi hid := h.degree_pos i hi (hid.trans hde)
  disjoint_blocks i j hid hjd hij :=
    h.disjoint_blocks i j (hid.trans hde) (hjd.trans hde) hij
  anticomplete_blocks i j hid hjd hij :=
    h.anticomplete_blocks i j (hid.trans hde) (hjd.trans hde) hij

private lemma disjoint_top_lower {G : SimpleGraph V} {X : Finset V}
    {B : ℕ → Finset V} {d : ℕ}
    (h : CorrectionTower G X B (d + 1)) :
    Disjoint (B (d + 1)) (BThrough B d) := by
  rw [Finset.disjoint_left]
  intro v hvtop hvlower
  simp only [BThrough, Finset.mem_biUnion] at hvlower
  obtain ⟨i, hi, hvi⟩ := hvlower
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hine : d + 1 ≠ i := by omega
  exact Finset.disjoint_left.mp
    (h.disjoint_blocks (d + 1) i (by omega) (by omega) hine) hvtop hvi

/-- Adjoining vertices from the top block to the base preserves the lower
correction tower: distinct correction blocks are anticomplete, so every
lower-block degree is unchanged. -/
lemma extendBaseByTop {G : SimpleGraph V} {X C : Finset V}
    {B : ℕ → Finset V} {d : ℕ}
    (h : CorrectionTower G X B (d + 1)) (hC : C ⊆ B (d + 1)) :
    CorrectionTower G (X ∪ C) B d := by
  have hlow := h.restrict (Nat.le_succ d)
  have hCdisj : Disjoint C (BThrough B d) := by
    rw [Finset.disjoint_left]
    intro c hc hv
    exact Finset.disjoint_left.mp (disjoint_top_lower h) (hC hc) hv
  refine
    { disjoint_base := ?_
      card_zero := h.card_zero
      indep_zero := h.indep_zero
      degree_zero := ?_
      card_pos := hlow.card_pos
      degree_pos := ?_
      disjoint_blocks := hlow.disjoint_blocks
      anticomplete_blocks := hlow.anticomplete_blocks }
  · exact Finset.disjoint_union_left.mpr ⟨hlow.disjoint_base, hCdisj⟩
  · intro b hb
    rw [degreeInto_union_eq_left_of_anticomplete G]
    · exact h.degree_zero b hb
    · intro c hc
      exact h.anticomplete_blocks 0 (d + 1) (by omega) (by omega) (by omega)
        hb (hC hc)
  · intro i hi hid b hb
    rw [degreeInto_union_eq_left_of_anticomplete G]
    · exact h.degree_pos i hi (by omega) b hb
    · intro c hc
      exact h.anticomplete_blocks i (d + 1) (by omega) (by omega) (by omega)
        hb (hC hc)

end CorrectionTower

/-- AKS Proposition 3.1 in tower form.  Every deficit below the capacity
`2^(d+2)` can be corrected using blocks `B 0, ..., B d`. -/
theorem CorrectionTower.realizes {G : SimpleGraph V} {X : Finset V}
    {B : ℕ → Finset V} {d D : ℕ}
    (h : CorrectionTower G X B d) (hD : D < 2 ^ (d + 2)) :
    ∃ C ⊆ BThrough B d,
      edgeCount G (X ∪ C) = edgeCount G X + D := by
  induction d generalizing X D with
  | zero =>
      have hDcard : D ≤ (B 0).card := by
        rw [h.card_zero]
        norm_num at hD ⊢
        omega
      obtain ⟨C, hC, hCcard⟩ := (B 0).exists_subset_card_eq hDcard
      have hXC : Disjoint X C :=
        h.disjoint_base.mono_right (hC.trans (subset_BThrough B (by omega)))
      have hCindep : G.IsIndepSet ((C : Finset V) : Set V) := by
        intro p hp q hq hpq
        exact h.indep_zero (hC hp) (hC hq) hpq
      have hsum : ∑ b ∈ C, degreeInto G b X = D := by
        calc
          _ = ∑ _b ∈ C, 1 := by
            apply Finset.sum_congr rfl
            intro b hb
            exact h.degree_zero b (hC hb)
          _ = C.card := by simp
          _ = D := hCcard
      refine ⟨C, hC.trans (subset_BThrough B (by omega)), ?_⟩
      rw [edgeCount_union_independent G X C hXC hCindep, hsum]
  | succ d ih =>
      by_cases hsmall : D < 2 ^ (d + 2)
      · obtain ⟨C, hC, hcount⟩ :=
          ih (h.restrict (Nat.le_succ d)) hsmall
        refine ⟨C, hC.trans (BThrough_mono B (Nat.le_succ d)), hcount⟩
      · have hDlow : 2 ^ ((d + 1) + 1) ≤ D := by
          simpa [Nat.add_assoc] using Nat.le_of_not_gt hsmall
        have hDhigh : D < 2 ^ ((d + 1) + 2) := by
          simpa [Nat.add_assoc] using hD
        have hcard : (B (d + 1)).card = 2 :=
          h.card_pos (d + 1) (by omega) (by omega)
        obtain ⟨p, q, hpq, hBtop⟩ := Finset.card_eq_two.mp hcard
        have hpTop : p ∈ B (d + 1) := by rw [hBtop]; simp
        have hqTop : q ∈ B (d + 1) := by rw [hBtop]; simp
        have hpX : p ∉ X := by
          intro hp
          exact Finset.disjoint_left.mp h.disjoint_base hp
            (subset_BThrough B (by omega) hpTop)
        have hqX : q ∉ X := by
          intro hq
          exact Finset.disjoint_left.mp h.disjoint_base hq
            (subset_BThrough B (by omega) hqTop)
        have hpdeg := h.degree_pos (d + 1) (by omega) (by omega) p hpTop
        have hqdeg := h.degree_pos (d + 1) (by omega) (by omega) q hqTop
        obtain ⟨C, hCpair, D', hD', hpair⟩ :=
          exists_pair_correction G X p q (d + 1) D hpX hqX hpq
            hpdeg.1 hpdeg.2 hqdeg.1 hqdeg.2 hDlow hDhigh
        have hCtop : C ⊆ B (d + 1) := by
          intro c hc
          rw [hBtop]
          exact hCpair hc
        have hlower : CorrectionTower G (X ∪ C) B d :=
          h.extendBaseByTop hCtop
        obtain ⟨C', hC', hcount'⟩ := ih hlower hD'
        refine ⟨C ∪ C', ?_, ?_⟩
        · intro c hc
          rcases Finset.mem_union.mp hc with hc | hc
          · exact subset_BThrough B (by omega) (hCtop hc)
          · exact BThrough_mono B (Nat.le_succ d) (hC' hc)
        · calc
            edgeCount G (X ∪ (C ∪ C')) = edgeCount G ((X ∪ C) ∪ C') := by
              simp only [Finset.union_assoc]
            _ = edgeCount G (X ∪ C) + D' := hcount'
            _ = edgeCount G X + D := hpair

/-- The union of the `A`-blocks with indices strictly below `r`. -/
def ABefore (A : ℕ → Finset V) (r : ℕ) : Finset V :=
  (Finset.range r).biUnion A

/-- A longest-prefix candidate: all blocks through `A d`, followed by a
partial prefix of `A (d+1)`. -/
def blockPrefix (A : ℕ → Finset V) (d : ℕ) (P : Finset V) : Finset V :=
  ABefore A (d + 1) ∪ P

@[simp] lemma mem_ABefore {A : ℕ → Finset V} {r : ℕ} {v : V} :
    v ∈ ABefore A r ↔ ∃ i < r, v ∈ A i := by
  simp [ABefore]

lemma ABefore_succ (A : ℕ → Finset V) (r : ℕ) :
    ABefore A (r + 1) = ABefore A r ∪ A r := by
  ext v
  simp only [mem_ABefore, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hvi⟩
    by_cases hir : i = r
    · exact Or.inr (hir ▸ hvi)
    · exact Or.inl ⟨i, by omega, hvi⟩
  · rintro (⟨i, hi, hvi⟩ | hvr)
    · exact ⟨i, by omega, hvi⟩
    · exact ⟨r, by omega, hvr⟩

lemma sum_range_two_pow_add_one (r : ℕ) :
    (∑ i ∈ Finset.range r, 2 ^ i) + 1 = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, Nat.pow_succ]
      omega

/-- The structural conclusion of AKS Lemma 3.2.  This definition separates
the combinatorial block construction from Proposition 3.4's deterministic
interpolation argument. -/
structure AKSBlockSystem (G : SimpleGraph V) (ε : ℝ) (K : ℕ)
    (A B : ℕ → Finset V) : Prop where
  cardA : ∀ i, i ≤ K + 1 → (A i).card = 2 ^ i
  cardB_zero : (B 0).card = 3
  cardB_pos : ∀ i, 1 ≤ i → i ≤ K + 1 → (B i).card = 2
  disjoint_AA : ∀ i j, i ≤ K + 1 → j ≤ K + 1 → i ≠ j →
    Disjoint (A i) (A j)
  disjoint_BB : ∀ i j, i ≤ K + 1 → j ≤ K + 1 → i ≠ j →
    Disjoint (B i) (B j)
  disjoint_AB : ∀ i j, i ≤ K + 1 → j ≤ K + 1 →
    Disjoint (A i) (B j)
  indep_B_zero : G.IsIndepSet ((B 0 : Finset V) : Set V)
  complete_diag : ∀ i, i ≤ K + 1 → CompleteTo G (B i) (A i)
  anti_later : ∀ i j, i < j → j ≤ K + 1 → AnticompleteTo G (B i) (A j)
  anti_BB : ∀ i j, i ≤ K + 1 → j ≤ K + 1 → i ≠ j →
    AnticompleteTo G (B i) (B j)
  dense_A : ∀ i, i ≤ K + 1 →
    6 * ε * ((2 ^ i).choose 2 : ℝ) ≤ (edgeCount G (A i) : ℝ)

/-- Reverse an anticomplete relation, using symmetry of graph adjacency. -/
lemma AnticompleteTo.symm {G : SimpleGraph V} {S T : Finset V}
    (h : AnticompleteTo G S T) : AnticompleteTo G T S := by
  intro t ht s hs
  simpa only [G.adj_comm] using h hs ht

/-- Convert a positive integer block index to the corresponding zero-based
index in a length `K+1` pair chain. -/
def positiveChainIndex (K r : ℕ) (hr : 1 ≤ r) (hrK : r ≤ K + 1) :
    Fin (K + 1) := ⟨r - 1, by omega⟩

/-- Prepend the initial dense singleton to the dense blocks of a pair chain. -/
def blocksWithInitialA {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {Cnext : Finset V} (A0 : Finset V)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext) (r : ℕ) : Finset V :=
  if hr0 : r = 0 then A0
  else if hrK : r ≤ K + 1 then
    chain.blockA ⟨r - 1, by omega⟩
  else ∅

/-- Prepend the initial independent triple to the correcting pairs of a pair
chain. -/
def blocksWithInitialB {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {Cnext : Finset V} (B0 : Finset V)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext) (r : ℕ) : Finset V :=
  if hr0 : r = 0 then B0
  else if hrK : r ≤ K + 1 then
    chain.blockB ⟨r - 1, by omega⟩
  else ∅

@[simp] lemma blocksWithInitialA_zero {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {Cnext : Finset V} (A0 : Finset V)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext) :
    blocksWithInitialA A0 chain 0 = A0 := by
  simp [blocksWithInitialA]

@[simp] lemma blocksWithInitialB_zero {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {Cnext : Finset V} (B0 : Finset V)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext) :
    blocksWithInitialB B0 chain 0 = B0 := by
  simp [blocksWithInitialB]

lemma blocksWithInitialA_pos {G : SimpleGraph V} {ε : ℝ} {K r : ℕ}
    {Cnext : Finset V} (A0 : Finset V)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext)
    (hr : 1 ≤ r) (hrK : r ≤ K + 1) :
    blocksWithInitialA A0 chain r =
      chain.blockA (positiveChainIndex K r hr hrK) := by
  simp [blocksWithInitialA, positiveChainIndex, Nat.ne_of_gt hr, hrK]

lemma blocksWithInitialB_pos {G : SimpleGraph V} {ε : ℝ} {K r : ℕ}
    {Cnext : Finset V} (B0 : Finset V)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext)
    (hr : 1 ≤ r) (hrK : r ≤ K + 1) :
    blocksWithInitialB B0 chain r =
      chain.blockB (positiveChainIndex K r hr hrK) := by
  simp [blocksWithInitialB, positiveChainIndex, Nat.ne_of_gt hr, hrK]

namespace AKSBlockSystem

/-- An initial triple block followed by a length `K+1` recursive pair chain
is an AKS block system through index `K+1`. -/
theorem of_initial_and_pairChain
    {G : SimpleGraph V} {ε : ℝ} {K : ℕ} {A0 B0 Cnext : Finset V}
    (initial : InitialTripleBlock G A0 B0 Cnext)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext) :
    AKSBlockSystem G ε K (blocksWithInitialA A0 chain)
      (blocksWithInitialB B0 chain) := by
  refine {
    cardA := ?_
    cardB_zero := ?_
    cardB_pos := ?_
    disjoint_AA := ?_
    disjoint_BB := ?_
    disjoint_AB := ?_
    indep_B_zero := ?_
    complete_diag := ?_
    anti_later := ?_
    anti_BB := ?_
    dense_A := ?_
  }
  · intro r hrK
    by_cases hr0 : r = 0
    · subst r
      simpa using initial.card_A
    · have hr : 1 ≤ r := by omega
      rw [blocksWithInitialA_pos A0 chain hr hrK]
      have hcard := chain.card_blockA (positiveChainIndex K r hr hrK)
      simpa [positiveChainIndex, show 1 + (r - 1) = r by omega] using hcard
  · simpa using initial.card_B
  · intro r hr hrK
    rw [blocksWithInitialB_pos B0 chain hr hrK]
    exact chain.card_blockB (positiveChainIndex K r hr hrK)
  · intro r s hrK hsK hrs
    by_cases hr0 : r = 0
    · subst r
      have hs : 1 ≤ s := by omega
      rw [blocksWithInitialA_zero,
        blocksWithInitialA_pos A0 chain hs hsK]
      exact initial.disjoint_A_next.mono_right
        (chain.blockA_subset_source (positiveChainIndex K s hs hsK))
    · have hr : 1 ≤ r := by omega
      by_cases hs0 : s = 0
      · subst s
        rw [blocksWithInitialA_pos A0 chain hr hrK,
          blocksWithInitialA_zero]
        exact (initial.disjoint_A_next.mono_right
          (chain.blockA_subset_source
            (positiveChainIndex K r hr hrK))).symm
      · have hs : 1 ≤ s := by omega
        rw [blocksWithInitialA_pos A0 chain hr hrK,
          blocksWithInitialA_pos A0 chain hs hsK]
        apply chain.disjoint_blockA_of_ne
        intro hidx
        have hval := congrArg Fin.val hidx
        simp [positiveChainIndex] at hval
        omega
  · intro r s hrK hsK hrs
    by_cases hr0 : r = 0
    · subst r
      have hs : 1 ≤ s := by omega
      rw [blocksWithInitialB_zero,
        blocksWithInitialB_pos B0 chain hs hsK]
      exact initial.disjoint_B_next.mono_right
        (chain.blockB_subset_source (positiveChainIndex K s hs hsK))
    · have hr : 1 ≤ r := by omega
      by_cases hs0 : s = 0
      · subst s
        rw [blocksWithInitialB_pos B0 chain hr hrK,
          blocksWithInitialB_zero]
        exact (initial.disjoint_B_next.mono_right
          (chain.blockB_subset_source
            (positiveChainIndex K r hr hrK))).symm
      · have hs : 1 ≤ s := by omega
        rw [blocksWithInitialB_pos B0 chain hr hrK,
          blocksWithInitialB_pos B0 chain hs hsK]
        apply chain.disjoint_blockB_of_ne
        intro hidx
        have hval := congrArg Fin.val hidx
        simp [positiveChainIndex] at hval
        omega
  · intro r s hrK hsK
    by_cases hr0 : r = 0
    · subst r
      by_cases hs0 : s = 0
      · subst s
        simpa using initial.disjoint_AB
      · have hs : 1 ≤ s := by omega
        rw [blocksWithInitialA_zero,
          blocksWithInitialB_pos B0 chain hs hsK]
        exact initial.disjoint_A_next.mono_right
          (chain.blockB_subset_source (positiveChainIndex K s hs hsK))
    · have hr : 1 ≤ r := by omega
      by_cases hs0 : s = 0
      · subst s
        rw [blocksWithInitialA_pos A0 chain hr hrK,
          blocksWithInitialB_zero]
        exact (initial.disjoint_B_next.mono_right
          (chain.blockA_subset_source
            (positiveChainIndex K r hr hrK))).symm
      · have hs : 1 ≤ s := by omega
        rw [blocksWithInitialA_pos A0 chain hr hrK,
          blocksWithInitialB_pos B0 chain hs hsK]
        exact chain.disjoint_blockA_blockB
          (positiveChainIndex K r hr hrK)
          (positiveChainIndex K s hs hsK)
  · simpa using initial.indep_B
  · intro r hrK
    by_cases hr0 : r = 0
    · subst r
      simpa using initial.complete
    · have hr : 1 ≤ r := by omega
      rw [blocksWithInitialA_pos A0 chain hr hrK,
        blocksWithInitialB_pos B0 chain hr hrK]
      exact chain.complete_block (positiveChainIndex K r hr hrK)
  · intro r s hrs hsK
    have hs : 1 ≤ s := by omega
    by_cases hr0 : r = 0
    · subst r
      rw [blocksWithInitialB_zero,
        blocksWithInitialA_pos A0 chain hs hsK]
      intro b hb a ha
      exact initial.anti_next hb
        (chain.blockA_subset_source (positiveChainIndex K s hs hsK) ha)
    · have hr : 1 ≤ r := by omega
      have hrK : r ≤ K + 1 := by omega
      rw [blocksWithInitialB_pos B0 chain hr hrK,
        blocksWithInitialA_pos A0 chain hs hsK]
      apply chain.anticomplete_blockB_blockA_of_lt
      simp [positiveChainIndex]
      omega
  · intro r s hrK hsK hrs
    by_cases hr0 : r = 0
    · subst r
      have hs : 1 ≤ s := by omega
      rw [blocksWithInitialB_zero,
        blocksWithInitialB_pos B0 chain hs hsK]
      intro b hb x hx
      exact initial.anti_next hb
        (chain.blockB_subset_source (positiveChainIndex K s hs hsK) hx)
    · have hr : 1 ≤ r := by omega
      by_cases hs0 : s = 0
      · subst s
        rw [blocksWithInitialB_pos B0 chain hr hrK,
          blocksWithInitialB_zero]
        apply AnticompleteTo.symm
        intro b hb x hx
        exact initial.anti_next hb
          (chain.blockB_subset_source (positiveChainIndex K r hr hrK) hx)
      · have hs : 1 ≤ s := by omega
        rw [blocksWithInitialB_pos B0 chain hr hrK,
          blocksWithInitialB_pos B0 chain hs hsK]
        have hidx : positiveChainIndex K r hr hrK ≠
            positiveChainIndex K s hs hsK := by
          intro h
          have hval := congrArg Fin.val h
          simp [positiveChainIndex] at hval
          omega
        rcases lt_or_gt_of_ne hidx with hlt | hgt
        · exact chain.anticomplete_blockB_blockB_of_lt hlt
        · exact AnticompleteTo.symm
            (chain.anticomplete_blockB_blockB_of_lt hgt)
  · intro r hrK
    by_cases hr0 : r = 0
    · subst r
      simp
    · have hr : 1 ≤ r := by omega
      rw [blocksWithInitialA_pos A0 chain hr hrK]
      have hdense := chain.dense_blockA (positiveChainIndex K r hr hrK)
      simpa [positiveChainIndex, show 1 + (r - 1) = r by omega] using hdense

lemma card_ABefore_lt_pow {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {r : ℕ} (hr : r ≤ K + 2) :
    (ABefore A r).card < 2 ^ r := by
  have hcardLe : (ABefore A r).card ≤
      ∑ j ∈ Finset.range r, (A j).card := Finset.card_biUnion_le
  have hsum : (∑ j ∈ Finset.range r, (A j).card) + 1 = 2 ^ r := by
    rw [show (∑ j ∈ Finset.range r, (A j).card) =
        ∑ j ∈ Finset.range r, 2 ^ j by
      apply Finset.sum_congr rfl
      intro j hj
      exact h.cardA j (by
        have hjr := Finset.mem_range.mp hj
        omega)]
    exact sum_range_two_pow_add_one r
  omega

lemma disjoint_ABefore_block {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {r : ℕ} (hr : r ≤ K + 1) :
    Disjoint (ABefore A r) (A r) := by
  rw [Finset.disjoint_left]
  intro v hvBefore hvBlock
  obtain ⟨i, hir, hvi⟩ := mem_ABefore.mp hvBefore
  exact Finset.disjoint_left.mp
    (h.disjoint_AA i r (by omega) hr (by omega)) hvi hvBlock

lemma degreeInto_blockPrefix_band {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {d i : ℕ} (hd : d ≤ K) (hi : i ≤ d) {P : Finset V}
    (hP : P ⊆ A (d + 1)) {b : V} (hb : b ∈ B i) :
    2 ^ i ≤ degreeInto G b (blockPrefix A d P) ∧
      degreeInto G b (blockPrefix A d P) < 2 ^ (i + 1) := by
  have hiK : i ≤ K + 1 := by omega
  have hdK : d + 1 ≤ K + 1 := by omega
  have hAiPrefix : A i ⊆ blockPrefix A d P := by
    intro v hv
    exact Finset.mem_union_left P (mem_ABefore.mpr ⟨i, by omega, hv⟩)
  have hdegAi : degreeInto G b (A i) = (A i).card := by
    rw [degreeInto]
    congr 1
    ext v
    simp only [Finset.mem_inter]
    constructor
    · exact fun hv ↦ hv.2
    · intro hv
      exact ⟨by simpa using h.complete_diag i hiK hb hv, hv⟩
  constructor
  · rw [← h.cardA i hiK, ← hdegAi]
    exact degreeInto_mono G b hAiPrefix
  · have hneighbor :
        G.neighborFinset b ∩ blockPrefix A d P ⊆ ABefore A (i + 1) := by
      intro v hv
      obtain ⟨hvNeighbor, hvPrefix'⟩ := Finset.mem_inter.mp hv
      have hbv : G.Adj b v := by simpa using hvNeighbor
      have hvPrefix : v ∈ ABefore A (d + 1) ∪ P := hvPrefix'
      rcases Finset.mem_union.mp hvPrefix with hvA | hvP
      · obtain ⟨j, hjd, hvj⟩ := mem_ABefore.mp hvA
        by_cases hji : j ≤ i
        · exact mem_ABefore.mpr ⟨j, by omega, hvj⟩
        · exfalso
          exact h.anti_later i j (by omega) (by omega) hb hvj hbv
      · exfalso
        exact h.anti_later i (d + 1) (by omega) hdK hb (hP hvP) hbv
    have hcardBefore : (ABefore A (i + 1)).card < 2 ^ (i + 1) := by
      have hcardLe : (ABefore A (i + 1)).card ≤
          ∑ j ∈ Finset.range (i + 1), (A j).card := by
        exact Finset.card_biUnion_le
      have hsum : (∑ j ∈ Finset.range (i + 1), (A j).card) + 1 =
          2 ^ (i + 1) := by
        rw [show (∑ j ∈ Finset.range (i + 1), (A j).card) =
            ∑ j ∈ Finset.range (i + 1), 2 ^ j by
          apply Finset.sum_congr rfl
          intro j hj
          exact h.cardA j (by
            have := Finset.mem_range.mp hj
            omega)]
        exact sum_range_two_pow_add_one (i + 1)
      omega
    change (G.neighborFinset b ∩ blockPrefix A d P).card < 2 ^ (i + 1)
    exact (Finset.card_le_card hneighbor).trans_lt hcardBefore

lemma degreeInto_blockPrefix_zero {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {d : ℕ} (hd : d ≤ K) {P : Finset V} (hP : P ⊆ A (d + 1))
    {b : V} (hb : b ∈ B 0) :
    degreeInto G b (blockPrefix A d P) = 1 := by
  have hband := h.degreeInto_blockPrefix_band hd (Nat.zero_le d) hP hb
  have hlo : 1 ≤ degreeInto G b (blockPrefix A d P) := by
    simpa using hband.1
  have hhi : degreeInto G b (blockPrefix A d P) < 2 := by
    simpa using hband.2
  omega

lemma disjoint_blockPrefix_BThrough {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {d : ℕ} (hd : d ≤ K) {P : Finset V} (hP : P ⊆ A (d + 1)) :
    Disjoint (blockPrefix A d P) (BThrough B d) := by
  rw [Finset.disjoint_left]
  intro v hvPrefix hvB
  simp only [BThrough, Finset.mem_biUnion] at hvB
  obtain ⟨j, hj, hvj⟩ := hvB
  have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change v ∈ ABefore A (d + 1) ∪ P at hvPrefix
  rcases Finset.mem_union.mp hvPrefix with hvA | hvP
  · obtain ⟨i, hi, hvi⟩ := mem_ABefore.mp hvA
    have hid : i ≤ d := by omega
    exact Finset.disjoint_left.mp
      (h.disjoint_AB i j (by omega) (by omega)) hvi hvj
  · exact Finset.disjoint_left.mp
      (h.disjoint_AB (d + 1) j (by omega) (by omega)) (hP hvP) hvj

/-- The degree-band consequences of an AKS block system form precisely the
correction tower consumed by `CorrectionTower.realizes`. -/
lemma toCorrectionTower {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {d : ℕ} (hd : d ≤ K) {P : Finset V} (hP : P ⊆ A (d + 1)) :
    CorrectionTower G (blockPrefix A d P) B d where
  disjoint_base := h.disjoint_blockPrefix_BThrough hd hP
  card_zero := h.cardB_zero
  indep_zero := h.indep_B_zero
  degree_zero b hb := h.degreeInto_blockPrefix_zero hd hP hb
  card_pos i hi hid := h.cardB_pos i hi (by omega)
  degree_pos i hi hid b hb := h.degreeInto_blockPrefix_band hd hid hP hb
  disjoint_blocks i j hid hjd hij :=
    h.disjoint_BB i j (by omega) (by omega) hij
  anticomplete_blocks i j hid hjd hij :=
    h.anti_BB i j (by omega) (by omega) hij

/-- Direct interpolation consequence for one partial `A`-prefix. -/
theorem realizes_from_blockPrefix {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {d D : ℕ} (hd : d ≤ K) {P : Finset V} (hP : P ⊆ A (d + 1))
    (hD : D < 2 ^ (d + 2)) :
    ∃ C ⊆ BThrough B d,
      edgeCount G (blockPrefix A d P ∪ C) =
        edgeCount G (blockPrefix A d P) + D := by
  exact (h.toCorrectionTower hd hP).realizes hD

/-- Interpolation across one `A`-block.  If the target lies between the
edge counts before and after adjoining `A r`, the lower correction blocks
realize it exactly. -/
theorem realizes_between_blocks {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    {r y : ℕ} (hrPos : 1 ≤ r) (hrK : r ≤ K)
    (hbefore : edgeCount G (ABefore A r) ≤ y)
    (hafter : y ≤ edgeCount G (ABefore A r ∪ A r)) :
    ∃ S : Finset V, edgeCount G S = y := by
  obtain ⟨P, hP, hbase, hdef⟩ :=
    exists_subset_with_small_deficit G (ABefore A r) (A r)
      (h.disjoint_ABefore_block (by omega)) y hbefore hafter
  let d := r - 1
  have hd : d ≤ K := by omega
  have hdOne : d + 1 = r := by
    dsimp [d]
    omega
  have hprefix : blockPrefix A d P = ABefore A r ∪ P := by
    simp only [blockPrefix, hdOne]
  let D := y - edgeCount G (blockPrefix A d P)
  have hD : D < 2 ^ (d + 2) := by
    have hcardBefore := h.card_ABefore_lt_pow (r := r) (by omega)
    have hcardA := h.cardA r (by omega)
    have hpow : 2 ^ (d + 2) = 2 ^ r * 2 := by
      rw [show d + 2 = r + 1 by omega, Nat.pow_succ]
    dsimp [D]
    rw [hprefix]
    rcases hdef with heq | hsmall
    · rw [heq]
      simp
    · rw [hcardA] at hsmall
      omega
  have hP' : P ⊆ A (d + 1) := by simpa [hdOne] using hP
  obtain ⟨C, hC, hcount⟩ := h.realizes_from_blockPrefix hd hP' hD
  refine ⟨blockPrefix A d P ∪ C, ?_⟩
  rw [hcount]
  exact Nat.add_sub_of_le (by simpa [hprefix] using hbase)

/-- AKS Corollary 3.3, combinatorial form: a block system realizes every
integer edge count up to the edge count already present in its last full
`A`-block. -/
theorem realizes_le_block {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    (hK : 1 ≤ K) {y : ℕ} (hy : y ≤ edgeCount G (A K)) :
    ∃ S : Finset V, edgeCount G S = y := by
  by_cases hy0 : y = 0
  · subst y
    exact ⟨∅, edgeCount_eq_zero_of_card_le_one G (by simp)⟩
  let good : Finset ℕ :=
    (Finset.Icc 1 K).filter fun r ↦ y ≤ edgeCount G (ABefore A (r + 1))
  have hgood : good.Nonempty := by
    refine ⟨K, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hK, le_rfl⟩, ?_⟩
    exact hy.trans (edgeCount_mono G (by
      intro v hv
      exact mem_ABefore.mpr ⟨K, by omega, hv⟩))
  obtain ⟨r, hrGood, hrMin⟩ := good.exists_min_image id hgood
  have hrIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hrGood).1
  have hrPos : 1 ≤ r := hrIcc.1
  have hrK : r ≤ K := hrIcc.2
  have hafterRaw : y ≤ edgeCount G (ABefore A (r + 1)) :=
    (Finset.mem_filter.mp hrGood).2
  have hbefore : edgeCount G (ABefore A r) < y := by
    by_contra hnot
    have hyBefore : y ≤ edgeCount G (ABefore A r) := Nat.le_of_not_gt hnot
    by_cases hrOne : r = 1
    · subst r
      have hcard : (ABefore A 1).card ≤ 1 := by
        rw [ABefore_succ A 0]
        simpa [ABefore] using (h.cardA 0 (by omega)).le
      have hzero := edgeCount_eq_zero_of_card_le_one G hcard
      omega
    · let s := r - 1
      have hsPos : 1 ≤ s := by
        dsimp [s]
        omega
      have hsK : s ≤ K := by
        dsimp [s]
        omega
      have hsSucc : s + 1 = r := by
        dsimp [s]
        omega
      have hsGood : s ∈ good := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hsPos, hsK⟩, ?_⟩
        simpa [hsSucc] using hyBefore
      have hrs := hrMin s hsGood
      dsimp only [id_eq] at hrs
      omega
  apply h.realizes_between_blocks hrPos hrK hbefore.le
  simpa only [ABefore_succ] using hafterRaw

/-- Density-form endpoint of AKS Corollary 3.3. -/
theorem realizes_up_to_density {G : SimpleGraph V} {ε : ℝ} {K : ℕ}
    {A B : ℕ → Finset V} (h : AKSBlockSystem G ε K A B)
    (hK : 1 ≤ K) {y : ℕ}
    (hy : (y : ℝ) ≤ 6 * ε * ((2 ^ K).choose 2 : ℝ)) :
    ∃ S : Finset V, edgeCount G S = y := by
  apply h.realizes_le_block hK
  have hy' : (y : ℝ) ≤ (edgeCount G (A K) : ℝ) :=
    hy.trans (h.dense_A K (by omega))
  exact_mod_cast hy'

theorem hasPrescribedCounts_of_blockSystem {G : SimpleGraph V} {ε : ℝ}
    {K M : ℕ} {A B : ℕ → Finset V}
    (h : AKSBlockSystem G ε K A B) (hK : 1 ≤ K)
    (hM : (M : ℝ) ≤ 6 * ε * ((2 ^ K).choose 2 : ℝ)) :
    ∀ y ≤ M, ∃ S : Finset V, edgeCount G S = y := by
  intro y hy
  apply h.realizes_up_to_density hK
  have hyCast : (y : ℝ) ≤ (M : ℝ) := by exact_mod_cast hy
  exact hyCast.trans hM

end AKSBlockSystem

/-- Complete-sequence subset sums.  The hypothesis says that the next
weight is at most one plus the total of all earlier weights. -/
lemma exists_subset_sum_eq_of_complete_sequence (w : ℕ → ℕ) :
    ∀ k y, (∀ i < k, w i ≤ 1 + ∑ j ∈ Finset.range i, w j) →
      y ≤ ∑ i ∈ Finset.range k, w i →
      ∃ I ⊆ Finset.range k, ∑ i ∈ I, w i = y := by
  intro k
  induction k with
  | zero =>
      intro y _ hy
      simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hy
      subst y
      exact ⟨∅, by simp⟩
  | succ k ih =>
      intro y hcomplete hy
      let total := ∑ i ∈ Finset.range k, w i
      by_cases hy0 : y ≤ total
      · obtain ⟨I, hI, hsum⟩ := ih y (fun i hi ↦ hcomplete i (hi.trans (Nat.lt_succ_self k))) hy0
        exact ⟨I, hI.trans (Finset.range_mono (Nat.le_succ k)), hsum⟩
      · have htotal_lt : total < y := Nat.lt_of_not_ge hy0
        have hw : w k ≤ total + 1 := by
          simpa [total, add_comm] using hcomplete k (Nat.lt_succ_self k)
        have hrem : y - w k ≤ total := by
          rw [Finset.sum_range_succ] at hy
          omega
        obtain ⟨I, hI, hsum⟩ :=
          ih (y - w k) (fun i hi ↦ hcomplete i (hi.trans (Nat.lt_succ_self k))) hrem
        refine ⟨insert k I, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · exact Finset.mem_range.mpr ((Finset.mem_range.mp (hI hi)).trans (Nat.lt_succ_self k))
        · have hkI : k ∉ I := fun hk ↦ (Nat.lt_irrefl k) (Finset.mem_range.mp (hI hk))
          rw [Finset.sum_insert hkI, hsum]
          have hwle : w k ≤ y := by omega
          omega

/-- Graph-level interpolation from a complete sequence of independent
correction vertices.  This is the exact final step of the AKS block
argument once the block construction has supplied the vertices and degree
bounds. -/
lemma exists_induced_edge_correction (G : SimpleGraph V) (A : Finset V)
    (b : ℕ → V) (k : ℕ)
    (hbinj : Set.InjOn b (Finset.range k : Set ℕ))
    (hdisj : Disjoint A ((Finset.range k).image b))
    (hindep : G.IsIndepSet (((Finset.range k).image b : Finset V) : Set V))
    (hcomplete : ∀ i < k,
      degreeInto G (b i) A ≤
        1 + ∑ j ∈ Finset.range i, degreeInto G (b j) A)
    (y : ℕ)
    (hy : y ≤ ∑ i ∈ Finset.range k, degreeInto G (b i) A) :
    ∃ I ⊆ Finset.range k,
      edgeCount G (A ∪ I.image b) = edgeCount G A + y := by
  let w : ℕ → ℕ := fun i ↦ degreeInto G (b i) A
  obtain ⟨I, hI, hsum⟩ :=
    exists_subset_sum_eq_of_complete_sequence w k y hcomplete hy
  have hdisjI : Disjoint A (I.image b) := by
    rw [Finset.disjoint_left]
    intro a haA haImage
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp haImage
    exact Finset.disjoint_left.mp hdisj haA
      (Finset.mem_image.mpr ⟨i, hI hiI, rfl⟩)
  have hindepI : G.IsIndepSet ((I.image b : Finset V) : Set V) := by
    have hImage : I.image b ⊆ (Finset.range k).image b := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨i, hI hi, rfl⟩
    intro x hx y hy hxy
    exact hindep (hImage hx) (hImage hy) hxy
  have hsumImage : ∑ v ∈ I.image b, degreeInto G v A = y := by
    rw [Finset.sum_image]
    · exact hsum
    · intro i hi j hj hij
      exact hbinj (hI hi) (hI hj) hij
  refine ⟨I, hI, ?_⟩
  rw [edgeCount_union_independent G A (I.image b) hdisjI hindepI,
    hsumImage]

/-- A graph realizes every edge count up to `M`. -/
def HasPrescribedCounts (G : SimpleGraph V) (M : ℕ) : Prop :=
  ∀ y ≤ M, ∃ S : Finset V, edgeCount G S = y

/-- Existential block-system output of the initial-triple plus recursive-pair
construction. -/
theorem exists_AKSBlockSystem_of_initial_and_pairChain
    {G : SimpleGraph V} {ε : ℝ} {K : ℕ} {A0 B0 Cnext : Finset V}
    (initial : InitialTripleBlock G A0 B0 Cnext)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext) :
    ∃ A B : ℕ → Finset V, AKSBlockSystem G ε K A B := by
  exact ⟨blocksWithInitialA A0 chain, blocksWithInitialB B0 chain,
    AKSBlockSystem.of_initial_and_pairChain initial chain⟩

/-- Endpoint composition: an initial triple block and its recursive positive
pair chain realize every prescribed count throughout the density interval of
the final certified dyadic block. -/
theorem hasPrescribedCounts_of_initial_and_pairChain
    {G : SimpleGraph V} {ε : ℝ} {K M : ℕ} {A0 B0 Cnext : Finset V}
    (initial : InitialTripleBlock G A0 B0 Cnext)
    (chain : PairBlockChain G ε 1 (K + 1) Cnext)
    (hK : 1 ≤ K)
    (hM : (M : ℝ) ≤ 6 * ε * ((2 ^ K).choose 2 : ℝ)) :
    HasPrescribedCounts G M := by
  exact AKSBlockSystem.hasPrescribedCounts_of_blockSystem
    (AKSBlockSystem.of_initial_and_pairChain initial chain) hK hM

/-- Full finite construction endpoint.  An actual initial triple extension
and a balanced/numeric sized supply for every subsequent reservoir assemble
into the chain consumed by the exact prescribed-count theorem. -/
theorem hasPrescribedCounts_of_initial_and_sizedSupply
    {G : SimpleGraph V} {ε : ℝ} {K M d0 : ℕ} {C0 : Finset V}
    (initial : InitialTripleExtension G d0 C0)
    (minSize : ℕ → ℕ)
    (hstart : minSize 1 ≤ d0 + 1)
    (hsupply : ∀ j, 1 ≤ j → j < 1 + (K + 1) → ∀ R : Finset V,
      minSize j ≤ R.card →
        Nonempty (SizedPairExtension G ε j (minSize (j + 1)) R))
    (hK : 1 ≤ K)
    (hM : (M : ℝ) ≤ 6 * ε * ((2 ^ K).choose 2 : ℝ)) :
    HasPrescribedCounts G M := by
  have hsource : minSize 1 ≤ initial.Cnext.card := by
    have hlarge := initial.next_large
    omega
  obtain ⟨chain⟩ := PairBlockChain.exists_of_sized_supply minSize hsource hsupply
  exact hasPrescribedCounts_of_initial_and_pairChain initial.initial chain hK hM

/-- The target-specific output of the AKS longest-prefix and block
construction.  `A` is the longest prefix below the target and `b` enumerates
the independent correction vertices in increasing block order. -/
structure CorrectionData (G : SimpleGraph V) (y : ℕ) where
  A : Finset V
  b : ℕ → V
  k : ℕ
  binj : Set.InjOn b (Finset.range k : Set ℕ)
  disjoint : Disjoint A ((Finset.range k).image b)
  independent :
    G.IsIndepSet (((Finset.range k).image b : Finset V) : Set V)
  complete : ∀ i < k,
    degreeInto G (b i) A ≤
      1 + ∑ j ∈ Finset.range i, degreeInto G (b j) A
  base_le : edgeCount G A ≤ y
  enough :
    y - edgeCount G A ≤
      ∑ i ∈ Finset.range k, degreeInto G (b i) A

/-- The formal Corollary 3.3 endpoint: target-specific AKS correction data
realizes the target exactly. -/
lemma CorrectionData.realizes {G : SimpleGraph V} {y : ℕ}
    (D : CorrectionData G y) :
    ∃ S : Finset V, edgeCount G S = y := by
  obtain ⟨I, hI, hcount⟩ :=
    exists_induced_edge_correction G D.A D.b D.k D.binj D.disjoint
      D.independent D.complete (y - edgeCount G D.A) D.enough
  refine ⟨D.A ∪ I.image D.b, ?_⟩
  rw [hcount]
  exact Nat.add_sub_of_le D.base_le

/-- Uniform target-specific correction data gives all prescribed counts in
the required initial interval. -/
lemma hasPrescribedCounts_of_correctionData {G : SimpleGraph V} {M : ℕ}
    (hdata : ∀ y ≤ M, CorrectionData G y) :
    HasPrescribedCounts G M := by
  intro y hy
  exact (hdata y hy).realizes

end DiscreteInterpolation

end AKSGraph
end Erdos88

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
import ErdosProblems.Erdos722.Transversal
import Mathlib

/-!
# The iterated clique-exchange gadget

The finite-field trade in `Transversal` isolates one prescribed edge.  The
exchange gadget used by the absorber is obtained by gluing two fresh copies
of that trade for each edge of a designated positive clique.  This file
packages the finite iteration and its separation invariant.
-/

namespace Erdos722.Exchange

open Finset
open Erdos722.Transversal

noncomputable section

/-! ## Equivalences respecting a distinguished subset -/

/-- Equal finite sets with equally large distinguished subsets admit an
equivalence carrying the first distinguished subset onto the second. -/
theorem exists_equiv_subtype_respecting
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {A : Finset V} {B : Finset W} {S : Finset V} {T : Finset W}
    (hSA : S ⊆ A) (hTB : T ⊆ B)
    (hcard : A.card = B.card) (hsmall : S.card = T.card) :
    ∃ σ : ↑A ≃ ↑B, ∀ x : ↑A, x.1 ∈ S ↔ (σ x).1 ∈ T := by
  classical
  have hcomp : (A \ S).card = (B \ T).card := by
    rw [Finset.card_sdiff_of_subset hSA, Finset.card_sdiff_of_subset hTB,
      hcard, hsmall]
  let σS : ↑S ≃ ↑T := Fintype.equivOfCardEq (by simpa using hsmall)
  let σC : ↑(A \ S) ≃ ↑(B \ T) := Fintype.equivOfCardEq (by simpa using hcomp)
  let toFun : ↑A → ↑B := fun x ↦
    if hx : x.1 ∈ S then
      ⟨(σS ⟨x.1, hx⟩).1, hTB (σS ⟨x.1, hx⟩).2⟩
    else
      ⟨(σC ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).1,
        (Finset.mem_sdiff.mp (σC ⟨x.1,
          Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).1⟩
  let invFun : ↑B → ↑A := fun y ↦
    if hy : y.1 ∈ T then
      ⟨(σS.symm ⟨y.1, hy⟩).1, hSA (σS.symm ⟨y.1, hy⟩).2⟩
    else
      ⟨(σC.symm ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).1,
        (Finset.mem_sdiff.mp (σC.symm ⟨y.1,
          Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).2).1⟩
  have hto_mem (x : ↑A) : x.1 ∈ S ↔ (toFun x).1 ∈ T := by
    by_cases hx : x.1 ∈ S
    · simp [toFun, hx]
    · have hcnot : (σC ⟨x.1,
          Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).1 ∉ T :=
        (Finset.mem_sdiff.mp (σC ⟨x.1,
          Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).2
      simp [toFun, hx, hcnot]
  have hinv_mem (y : ↑B) : y.1 ∈ T ↔ (invFun y).1 ∈ S := by
    by_cases hy : y.1 ∈ T
    · simp [invFun, hy]
    · have hcnot : (σC.symm ⟨y.1,
          Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).1 ∉ S :=
        (Finset.mem_sdiff.mp (σC.symm ⟨y.1,
          Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).2).2
      simp [invFun, hy, hcnot]
  let σ : ↑A ≃ ↑B :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        by_cases hx : x.1 ∈ S
        · have hy : (toFun x).1 ∈ T := (hto_mem x).mp hx
          apply Subtype.ext
          simp [toFun, invFun, hx, hy, σS]
        · have hy : (toFun x).1 ∉ T := fun h ↦ hx ((hto_mem x).mpr h)
          have hto : toFun x =
              ⟨(σC ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).1,
                (Finset.mem_sdiff.mp (σC ⟨x.1,
                  Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).1⟩ := by
            simp [toFun, hx]
          rw [hto]
          have hy' : (σC ⟨x.1,
              Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩).1 ∉ T := by
            simpa [hto] using hy
          apply Subtype.ext
          simp [invFun, hy', σC]
      right_inv := by
        intro y
        by_cases hy : y.1 ∈ T
        · have hx : (invFun y).1 ∈ S := (hinv_mem y).mp hy
          apply Subtype.ext
          simp [toFun, invFun, hx, hy, σS]
        · have hx : (invFun y).1 ∉ S := fun h ↦ hy ((hinv_mem y).mpr h)
          have hinv : invFun y =
              ⟨(σC.symm ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).1,
                (Finset.mem_sdiff.mp (σC.symm ⟨y.1,
                  Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).2).1⟩ := by
            simp [invFun, hy]
          rw [hinv]
          have hx' : (σC.symm ⟨y.1,
              Finset.mem_sdiff.mpr ⟨y.2, hy⟩⟩).1 ∉ S := by
            simpa [hinv] using hx
          apply Subtype.ext
          simp [toFun, hx', σC] }
  exact ⟨σ, fun x ↦ hto_mem x⟩

/-- An equivalence between two unions can simultaneously preserve both
members of the pair once the individual and intersection cardinalities
agree. -/
theorem exists_equiv_subtype_respecting_pair
    {V W : Type*} [DecidableEq V] [DecidableEq W] [Nonempty W]
    {A : Finset V} {B : Finset W}
    {S₁ S₂ : Finset V} {T₁ T₂ : Finset W}
    (hA : A = S₁ ∪ S₂) (hB : B = T₁ ∪ T₂)
    (hcard : A.card = B.card)
    (hcard₁ : S₁.card = T₁.card)
    (hinter : (S₁ ∩ S₂).card = (T₁ ∩ T₂).card) :
    ∃ σ : ↑A ≃ ↑B,
      (∀ x : ↑A, x.1 ∈ S₁ ↔ (σ x).1 ∈ T₁) ∧
      (∀ x : ↑A, x.1 ∈ S₂ ↔ (σ x).1 ∈ T₂) := by
  classical
  have hS₁A : S₁ ⊆ A := by rw [hA]; exact Finset.subset_union_left
  have hT₁B : T₁ ⊆ B := by rw [hB]; exact Finset.subset_union_left
  obtain ⟨σ₁, hσ₁⟩ := exists_equiv_subtype_respecting
    (Finset.inter_subset_left : S₁ ∩ S₂ ⊆ S₁)
    (Finset.inter_subset_left : T₁ ∩ T₂ ⊆ T₁)
    hcard₁ hinter
  let sA : Finset ↑A := (Finset.univ : Finset ↑A).filter fun x ↦ x.1 ∈ S₁
  let fallback : W := Classical.choice (inferInstance : Nonempty W)
  let f : ↑A → W := fun x ↦
    if hx : x.1 ∈ S₁ then (σ₁ ⟨x.1, hx⟩).1 else fallback
  have himage : Finset.image f sA ⊆ B := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxS₁ : x.1 ∈ S₁ := (Finset.mem_filter.mp hx).2
    simp only [f, hxS₁, dite_true]
    exact hT₁B (σ₁ ⟨x.1, hxS₁⟩).2
  have hinj : Set.InjOn f (↑sA : Set ↑A) := by
    intro x hx y hy hxy
    have hxS₁ : x.1 ∈ S₁ := (Finset.mem_filter.mp hx).2
    have hyS₁ : y.1 ∈ S₁ := (Finset.mem_filter.mp hy).2
    have hσ : σ₁ ⟨x.1, hxS₁⟩ = σ₁ ⟨y.1, hyS₁⟩ := by
      apply Subtype.ext
      simpa [f, hxS₁, hyS₁] using hxy
    exact Subtype.ext (congrArg (fun z : ↑S₁ ↦ z.1) (σ₁.injective hσ))
  have htypeCard : Fintype.card ↑A = B.card := by simpa using hcard
  obtain ⟨σ, hσext⟩ := Finset.exists_equiv_extend_of_card_eq
    htypeCard himage hinj
  have hpres₁ (x : ↑A) : x.1 ∈ S₁ ↔ (σ x).1 ∈ T₁ := by
    constructor
    · intro hx
      have hxsA : x ∈ sA := by simp [sA, hx]
      have hext := hσext x hxsA
      have hval : (σ x).1 = (σ₁ ⟨x.1, hx⟩).1 := by
        simpa [f, hx] using hext
      rw [hval]
      exact (σ₁ ⟨x.1, hx⟩).2
    · intro hx
      let zT : ↑T₁ := ⟨(σ x).1, hx⟩
      obtain ⟨zS, hzS⟩ := σ₁.surjective zT
      let zA : ↑A := ⟨zS.1, hS₁A zS.2⟩
      have hzAs : zA ∈ sA := by simp [sA, zA, zS.2]
      have hext := hσext zA hzAs
      have hσzx : σ zA = σ x := by
        apply Subtype.ext
        have hzval : (σ₁ zS).1 = (σ x).1 :=
          congrArg Subtype.val hzS
        have hext' : (σ zA).1 = (σ₁ zS).1 := by
          simpa [f, zA, zS.2] using hext
        exact hext'.trans hzval
      have hzAx : zA = x := σ.injective hσzx
      exact hzAx ▸ zS.2
  have hpresInter (x : ↑A) : x.1 ∈ S₁ ∩ S₂ ↔
      (σ x).1 ∈ T₁ ∩ T₂ := by
    constructor
    · intro hx
      have hxData := Finset.mem_inter.mp hx
      have hxsA : x ∈ sA := by simp [sA, hxData.1]
      have hext := hσext x hxsA
      have hsmall := (hσ₁ ⟨x.1, hxData.1⟩).mp hx
      have hval : (σ x).1 = (σ₁ ⟨x.1, hxData.1⟩).1 := by
        simpa [f, hxData.1] using hext
      rw [hval]
      exact hsmall
    · intro hx
      have hxData := Finset.mem_inter.mp hx
      have hxS₁ : x.1 ∈ S₁ := (hpres₁ x).mpr hxData.1
      have hxsA : x ∈ sA := by simp [sA, hxS₁]
      have hext := hσext x hxsA
      apply (hσ₁ ⟨x.1, hxS₁⟩).mpr
      have hval : (σ x).1 = (σ₁ ⟨x.1, hxS₁⟩).1 := by
        simpa [f, hxS₁] using hext
      rwa [← hval]
  refine ⟨σ, hpres₁, ?_⟩
  intro x
  constructor
  · intro hxS₂
    by_cases hxS₁ : x.1 ∈ S₁
    · exact (Finset.mem_inter.mp
        ((hpresInter x).mp (Finset.mem_inter.mpr ⟨hxS₁, hxS₂⟩))).2
    · have hxB : (σ x).1 ∈ B := (σ x).2
      have hxUnion : (σ x).1 ∈ T₁ ∪ T₂ := by
        exact (by rw [← hB]; exact hxB)
      rcases Finset.mem_union.mp hxUnion with hxT₁ | hxT₂
      · exact (hxS₁ ((hpres₁ x).mpr hxT₁)).elim
      · exact hxT₂
  · intro hxT₂
    by_cases hxT₁ : (σ x).1 ∈ T₁
    · exact (Finset.mem_inter.mp
        ((hpresInter x).mpr (Finset.mem_inter.mpr ⟨hxT₁, hxT₂⟩))).2
    · have hxA : x.1 ∈ A := x.2
      have hxUnion : x.1 ∈ S₁ ∪ S₂ := by
        exact (by rw [← hA]; exact hxA)
      rcases Finset.mem_union.mp hxUnion with hxS₁ | hxS₂
      · exact (hxT₁ ((hpres₁ x).mp hxS₁)).elim
      · exact hxS₂

/-! ## Packaged trades and their distinguished root -/

/-- A finite uniform clique trade with its common host recorded. -/
structure TradeData (q r : ℕ) where
  V : Type
  decEq : DecidableEq V
  fintype : Fintype V
  host : Finset (Finset V)
  positive : Finset (Finset V)
  negative : Finset (Finset V)
  host_uniform : ∀ A ∈ host, A.card = r
  positive_decomp : @IsUniformDecomposition V decEq host positive q r
  negative_decomp : @IsUniformDecomposition V decEq host negative q r

/-- The original labelled root clique after an injective relabelling. -/
def mappedRoot {V : Type*} [DecidableEq V] {q : ℕ}
    (f : Fin q ↪ V) : Finset V :=
  (Finset.univ : Finset (Fin q)).map f

/-- A labelled edge of the original root clique after relabelling. -/
def mappedRootEdge {V : Type*} [DecidableEq V] {q : ℕ}
    (f : Fin q ↪ V) (e : Finset (Fin q)) : Finset V :=
  e.map f

@[simp] theorem card_mappedRoot {V : Type*} [DecidableEq V] {q : ℕ}
    (f : Fin q ↪ V) : (mappedRoot f).card = q := by
  simp [mappedRoot]

@[simp] theorem card_mappedRootEdge {V : Type*} [DecidableEq V] {q : ℕ}
    (f : Fin q ↪ V) (e : Finset (Fin q)) :
    (mappedRootEdge f e).card = e.card := by
  simp [mappedRootEdge]

theorem mappedRootEdge_subset_mappedRoot
    {V : Type*} [DecidableEq V] {q : ℕ}
    (f : Fin q ↪ V) (e : Finset (Fin q)) :
    mappedRootEdge f e ⊆ mappedRoot f := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The finite type indexing the `r`-edges of the original root. -/
abbrev RootEdge (q r : ℕ) :=
  {e : Finset (Fin q) // e ∈ (Finset.univ : Finset (Fin q)).powersetCard r}

@[simp] theorem RootEdge.card {q r : ℕ} (e : RootEdge q r) :
    e.1.card = r := by
  exact (Finset.mem_powersetCard.mp e.2).2

/-- An iterated exchange together with the already isolated negative
cliques.  The indices remain edges of the original labelled root, so the
invariant survives the changing vertex type created by gluing. -/
structure PartialExchange (q r : ℕ) (done : Finset (RootEdge q r))
    extends TradeData q r where
  rootEmbedding : Fin q ↪ toTradeData.V
  root_mem : mappedRoot rootEmbedding ∈ toTradeData.positive
  special : RootEdge q r → Finset toTradeData.V
  special_mem : ∀ e ∈ done, special e ∈ toTradeData.negative
  special_inter_root : ∀ e ∈ done,
    special e ∩ mappedRoot rootEmbedding = mappedRootEdge rootEmbedding e.1
  special_outer_disjoint : ∀ e ∈ done, ∀ e' ∈ done, e ≠ e' →
    Disjoint (special e \ mappedRoot rootEmbedding)
      (special e' \ mappedRoot rootEmbedding)
  positive_special_unique : ∀ Q ∈ toTradeData.positive,
    Q ≠ mappedRoot rootEmbedding →
    ∀ e ∈ done, ∀ e' ∈ done,
      (∃ g ∈ Q.powersetCard r, g ∈ (special e).powersetCard r) →
      (∃ g ∈ Q.powersetCard r, g ∈ (special e').powersetCard r) →
      e = e'
  positive_inter_special_card_le : ∀ e ∈ done,
    ∀ Q ∈ toTradeData.positive, (Q ∩ special e).card ≤ r
  special_isolated : ∀ e ∈ done, ∀ A ∈ toTradeData.host,
    A ⊆ mappedRoot rootEmbedding ∪ special e →
      A ⊆ mappedRoot rootEmbedding ∨ A ⊆ special e

/-- A base trade with one positive and one negative block meeting exactly
in its designated edge. -/
structure BaseExchange (q r : ℕ) extends TradeData q r where
  plus : Finset toTradeData.V
  minus : Finset toTradeData.V
  edge : Finset toTradeData.V
  plus_mem : plus ∈ toTradeData.positive
  minus_mem : minus ∈ toTradeData.negative
  inter_eq : plus ∩ minus = edge
  edge_card : edge.card = r
  positive_inter_minus_card_le : ∀ Q ∈ toTradeData.positive,
    (Q ∩ minus).card ≤ r

/-- The prime-field polynomial trade supplies the base exchange. -/
theorem exists_baseExchange (q r : ℕ) (hq : 0 < q) (hrq : r ≤ q) :
    Nonempty (BaseExchange q r) := by
  obtain ⟨p, hp, hqp, _hpq, hbase⟩ :=
    exists_zmod_base_exchange q r hq hrq
  let : Fact p.Prime := ⟨hp⟩
  let host := transversalHost (I := Fin q) (F := ZMod p) r
  let positive := polynomialBlocks (zmodNodes q p) r
  let negative := shiftedPolynomialBlocks (zmodNodes q p)
    (prefixShift (zmodNodes q p) r) r
  let plus := graph (fun _ : Fin q ↦ (0 : ZMod p))
  let minus : Finset (Fin q × ZMod p) :=
    graph (prefixShift (zmodNodes q p) r)
  let edge : Finset (Fin q × ZMod p) :=
    zeroPrefixEdge (F := ZMod p) q r
  have hpos : IsUniformDecomposition host positive q r := by
    simpa [host, positive] using
      (polynomialBlocks_decompose (zmodNodes_injective hqp.le) r)
  have hneg : IsUniformDecomposition host negative q r := by
    simpa [host, negative] using
      (shiftedPolynomialBlocks_decompose (zmodNodes_injective hqp.le)
        (prefixShift (zmodNodes q p) r) r)
  refine ⟨
    { V := Fin q × ZMod p
      decEq := inferInstance
      fintype := inferInstance
      host := host
      positive := positive
      negative := negative
      host_uniform := fun A hA ↦ (mem_transversalHost.mp hA).1
      positive_decomp := hpos
      negative_decomp := hneg
      plus := plus
      minus := minus
      edge := edge
      plus_mem := by
        exact zero_graph_mem_polynomialBlocks (zmodNodes q p) r
      minus_mem := by
        exact prefixShift_graph_mem_shiftedPolynomialBlocks
          (zmodNodes q p) r
      inter_eq := by
        exact zero_graph_inter_prefixShift (zmodNodes_injective hqp.le)
      edge_card := by
        exact card_zeroPrefixEdge hrq
      positive_inter_minus_card_le := by
        intro Q hQ
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hQ
        exact graph_inter_prefixShift_card_le
          (zmodNodes_injective hqp.le) hrq hf }⟩

/-- The unprocessed base package has the zero graph as its positive root. -/
theorem exists_initialPartialExchange (q r : ℕ)
    (hq : 0 < q) (hrq : r ≤ q) :
    Nonempty (PartialExchange q r ∅) := by
  obtain ⟨B⟩ := exists_baseExchange q r hq hrq
  let : DecidableEq B.V := B.decEq
  let : Fintype B.V := B.fintype
  have hpluscard : B.plus.card = q :=
    B.positive_decomp.1 B.plus B.plus_mem
  let f : Fin q ↪ B.V :=
    (Finset.equivFinOfCardEq hpluscard).symm.toEmbedding.trans
      (Function.Embedding.subtype (fun x : B.V ↦ x ∈ B.plus))
  have hroot : mappedRoot f = B.plus := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
      exact ((Finset.equivFinOfCardEq hpluscard).symm i).2
    · intro hx
      let y : ↑B.plus := ⟨x, hx⟩
      apply Finset.mem_map.mpr
      refine ⟨Finset.equivFinOfCardEq hpluscard y, Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val
        ((Finset.equivFinOfCardEq hpluscard).symm_apply_apply y)
  refine ⟨
    { toTradeData := B.toTradeData
      rootEmbedding := f
      root_mem := hroot.symm ▸ B.plus_mem
      special := fun _ ↦ ∅
      special_mem := by simp
      special_inter_root := by simp
      special_outer_disjoint := by simp
      positive_special_unique := by simp
      positive_inter_special_card_le := by simp
      special_isolated := by simp }⟩

/-! ## The two-gluing isolation step -/

theorem TradeData.exists_negative_containing
    {q r : ℕ} (T : TradeData q r)
    {e : Finset T.V} (hehost : e ∈ T.host) :
    ∃ Q ∈ T.negative, e ⊆ Q := by
  let : DecidableEq T.V := T.decEq
  have hcard := T.negative_decomp.2.2 e hehost
  obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp hcard
  refine ⟨Q, ?_, ?_⟩
  · have : Q ∈ T.negative.filter (e ⊆ ·) := by simp [hQ]
    exact (Finset.mem_filter.mp this).1
  · have : Q ∈ T.negative.filter (e ⊆ ·) := by simp [hQ]
    exact (Finset.mem_filter.mp this).2

theorem TradeData.exists_positive_containing
    {q r : ℕ} (T : TradeData q r)
    {e : Finset T.V} (hehost : e ∈ T.host) :
    ∃ Q ∈ T.positive, e ⊆ Q := by
  let : DecidableEq T.V := T.decEq
  have hcard := T.positive_decomp.2.2 e hehost
  obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp hcard
  refine ⟨Q, ?_, ?_⟩
  · have : Q ∈ T.positive.filter (e ⊆ ·) := by simp [hQ]
    exact (Finset.mem_filter.mp this).1
  · have : Q ∈ T.positive.filter (e ⊆ ·) := by simp [hQ]
    exact (Finset.mem_filter.mp this).2

@[simp] theorem mappedRoot_trans
    {V W : Type*} [DecidableEq V] [DecidableEq W] {q : ℕ}
    (f : Fin q ↪ V) (g : V ↪ W) :
    mappedRoot (f.trans g) = (mappedRoot f).map g := by
  simp [mappedRoot, Finset.map_map]

@[simp] theorem mappedRootEdge_trans
    {V W : Type*} [DecidableEq V] [DecidableEq W] {q : ℕ}
    (f : Fin q ↪ V) (g : V ↪ W) (e : Finset (Fin q)) :
    mappedRootEdge (f.trans g) e = (mappedRootEdge f e).map g := by
  simp [mappedRootEdge, Finset.map_map]

/-- A set in the fresh right trade meets a mapped old set precisely in the
part of the gluing clique prescribed by the gluing equivalence. -/
theorem map_right_inter_map_left_eq
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↑Q₁ ≃ ↑Q₂)
    {A₁ S₁ : Finset V₁} {A₂ T₂ : Finset V₂}
    (hS₁Q₁ : S₁ ⊆ Q₁) (hS₁A₁ : S₁ ⊆ A₁)
    (hT₂Q₂ : T₂ ⊆ Q₂) (hinter : A₂ ∩ Q₂ = T₂)
    (hequiv : ∀ x : ↑Q₁, x.1 ∈ S₁ ↔ (equiv x).1 ∈ T₂) :
    A₂.map (glueRightEmbedding equiv) ∩
        A₁.map (glueLeftEmbedding V₁ V₂ Q₂) =
      S₁.map (glueLeftEmbedding V₁ V₂ Q₂) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzR, hzL⟩ := Finset.mem_inter.mp hz
    obtain ⟨v₂, hv₂A, hv₂z⟩ := Finset.mem_map.mp hzR
    obtain ⟨v₁, _hv₁A, hv₁z⟩ := Finset.mem_map.mp hzL
    have hv₂Q : v₂ ∈ Q₂ := by
      by_contra hv₂Q
      have hsum := hv₂z.trans hv₁z.symm
      simp [glueRightEmbedding, glueRightFun, glueLeftEmbedding, hv₂Q] at hsum
    have hv₂T : v₂ ∈ T₂ := by
      have : v₂ ∈ A₂ ∩ Q₂ := Finset.mem_inter.mpr ⟨hv₂A, hv₂Q⟩
      simpa [hinter] using this
    let x : ↑Q₁ := equiv.symm ⟨v₂, hv₂Q⟩
    have hxS : x.1 ∈ S₁ := (hequiv x).mpr (by simpa [x] using hv₂T)
    apply Finset.mem_map.mpr
    refine ⟨x.1, hxS, ?_⟩
    have hv₂eq : (equiv x).1 = v₂ := by simp [x]
    rw [← hv₂z]
    simp [glueRightEmbedding, glueRightFun, glueLeftEmbedding, hv₂Q,
      x, hv₂eq]
  · intro hz
    obtain ⟨v₁, hv₁S, hv₁z⟩ := Finset.mem_map.mp hz
    have hv₁Q : v₁ ∈ Q₁ := hS₁Q₁ hv₁S
    let x : ↑Q₁ := ⟨v₁, hv₁Q⟩
    let y : ↑Q₂ := equiv x
    have hyT : y.1 ∈ T₂ := (hequiv x).mp hv₁S
    have hyA : y.1 ∈ A₂ := by
      have : y.1 ∈ A₂ ∩ Q₂ := by
        rw [hinter]
        exact hyT
      exact (Finset.mem_inter.mp this).1
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_map.mpr
      refine ⟨y.1, hyA, ?_⟩
      rw [← hv₁z]
      simp [y, x, glueRightEmbedding, glueRightFun, glueLeftEmbedding]
    · apply Finset.mem_map.mpr
      exact ⟨v₁, hS₁A₁ hv₁S, hv₁z⟩

/-- Output of the two-gluing operation.  The fresh special negative block
meets the image of the entire old vertex set in exactly the requested edge;
old positive blocks and old negative blocks not containing that edge
survive. -/
def tradeMap {q r : ℕ} (U : TradeData q r) {V : Type*}
    (f : V ↪ U.V) (A : Finset V) : Finset U.V := by
  letI : DecidableEq U.V := U.decEq
  exact A.map f

def tradeUniverse {q r : ℕ} (T : TradeData q r) : Finset T.V := by
  letI : Fintype T.V := T.fintype
  exact Finset.univ

def tradeInter {q r : ℕ} (T : TradeData q r)
    (A B : Finset T.V) : Finset T.V := by
  letI : DecidableEq T.V := T.decEq
  exact A ∩ B

def tradeUnion {q r : ℕ} (T : TradeData q r)
    (A B : Finset T.V) : Finset T.V := by
  letI : DecidableEq T.V := T.decEq
  exact A ∪ B

structure IsolatedExtension {q r : ℕ} (T : TradeData q r)
    (root e : Finset T.V) where
  data : TradeData q r
  oldEmbedding : T.V ↪ data.V
  root_mem : tradeMap data oldEmbedding root ∈ data.positive
  special : Finset data.V
  special_mem : special ∈ data.negative
  special_inter_old : tradeInter data special
      (tradeMap data oldEmbedding (tradeUniverse T)) =
    tradeMap data oldEmbedding e
  positive_survives : ∀ Q ∈ T.positive,
    tradeMap data oldEmbedding Q ∈ data.positive
  positive_inter_special_card_le : ∀ Q ∈ data.positive,
    (tradeInter data Q special).card ≤ r
  negative_survives : ∀ Q ∈ T.negative, ¬ e ⊆ Q →
    tradeMap data oldEmbedding Q ∈ data.negative
  host_inside_old : ∀ A ∈ data.host,
    A ⊆ tradeMap data oldEmbedding (tradeUniverse T) →
      ∃ A₀ ∈ T.host, tradeMap data oldEmbedding A₀ = A
  special_isolated : ∀ A ∈ data.host,
    A ⊆ tradeUnion data (tradeMap data oldEmbedding root) special →
      A ⊆ tradeMap data oldEmbedding root ∨ A ⊆ special
  special_trace_isolated : ∀ A ∈ data.host,
    tradeInter data A
        (tradeUnion data (tradeMap data oldEmbedding root) special) ⊆
          tradeMap data oldEmbedding root ∨
      tradeInter data A
        (tradeUnion data (tradeMap data oldEmbedding root) special) ⊆ special

/-- Gluing two fresh base trades along the current negative block through
`e` isolates a new negative block from the entire old vertex set. -/
theorem exists_isolatedExtension
    {q r : ℕ} (hqr : r < q) (T : TradeData q r)
    (B : BaseExchange q r) {root e : Finset T.V}
    (hroot : root ∈ T.positive) (hesub : e ⊆ root)
    (hecard : e.card = r) :
    Nonempty (IsolatedExtension T root e) := by
  let : DecidableEq T.V := T.decEq
  let : Fintype T.V := T.fintype
  let : DecidableEq B.V := B.decEq
  let : Fintype B.V := B.fintype
  have hehost : e ∈ T.host :=
    T.positive_decomp.2.1 root hroot
      (Finset.mem_powersetCard.mpr ⟨hesub, hecard⟩)
  obtain ⟨C, hCneg, heC⟩ := T.exists_negative_containing hehost
  have hCcard : C.card = q := T.negative_decomp.1 C hCneg
  have hpluscard : B.plus.card = q :=
    B.positive_decomp.1 B.plus B.plus_mem
  have hedgePlus : B.edge ⊆ B.plus := by
    rw [← B.inter_eq]
    exact Finset.inter_subset_left
  obtain ⟨σ₁, hσ₁⟩ := exists_equiv_subtype_respecting
    heC hedgePlus (hCcard.trans hpluscard.symm)
      (hecard.trans B.edge_card.symm)

  let V₁ := GluedVertex T.V B.V B.plus
  let left₁ : T.V ↪ V₁ := glueLeftEmbedding T.V B.V B.plus
  let right₁ : B.V ↪ V₁ := glueRightEmbedding σ₁
  let host₁ : Finset (Finset V₁) :=
    mapFamily left₁ T.host ∪
      mapFamily right₁ (B.host \ B.plus.powersetCard r)
  let positive₁ : Finset (Finset V₁) :=
    mapFamily left₁ T.positive ∪
      mapFamily right₁ (B.positive.erase B.plus)
  let negative₁ : Finset (Finset V₁) :=
    mapFamily left₁ (T.negative.erase C) ∪
      mapFamily right₁ B.negative
  have hleftUniform₁ : ∀ A ∈ mapFamily left₁ T.host, A.card = r :=
    uniform_mapFamily T.host_uniform left₁
  have hrightResidualUniform₁ : ∀ A ∈
      mapFamily right₁ (B.host \ B.plus.powersetCard r), A.card = r :=
    uniform_mapFamily
      (fun A hA ↦ B.host_uniform A (Finset.mem_sdiff.mp hA).1) right₁
  have hpos₁ : IsUniformDecomposition host₁ positive₁ q r := by
    exact (T.positive_decomp.map left₁).union
      ((B.positive_decomp.erase B.host_uniform B.plus_mem).map right₁)
      hleftUniform₁ hrightResidualUniform₁
      (disjoint_glue_left_right_residual σ₁ B.host_uniform) hqr.le
  have hneg₁alt : IsUniformDecomposition
      (mapFamily left₁ (T.host \ C.powersetCard r) ∪
        mapFamily right₁ B.host) negative₁ q r := by
    exact ((T.negative_decomp.erase T.host_uniform hCneg).map left₁).union
      (B.negative_decomp.map right₁)
      (uniform_mapFamily
        (fun A hA ↦ T.host_uniform A (Finset.mem_sdiff.mp hA).1) left₁)
      (uniform_mapFamily B.host_uniform right₁)
      (disjoint_glue_left_residual_right σ₁ T.host_uniform) hqr.le
  have hhosts₁ : host₁ =
      mapFamily left₁ (T.host \ C.powersetCard r) ∪
        mapFamily right₁ B.host := by
    exact glued_host_eq σ₁
      (T.negative_decomp.2.1 C hCneg) (B.positive_decomp.2.1 B.plus B.plus_mem)
  have hneg₁ : IsUniformDecomposition host₁ negative₁ q r :=
    hhosts₁.symm ▸ hneg₁alt
  have huniform₁ : ∀ A ∈ host₁, A.card = r := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact uniform_mapFamily T.host_uniform left₁ A hA
    · exact uniform_mapFamily
        (fun E hE ↦ B.host_uniform E (Finset.mem_sdiff.mp hE).1)
        right₁ A hA
  let N₁ : Finset V₁ := B.minus.map right₁
  have hN₁neg : N₁ ∈ negative₁ := by
    apply Finset.mem_union_right
    exact mem_mapFamily.mpr ⟨B.minus, B.minus_mem, rfl⟩
  let e₁ : Finset V₁ := e.map left₁
  have hN₁inter : N₁ ∩ (Finset.univ : Finset T.V).map left₁ = e₁ := by
    apply map_right_inter_map_left_eq σ₁ heC
      (Finset.subset_univ e) hedgePlus
    · simpa [Finset.inter_comm] using B.inter_eq
    · exact hσ₁

  have hN₁card : N₁.card = q := by
    simp [N₁, B.negative_decomp.1 B.minus B.minus_mem]
  obtain ⟨σ₂, hσ₂⟩ := exists_equiv_subtype_respecting
    (by
      intro x hx
      have : x ∈ N₁ ∩ (Finset.univ : Finset T.V).map left₁ := by
        rw [hN₁inter]
        exact hx
      exact (Finset.mem_inter.mp this).1)
    hedgePlus (hN₁card.trans hpluscard.symm)
      (by simp [e₁, hecard, B.edge_card])

  let V₂ := GluedVertex V₁ B.V B.plus
  let left₂ : V₁ ↪ V₂ := glueLeftEmbedding V₁ B.V B.plus
  let right₂ : B.V ↪ V₂ := glueRightEmbedding σ₂
  let host₂ : Finset (Finset V₂) :=
    mapFamily left₂ host₁ ∪
      mapFamily right₂ (B.host \ B.plus.powersetCard r)
  let positive₂ : Finset (Finset V₂) :=
    mapFamily left₂ positive₁ ∪
      mapFamily right₂ (B.positive.erase B.plus)
  let negative₂ : Finset (Finset V₂) :=
    mapFamily left₂ (negative₁.erase N₁) ∪
      mapFamily right₂ B.negative
  have huniform₂ : ∀ A ∈ host₂, A.card = r := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact uniform_mapFamily huniform₁ left₂ A hA
    · exact uniform_mapFamily
        (fun E hE ↦ B.host_uniform E (Finset.mem_sdiff.mp hE).1)
        right₂ A hA
  have hpos₂ : IsUniformDecomposition host₂ positive₂ q r := by
    exact (hpos₁.map left₂).union
      ((B.positive_decomp.erase B.host_uniform B.plus_mem).map right₂)
      (uniform_mapFamily huniform₁ left₂)
      (uniform_mapFamily
        (fun E hE ↦ B.host_uniform E (Finset.mem_sdiff.mp hE).1) right₂)
      (disjoint_glue_left_right_residual σ₂ B.host_uniform) hqr.le
  have hneg₂alt : IsUniformDecomposition
      (mapFamily left₂ (host₁ \ N₁.powersetCard r) ∪
        mapFamily right₂ B.host) negative₂ q r := by
    exact ((hneg₁.erase huniform₁ hN₁neg).map left₂).union
      (B.negative_decomp.map right₂)
      (uniform_mapFamily
        (fun A hA ↦ huniform₁ A (Finset.mem_sdiff.mp hA).1) left₂)
      (uniform_mapFamily B.host_uniform right₂)
      (disjoint_glue_left_residual_right σ₂ huniform₁) hqr.le
  have hhosts₂ : host₂ =
      mapFamily left₂ (host₁ \ N₁.powersetCard r) ∪
        mapFamily right₂ B.host := by
    exact glued_host_eq σ₂ (hneg₁.2.1 N₁ hN₁neg)
      (B.positive_decomp.2.1 B.plus B.plus_mem)
  have hneg₂ : IsUniformDecomposition host₂ negative₂ q r :=
    hhosts₂.symm ▸ hneg₂alt

  let old : T.V ↪ V₂ := left₁.trans left₂
  let N₂ : Finset V₂ := B.minus.map right₂
  have hN₂neg : N₂ ∈ negative₂ := by
    apply Finset.mem_union_right
    exact mem_mapFamily.mpr ⟨B.minus, B.minus_mem, rfl⟩
  have hN₂inter : N₂ ∩ (Finset.univ : Finset T.V).map old =
      e.map old := by
    have h := map_right_inter_map_left_eq
      (A₁ := (Finset.univ : Finset T.V).map left₁) (S₁ := e₁)
      (A₂ := B.minus) (T₂ := B.edge) σ₂
      (by
        intro x hx
        have : x ∈ N₁ ∩ (Finset.univ : Finset T.V).map left₁ := by
          rw [hN₁inter]
          exact hx
        exact (Finset.mem_inter.mp this).1)
      (by
        intro x hx
        change x ∈ e.map left₁ at hx
        obtain ⟨v, _hv, hvx⟩ := Finset.mem_map.mp hx
        apply Finset.mem_map.mpr
        exact ⟨v, Finset.mem_univ v, hvx⟩)
      hedgePlus (by simpa [Finset.inter_comm] using B.inter_eq) hσ₂
    simpa [N₂, e₁, old, Finset.map_map] using h
  have hpositiveSurvives : ∀ Q ∈ T.positive,
      Q.map old ∈ positive₂ := by
    intro Q hQ
    apply Finset.mem_union_left
    apply mem_mapFamily.mpr
    refine ⟨Q.map left₁, ?_, by simp [old, Finset.map_map]⟩
    apply Finset.mem_union_left
    exact mem_mapFamily.mpr ⟨Q, hQ, rfl⟩
  have hnegativeSurvives : ∀ Q ∈ T.negative, ¬ e ⊆ Q →
      Q.map old ∈ negative₂ := by
    intro Q hQ heQ
    have hQC : Q ≠ C := by
      intro h
      exact heQ (h ▸ heC)
    have hQneg₁ : Q.map left₁ ∈ negative₁ := by
      apply Finset.mem_union_left
      exact mem_mapFamily.mpr ⟨Q, Finset.mem_erase.mpr ⟨hQC, hQ⟩, rfl⟩
    have hQN : Q.map left₁ ≠ N₁ := by
      intro hEq
      have hsubOld : Q.map left₁ ⊆ (Finset.univ : Finset T.V).map left₁ := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have hinterSelf : N₁ ∩ (Finset.univ : Finset T.V).map left₁ = N₁ := by
        rw [Finset.inter_eq_left]
        exact hEq ▸ hsubOld
      have hNe : N₁ = e₁ := hinterSelf.symm.trans hN₁inter
      have hqeqr : q = r := by
        calc
          q = (Q.map left₁).card := by
            simp [T.negative_decomp.1 Q hQ]
          _ = N₁.card := congrArg Finset.card hEq
          _ = e₁.card := congrArg Finset.card hNe
          _ = r := by simp [e₁, hecard]
      omega
    apply Finset.mem_union_left
    exact mem_mapFamily.mpr
      ⟨Q.map left₁, Finset.mem_erase.mpr ⟨hQN, hQneg₁⟩,
        by simp [old, Finset.map_map]⟩
  have he₁N₁ : e₁ ⊆ N₁ := by
    intro x hx
    have hx' : x ∈ N₁ ∩ (Finset.univ : Finset T.V).map left₁ := by
      rw [hN₁inter]
      exact hx
    exact (Finset.mem_inter.mp hx').1
  have he₁root : e₁ ⊆ root.map left₁ := by
    exact Finset.map_subset_map.mpr hesub
  have hN₁interRoot : N₁ ∩ root.map left₁ = e₁ := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxOld : x ∈ (Finset.univ : Finset T.V).map left₁ := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hx).2
        exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have hx' : x ∈ N₁ ∩ (Finset.univ : Finset T.V).map left₁ :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxOld⟩
      rw [hN₁inter] at hx'
      exact hx'
    · intro x hx
      exact Finset.mem_inter.mpr ⟨he₁N₁ hx, he₁root hx⟩
  have hN₂interV₁ : N₂ ∩ (Finset.univ : Finset V₁).map left₂ =
      e₁.map left₂ := by
    have h := map_right_inter_map_left_eq
      (A₁ := (Finset.univ : Finset V₁)) (S₁ := e₁)
      (A₂ := B.minus) (T₂ := B.edge) σ₂
      he₁N₁ (Finset.subset_univ e₁) hedgePlus
      (by simpa [Finset.inter_comm] using B.inter_eq) hσ₂
    simpa [N₂] using h
  have hedgeMinus : B.edge ⊆ B.minus := by
    rw [← B.inter_eq]
    exact Finset.inter_subset_right
  have hrightRootSubset (y : B.V)
      (hy : right₂ y ∈ root.map old) : y ∈ B.minus := by
    have hyLeft : right₂ y ∈ (root.map left₁).map left₂ := by
      simpa [old, Finset.map_map] using hy
    obtain ⟨hyPlus, hyRoot⟩ :=
      (glueRightEmbedding_mem_map_left_iff σ₂ (root.map left₁) y).mp hyLeft
    let x : ↑N₁ := σ₂.symm ⟨y, hyPlus⟩
    have hxe : x.1 ∈ e₁ := by
      have hx : x.1 ∈ N₁ ∩ root.map left₁ :=
        Finset.mem_inter.mpr ⟨x.2, hyRoot⟩
      rw [hN₁interRoot] at hx
      exact hx
    have hyEdge : y ∈ B.edge := by
      have hxEdge := (hσ₂ x).mp hxe
      simpa [x] using hxEdge
    exact hedgeMinus hyEdge
  refine ⟨
    { data :=
        { V := V₂
          decEq := inferInstance
          fintype := inferInstance
          host := host₂
          positive := positive₂
          negative := negative₂
          host_uniform := huniform₂
          positive_decomp := hpos₂
          negative_decomp := hneg₂ }
      oldEmbedding := old
      root_mem := hpositiveSurvives root hroot
      special := N₂
      special_mem := hN₂neg
      special_inter_old := hN₂inter
      positive_survives := hpositiveSurvives
      positive_inter_special_card_le := by
        intro Q hQ
        change (Q ∩ N₂).card ≤ r
        rcases Finset.mem_union.mp hQ with hQleft | hQright
        · obtain ⟨Q₁, hQ₁, rfl⟩ := mem_mapFamily.mp hQleft
          have hsub : Q₁.map left₂ ∩ N₂ ⊆ e₁.map left₂ := by
            intro x hx
            have hxQ : x ∈ Q₁.map left₂ := (Finset.mem_inter.mp hx).1
            have hxN : x ∈ N₂ := (Finset.mem_inter.mp hx).2
            have hxV₁ : x ∈ (Finset.univ : Finset V₁).map left₂ := by
              obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxQ
              exact Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩
            have hxInter : x ∈ N₂ ∩
                (Finset.univ : Finset V₁).map left₂ :=
              Finset.mem_inter.mpr ⟨hxN, hxV₁⟩
            rw [hN₂interV₁] at hxInter
            exact hxInter
          calc
            (Q₁.map left₂ ∩ N₂).card ≤ (e₁.map left₂).card :=
              Finset.card_le_card hsub
            _ = r := by simp [e₁, hecard]
        · obtain ⟨Q₂, hQ₂, rfl⟩ := mem_mapFamily.mp hQright
          have hQ₂pos : Q₂ ∈ B.positive :=
            Finset.mem_of_mem_erase hQ₂
          have hbound := B.positive_inter_minus_card_le Q₂ hQ₂pos
          simpa [N₂, ← Finset.map_inter] using hbound
      negative_survives := hnegativeSurvives
      host_inside_old := by
        intro A hA hsub
        change A ⊆ (Finset.univ : Finset T.V).map old at hsub
        have hsubV₁ : A ⊆ (Finset.univ : Finset V₁).map left₂ := by
          intro x hx
          obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (hsub hx)
          exact Finset.mem_map.mpr
            ⟨left₁ v, Finset.mem_univ _, by simp [old]⟩
        obtain ⟨A₁, hA₁, hmap₁⟩ :=
          exists_left_preimage_of_mem_gluedHost_of_subset_left
            σ₂ B.host_uniform hA hsubV₁
        have hA₁sub : A₁ ⊆ (Finset.univ : Finset T.V).map left₁ := by
          have hmapSub : A₁.map left₂ ⊆
              ((Finset.univ : Finset T.V).map left₁).map left₂ := by
            rw [hmap₁]
            simpa [old, Finset.map_map] using hsub
          exact Finset.map_subset_map.mp hmapSub
        obtain ⟨A₀, hA₀, hmap₀⟩ :=
          exists_left_preimage_of_mem_gluedHost_of_subset_left
            σ₁ B.host_uniform hA₁ hA₁sub
        refine ⟨A₀, hA₀, ?_⟩
        change A₀.map old = A
        rw [← hmap₁, ← hmap₀]
        simp [old, left₁, left₂, Finset.map_map]
      special_isolated := by
        intro A hA hsub
        rcases Finset.mem_union.mp hA with hleft | hright
        · left
          obtain ⟨A₁, _hA₁, rfl⟩ := mem_mapFamily.mp hleft
          intro x hx
          have hxUnion := hsub hx
          rcases Finset.mem_union.mp hxUnion with hxRoot | hxN₂
          · exact hxRoot
          · have hxV₁ : x ∈ (Finset.univ : Finset V₁).map left₂ := by
              obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
              exact Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩
            have hxe₁ : x ∈ e₁.map left₂ := by
              have : x ∈ N₂ ∩ (Finset.univ : Finset V₁).map left₂ :=
                Finset.mem_inter.mpr ⟨hxN₂, hxV₁⟩
              rw [hN₂interV₁] at this
              exact this
            obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxe₁
            obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
            exact Finset.mem_map.mpr
              ⟨u, hesub hu, by simp [old]⟩
        · right
          obtain ⟨A₂, _hA₂, rfl⟩ := mem_mapFamily.mp hright
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
          have hxUnion := hsub (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
          rcases Finset.mem_union.mp hxUnion with hxRoot | hxN₂
          · exact Finset.mem_map.mpr ⟨y, hrightRootSubset y hxRoot, rfl⟩
          · exact hxN₂
      special_trace_isolated := by
        intro A hA
        rcases Finset.mem_union.mp hA with hleft | hright
        · left
          obtain ⟨A₁, _hA₁, rfl⟩ := mem_mapFamily.mp hleft
          intro x hx
          have hxA : x ∈ A₁.map left₂ := (Finset.mem_inter.mp hx).1
          have hxUnion := (Finset.mem_inter.mp hx).2
          rcases Finset.mem_union.mp hxUnion with hxRoot | hxN₂
          · exact hxRoot
          · have hxV₁ : x ∈ (Finset.univ : Finset V₁).map left₂ := by
              obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxA
              exact Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩
            have hxe₁ : x ∈ e₁.map left₂ := by
              have : x ∈ N₂ ∩ (Finset.univ : Finset V₁).map left₂ :=
                Finset.mem_inter.mpr ⟨hxN₂, hxV₁⟩
              rw [hN₂interV₁] at this
              exact this
            obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxe₁
            obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
            exact Finset.mem_map.mpr
              ⟨u, hesub hu, by simp [old]⟩
        · right
          obtain ⟨A₂, _hA₂, rfl⟩ := mem_mapFamily.mp hright
          intro x hx
          have hxA : x ∈ A₂.map right₂ := (Finset.mem_inter.mp hx).1
          have hxUnion := (Finset.mem_inter.mp hx).2
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxA
          rcases Finset.mem_union.mp hxUnion with hxRoot | hxN₂
          · exact Finset.mem_map.mpr ⟨y, hrightRootSubset y hxRoot, rfl⟩
          · exact hxN₂ }⟩

/-! ## Iterating the isolation step -/

/-- The edge inserted by the final two-gluing round has the full trace
isolation property needed for an admissible two-clique extension. -/
def PartialExchange.SpecialTraceIsolated
    {q r : ℕ} {done : Finset (RootEdge q r)}
    (P : PartialExchange q r done) (e : RootEdge q r) : Prop := by
  letI : DecidableEq P.V := P.decEq
  exact ∀ A ∈ P.host,
      tradeInter P.toTradeData A
          (tradeUnion P.toTradeData (mappedRoot P.rootEmbedding) (P.special e)) ⊆
            mappedRoot P.rootEmbedding ∨
        tradeInter P.toTradeData A
          (tradeUnion P.toTradeData (mappedRoot P.rootEmbedding) (P.special e)) ⊆
            P.special e

/-- Every positive block meets a distinguished special negative block in
at most the vertices of one `r`-edge. -/
def PartialExchange.SpecialPositiveInterBounded
    {q r : ℕ} {done : Finset (RootEdge q r)}
    (P : PartialExchange q r done) (e : RootEdge q r) : Prop := by
  letI : DecidableEq P.V := P.decEq
  exact ∀ Q ∈ P.positive, (Q ∩ P.special e).card ≤ r

/-- One more root edge can be isolated while preserving all previously
isolated negative blocks.  The newly inserted special block also has the
stronger trace-isolation property. -/
theorem exists_partialExchange_insert_with_trace_and_bound
    {q r : ℕ} (hqr : r < q) (B : BaseExchange q r)
    {done : Finset (RootEdge q r)} (P : PartialExchange q r done)
    (e : RootEdge q r) (he : e ∉ done) :
    ∃ Q : PartialExchange q r (insert e done),
      Q.SpecialTraceIsolated e ∧ Q.SpecialPositiveInterBounded e := by
  let : DecidableEq P.V := P.decEq
  let : Fintype P.V := P.fintype
  let root := mappedRoot P.rootEmbedding
  let edge := mappedRootEdge P.rootEmbedding e.1
  obtain ⟨X⟩ := exists_isolatedExtension hqr P.toTradeData B
    P.root_mem (mappedRootEdge_subset_mappedRoot P.rootEmbedding e.1)
    (by simp [edge])
  let : DecidableEq X.data.V := X.data.decEq
  let : Fintype X.data.V := X.data.fintype
  let old := X.oldEmbedding
  let newRoot := root.map old
  have hSpecialInterOld : X.special ∩
      (Finset.univ : Finset P.V).map old = edge.map old := by
    simpa [tradeInter, tradeMap, tradeUniverse, old, edge] using
      X.special_inter_old

  have hnotSubset (j : RootEdge q r) (hj : j ∈ done) (hje : j ≠ e) :
      ¬ edge ⊆ P.special j := by
    intro hsub
    have hinterSub : edge ⊆ P.special j ∩ root := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨hsub hx, mappedRootEdge_subset_mappedRoot P.rootEmbedding e.1 hx⟩
    rw [P.special_inter_root j hj] at hinterSub
    have heq : edge = mappedRootEdge P.rootEmbedding j.1 := by
      apply Finset.eq_of_subset_of_card_le hinterSub
      simp [edge]
    have : e.1 = j.1 := Finset.map_injective P.rootEmbedding heq
    exact hje (Subtype.ext this.symm)

  have hnewInterRoot : X.special ∩ newRoot = edge.map old := by
    ext x
    constructor
    · intro hx
      have hxSpecial : x ∈ X.special := (Finset.mem_inter.mp hx).1
      have hxRoot : x ∈ newRoot := (Finset.mem_inter.mp hx).2
      have hxOld : x ∈ (Finset.univ : Finset P.V).map old := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxRoot
        exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have : x ∈ X.special ∩
          (Finset.univ : Finset P.V).map old :=
        Finset.mem_inter.mpr ⟨hxSpecial, hxOld⟩
      rw [hSpecialInterOld] at this
      exact this
    · intro hx
      have hxOld : x ∈ (Finset.univ : Finset P.V).map old := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have hxSpecial : x ∈ X.special := by
        have : x ∈ X.special ∩
            (Finset.univ : Finset P.V).map old := by
          rw [hSpecialInterOld]
          exact hx
        exact (Finset.mem_inter.mp this).1
      have hxRoot : x ∈ newRoot := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
        apply Finset.mem_map.mpr
        exact ⟨v, mappedRootEdge_subset_mappedRoot P.rootEmbedding e.1 hv, rfl⟩
      exact Finset.mem_inter.mpr ⟨hxSpecial, hxRoot⟩

  have hnewOldOuter (j : RootEdge q r) :
      Disjoint (X.special \ newRoot)
        ((P.special j).map old \ newRoot) := by
    rw [Finset.disjoint_left]
    intro x hxNew hxOld
    have hxSpecial : x ∈ X.special := (Finset.mem_sdiff.mp hxNew).1
    have hxNotRoot : x ∉ newRoot := (Finset.mem_sdiff.mp hxNew).2
    have hxOldUniverse : x ∈ (Finset.univ : Finset P.V).map old := by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp hxOld).1
      exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
    have hxEdge : x ∈ edge.map old := by
      have : x ∈ X.special ∩
          (Finset.univ : Finset P.V).map old :=
        Finset.mem_inter.mpr ⟨hxSpecial, hxOldUniverse⟩
      rw [hSpecialInterOld] at this
      exact this
    apply hxNotRoot
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxEdge
    apply Finset.mem_map.mpr
    exact ⟨v, mappedRootEdge_subset_mappedRoot P.rootEmbedding e.1 hv, rfl⟩

  have positive_eq_mapped_old_of_common_old_edge
      (Q : Finset X.data.V) (hQ : Q ∈ X.data.positive)
      (g : Finset X.data.V) (hgQ : g ∈ Q.powersetCard r)
      (hgOld : g ⊆ (Finset.univ : Finset P.V).map old) :
      ∃ Q₀ ∈ P.positive, Q = Q₀.map old := by
    have hgHost : g ∈ X.data.host :=
      X.data.positive_decomp.2.1 Q hQ hgQ
    obtain ⟨g₀, hg₀Host, hg₀map⟩ :=
      X.host_inside_old g hgHost hgOld
    change g₀.map old = g at hg₀map
    obtain ⟨Q₀, hQ₀, hg₀Q₀⟩ :=
      P.toTradeData.exists_positive_containing hg₀Host
    have hQ₀map : Q₀.map old ∈ X.data.positive := by
      simpa [tradeMap] using X.positive_survives Q₀ hQ₀
    have hgMapped : g ∈ (Q₀.map old).powersetCard r := by
      rw [← hg₀map]
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.map_subset_map.mpr hg₀Q₀, by
          rw [Finset.card_map]
          exact P.host_uniform g₀ hg₀Host⟩
    exact ⟨Q₀, hQ₀,
      X.data.positive_decomp.blocks_eq_of_common_edge
        hQ hQ₀map hgQ hgMapped⟩

  let special : RootEdge q r → Finset X.data.V := fun j ↦
    if j = e then X.special else (P.special j).map old
  let Q : PartialExchange q r (insert e done) :=
    { toTradeData := X.data
      rootEmbedding := P.rootEmbedding.trans old
      root_mem := by simpa [root, old, tradeMap] using X.root_mem
      special := special
      special_mem := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [special, X.special_mem]
        · by_cases hje : j = e
          · simp [special, hje, X.special_mem]
          · simp only [special, hje, ↓reduceIte]
            simpa [tradeMap, old] using
              (X.negative_survives (P.special j) (P.special_mem j hj)
                (hnotSubset j hj hje))
      special_inter_root := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [special, newRoot, root, edge, old] using hnewInterRoot
        · by_cases hje : j = e
          · subst j
            simpa [special, newRoot, root, edge, old] using hnewInterRoot
          · simp only [special, hje, ↓reduceIte]
            rw [mappedRoot_trans, ← Finset.map_inter,
              P.special_inter_root j hj, mappedRootEdge_trans]
      special_outer_disjoint := by
        intro j hj k hk hjk
        by_cases hje : j = e
        · subst j
          by_cases hke : k = e
          · subst k
            exact (hjk rfl).elim
          · simpa [special, hke, newRoot, root, old] using hnewOldOuter k
        · by_cases hke : k = e
          · subst k
            have h := (hnewOldOuter j).symm
            simpa [special, hje, newRoot, root, old] using h
          · have hjDone : j ∈ done :=
              (Finset.mem_insert.mp hj).resolve_left hje
            have hkDone : k ∈ done :=
              (Finset.mem_insert.mp hk).resolve_left hke
            have hdis := P.special_outer_disjoint j hjDone k hkDone hjk
            have hmap : Disjoint
                ((P.special j \ mappedRoot P.rootEmbedding).map old)
                ((P.special k \ mappedRoot P.rootEmbedding).map old) :=
              (Finset.disjoint_map old).2 hdis
            simpa only [special, hje, hke, if_false, mappedRoot_trans,
              Finset.map_sdiff] using hmap
      positive_special_unique := by
        intro A hA hAroot j hj k hk hjEdge hkEdge
        by_cases hje : j = e
        · subst j
          by_cases hke : k = e
          · exact hke.symm
          · have hkDone : k ∈ done :=
              (Finset.mem_insert.mp hk).resolve_left hke
            obtain ⟨gk, hgkA, hgkSpecial⟩ := hkEdge
            have hgkOld : gk ⊆
                (Finset.univ : Finset P.V).map old := by
              intro x hx
              have hxSpecial : x ∈ (P.special k).map old := by
                simpa [special, hke] using
                  (Finset.mem_powersetCard.mp hgkSpecial).1 hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxSpecial
              exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
            obtain ⟨A₀, hA₀, hAeq⟩ :=
              positive_eq_mapped_old_of_common_old_edge
                A hA gk hgkA hgkOld
            obtain ⟨gj, hgjA, hgjSpecial⟩ := hjEdge
            have hgjOld : gj ⊆
                (Finset.univ : Finset P.V).map old := by
              intro x hx
              rw [hAeq] at hgjA
              have hxA : x ∈ A₀.map old :=
                (Finset.mem_powersetCard.mp hgjA).1 hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxA
              exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
            have hgjEdge : gj ⊆ edge.map old := by
              intro x hx
              have hxSpecial : x ∈ X.special := by
                simpa [special] using
                  (Finset.mem_powersetCard.mp hgjSpecial).1 hx
              have hxInter : x ∈ X.special ∩
                  (Finset.univ : Finset P.V).map old :=
                Finset.mem_inter.mpr ⟨hxSpecial, hgjOld hx⟩
              rw [hSpecialInterOld] at hxInter
              exact hxInter
            have hgjEq : gj = edge.map old := by
              apply Finset.eq_of_subset_of_card_le hgjEdge
              simp [edge, RootEdge.card,
                (Finset.mem_powersetCard.mp hgjA).2]
            have hedgeA₀ : edge ⊆ A₀ := by
              apply Finset.map_subset_map.mp
              rw [← hgjEq, ← hAeq]
              exact (Finset.mem_powersetCard.mp hgjA).1
            have hedgeA₀mem : edge ∈ A₀.powersetCard r :=
              Finset.mem_powersetCard.mpr ⟨hedgeA₀, by simp [edge]⟩
            have hedgeRoot : edge ∈
                (mappedRoot P.rootEmbedding).powersetCard r :=
              Finset.mem_powersetCard.mpr
                ⟨mappedRootEdge_subset_mappedRoot P.rootEmbedding e.1,
                  by simp [edge]⟩
            have hA₀root := P.positive_decomp.blocks_eq_of_common_edge
              hA₀ P.root_mem hedgeA₀mem hedgeRoot
            exfalso
            apply hAroot
            rw [hAeq, hA₀root, mappedRoot_trans]
        · have hjDone : j ∈ done :=
              (Finset.mem_insert.mp hj).resolve_left hje
          by_cases hke : k = e
          · subst k
            obtain ⟨gj, hgjA, hgjSpecial⟩ := hjEdge
            have hgjOld : gj ⊆
                (Finset.univ : Finset P.V).map old := by
              intro x hx
              have hxSpecial : x ∈ (P.special j).map old := by
                simpa [special, hje] using
                  (Finset.mem_powersetCard.mp hgjSpecial).1 hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxSpecial
              exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
            obtain ⟨A₀, hA₀, hAeq⟩ :=
              positive_eq_mapped_old_of_common_old_edge
                A hA gj hgjA hgjOld
            obtain ⟨gk, hgkA, hgkSpecial⟩ := hkEdge
            have hgkOld : gk ⊆
                (Finset.univ : Finset P.V).map old := by
              intro x hx
              rw [hAeq] at hgkA
              have hxA : x ∈ A₀.map old :=
                (Finset.mem_powersetCard.mp hgkA).1 hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxA
              exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
            have hgkEdge : gk ⊆ edge.map old := by
              intro x hx
              have hxSpecial : x ∈ X.special := by
                simpa [special] using
                  (Finset.mem_powersetCard.mp hgkSpecial).1 hx
              have hxInter : x ∈ X.special ∩
                  (Finset.univ : Finset P.V).map old :=
                Finset.mem_inter.mpr ⟨hxSpecial, hgkOld hx⟩
              rw [hSpecialInterOld] at hxInter
              exact hxInter
            have hgkEq : gk = edge.map old := by
              apply Finset.eq_of_subset_of_card_le hgkEdge
              simp [edge, RootEdge.card,
                (Finset.mem_powersetCard.mp hgkA).2]
            have hedgeA₀ : edge ⊆ A₀ := by
              apply Finset.map_subset_map.mp
              rw [← hgkEq, ← hAeq]
              exact (Finset.mem_powersetCard.mp hgkA).1
            have hedgeA₀mem : edge ∈ A₀.powersetCard r :=
              Finset.mem_powersetCard.mpr ⟨hedgeA₀, by simp [edge]⟩
            have hedgeRoot : edge ∈
                (mappedRoot P.rootEmbedding).powersetCard r :=
              Finset.mem_powersetCard.mpr
                ⟨mappedRootEdge_subset_mappedRoot P.rootEmbedding e.1,
                  by simp [edge]⟩
            have hA₀root := P.positive_decomp.blocks_eq_of_common_edge
              hA₀ P.root_mem hedgeA₀mem hedgeRoot
            exfalso
            apply hAroot
            rw [hAeq, hA₀root, mappedRoot_trans]
          · have hkDone : k ∈ done :=
              (Finset.mem_insert.mp hk).resolve_left hke
            obtain ⟨gj, hgjA, hgjSpecial⟩ := hjEdge
            have hgjOld : gj ⊆
                (Finset.univ : Finset P.V).map old := by
              intro x hx
              have hxSpecial : x ∈ (P.special j).map old := by
                simpa [special, hje] using
                  (Finset.mem_powersetCard.mp hgjSpecial).1 hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxSpecial
              exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
            obtain ⟨A₀, hA₀, hAeq⟩ :=
              positive_eq_mapped_old_of_common_old_edge
                A hA gj hgjA hgjOld
            have hA₀root : A₀ ≠ mappedRoot P.rootEmbedding := by
              intro hEq
              apply hAroot
              rw [hAeq, hEq, mappedRoot_trans]
            have pullWitness (g : Finset X.data.V)
                (hgA : g ∈ A.powersetCard r)
                (s : RootEdge q r) (hs : s ≠ e)
                (hgS : g ∈ (special s).powersetCard r) :
                ∃ g₀ ∈ A₀.powersetCard r,
                  g₀ ∈ (P.special s).powersetCard r := by
              have hgOld : g ⊆
                  (Finset.univ : Finset P.V).map old := by
                intro x hx
                have hxSpecial : x ∈ (P.special s).map old := by
                  simpa [special, hs] using
                    (Finset.mem_powersetCard.mp hgS).1 hx
                obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxSpecial
                exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
              have hgHost : g ∈ X.data.host :=
                X.data.positive_decomp.2.1 A hA hgA
              obtain ⟨g₀, hg₀Host, hg₀map⟩ :=
                X.host_inside_old g hgHost hgOld
              change g₀.map old = g at hg₀map
              have hg₀A : g₀ ⊆ A₀ := by
                apply Finset.map_subset_map.mp
                rw [hg₀map, ← hAeq]
                exact (Finset.mem_powersetCard.mp hgA).1
              have hg₀S : g₀ ⊆ P.special s := by
                apply Finset.map_subset_map.mp
                rw [hg₀map]
                simpa [special, hs] using
                  (Finset.mem_powersetCard.mp hgS).1
              have hg₀card : g₀.card = r := P.host_uniform g₀ hg₀Host
              exact ⟨g₀,
                Finset.mem_powersetCard.mpr ⟨hg₀A, hg₀card⟩,
                Finset.mem_powersetCard.mpr ⟨hg₀S, hg₀card⟩⟩
            have hjOldEdge := pullWitness gj hgjA j hje hgjSpecial
            obtain ⟨gk, hgkA, hgkSpecial⟩ := hkEdge
            have hkOldEdge := pullWitness gk hgkA k hke hgkSpecial
            exact P.positive_special_unique A₀ hA₀ hA₀root
              j hjDone k hkDone hjOldEdge hkOldEdge
      positive_inter_special_card_le := by
        intro j hj A hA
        by_cases hje : j = e
        · subst j
          simpa [special, tradeInter] using
            X.positive_inter_special_card_le A hA
        · have hjDone : j ∈ done :=
              (Finset.mem_insert.mp hj).resolve_left hje
          by_cases hle : (A ∩ special j).card ≤ r
          · exact hle
          · have hrle : r ≤ (A ∩ special j).card := Nat.le_of_not_ge hle
            obtain ⟨g, hgInter⟩ := Finset.powersetCard_nonempty.mpr hrle
            have hgData := Finset.mem_powersetCard.mp hgInter
            have hgA : g ∈ A.powersetCard r :=
              Finset.mem_powersetCard.mpr
                ⟨hgData.1.trans Finset.inter_subset_left, hgData.2⟩
            have hgSpecial : g ∈ (special j).powersetCard r :=
              Finset.mem_powersetCard.mpr
                ⟨hgData.1.trans Finset.inter_subset_right, hgData.2⟩
            have hgOld : g ⊆
                (Finset.univ : Finset P.V).map old := by
              intro x hx
              have hxSpecial : x ∈ (P.special j).map old := by
                simpa [special, hje] using
                  (Finset.mem_powersetCard.mp hgSpecial).1 hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxSpecial
              exact Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩
            obtain ⟨A₀, hA₀, hAeq⟩ :=
              positive_eq_mapped_old_of_common_old_edge
                A hA g hgA hgOld
            have hbound := P.positive_inter_special_card_le
              j hjDone A₀ hA₀
            rw [hAeq]
            simpa [special, hje, ← Finset.map_inter] using hbound
      special_isolated := by
        intro j hj A hA hsub
        by_cases hje : j = e
        · subst j
          have hresult := X.special_isolated A hA (by
            simpa [special, newRoot, root, old, tradeUnion, tradeMap,
              mappedRoot_trans] using hsub)
          simpa [special, newRoot, root, old, tradeUnion, tradeMap,
            mappedRoot_trans] using hresult
        · have hjDone : j ∈ done :=
            (Finset.mem_insert.mp hj).resolve_left hje
          have hsubOld : A ⊆ (Finset.univ : Finset P.V).map old := by
            intro x hx
            have hxUnion := hsub hx
            rcases Finset.mem_union.mp hxUnion with hxRoot | hxSpecial
            · have hxRoot' : x ∈ newRoot := by
                simpa [newRoot, root] using hxRoot
              obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxRoot'
              exact Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩
            · have hxMapped : x ∈ (P.special j).map old := by
                simpa [special, hje] using hxSpecial
              obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hxMapped
              exact Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩
          obtain ⟨A₀, hA₀, hmap₀⟩ := X.host_inside_old A hA hsubOld
          change A₀.map old = A at hmap₀
          have hsub₀ : A₀ ⊆ root ∪ P.special j := by
            have hmapSub : A₀.map old ⊆ (root ∪ P.special j).map old := by
              rw [hmap₀]
              simpa [special, hje, newRoot, Finset.map_union] using hsub
            exact Finset.map_subset_map.mp hmapSub
          rcases P.special_isolated j hjDone A₀ hA₀ hsub₀ with hroot | hspecial
          · left
            rw [mappedRoot_trans]
            change A ⊆ root.map old
            rw [← hmap₀]
            exact Finset.map_subset_map.mpr hroot
          · right
            change A ⊆ special j
            simp only [special, hje, if_false]
            rw [← hmap₀]
            exact Finset.map_subset_map.mpr hspecial }
  refine ⟨Q, ?_, ?_⟩
  · simpa [PartialExchange.SpecialTraceIsolated, Q, special, newRoot,
      root, old, tradeInter, tradeUnion, tradeMap, mappedRoot_trans] using
        X.special_trace_isolated
  · simpa [PartialExchange.SpecialPositiveInterBounded, Q, special,
      tradeInter] using X.positive_inter_special_card_le

/-- The trace-only projection of the strengthened insertion theorem. -/
theorem exists_partialExchange_insert_with_trace
    {q r : ℕ} (hqr : r < q) (B : BaseExchange q r)
    {done : Finset (RootEdge q r)} (P : PartialExchange q r done)
    (e : RootEdge q r) (he : e ∉ done) :
    ∃ Q : PartialExchange q r (insert e done), Q.SpecialTraceIsolated e := by
  obtain ⟨Q, htrace, _hbound⟩ :=
    exists_partialExchange_insert_with_trace_and_bound hqr B P e he
  exact ⟨Q, htrace⟩

/-- One more root edge can be isolated while preserving all previously
isolated negative blocks. -/
theorem exists_partialExchange_insert
    {q r : ℕ} (hqr : r < q) (B : BaseExchange q r)
    {done : Finset (RootEdge q r)} (P : PartialExchange q r done)
    (e : RootEdge q r) (he : e ∉ done) :
    Nonempty (PartialExchange q r (insert e done)) := by
  obtain ⟨Q, _⟩ :=
    exists_partialExchange_insert_with_trace hqr B P e he
  exact ⟨Q⟩

/-- Iterating the two-gluing step over any finite set of labelled root
edges produces the corresponding partial exchange. -/
theorem exists_partialExchange
    {q r : ℕ} (hqr : r < q) (done : Finset (RootEdge q r)) :
    Nonempty (PartialExchange q r done) := by
  have hq : 0 < q := by omega
  obtain ⟨B⟩ := exists_baseExchange q r hq hqr.le
  induction done using Finset.induction_on with
  | empty => exact exists_initialPartialExchange q r hq hqr.le
  | @insert e done he ih =>
      obtain ⟨P⟩ := ih
      exact exists_partialExchange_insert hqr B P e he

/-- The exchange gadget in which every edge of the labelled positive root
has its own isolated negative block. -/
abbrev FullExchange (q r : ℕ) :=
  PartialExchange q r (Finset.univ : Finset (RootEdge q r))

theorem exists_fullExchange {q r : ℕ} (hqr : r < q) :
    Nonempty (FullExchange q r) := by
  exact exists_partialExchange hqr Finset.univ

/-- A complete partial exchange may be constructed with any prescribed
root edge processed in the final round.  The last round retains both trace
isolation and the one-edge positive/special intersection bound. -/
theorem exists_completePartialExchange_with_trace_and_bound
    {q r : ℕ} (hqr : r < q)
    (e : RootEdge q r) :
    ∃ E : PartialExchange q r
        (insert e ((Finset.univ : Finset (RootEdge q r)).erase e)),
      E.SpecialTraceIsolated e ∧ E.SpecialPositiveInterBounded e := by
  have hq : 0 < q := by omega
  obtain ⟨B⟩ := exists_baseExchange q r hq hqr.le
  obtain ⟨P⟩ := exists_partialExchange hqr
    ((Finset.univ : Finset (RootEdge q r)).erase e)
  obtain ⟨E, hEtrace, hEbound⟩ :=
    exists_partialExchange_insert_with_trace_and_bound
    hqr B P e (by simp)
  exact ⟨E, hEtrace, hEbound⟩

/-- Trace-only projection of the final-round construction. -/
theorem exists_completePartialExchange_with_trace {q r : ℕ} (hqr : r < q)
    (e : RootEdge q r) :
    ∃ E : PartialExchange q r
        (insert e ((Finset.univ : Finset (RootEdge q r)).erase e)),
      E.SpecialTraceIsolated e := by
  obtain ⟨E, htrace, _hbound⟩ :=
    exists_completePartialExchange_with_trace_and_bound hqr e
  exact ⟨E, htrace⟩

end

end Erdos722.Exchange

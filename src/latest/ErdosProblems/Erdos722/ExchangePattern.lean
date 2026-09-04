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
import ErdosProblems.Erdos722.Exchange
import ErdosProblems.Erdos722.RootedEmbedding
import Mathlib

/-!
# A finite rooted pattern for the full exchange gadget

`Exchange.exists_fullExchange` produces a gadget on an abstract finite
vertex type.  Rooted random-greedy embedding is formulated on `Fin v`.
This file performs that harmless relabelling once and retains the positive
and negative decompositions and every isolated special block.
-/

namespace Erdos722.ExchangePattern

open Finset
open Erdos722.Transversal
open Erdos722.Exchange
open Erdos722.RootedEmbedding

noncomputable section

/-- A full exchange relabelled onto `Fin v`, ready to be used as a rooted
embedding pattern. -/
structure RelabeledFullExchange (q r : ℕ) where
  v : ℕ
  pattern : RootedPattern v r
  rootEmbedding : Fin q ↪ Fin v
  root_eq : pattern.root = mappedRoot rootEmbedding
  positive : Finset (Finset (Fin v))
  negative : Finset (Finset (Fin v))
  positive_decomp : IsUniformDecomposition pattern.edges positive q r
  negative_decomp : IsUniformDecomposition pattern.edges negative q r
  root_mem : mappedRoot rootEmbedding ∈ positive
  special : RootEdge q r → Finset (Fin v)
  special_mem : ∀ e, special e ∈ negative
  special_inter_root : ∀ e,
    special e ∩ mappedRoot rootEmbedding = mappedRootEdge rootEmbedding e.1
  special_outer_disjoint : ∀ e e', e ≠ e' →
    Disjoint (special e \ mappedRoot rootEmbedding)
      (special e' \ mappedRoot rootEmbedding)
  positive_special_unique : ∀ Q ∈ positive,
    Q ≠ mappedRoot rootEmbedding →
    ∀ e e',
      (∃ g ∈ Q.powersetCard r, g ∈ (special e).powersetCard r) →
      (∃ g ∈ Q.powersetCard r, g ∈ (special e').powersetCard r) →
      e = e'
  positive_inter_special_card_le : ∀ e, ∀ Q ∈ positive,
    (Q ∩ special e).card ≤ r
  special_isolated : ∀ e, ∀ A ∈ pattern.edges,
    A ⊆ pattern.root ∪ special e →
      A ⊆ pattern.root ∨ A ⊆ special e

/-- Strong admissibility for a distinguished special clique: every host
edge meets the two-clique root wholly on one of its two sides. -/
def RelabeledFullExchange.SpecialTraceIsolated
    (E : RelabeledFullExchange q r) (e : RootEdge q r) : Prop :=
  ∀ A ∈ E.pattern.edges,
    A ∩ (E.pattern.root ∪ E.special e) ⊆ E.pattern.root ∨
      A ∩ (E.pattern.root ∪ E.special e) ⊆ E.special e

/-- The distinguished negative root meets every positive block in at most
one `r`-edge worth of vertices. -/
def RelabeledFullExchange.SpecialPositiveInterBounded
    (E : RelabeledFullExchange q r) (e : RootEdge q r) : Prop :=
  ∀ Q ∈ E.positive, (Q ∩ E.special e).card ≤ r

@[simp] theorem RelabeledFullExchange.root_card
    (E : RelabeledFullExchange q r) : E.pattern.root.card = q := by
  rw [E.root_eq]
  exact card_mappedRoot E.rootEmbedding

theorem RelabeledFullExchange.root_nonempty
    (E : RelabeledFullExchange q r) (hq : 0 < q) :
    E.pattern.root.Nonempty := by
  apply Finset.card_pos.mp
  simpa using hq

theorem RelabeledFullExchange.root_card_lt_v
    (E : RelabeledFullExchange q r) (hqr : r < q) :
    E.pattern.root.card < E.v := by
  classical
  have hedgeFamily :
      ((Finset.univ : Finset (Fin q)).powersetCard r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard]
    simpa using Nat.choose_pos hqr.le
  obtain ⟨e, he⟩ := hedgeFamily
  let eRoot : RootEdge q r := ⟨e, he⟩
  have hspecialCard : (E.special eRoot).card = q :=
    E.negative_decomp.1 (E.special eRoot) (E.special_mem eRoot)
  have hnotSub : ¬E.special eRoot ⊆ E.pattern.root := by
    intro hsub
    have hinter : E.special eRoot ∩ E.pattern.root = E.special eRoot :=
      Finset.inter_eq_left.mpr hsub
    have hEq := E.special_inter_root eRoot
    rw [← E.root_eq, hinter] at hEq
    have hcards := congrArg Finset.card hEq
    rw [hspecialCard, card_mappedRootEdge, RootEdge.card] at hcards
    omega
  have hproper : E.pattern.root ⊂ (Finset.univ : Finset (Fin E.v)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    apply hnotSub
    rw [heq]
    exact Finset.subset_univ _
  have hcard := Finset.card_lt_card hproper
  simpa using hcard

theorem RelabeledFullExchange.root_not_mem_negative
    (E : RelabeledFullExchange q r) (hqr : r < q) :
    E.pattern.root ∉ E.negative := by
  classical
  have hedgeFamily :
      ((Finset.univ : Finset (Fin q)).powersetCard r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard]
    simpa using Nat.choose_pos hqr.le
  obtain ⟨e, he⟩ := hedgeFamily
  let eRoot : RootEdge q r := ⟨e, he⟩
  intro hrootNeg
  have hedgeRoot : mappedRootEdge E.rootEmbedding e ⊆ E.pattern.root := by
    rw [E.root_eq]
    exact mappedRootEdge_subset_mappedRoot E.rootEmbedding e
  have hedgeSpecial : mappedRootEdge E.rootEmbedding e ⊆ E.special eRoot := by
    intro x hx
    have : x ∈ E.special eRoot ∩ mappedRoot E.rootEmbedding := by
      rw [E.special_inter_root eRoot]
      exact hx
    exact (Finset.mem_inter.mp this).1
  have hcommonRoot : mappedRootEdge E.rootEmbedding e ∈
      E.pattern.root.powersetCard r := by
    exact Finset.mem_powersetCard.mpr
      ⟨hedgeRoot, by simpa using (Finset.mem_powersetCard.mp he).2⟩
  have hcommonSpecial : mappedRootEdge E.rootEmbedding e ∈
      (E.special eRoot).powersetCard r := by
    exact Finset.mem_powersetCard.mpr
      ⟨hedgeSpecial, by simpa using (Finset.mem_powersetCard.mp he).2⟩
  have heq := E.negative_decomp.blocks_eq_of_common_edge
    hrootNeg (E.special_mem eRoot) hcommonRoot hcommonSpecial
  have hinter := E.special_inter_root eRoot
  rw [← E.root_eq, ← heq, Finset.inter_self] at hinter
  have hcards := congrArg Finset.card hinter
  rw [E.root_card, card_mappedRootEdge, RootEdge.card] at hcards
  omega

/-! ## Cancelling blocks common to the two sides -/

/-- Remove every block occurring on both sides of a full exchange.  The
corresponding clique boundaries are removed from the common host.  This
does not alter the signed trade, the positive root, or any distinguished
negative block, and it makes the two block families literally disjoint. -/
def RelabeledFullExchange.cancelCommon
    (E : RelabeledFullExchange q r) (hqr : r < q) :
    RelabeledFullExchange q r := by
  classical
  let common := E.positive ∩ E.negative
  let edges := E.pattern.edges \
    common.biUnion (fun B ↦ B.powersetCard r)
  let positive := E.positive \ common
  let negative := E.negative \ common
  let pattern : RootedPattern E.v r :=
    { edges := edges
      root := E.pattern.root
      uniform := fun A hA ↦ E.pattern.uniform A (Finset.mem_sdiff.mp hA).1 }
  have hcommonPositive : common ⊆ E.positive := Finset.inter_subset_left
  have hcommonNegative : common ⊆ E.negative := Finset.inter_subset_right
  have hpositive : IsUniformDecomposition edges positive q r := by
    simpa [edges, positive] using E.positive_decomp.sdiff_blocks
      E.pattern.uniform hcommonPositive
  have hnegative : IsUniformDecomposition edges negative q r := by
    simpa [edges, negative] using E.negative_decomp.sdiff_blocks
      E.pattern.uniform hcommonNegative
  have hspecialNotPositive (e : RootEdge q r) : E.special e ∉ E.positive := by
    intro hpos
    have hbound := E.positive_inter_special_card_le e (E.special e) hpos
    have hcard : (E.special e).card = q :=
      E.negative_decomp.1 (E.special e) (E.special_mem e)
    rw [Finset.inter_self, hcard] at hbound
    omega
  exact
    { v := E.v
      pattern := pattern
      rootEmbedding := E.rootEmbedding
      root_eq := E.root_eq
      positive := positive
      negative := negative
      positive_decomp := hpositive
      negative_decomp := hnegative
      root_mem := Finset.mem_sdiff.mpr
        ⟨E.root_mem, fun hcommon ↦
          E.root_not_mem_negative hqr (by
            rw [E.root_eq]
            exact (Finset.mem_inter.mp hcommon).2)⟩
      special := E.special
      special_mem := fun e ↦ Finset.mem_sdiff.mpr
        ⟨E.special_mem e, fun hcommon ↦
          hspecialNotPositive e (Finset.mem_inter.mp hcommon).1⟩
      special_inter_root := E.special_inter_root
      special_outer_disjoint := E.special_outer_disjoint
      positive_special_unique := by
        intro Q hQ
        exact E.positive_special_unique Q (Finset.mem_sdiff.mp hQ).1
      positive_inter_special_card_le := by
        intro e Q hQ
        exact E.positive_inter_special_card_le e Q
          (Finset.mem_sdiff.mp hQ).1
      special_isolated := by
        intro e A hA
        exact E.special_isolated e A (Finset.mem_sdiff.mp hA).1 }

theorem RelabeledFullExchange.cancelCommon_disjoint
    (E : RelabeledFullExchange q r) (hqr : r < q) :
    Disjoint (E.cancelCommon hqr).positive (E.cancelCommon hqr).negative := by
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  exact (Finset.mem_sdiff.mp hBpos).2
    (Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hBpos).1, (Finset.mem_sdiff.mp hBneg).1⟩)

theorem RelabeledFullExchange.cancelCommon_trace
    (E : RelabeledFullExchange q r) (hqr : r < q)
    (e : RootEdge q r) (htrace : E.SpecialTraceIsolated e) :
    (E.cancelCommon hqr).SpecialTraceIsolated e := by
  intro A hA
  exact htrace A (Finset.mem_sdiff.mp hA).1

theorem RelabeledFullExchange.cancelCommon_bound
    (E : RelabeledFullExchange q r) (hqr : r < q)
    (e : RootEdge q r) (hbound : E.SpecialPositiveInterBounded e) :
    (E.cancelCommon hqr).SpecialPositiveInterBounded e := by
  intro Q hQ
  exact hbound Q (Finset.mem_sdiff.mp hQ).1

/-- The root for a two-clique elimination move: the designated positive
root together with one isolated negative special block. -/
def RelabeledFullExchange.eliminationPattern
    (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    RootedPattern E.v r :=
  { edges := E.pattern.edges
    root := E.pattern.root ∪ E.special e
    uniform := E.pattern.uniform }

@[simp] theorem RelabeledFullExchange.eliminationPattern_root
    (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    (E.eliminationPattern e).root = E.pattern.root ∪ E.special e := rfl

theorem RelabeledFullExchange.eliminationPattern_root_card
    (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    (E.eliminationPattern e).root.card = 2 * q - r := by
  have hspecial : (E.special e).card = q :=
    E.negative_decomp.1 (E.special e) (E.special_mem e)
  have hinter : E.pattern.root ∩ E.special e =
      mappedRootEdge E.rootEmbedding e.1 := by
    rw [Finset.inter_comm, E.root_eq, E.special_inter_root e]
  have hcount := Finset.card_union_add_card_inter E.pattern.root (E.special e)
  rw [hinter, E.root_card, hspecial,
    card_mappedRootEdge, RootEdge.card] at hcount
  have hrq : r ≤ q := by
    have hcard := Finset.card_le_univ e.1
    simpa [RootEdge.card] using hcard
  change #(E.pattern.root ∪ E.special e) = 2 * q - r
  omega

lemma exists_rootEdge_ne (hr : 0 < r) (hqr : r < q)
    (e : RootEdge q r) : ∃ e' : RootEdge q r, e' ≠ e := by
  classical
  have hchoose : 1 < Nat.choose q r := by
    have hpos : 0 < Nat.choose q r := Nat.choose_pos hqr.le
    have hne : Nat.choose q r ≠ 1 := by
      intro heq
      rcases Nat.choose_eq_one_iff.mp heq with hrzero | hqr'
      · exact hr.ne' hrzero
      · exact hqr.ne hqr'.symm
    omega
  have hcard : 1 <
      ((Finset.univ : Finset (Fin q)).powersetCard r).card := by
    simpa using hchoose
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  by_cases hae : a = e.1
  · refine ⟨⟨b, hb⟩, ?_⟩
    intro hbe
    apply hab
    exact hae.trans (congrArg Subtype.val hbe).symm
  · exact ⟨⟨a, ha⟩, fun hae' ↦ hae (congrArg Subtype.val hae')⟩

theorem RelabeledFullExchange.eliminationPattern_root_card_lt_v
    (E : RelabeledFullExchange q r) (hr : 0 < r) (hqr : r < q)
    (e : RootEdge q r) :
    (E.eliminationPattern e).root.card < E.v := by
  classical
  obtain ⟨e', he'⟩ := exists_rootEdge_ne hr hqr e
  have hspecial' : (E.special e').card = q :=
    E.negative_decomp.1 (E.special e') (E.special_mem e')
  have hinter' : E.pattern.root ∩ E.special e' =
      mappedRootEdge E.rootEmbedding e'.1 := by
    rw [Finset.inter_comm, E.root_eq, E.special_inter_root e']
  have houterCard : (E.special e' \ E.pattern.root).card = q - r := by
    rw [Finset.card_sdiff, hinter', hspecial',
      card_mappedRootEdge, RootEdge.card]
  have houterNonempty : (E.special e' \ E.pattern.root).Nonempty := by
    rw [← Finset.card_pos, houterCard]
    omega
  obtain ⟨x, hx⟩ := houterNonempty
  have hxNotSpecial : x ∉ E.special e := by
    intro hxe
    have hxOuterE : x ∈ E.special e \ E.pattern.root :=
      Finset.mem_sdiff.mpr ⟨hxe, (Finset.mem_sdiff.mp hx).2⟩
    exact Finset.disjoint_left.mp
      (E.special_outer_disjoint e' e he')
      (by simpa [E.root_eq] using hx)
      (by simpa [E.root_eq] using hxOuterE)
  have hxNotRoot : x ∉ (E.eliminationPattern e).root := by
    simp only [RelabeledFullExchange.eliminationPattern_root,
      Finset.mem_union]
    exact fun h ↦ h.elim (Finset.mem_sdiff.mp hx).2 hxNotSpecial
  have hproper : (E.eliminationPattern e).root ⊂
      (Finset.univ : Finset (Fin E.v)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    apply hxNotRoot
    rw [heq]
    exact Finset.mem_univ x
  simpa using Finset.card_lt_card hproper

/-- The checked algebraic full exchange has a finite relabelling with a
distinguished special block satisfying strong trace isolation. -/
theorem exists_relabeledFullExchange_with_trace {q r : ℕ} (hqr : r < q) :
    ∃ E : RelabeledFullExchange q r,
      ∃ e : RootEdge q r,
        E.SpecialTraceIsolated e ∧ E.SpecialPositiveInterBounded e := by
  classical
  have hedgeFamily :
      ((Finset.univ : Finset (Fin q)).powersetCard r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard]
    simpa using Nat.choose_pos hqr.le
  obtain ⟨edge, hedge⟩ := hedgeFamily
  let e₀ : RootEdge q r := ⟨edge, hedge⟩
  obtain ⟨E, hEtrace, hEbound⟩ :=
    exists_completePartialExchange_with_trace_and_bound hqr e₀
  let : DecidableEq E.V := E.decEq
  let : Fintype E.V := E.fintype
  let σ : E.V ≃ Fin (Fintype.card E.V) := Fintype.equivFin E.V
  let emb : E.V ↪ Fin (Fintype.card E.V) := σ.toEmbedding
  let rootEmbedding : Fin q ↪ Fin (Fintype.card E.V) :=
    E.rootEmbedding.trans emb
  let host := mapFamily emb E.host
  let positive := mapFamily emb E.positive
  let negative := mapFamily emb E.negative
  let pattern : RootedPattern (Fintype.card E.V) r :=
    { edges := host
      root := mappedRoot rootEmbedding
      uniform := by
        intro A hA
        obtain ⟨A₀, hA₀, rfl⟩ := mem_mapFamily.mp hA
        simpa [host, emb] using E.host_uniform A₀ hA₀ }
  let special : RootEdge q r → Finset (Fin (Fintype.card E.V)) :=
    fun e ↦ (E.special e).map emb
  let R : RelabeledFullExchange q r := by
    refine {
      v := Fintype.card E.V
      pattern := pattern
      rootEmbedding := rootEmbedding
      root_eq := rfl
      positive := positive
      negative := negative
      positive_decomp := ?_
      negative_decomp := ?_
      root_mem := ?_
      special := special
      special_mem := ?_
      special_inter_root := ?_
      special_outer_disjoint := ?_
      positive_special_unique := ?_
      positive_inter_special_card_le := ?_
      special_isolated := ?_ }
    · simpa [pattern, host, positive, emb] using
        E.positive_decomp.map emb
    · simpa [pattern, host, negative, emb] using
        E.negative_decomp.map emb
    · apply mem_mapFamily.mpr
      refine ⟨mappedRoot E.rootEmbedding, E.root_mem, ?_⟩
      exact (mappedRoot_trans E.rootEmbedding emb).symm
    · intro e
      exact mem_mapFamily.mpr
        ⟨E.special e, E.special_mem e (by simp), rfl⟩
    · intro e
      dsimp [special]
      have hroot : mappedRoot rootEmbedding =
          (mappedRoot E.rootEmbedding).map emb := by
        simpa [rootEmbedding] using mappedRoot_trans E.rootEmbedding emb
      have hedge : mappedRootEdge rootEmbedding e.1 =
          (mappedRootEdge E.rootEmbedding e.1).map emb := by
        simpa [rootEmbedding] using mappedRootEdge_trans E.rootEmbedding emb e.1
      rw [hroot, ← Finset.map_inter,
        E.special_inter_root e (by simp), hedge]
    · intro e e' hee'
      have h := E.special_outer_disjoint e (by simp)
        e' (by simp) hee'
      have hmap := (Finset.disjoint_map emb).2 h
      have hroot : mappedRoot rootEmbedding =
          (mappedRoot E.rootEmbedding).map emb := by
        simpa [rootEmbedding] using mappedRoot_trans E.rootEmbedding emb
      simpa [special, Finset.map_sdiff, hroot] using hmap
    · intro Q hQ hQroot e e' heEdge he'Edge
      obtain ⟨Q₀, hQ₀, rfl⟩ := mem_mapFamily.mp hQ
      have hQ₀root : Q₀ ≠ mappedRoot E.rootEmbedding := by
        intro hEq
        apply hQroot
        rw [hEq]
        exact (mappedRoot_trans E.rootEmbedding emb).symm
      have pullEdge (a : RootEdge q r)
          (ha : ∃ g ∈ (Q₀.map emb).powersetCard r,
            g ∈ (special a).powersetCard r) :
          ∃ g₀ ∈ Q₀.powersetCard r,
            g₀ ∈ (E.special a).powersetCard r := by
        obtain ⟨g, hgQ, hgS⟩ := ha
        let g₀ : Finset E.V := g.map σ.symm.toEmbedding
        have hg₀map : g₀.map emb = g := by
          simp [g₀, emb, σ, Finset.map_map]
        have hg₀Q : g₀ ⊆ Q₀ := by
          apply Finset.map_subset_map.mp
          rw [hg₀map]
          exact (Finset.mem_powersetCard.mp hgQ).1
        have hg₀S : g₀ ⊆ E.special a := by
          apply Finset.map_subset_map.mp
          rw [hg₀map]
          simpa [special] using (Finset.mem_powersetCard.mp hgS).1
        have hg₀card : g₀.card = r := by
          rw [← Finset.card_map emb, hg₀map]
          exact (Finset.mem_powersetCard.mp hgQ).2
        exact ⟨g₀, Finset.mem_powersetCard.mpr ⟨hg₀Q, hg₀card⟩,
          Finset.mem_powersetCard.mpr ⟨hg₀S, hg₀card⟩⟩
      exact E.positive_special_unique Q₀ hQ₀ hQ₀root
        e (by simp) e' (by simp) (pullEdge e heEdge) (pullEdge e' he'Edge)
    · intro e Q hQ
      obtain ⟨Q₀, hQ₀, rfl⟩ := mem_mapFamily.mp hQ
      have hbound := E.positive_inter_special_card_le e (by simp) Q₀ hQ₀
      simpa [special, ← Finset.map_inter] using hbound
    · intro e A hA hsub
      obtain ⟨A₀, hA₀, rfl⟩ := mem_mapFamily.mp hA
      have hroot : mappedRoot rootEmbedding =
          (mappedRoot E.rootEmbedding).map emb := by
        simpa [rootEmbedding] using mappedRoot_trans E.rootEmbedding emb
      have hsub₀ : A₀ ⊆ mappedRoot E.rootEmbedding ∪ E.special e := by
        have hmapSub : A₀.map emb ⊆
            (mappedRoot E.rootEmbedding ∪ E.special e).map emb := by
          simpa [pattern, special, hroot, Finset.map_union] using hsub
        exact Finset.map_subset_map.mp hmapSub
      rcases E.special_isolated e (by simp) A₀ hA₀ hsub₀ with
        hroot₀ | hspecial₀
      · left
        have hmapRoot : A₀.map emb ⊆
            (mappedRoot E.rootEmbedding).map emb :=
          Finset.map_subset_map.mpr hroot₀
        simpa [pattern, hroot] using hmapRoot
      · right
        have hmapSpecial : A₀.map emb ⊆ (E.special e).map emb :=
          Finset.map_subset_map.mpr hspecial₀
        simpa [special] using hmapSpecial
  refine ⟨R, e₀, ?_, ?_⟩
  · intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := mem_mapFamily.mp hA
    rcases hEtrace A₀ hA₀ with hrootTrace | hspecialTrace
    · left
      have hmap :
          (tradeInter E.toTradeData A₀
            (tradeUnion E.toTradeData (mappedRoot E.rootEmbedding)
              (E.special e₀))).map emb ⊆
              (mappedRoot E.rootEmbedding).map emb :=
        Finset.map_subset_map.mpr hrootTrace
      simpa [RelabeledFullExchange.SpecialTraceIsolated, R, pattern, special,
        rootEmbedding, tradeInter, tradeUnion, Finset.map_inter,
        Finset.map_union, mappedRoot_trans] using hmap
    · right
      have hmap :
          (tradeInter E.toTradeData A₀
            (tradeUnion E.toTradeData (mappedRoot E.rootEmbedding)
              (E.special e₀))).map emb ⊆ (E.special e₀).map emb :=
        Finset.map_subset_map.mpr hspecialTrace
      simpa [RelabeledFullExchange.SpecialTraceIsolated, R, pattern, special,
        rootEmbedding, tradeInter, tradeUnion, Finset.map_inter,
        Finset.map_union, mappedRoot_trans] using hmap
  · intro Q hQ
    obtain ⟨Q₀, hQ₀, rfl⟩ := mem_mapFamily.mp hQ
    have hbound := hEbound Q₀ hQ₀
    simpa [RelabeledFullExchange.SpecialPositiveInterBounded, R, positive,
      special, tradeInter, ← Finset.map_inter] using hbound

/-- Strengthened finite package used by Booleanization: common blocks of
the two trade sides have been cancelled once and for all. -/
theorem exists_relabeledFullExchange_with_trace_and_disjoint
    {q r : ℕ} (hqr : r < q) :
    ∃ E : RelabeledFullExchange q r,
      ∃ e : RootEdge q r,
        E.SpecialTraceIsolated e ∧
          E.SpecialPositiveInterBounded e ∧
          Disjoint E.positive E.negative := by
  obtain ⟨E, e, htrace, hbound⟩ :=
    exists_relabeledFullExchange_with_trace hqr
  let E' := E.cancelCommon hqr
  exact ⟨E', e, E.cancelCommon_trace hqr e htrace,
    E.cancelCommon_bound hqr e hbound, E.cancelCommon_disjoint hqr⟩

/-- The checked algebraic full exchange has a canonical finite relabelling. -/
theorem exists_relabeledFullExchange {q r : ℕ} (hqr : r < q) :
    Nonempty (RelabeledFullExchange q r) := by
  obtain ⟨E, _e, _hproperties⟩ := exists_relabeledFullExchange_with_trace hqr
  exact ⟨E⟩

end

end Erdos722.ExchangePattern

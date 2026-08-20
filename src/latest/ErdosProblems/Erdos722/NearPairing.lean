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
import ErdosProblems.Erdos722.ExchangeEliminationEmbedding
import Mathlib

/-!
# Pairing the near splitting cliques

The Boolean boundary condition says that at each input edge there are at
least as many positive near occurrences as negative ones.  This file makes
that fibrewise matching finite and explicit, then turns each matched pair
into an `EliminationPair` for the first elimination bank.
-/

namespace Erdos722.NearPairing

open Finset
open Erdos722.Transversal
open Erdos722.Reserve
open Erdos722.Exchange
open Erdos722.ExchangePattern
open Erdos722.ExchangeEmbedding
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.RootedFamilyMultiEmbedding
open Erdos722.RootedFamilyAsymptotic
open Erdos722.LocalDecoderAsymptotic
open Erdos722.ExchangeEliminationEmbedding
open Erdos722.AdaptiveChernoff
open Filter

noncomputable section

/-- If a face is split across two special blocks with the same distinguished
root edge, and is not contained in the first block, then the second
embedding sends a non-root pattern vertex into that face.  This is the
geometric implication used to dominate every newly created mixed pair by
an outside-root-touch counter. -/
theorem mixedSpecialFace_current_touchesOutsideRoot
    {E : RelabeledFullExchange k r}
    (previous current : Fin E.v ↪ Fin n)
    (previousEdge currentEdge : RootEdge k r)
    (J : Finset (Fin n))
    (hedge : mapEdge (E.rootEmbedding.trans previous) previousEdge.1 =
      mapEdge (E.rootEmbedding.trans current) currentEdge.1)
    (hunion : J ⊆ mappedSpecial E previous previousEdge ∪
      mappedSpecial E current currentEdge)
    (hnotPrevious : ¬J ⊆ mappedSpecial E previous previousEdge) :
    OutsideRootTouches E.pattern.root J current := by
  classical
  obtain ⟨y, hyJ, hyNotPrevious⟩ := Finset.not_subset.mp hnotPrevious
  have hyCurrent : y ∈ mappedSpecial E current currentEdge := by
    rcases Finset.mem_union.mp (hunion hyJ) with hyPrevious | hyCurrent
    · exact False.elim (hyNotPrevious hyPrevious)
    · exact hyCurrent
  have hyNotRoot : y ∉ mapEdge current E.pattern.root := by
    intro hyRoot
    have hyCurrentInter : y ∈
        mappedSpecial E current currentEdge ∩
          mapEdge current E.pattern.root :=
      Finset.mem_inter.mpr ⟨hyCurrent, hyRoot⟩
    have hyCurrentEdge : y ∈
        mapEdge (E.rootEmbedding.trans current) currentEdge.1 := by
      rw [← mappedSpecial_inter_mappedRoot E current currentEdge]
      exact hyCurrentInter
    have hyPreviousEdge : y ∈
        mapEdge (E.rootEmbedding.trans previous) previousEdge.1 := by
      rw [hedge]
      exact hyCurrentEdge
    have hyPreviousInter : y ∈
        mappedSpecial E previous previousEdge ∩
          mapEdge previous E.pattern.root := by
      rw [mappedSpecial_inter_mappedRoot E previous previousEdge]
      exact hyPreviousEdge
    exact hyNotPrevious (Finset.mem_inter.mp hyPreviousInter).1
  change y ∈ (E.special currentEdge).map current at hyCurrent
  obtain ⟨x, hxSpecial, hxy⟩ := Finset.mem_map.mp hyCurrent
  have hxNotRoot : x ∉ E.pattern.root := by
    intro hxRoot
    apply hyNotRoot
    exact Finset.mem_map.mpr ⟨x, hxRoot, hxy⟩
  exact ⟨x, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ x, hxNotRoot⟩, hxy ▸ hyJ⟩

/-- Finite fibrewise Hall matching in the special case where every edge is
confined to one key fibre. -/
theorem exists_fiberwiseEmbedding
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (positive negative : Finset α) (key : α → β)
    (hcard : ∀ b : β,
      (negative.filter fun x ↦ key x = b).card ≤
        (positive.filter fun x ↦ key x = b).card) :
    ∃ f : ↥negative ↪ ↥positive, ∀ x, key (f x).1 = key x.1 := by
  classical
  let negFiber (b : β) := negative.filter fun x ↦ key x = b
  let posFiber (b : β) := positive.filter fun x ↦ key x = b
  let emb (b : β) : ↥(negFiber b) ↪ ↥(posFiber b) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa [negFiber, posFiber] using hcard b))
  let fiberMap (b : β) (x : α) : α :=
    if hx : x ∈ negFiber b then (emb b ⟨x, hx⟩).1 else x
  have hfiberMap_mem (x : ↥negative) :
      fiberMap (key x.1) x.1 ∈ positive := by
    have hxFiber : x.1 ∈ negFiber (key x.1) :=
      Finset.mem_filter.mpr ⟨x.2, rfl⟩
    change (if hx : x.1 ∈ negFiber (key x.1) then
      (emb (key x.1) ⟨x.1, hx⟩).1 else x.1) ∈ positive
    rw [dif_pos hxFiber]
    exact (Finset.mem_filter.mp (emb (key x.1) ⟨x.1, hxFiber⟩).2).1
  let fval (x : ↥negative) : ↥positive :=
    ⟨fiberMap (key x.1) x.1, hfiberMap_mem x⟩
  have hfkey (x : ↥negative) : key (fval x).1 = key x.1 := by
    have hxFiber : x.1 ∈ negFiber (key x.1) :=
      Finset.mem_filter.mpr ⟨x.2, rfl⟩
    change key (if hx : x.1 ∈ negFiber (key x.1) then
      (emb (key x.1) ⟨x.1, hx⟩).1 else x.1) = key x.1
    rw [dif_pos hxFiber]
    exact (Finset.mem_filter.mp (emb (key x.1) ⟨x.1, hxFiber⟩).2).2
  have hfinj : Function.Injective fval := by
    intro x y hxy
    have hkey : key x.1 = key y.1 := by
      rw [← hfkey x, ← hfkey y, hxy]
    have hxFiber : x.1 ∈ negFiber (key x.1) :=
      Finset.mem_filter.mpr ⟨x.2, rfl⟩
    have hyFiber : y.1 ∈ negFiber (key x.1) :=
      Finset.mem_filter.mpr ⟨y.2, hkey.symm⟩
    have hmap : fiberMap (key x.1) x.1 = fiberMap (key x.1) y.1 := by
      calc
        fiberMap (key x.1) x.1 = fiberMap (key y.1) y.1 :=
          congrArg Subtype.val hxy
        _ = fiberMap (key x.1) y.1 :=
          (congrArg (fun b ↦ fiberMap b y.1) hkey).symm
    have hemb :
        emb (key x.1) ⟨x.1, hxFiber⟩ =
          emb (key x.1) ⟨y.1, hyFiber⟩ := by
      apply Subtype.ext
      simpa [fiberMap, hxFiber, hyFiber] using hmap
    have hsource := (emb (key x.1)).injective hemb
    apply Subtype.ext
    simpa using congrArg Subtype.val hsource
  exact ⟨⟨fval, hfinj⟩, hfkey⟩

theorem incidenceCount_image_of_injective
    {X : Type*} [DecidableEq X]
    (s : Finset X) (F : X → Finset (Fin n))
    (hF : Set.InjOn F s) (g : Finset (Fin n)) :
    Transversal.incidenceCount (s.image F) g =
      ∑ x ∈ s, if g ⊆ F x then 1 else 0 := by
  rw [Transversal.incidenceCount]
  have hfilter : (s.image F).filter (fun B ↦ g ⊆ B) =
      (s.filter fun x ↦ g ⊆ F x).image F := by
    ext B
    constructor
    · intro hB
      have hm := Finset.mem_filter.mp hB
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm.1
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hx, hm.2⟩, rfl⟩
    · intro hB
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hB
      have hm := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨x, hm.1, rfl⟩, hm.2⟩
  rw [hfilter, Finset.card_image_of_injOn (fun x hx y hy hxy ↦
    hF (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)]
  simp

abbrev NearOccurrence
    (roots : Finset (Finset (Fin n))) (multiplicity k r : ℕ) :=
  (↥roots × Fin multiplicity) × RootEdge k r

/-- Ground codimension-one faces tracked by the splitting bank. -/
abbrev SplittingFace (n r : ℕ) :=
  {J : Finset (Fin n) // J ∈ Typicality.uniformEdges n (r - 1)}

/-- Uniform numerator for one outside-root-touch counter. -/
def splittingTouchNumerator (E : RelabeledFullExchange k r) (n : ℕ) : ℕ :=
  (E.v - E.pattern.root.card) * (r - 1) *
    n ^ (E.v - (E.pattern.root.card + 1))

@[simp] theorem card_splittingFace (n r : ℕ) :
    Fintype.card (SplittingFace n r) = Nat.choose n (r - 1) := by
  classical
  simp [SplittingFace, Typicality.uniformEdges]

theorem card_splittingCounterTargets_le
    (P : RootedPattern v r) (n : ℕ) :
    Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) ≤
      (P.freeEdges.card + 1) * n ^ (r - 1) := by
  calc
    Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) =
        Fintype.card (RelevantFaceLoadTarget P n) +
          Fintype.card (SplittingFace n r) := by simp
    _ ≤ P.freeEdges.card * Nat.choose n (r - 1) +
          Nat.choose n (r - 1) :=
      Nat.add_le_add (card_relevantFaceLoadTarget_le P n)
        (le_of_eq (card_splittingFace n r))
    _ = (P.freeEdges.card + 1) * Nat.choose n (r - 1) := by
      rw [Nat.add_mul, one_mul]
    _ ≤ (P.freeEdges.card + 1) * n ^ (r - 1) :=
      Nat.mul_le_mul_left _ (Nat.choose_le_pow n (r - 1))

/-- Adding one ground-face counter per codimension-one face preserves the
polynomial-versus-exponential union bound used by the rooted construction. -/
theorem eventually_splittingCounter_exponential_union_bound
    (P : RootedPattern v r) (hr : 0 < r) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) < 1 := by
  let c := decoderPathExponent d
  let M := decoderPathMultiplier v r
  let C0 : ℝ := P.freeEdges.card + 1
  have hc : 0 < c := by
    simpa [c] using (decoder_exponent_identities hd).2.2.2
  have hMnat : 0 < M := decoderPathMultiplier_pos v r hr
  have hM : 0 < (M : ℝ) := by exact_mod_cast hMnat
  have hdecay := tendsto_pow_mul_exp_neg_rpow_atTop (r - 1) hc
    (show (0 : ℝ) < (M : ℝ) / 4 by positivity)
  have hconst : Tendsto
      (fun x : ℝ ↦ C0 *
        (x ^ (r - 1) * Real.exp (-((M : ℝ) / 4) * x ^ c)))
      atTop (nhds 0) := by
    have hC0 : Tendsto (fun _ : ℝ ↦ C0) atTop (nhds C0) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hC0.mul hdecay
  have hnat := hconst.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C0 * ((n : ℝ) ^ (r - 1) *
        Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have hcap := eventually_half_path_rpow_mul_le_cap
    (v := v) hr hd
  filter_upwards [hsmall, hcap] with n hnsmall hcap
  have hcardNat : Fintype.card
      (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) ≤
        (P.freeEdges.card + 1) * n ^ (r - 1) :=
    card_splittingCounterTargets_le P n
  have hcardReal :
      (Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) : ℝ) ≤
        (P.freeEdges.card + 1 : ℕ) * (n : ℝ) ^ (r - 1) := by
    exact_mod_cast hcardNat
  have hspent : (M : ℝ) / 4 * (n : ℝ) ^ c ≤
      (decoderPathCap v r d n : ℝ) / 2 := by
    calc
      (M : ℝ) / 4 * (n : ℝ) ^ c =
          ((M : ℝ) * ((n : ℝ) ^ c / 2)) / 2 := by ring
      _ ≤ (decoderPathCap v r d n : ℝ) / 2 := by
        simpa [M, c] using
          div_le_div_of_nonneg_right hcap (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) ≤
        (P.freeEdges.card + 1 : ℕ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) := by
      gcongr
    _ ≤ (P.freeEdges.card + 1 : ℕ) * (n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c) := by
      gcongr
      convert neg_le_neg hspent using 1 <;> ring
    _ = C0 * ((n : ℝ) ^ (r - 1) *
          Real.exp (-((M : ℝ) / 4) * (n : ℝ) ^ c)) := by
      dsimp [C0]
      push_cast
      ring
    _ < 1 := hnsmall

theorem eventually_splittingCounter_scaled_exponential_union_bound
    (P : RootedPattern v r) (hr : 0 < r) (hd : 0 < d)
    (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      (Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) : ℝ) *
          Real.exp (-(scaledDecoderPathCap scale v r d n : ℝ) / 2) < 1 := by
  have hbase := eventually_splittingCounter_exponential_union_bound P hr hd
  filter_upwards [hbase] with n hn
  have hcapNat : decoderPathCap v r d n ≤
      scaledDecoderPathCap scale v r d n := by
    unfold scaledDecoderPathCap
    calc
      decoderPathCap v r d n = 1 * decoderPathCap v r d n := by simp
      _ ≤ scale * decoderPathCap v r d n :=
        Nat.mul_le_mul_right _ hscale
  have hcapReal : (decoderPathCap v r d n : ℝ) ≤
      (scaledDecoderPathCap scale v r d n : ℝ) := by
    exact_mod_cast hcapNat
  calc
    (Fintype.card
        (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) : ℝ) *
          Real.exp (-(scaledDecoderPathCap scale v r d n : ℝ) / 2) ≤
        (Fintype.card
          (Sum (RelevantFaceLoadTarget P n) (SplittingFace n r)) : ℝ) *
          Real.exp (-(decoderPathCap v r d n : ℝ) / 2) := by
      gcongr
    _ < 1 := hn

def nearOccurrenceBlock
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r) : Finset (Fin n) :=
  mappedSpecial E (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2

def nearOccurrenceEdge
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r) : Finset (Fin n) :=
  mapEdge
    (E.rootEmbedding.trans (S.embedding O.1.1.1 O.1.1.2 O.1.2)) O.2.1

def positiveNearOccurrences
    {n k r m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) :
    Finset (NearOccurrence roots (2 * m) k r) :=
  (positiveBankSelection (m := m) roots θ).product Finset.univ

def negativeNearOccurrences
    {n k r m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) :
    Finset (NearOccurrence roots (2 * m) k r) :=
  (negativeBankSelection (m := m) roots θ).product Finset.univ

@[simp] theorem nearOccurrenceEdge_card
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r) :
    (nearOccurrenceEdge S O).card = r := by
  simp [nearOccurrenceEdge, RootEdge.card]

@[simp] theorem nearOccurrenceBlock_card
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r) :
    (nearOccurrenceBlock S O).card = k := by
  exact mappedSpecial_card E _ O.2

theorem nearOccurrenceEdge_mem_root
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r) :
    nearOccurrenceEdge S O ∈ O.1.1.1.powersetCard r := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, nearOccurrenceEdge_card S O⟩
  rw [← S.root_image O.1.1.1 O.1.1.2 O.1.2]
  intro x hx
  change x ∈ mapEdge
    (E.rootEmbedding.trans (S.embedding O.1.1.1 O.1.1.2 O.1.2)) O.2.1 at hx
  have hxInter : x ∈ nearOccurrenceBlock S O ∩
      mapEdge (S.embedding O.1.1.1 O.1.1.2 O.1.2) E.pattern.root := by
    change x ∈ mappedSpecial E
      (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 ∩
        mapEdge (S.embedding O.1.1.1 O.1.1.2 O.1.2) E.pattern.root
    rw [mappedSpecial_inter_mappedRoot E _ O.2]
    exact hx
  exact (Finset.mem_inter.mp hxInter).2

theorem nearOccurrenceEdge_subset_block
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r) :
    nearOccurrenceEdge S O ⊆ nearOccurrenceBlock S O := by
  intro x hx
  change x ∈ mapEdge
    (E.rootEmbedding.trans (S.embedding O.1.1.1 O.1.1.2 O.1.2)) O.2.1 at hx
  have hxInter : x ∈ nearOccurrenceBlock S O ∩
      mapEdge (S.embedding O.1.1.1 O.1.1.2 O.1.2) E.pattern.root := by
    change x ∈ mappedSpecial E
      (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 ∩
        mapEdge (S.embedding O.1.1.1 O.1.1.2 O.1.2) E.pattern.root
    rw [mappedSpecial_inter_mappedRoot E _ O.2]
    exact hx
  exact (Finset.mem_inter.mp hxInter).1

/-- An `r`-edge of a near block which lies in the allocator's forbidden
family is necessarily the distinguished input edge.  Every other edge of
the special block is an image free edge, and hence avoids `forbidden`. -/
theorem nearOccurrenceBlock_edge_eq_distinguished_of_mem_forbidden
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (O : NearOccurrence roots multiplicity k r)
    {g : Finset (Fin n)}
    (hg : g ∈ (nearOccurrenceBlock S O).powersetCard r)
    (hgForbidden : g ∈ forbidden) :
    g = nearOccurrenceEdge S O := by
  have hgBlock : g ∈
      (mappedSpecial E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2).powersetCard r := by
    simpa [nearOccurrenceBlock] using hg
  rcases mappedSpecial_edge_eq_or_free E
      (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 hgBlock with heq | hfree
  · simpa [nearOccurrenceEdge] using heq
  · exact (Finset.disjoint_left.mp
      (S.free_disjoint_forbidden O.1.1.1 O.1.1.2 O.1.2)
      hfree hgForbidden).elim

/-- Distinct labelled occurrences give distinct special blocks. -/
theorem nearOccurrenceBlock_injective
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden) :
    Function.Injective (nearOccurrenceBlock S) := by
  intro O O' hblock
  by_cases hindex : O.1 = O'.1
  · have hblock' : mappedSpecial E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 =
      mappedSpecial E
        (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2 := by
      simpa [nearOccurrenceBlock] using hblock
    have hedge : O.2 = O'.2 := by
      have hinter := mappedSpecial_inter_mappedRoot E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2
      have hinter' := mappedSpecial_inter_mappedRoot E
        (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2
      have hInterEq : mappedSpecial E
          (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 ∩
            mapEdge (S.embedding O.1.1.1 O.1.1.2 O.1.2) E.pattern.root =
          mappedSpecial E
            (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2 ∩
            mapEdge (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2)
              E.pattern.root := by
        rw [hblock', hindex]
      have hmapEdge := hinter.symm.trans (hInterEq.trans hinter')
      have hmap : O.2.1.map
          (E.rootEmbedding.trans
            (S.embedding O.1.1.1 O.1.1.2 O.1.2)) =
          O'.2.1.map
          (E.rootEmbedding.trans
            (S.embedding O.1.1.1 O.1.1.2 O.1.2)) := by
        simpa [mapEdge, hindex] using hmapEdge
      exact Subtype.ext (Finset.map_injective _ hmap)
    exact Prod.ext hindex hedge
  · exfalso
    have hblock' : mappedSpecial E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 =
      mappedSpecial E
        (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2 := by
      simpa [nearOccurrenceBlock] using hblock
    have hdis := mappedNegative_multi_pairwise_disjoint S hr hrk
      hrootForbidden hindex
    exact Finset.disjoint_left.mp hdis
      (mappedSpecial_mem_mappedNegative E _ O.2)
      (by rw [hblock']
          exact mappedSpecial_mem_mappedNegative E _ O'.2)

/-- A common `r`-edge of two distinct near occurrences forces the two
occurrences to have the same distinguished input edge, and is exactly that
edge. -/
theorem nearOccurrence_common_edge_eq
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {O O' : NearOccurrence roots multiplicity k r} (hne : O ≠ O')
    {g : Finset (Fin n)}
    (hg : g ∈ (nearOccurrenceBlock S O).powersetCard r)
    (hg' : g ∈ (nearOccurrenceBlock S O').powersetCard r) :
    g = nearOccurrenceEdge S O ∧
      nearOccurrenceEdge S O = nearOccurrenceEdge S O' := by
  have hforbidden (A : NearOccurrence roots multiplicity k r) :
      nearOccurrenceEdge S A ∈ forbidden := by
    apply hrootForbidden
    apply Finset.mem_biUnion.mpr
    exact ⟨A.1.1.1, A.1.1.2, nearOccurrenceEdge_mem_root S A⟩
  by_cases hindex : O.1 = O'.1
  · exfalso
    have hmem' : mappedSpecial E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O'.2 ∈
      mappedNegative E (S.embedding O.1.1.1 O.1.1.2 O.1.2) := by
      simpa [hindex] using
        (mappedSpecial_mem_mappedNegative E
          (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2)
    have hspecial : mappedSpecial E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 =
      mappedSpecial E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O'.2 :=
      (mappedNegative_decomp E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2)).blocks_eq_of_common_edge
        (mappedSpecial_mem_mappedNegative E _ O.2) hmem'
        (by simpa [nearOccurrenceBlock] using hg)
        (by simpa [nearOccurrenceBlock, hindex] using hg')
    have hblocks : nearOccurrenceBlock S O = nearOccurrenceBlock S O' := by
      simpa [nearOccurrenceBlock, hindex] using hspecial
    exact hne (nearOccurrenceBlock_injective S hr hrk hrootForbidden hblocks)
  · have hgBlock : g ∈
        (mappedSpecial E
          (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2).powersetCard r := by
      simpa [nearOccurrenceBlock] using hg
    have hgBlock' : g ∈
        (mappedSpecial E
          (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2).powersetCard r := by
      simpa [nearOccurrenceBlock] using hg'
    rcases mappedSpecial_edge_eq_or_free E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 hgBlock with
      heq | hfree <;>
      rcases mappedSpecial_edge_eq_or_free E
        (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2 hgBlock' with
        heq' | hfree'
    · exact ⟨by simpa [nearOccurrenceEdge] using heq,
        by simpa [nearOccurrenceEdge] using heq.symm.trans heq'⟩
    · exfalso
      exact Finset.disjoint_left.mp
        (S.free_disjoint_forbidden O'.1.1.1 O'.1.1.2 O'.1.2)
          hfree' (by simpa [nearOccurrenceEdge, heq] using hforbidden O)
    · exfalso
      exact Finset.disjoint_left.mp
        (S.free_disjoint_forbidden O.1.1.1 O.1.1.2 O.1.2)
          hfree (by simpa [nearOccurrenceEdge, heq'] using hforbidden O')
    · exact False.elim (Finset.disjoint_left.mp
        (S.free_pairwise O.1.1.1 O.1.1.2 O.1.2
          O'.1.1.1 O'.1.1.2 O'.1.2 (multiIndex_label_ne hindex))
        hfree hfree')

/-- Each ground `r`-edge of a root has a unique labelled source edge. -/
theorem exists_unique_rootEdge_mapping_to
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (I : ↥roots × Fin multiplicity)
    {g : Finset (Fin n)} (hgcard : g.card = r) (hgroot : g ⊆ I.1.1) :
    ∃! e : RootEdge k r,
      mapEdge (E.rootEmbedding.trans
        (S.embedding I.1.1 I.1.2 I.2)) e.1 = g := by
  have hgMap : g ⊆
      (Finset.univ : Finset (Fin k)).map
        (E.rootEmbedding.trans (S.embedding I.1.1 I.1.2 I.2)) := by
    have h := hgroot
    rw [← S.root_image I.1.1 I.1.2 I.2] at h
    change g ⊆ E.pattern.root.map
      (S.embedding I.1.1 I.1.2 I.2) at h
    rw [E.root_eq, ← mappedRoot_trans] at h
    simpa [mapEdge, mappedRoot] using h
  obtain ⟨e, heuniv, hemap⟩ := Finset.subset_map_iff.mp hgMap
  have hecard : e.card = r := by
    simpa [hemap] using hgcard
  let eroot : RootEdge k r :=
    ⟨e, Finset.mem_powersetCard.mpr ⟨heuniv, hecard⟩⟩
  refine ⟨eroot, ?_, ?_⟩
  · simpa [mapEdge] using hemap.symm
  · intro e' he'
    apply Subtype.ext
    apply Finset.map_injective
      (E.rootEmbedding.trans (S.embedding I.1.1 I.1.2 I.2))
    simpa [mapEdge, eroot] using he'.trans hemap

/-- A fibre of labelled near occurrences has exactly one occurrence for
each selected layer whose root contains the ground edge. -/
theorem card_nearOccurrence_fiber
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (indices : Finset (↥roots × Fin multiplicity))
    (hrk : r ≤ k) {g : Finset (Fin n)} (hgcard : g.card = r) :
    (((indices.product (Finset.univ : Finset (RootEdge k r))).filter
        fun O ↦ nearOccurrenceEdge S O = g).card) =
      (indices.filter fun I ↦ g ⊆ I.1.1).card := by
  classical
  let left := (indices.product (Finset.univ : Finset (RootEdge k r))).filter
    fun O ↦ nearOccurrenceEdge S O = g
  let right := indices.filter fun I ↦ g ⊆ I.1.1
  apply Nat.le_antisymm
  · apply Finset.card_le_card_of_injOn Prod.fst
    · intro O hO
      have hm := Finset.mem_filter.mp hO
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_product.mp hm.1).1, ?_⟩
      have hedgeRoot := nearOccurrenceEdge_mem_root S O
      rw [hm.2] at hedgeRoot
      exact (Finset.mem_powersetCard.mp hedgeRoot).1
    · intro O hO O' hO' hfst
      have hOedge := (Finset.mem_filter.mp hO).2
      have hO'edge := (Finset.mem_filter.mp hO').2
      have hroot := (Finset.mem_filter.mp
        (show O.1 ∈ indices.filter fun I ↦ g ⊆ I.1.1 by
          apply Finset.mem_filter.mpr
          refine ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hO).1).1, ?_⟩
          have hm := nearOccurrenceEdge_mem_root S O
          rw [hOedge] at hm
          exact (Finset.mem_powersetCard.mp hm).1)).2
      have hu := exists_unique_rootEdge_mapping_to S O.1 hgcard hroot
      have hedge : O.2 = O'.2 := hu.unique
        (by simpa [nearOccurrenceEdge] using hOedge)
        (by simpa [nearOccurrenceEdge, hfst] using hO'edge)
      exact Prod.ext hfst hedge
  · let defaultEdge : RootEdge k r := Classical.choice
      (Finset.nonempty_coe_sort.mpr
        (Finset.powersetCard_nonempty.mpr (by simpa using hrk)))
    let sourceEdge (I : ↥roots × Fin multiplicity) : RootEdge k r :=
      if hI : g ⊆ I.1.1 then
        Classical.choose (exists_unique_rootEdge_mapping_to S I hgcard hI)
      else defaultEdge
    let lift (I : ↥roots × Fin multiplicity) :
        NearOccurrence roots multiplicity k r := (I, sourceEdge I)
    apply Finset.card_le_card_of_injOn lift
    · intro I hI
      have hm := Finset.mem_filter.mp hI
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hm.1, Finset.mem_univ _⟩, ?_⟩
      simpa [lift, sourceEdge, hm.2, nearOccurrenceEdge] using
        (Classical.choose_spec
          (exists_unique_rootEdge_mapping_to S I hgcard hm.2)).1
    · intro I hI I' hI' hlift
      exact congrArg Prod.fst hlift

/-- Nonnegativity of the selected signed boundary gives the fibrewise
cardinality inequality needed to match every negative near occurrence. -/
theorem negativeNearOccurrence_fiber_card_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k) (θ : Finset (Fin n) → ℤ)
    (hnonneg : ∀ g : Finset (Fin n), g.card = r →
      0 ≤
        (∑ I ∈ positiveBankSelection (m := m) roots θ,
          if g ⊆ I.1.1 then (1 : ℤ) else 0) -
        (∑ I ∈ negativeBankSelection (m := m) roots θ,
          if g ⊆ I.1.1 then (1 : ℤ) else 0))
    (g : Finset (Fin n)) :
    ((negativeNearOccurrences (k := k) (r := r) (m := m) roots θ).filter
        fun O ↦ nearOccurrenceEdge S O = g).card ≤
      ((positiveNearOccurrences (k := k) (r := r) (m := m) roots θ).filter
        fun O ↦ nearOccurrenceEdge S O = g).card := by
  by_cases hgcard : g.card = r
  · rw [show negativeNearOccurrences (k := k) (r := r) (m := m) roots θ =
        (negativeBankSelection (m := m) roots θ).product Finset.univ by
        rfl,
      card_nearOccurrence_fiber S
        (negativeBankSelection (m := m) roots θ) hrk hgcard,
      show positiveNearOccurrences (k := k) (r := r) (m := m) roots θ =
        (positiveBankSelection (m := m) roots θ).product Finset.univ by
        rfl,
      card_nearOccurrence_fiber S
        (positiveBankSelection (m := m) roots θ) hrk hgcard]
    have h := hnonneg g hgcard
    have hpos :
        (∑ I ∈ positiveBankSelection (m := m) roots θ,
          if g ⊆ I.1.1 then (1 : ℤ) else 0) =
        (((positiveBankSelection (m := m) roots θ).filter
          fun I ↦ g ⊆ I.1.1).card : ℤ) := by
      simp
    have hneg :
        (∑ I ∈ negativeBankSelection (m := m) roots θ,
          if g ⊆ I.1.1 then (1 : ℤ) else 0) =
        (((negativeBankSelection (m := m) roots θ).filter
          fun I ↦ g ⊆ I.1.1).card : ℤ) := by
      simp
    rw [hpos, hneg] at h
    exact_mod_cast (show
      (((negativeBankSelection (m := m) roots θ).filter
        fun I ↦ g ⊆ I.1.1).card : ℤ) ≤
      (((positiveBankSelection (m := m) roots θ).filter
        fun I ↦ g ⊆ I.1.1).card : ℤ) by omega)
  · have hnegEmpty :
        (negativeNearOccurrences (k := k) (r := r) (m := m) roots θ).filter
          (fun O ↦ nearOccurrenceEdge S O = g) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro O hO
      have hEq := (Finset.mem_filter.mp hO).2
      apply hgcard
      rw [← hEq]
      exact nearOccurrenceEdge_card S O
    simp [hnegEmpty]

theorem exists_nearOccurrenceMatching
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k) (θ : Finset (Fin n) → ℤ)
    (hnonneg : ∀ g : Finset (Fin n), g.card = r →
      0 ≤
        (∑ I ∈ positiveBankSelection (m := m) roots θ,
          if g ⊆ I.1.1 then (1 : ℤ) else 0) -
        (∑ I ∈ negativeBankSelection (m := m) roots θ,
          if g ⊆ I.1.1 then (1 : ℤ) else 0)) :
    ∃ f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
        ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ),
      ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1 := by
  exact exists_fiberwiseEmbedding
    (positiveNearOccurrences (k := k) (r := r) (m := m) roots θ)
    (negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)
    (nearOccurrenceEdge S)
    (negativeNearOccurrence_fiber_card_le S hrk θ hnonneg)

/-! ## Universal preallocation of compatible near pairs -/

/-- Every layer in the permanently positive half of the splitting bank. -/
def allPositiveBankIndices
    {n m : ℕ} (roots : Finset (Finset (Fin n))) :
    Finset (↥roots × Fin (2 * m)) :=
  (roots.attach.product (Finset.univ : Finset (Fin m))).map
    (bankIndexEmbedding (positiveBankLayerEmbedding m))

/-- Every layer in the permanently negative half of the splitting bank. -/
def allNegativeBankIndices
    {n m : ℕ} (roots : Finset (Finset (Fin n))) :
    Finset (↥roots × Fin (2 * m)) :=
  (roots.attach.product (Finset.univ : Finset (Fin m))).map
    (bankIndexEmbedding (negativeBankLayerEmbedding m))

theorem positiveBankSelection_subset_allPositiveBankIndices
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) :
    positiveBankSelection (m := m) roots θ ⊆
      allPositiveBankIndices (m := m) roots := by
  unfold positiveBankSelection allPositiveBankIndices positiveLayerSelection
  intro I hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hI
  exact Finset.mem_map.mpr
    ⟨J, Finset.filter_subset _ _ hJ, rfl⟩

theorem negativeBankSelection_subset_allNegativeBankIndices
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) :
    negativeBankSelection (m := m) roots θ ⊆
      allNegativeBankIndices (m := m) roots := by
  unfold negativeBankSelection allNegativeBankIndices negativeLayerSelection
  intro I hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hI
  exact Finset.mem_map.mpr
    ⟨J, Finset.filter_subset _ _ hJ, rfl⟩

theorem allPositiveBankIndices_disjoint_allNegativeBankIndices
    {n m : ℕ} (roots : Finset (Finset (Fin n))) :
    Disjoint (allPositiveBankIndices (m := m) roots)
      (allNegativeBankIndices (m := m) roots) := by
  apply Finset.disjoint_left.mpr
  intro I hIpos hIneg
  obtain ⟨Ipos, _hIpos, hpos⟩ := Finset.mem_map.mp hIpos
  obtain ⟨Ineg, _hIneg, hneg⟩ := Finset.mem_map.mp hIneg
  have hsnd := congrArg (fun I : ↥roots × Fin (2 * m) ↦ I.2.1)
    (hpos.trans hneg.symm)
  change Ipos.2.1 = m + Ineg.2.1 at hsnd
  omega

/-- Every positive splitting block in the permanent bank, independently of
the coefficient vector selected later.  Positive-labelled copies contribute
their negative decomposition; negative-labelled copies contribute the
positive decomposition with the input root removed. -/
def allPositiveSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    Finset (Finset (Fin n)) :=
  ((allPositiveBankIndices (m := m) roots).biUnion fun I ↦
      mappedNegative E (S.embedding I.1.1 I.1.2 I.2)) ∪
    ((allNegativeBankIndices (m := m) roots).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)

/-- The coefficient-independent permanently negative splitting bank after
all near negative blocks have been reserved for the first elimination
round.  Positive-labelled copies contribute their positive decomposition
with the input root erased; negative-labelled copies contribute only their
far negative blocks. -/
def allNegativeFarSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    Finset (Finset (Fin n)) :=
  ((allPositiveBankIndices (m := m) roots).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) ∪
    ((allNegativeBankIndices (m := m) roots).biUnion fun I ↦
      mappedFarNegative E (S.embedding I.1.1 I.1.2 I.2))

/-- Every permanently negative near splitting block. -/
def allNegativeNearSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    Finset (Finset (Fin n)) :=
  (allNegativeBankIndices (m := m) roots).biUnion fun I ↦
    mappedNearNegative E (S.embedding I.1.1 I.1.2 I.2)

private theorem splittingHost_edge_mem_rootBoundary_union_freeUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (I : ↥roots × Fin (2 * m)) {g : Finset (Fin n)}
    (hgHost : g ∈ mappedHost E (S.embedding I.1.1 I.1.2 I.2)) :
    g ∈ rootBoundary roots r ∪ S.freeUnion := by
  rcases mem_mappedRootBoundary_or_imageFreeEdges E
      (S.embedding I.1.1 I.1.2 I.2) hgHost with hgRoot | hgFree
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨I.1.1, I.1.2, ?_⟩
    simpa [S.root_image I.1.1 I.1.2 I.2] using hgRoot
  · exact Finset.mem_union_right _
      (S.image_subset_freeUnion I.1.1 I.1.2 I.2 hgFree)

/-- The complete boundary of the fixed positive splitting bank is supported
on prescribed input-root edges and the splitting allocator's free union. -/
theorem allPositiveSplittingBlocks_boundary_subset_rootBoundary_union_freeUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    (allPositiveSplittingBlocks S).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      rootBoundary roots r ∪ S.freeUnion := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    apply splittingHost_edge_mem_rootBoundary_union_freeUnion S I
    exact (mappedNegative_decomp E
      (S.embedding I.1.1 I.1.2 I.2)).2.1 B hBI hgB
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    apply splittingHost_edge_mem_rootBoundary_union_freeUnion S I
    exact (mappedPositive_decomp E
      (S.embedding I.1.1 I.1.2 I.2)).2.1 B
        (Finset.mem_erase.mp hBI).2 hgB

/-- The fixed near-negative bank has the same root/free support audit. -/
theorem allNegativeNearSplittingBlocks_boundary_subset_rootBoundary_union_freeUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    (allNegativeNearSplittingBlocks S).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      rootBoundary roots r ∪ S.freeUnion := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
  apply splittingHost_edge_mem_rootBoundary_union_freeUnion S I
  exact (mappedNegative_decomp E
    (S.embedding I.1.1 I.1.2 I.2)).2.1 B
      (mappedNearNegative_subset_mappedNegative E _ hBI) hgB

theorem selectedBankPositiveBlocks_subset_allPositiveSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (theta : Finset (Fin n) → ℤ) :
    selectedBankPositiveBlocks S theta ⊆ allPositiveSplittingBlocks S := by
  intro B hB
  rcases Finset.mem_union.mp hB with hB | hB
  · apply Finset.mem_union_left
    obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact Finset.mem_biUnion.mpr
      ⟨I, positiveBankSelection_subset_allPositiveBankIndices roots theta hI,
        hBI⟩
  · apply Finset.mem_union_right
    obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact Finset.mem_biUnion.mpr
      ⟨I, negativeBankSelection_subset_allNegativeBankIndices roots theta hI,
        hBI⟩

theorem selectedBankNegativeNearBlocks_subset_allNegativeNearSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (theta : Finset (Fin n) → ℤ) :
    selectedBankNegativeNearBlocks S theta ⊆
      allNegativeNearSplittingBlocks S := by
  intro B hB
  obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
  exact Finset.mem_biUnion.mpr
    ⟨I, negativeBankSelection_subset_allNegativeBankIndices roots theta hI,
      hBI⟩

theorem selectedBankFarNegativeBlocks_subset_allNegativeFarSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (theta : Finset (Fin n) → ℤ) :
    selectedBankFarNegativeBlocks S theta ⊆
      allNegativeFarSplittingBlocks S := by
  intro B hB
  rcases Finset.mem_union.mp hB with hB | hB
  · apply Finset.mem_union_left
    obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact Finset.mem_biUnion.mpr
      ⟨I, positiveBankSelection_subset_allPositiveBankIndices roots theta hI,
        hBI⟩
  · apply Finset.mem_union_right
    obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact Finset.mem_biUnion.mpr
      ⟨I, negativeBankSelection_subset_allNegativeBankIndices roots theta hI,
        hBI⟩

theorem allNegativeFarSplittingBlocks_uniform
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    {B : Finset (Fin n)} (hB : B ∈ allNegativeFarSplittingBlocks S) :
    B.card = k := by
  rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact (mappedPositive_decomp E
      (S.embedding I.1.1 I.1.2 I.2)).1 B (Finset.mem_erase.mp hBI).2
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact (mappedFarNegative_decomp E
      (S.embedding I.1.1 I.1.2 I.2)).1 B hBI

/-- Distinct blocks in the permanent far negative splitting bank have
edge-disjoint `r`-boundaries. -/
theorem allNegativeFarSplittingBlocks_pairwise_edgeDisjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    {B B' : Finset (Fin n)}
    (hB : B ∈ allNegativeFarSplittingBlocks S)
    (hB' : B' ∈ allNegativeFarSplittingBlocks S)
    (hne : B ≠ B') :
    Disjoint (B.powersetCard r) (B'.powersetCard r) := by
  classical
  have positive_edge_free
      (I : ↑roots × Fin (2 * m)) {Q e : Finset (Fin n)}
      (hQ : Q ∈ (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)
      (he : e ∈ Q.powersetCard r) :
      e ∈ imageFreeEdges E.pattern
        (S.embedding I.1.1 I.1.2 I.2) := by
    have hdec : IsUniformDecomposition
        (imageFreeEdges E.pattern (S.embedding I.1.1 I.1.2 I.2))
        ((mappedPositive E
          (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) k r := by
      simpa [S.root_image I.1.1 I.1.2 I.2] using
        mappedPositive_erase_decomp E
          (S.embedding I.1.1 I.1.2 I.2)
    exact hdec.2.1 Q hQ he
  apply Finset.disjoint_left.mpr
  intro e heB heB'
  rcases Finset.mem_union.mp hB with hB | hB <;>
    rcases Finset.mem_union.mp hB' with hB' | hB'
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨I', _hI', hB'I'⟩ := Finset.mem_biUnion.mp hB'
    by_cases hII' : I = I'
    · subst I'
      have hdec : IsUniformDecomposition
          (imageFreeEdges E.pattern (S.embedding I.1.1 I.1.2 I.2))
          ((mappedPositive E
            (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) k r := by
        simpa [S.root_image I.1.1 I.1.2 I.2] using
          mappedPositive_erase_decomp E
            (S.embedding I.1.1 I.1.2 I.2)
      exact hne (hdec.blocks_eq_of_common_edge hBI hB'I' heB heB')
    · exact Finset.disjoint_left.mp
        (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
          (multiIndex_label_ne hII'))
        (positive_edge_free I hBI heB)
        (positive_edge_free I' hB'I' heB')
  · obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨I', hI', hB'I'⟩ := Finset.mem_biUnion.mp hB'
    have hII' : I ≠ I' := by
      intro hEq
      subst I'
      exact Finset.disjoint_left.mp
        (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
          hI hI'
    exact Finset.disjoint_left.mp
      (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
        (multiIndex_label_ne hII'))
      (positive_edge_free I hBI heB)
      (mappedFarNegative_edges_subset_freeEdges E _ hB'I' heB')
  · obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨I', hI', hB'I'⟩ := Finset.mem_biUnion.mp hB'
    have hII' : I ≠ I' := by
      intro hEq
      subst I'
      exact Finset.disjoint_left.mp
        (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
          hI' hI
    exact Finset.disjoint_left.mp
      (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
        (multiIndex_label_ne hII'))
      (mappedFarNegative_edges_subset_freeEdges E _ hBI heB)
      (positive_edge_free I' hB'I' heB')
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨I', _hI', hB'I'⟩ := Finset.mem_biUnion.mp hB'
    by_cases hII' : I = I'
    · subst I'
      exact hne ((mappedFarNegative_decomp E
        (S.embedding I.1.1 I.1.2 I.2)).blocks_eq_of_common_edge
          hBI hB'I' heB heB')
    · exact Finset.disjoint_left.mp
        (mappedFarNegative_multi_edgeDisjoint S hII' hBI hB'I')
          heB heB'

theorem allNegativeFarSplittingBlocks_decomp
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k) :
    IsUniformDecomposition
      ((allNegativeFarSplittingBlocks S).biUnion
        (fun B ↦ B.powersetCard r))
      (allNegativeFarSplittingBlocks S) k r := by
  apply IsUniformDecomposition.of_pairwise_powersetCard
  · exact fun B hB ↦ allNegativeFarSplittingBlocks_uniform S hB
  · exact fun B hB B' hB' hne ↦
      allNegativeFarSplittingBlocks_pairwise_edgeDisjoint
        S hr hrk hB hB' hne

/-- The permanent far splitting bank uses no prescribed root edge: its
whole boundary is contained in the free-edge union charged by the splitting
allocator. -/
theorem cliqueBoundarySupport_allNegativeFarSplittingBlocks_subset_freeUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    (allNegativeFarSplittingBlocks S).biUnion
        (fun B ↦ B.powersetCard r) ⊆ S.freeUnion := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    apply S.image_subset_freeUnion I.1.1 I.1.2 I.2
    have hdec : IsUniformDecomposition
        (imageFreeEdges E.pattern (S.embedding I.1.1 I.1.2 I.2))
        ((mappedPositive E
          (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) k r := by
      simpa [S.root_image I.1.1 I.1.2 I.2] using
        mappedPositive_erase_decomp E
          (S.embedding I.1.1 I.1.2 I.2)
    exact hdec.2.1 B hBI hgB
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    apply S.image_subset_freeUnion I.1.1 I.1.2 I.2
    exact mappedFarNegative_edges_subset_freeEdges E
      (S.embedding I.1.1 I.1.2 I.2) hBI
      hgB

theorem allPositiveSplittingBlocks_uniform
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    {B : Finset (Fin n)} (hB : B ∈ allPositiveSplittingBlocks S) :
    B.card = k := by
  rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact (mappedNegative_decomp E
      (S.embedding I.1.1 I.1.2 I.2)).1 B hBI
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    exact (mappedPositive_decomp E
      (S.embedding I.1.1 I.1.2 I.2)).1 B (Finset.mem_erase.mp hBI).2

/-- If the underlying exchange has had common blocks cancelled, the whole
permanent positive splitting bank is block-disjoint from the permanent far
negative bank. -/
theorem allPositiveSplittingBlocks_disjoint_allNegativeFarSplittingBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (htradeDisjoint : Disjoint E.positive E.negative) :
    Disjoint (allPositiveSplittingBlocks S)
      (allNegativeFarSplittingBlocks S) := by
  classical
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  rcases Finset.mem_union.mp hBpos with hBpos | hBpos <;>
    rcases Finset.mem_union.mp hBneg with hBneg | hBneg
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hBpos
    obtain ⟨J, _hJ, hBJ⟩ := Finset.mem_biUnion.mp hBneg
    by_cases hIJ : I = J
    · subst J
      exact Finset.disjoint_left.mp
        (mappedPositive_disjoint_mappedNegative E
          (S.embedding I.1.1 I.1.2 I.2) htradeDisjoint).symm
          hBI (Finset.mem_erase.mp hBJ).2
    · exact Finset.disjoint_left.mp
        (mappedNegative_multi_disjoint_mappedPositiveErase
          S hr hrk hrootForbidden hIJ) hBI hBJ
  · obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hBpos
    obtain ⟨J, hJ, hBJ⟩ := Finset.mem_biUnion.mp hBneg
    have hIJ : I ≠ J := by
      intro hEq
      subst J
      exact Finset.disjoint_left.mp
        (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
          hI hJ
    exact Finset.disjoint_left.mp
      (mappedNegative_multi_pairwise_disjoint S hr hrk hrootForbidden hIJ)
        hBI (Finset.mem_sdiff.mp hBJ).1
  · obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hBpos
    obtain ⟨J, hJ, hBJ⟩ := Finset.mem_biUnion.mp hBneg
    have hIJ : I ≠ J := by
      intro hEq
      subst J
      exact Finset.disjoint_left.mp
        (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
          hJ hI
    exact Finset.disjoint_left.mp
      (mappedPositiveErase_multi_pairwise_disjoint S hrk.le hIJ)
        hBI hBJ
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hBpos
    obtain ⟨J, _hJ, hBJ⟩ := Finset.mem_biUnion.mp hBneg
    by_cases hIJ : I = J
    · subst J
      exact Finset.disjoint_left.mp
        (mappedPositive_disjoint_mappedNegative E
          (S.embedding I.1.1 I.1.2 I.2) htradeDisjoint)
          (Finset.mem_erase.mp hBI).2
          (Finset.mem_sdiff.mp hBJ).1
    · exact Finset.disjoint_left.mp
        (mappedNegative_multi_disjoint_mappedPositiveErase
          S hr hrk hrootForbidden (Ne.symm hIJ)).symm
          hBI (Finset.mem_sdiff.mp hBJ).1

theorem allNegativeNearSplittingBlocks_uniform
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    {B : Finset (Fin n)}
    (hB : B ∈ allNegativeNearSplittingBlocks S) :
    B.card = k := by
  obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
  exact (mappedNegative_decomp E
    (S.embedding I.1.1 I.1.2 I.2)).1 B
      (mappedNearNegative_subset_mappedNegative E _ hBI)

/-- The permanent far negative splitting bank is edge-disjoint from every
permanent negative near block. -/
theorem allNegativeFarSplittingBlocks_edgeDisjoint_negativeNear
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {B N : Finset (Fin n)}
    (hB : B ∈ allNegativeFarSplittingBlocks S)
    (hN : N ∈ allNegativeNearSplittingBlocks S) :
    Disjoint (B.powersetCard r) (N.powersetCard r) := by
  classical
  obtain ⟨J, hJ, hNJ⟩ := Finset.mem_biUnion.mp hN
  obtain ⟨a, _ha, haN⟩ := Finset.mem_image.mp hNJ
  subst N
  apply Finset.disjoint_left.mpr
  intro e heB heN
  have heClass := mappedSpecial_edge_eq_or_free E
    (S.embedding J.1.1 J.1.2 J.2) a (by simpa using heN)
  rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    have hII' : I ≠ J := by
      intro hEq
      subst J
      exact Finset.disjoint_left.mp
        (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
          hI hJ
    have heFreeI : e ∈ imageFreeEdges E.pattern
        (S.embedding I.1.1 I.1.2 I.2) := by
      have hdec : IsUniformDecomposition
          (imageFreeEdges E.pattern (S.embedding I.1.1 I.1.2 I.2))
          ((mappedPositive E
            (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) k r := by
        simpa [S.root_image I.1.1 I.1.2 I.2] using
          mappedPositive_erase_decomp E
            (S.embedding I.1.1 I.1.2 I.2)
      exact hdec.2.1 B hBI heB
    rcases heClass with heRoot | heFreeJ
    · have heForbidden : e ∈ forbidden := by
        apply hrootForbidden
        apply Finset.mem_biUnion.mpr
        refine ⟨J.1.1, J.1.2, ?_⟩
        apply Finset.mem_powersetCard.mpr
        refine ⟨?_, (Finset.mem_powersetCard.mp heN).2⟩
        rw [← S.root_image J.1.1 J.1.2 J.2]
        rw [heRoot]
        intro x hx
        have hxInter : x ∈ mappedSpecial E
            (S.embedding J.1.1 J.1.2 J.2) a ∩
              mapEdge (S.embedding J.1.1 J.1.2 J.2) E.pattern.root := by
          rw [mappedSpecial_inter_mappedRoot E _ a]
          exact hx
        exact (Finset.mem_inter.mp hxInter).2
      exact Finset.disjoint_left.mp
        (S.free_disjoint_forbidden I.1.1 I.1.2 I.2)
          heFreeI heForbidden
    · exact Finset.disjoint_left.mp
        (S.free_pairwise I.1.1 I.1.2 I.2 J.1.1 J.1.2 J.2
          (multiIndex_label_ne hII')) heFreeI heFreeJ
  · obtain ⟨I, _hI, hBI⟩ := Finset.mem_biUnion.mp hB
    by_cases hIJ : I = J
    · subst J
      have heHost := (mappedFarNegative_decomp E
        (S.embedding I.1.1 I.1.2 I.2)).2.1 B hBI heB
      exact (Finset.mem_sdiff.mp heHost).2
        (Finset.mem_biUnion.mpr
          ⟨mappedSpecial E (S.embedding I.1.1 I.1.2 I.2) a, hNJ, heN⟩)
    · have heFreeI := mappedFarNegative_edges_subset_freeEdges E _ hBI heB
      rcases heClass with heRoot | heFreeJ
      · have heForbidden : e ∈ forbidden := by
          apply hrootForbidden
          apply Finset.mem_biUnion.mpr
          refine ⟨J.1.1, J.1.2, ?_⟩
          apply Finset.mem_powersetCard.mpr
          refine ⟨?_, (Finset.mem_powersetCard.mp heN).2⟩
          rw [← S.root_image J.1.1 J.1.2 J.2]
          rw [heRoot]
          intro x hx
          have hxInter : x ∈ mappedSpecial E
              (S.embedding J.1.1 J.1.2 J.2) a ∩
                mapEdge (S.embedding J.1.1 J.1.2 J.2) E.pattern.root := by
            rw [mappedSpecial_inter_mappedRoot E _ a]
            exact hx
          exact (Finset.mem_inter.mp hxInter).2
        exact Finset.disjoint_left.mp
          (S.free_disjoint_forbidden I.1.1 I.1.2 I.2)
            heFreeI heForbidden
      · exact Finset.disjoint_left.mp
          (S.free_pairwise I.1.1 I.1.2 I.2 J.1.1 J.1.2 J.2
            (multiIndex_label_ne hIJ)) heFreeI heFreeJ

theorem selectedBankFarNegativeBlocks_disjoint_negativeNear
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (theta : Finset (Fin n) → ℤ) :
    Disjoint (selectedBankFarNegativeBlocks S theta)
      (selectedBankNegativeNearBlocks S theta) := by
  apply Finset.disjoint_left.mpr
  intro B hBfar hBnear
  have hBcard := allNegativeFarSplittingBlocks_uniform S
    (selectedBankFarNegativeBlocks_subset_allNegativeFarSplittingBlocks
      S theta hBfar)
  have hrB : r ≤ B.card := by rw [hBcard]; exact hrk.le
  obtain ⟨e, heB⟩ := (Finset.powersetCard_nonempty (s := B) (n := r)).mpr hrB
  exact Finset.disjoint_left.mp
    (allNegativeFarSplittingBlocks_edgeDisjoint_negativeNear
      S hrootForbidden
        (selectedBankFarNegativeBlocks_subset_allNegativeFarSplittingBlocks
          S theta hBfar)
        (selectedBankNegativeNearBlocks_subset_allNegativeNearSplittingBlocks
          S theta hBnear)) heB heB

theorem selectedBankNegativeBlocks_sdiff_near_eq_far
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (theta : Finset (Fin n) → ℤ) :
    selectedBankNegativeBlocks S theta \
        selectedBankNegativeNearBlocks S theta =
      selectedBankFarNegativeBlocks S theta := by
  rw [selectedBankNegativeBlocks_eq_far_union_near]
  ext B
  constructor
  · intro hB
    have hdata := Finset.mem_sdiff.mp hB
    rcases Finset.mem_union.mp hdata.1 with hfar | hnear
    · exact hfar
    · exact False.elim (hdata.2 hnear)
  · intro hB
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_union_left _ hB,
      fun hnear ↦ Finset.disjoint_left.mp
        (selectedBankFarNegativeBlocks_disjoint_negativeNear
          S hr hrk hrootForbidden theta) hB hnear⟩

lemma card_attach_filter_subset_eq
    {n : ℕ} (roots : Finset (Finset (Fin n))) (g : Finset (Fin n)) :
    (roots.attach.filter fun Q ↦ g ⊆ Q.1).card =
      (roots.filter fun Q ↦ g ⊆ Q).card := by
  calc
    (roots.attach.filter fun Q ↦ g ⊆ Q.1).card =
        ∑ Q ∈ roots.attach, if g ⊆ Q.1 then 1 else 0 := by simp
    _ = ∑ Q ∈ roots, if g ⊆ Q then 1 else 0 := by
      exact Finset.sum_attach roots (fun Q ↦ if g ⊆ Q then 1 else 0)
    _ = (roots.filter fun Q ↦ g ⊆ Q).card := by simp

theorem card_allPositiveBankIndices_through_edge
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (g : Finset (Fin n)) :
    ((allPositiveBankIndices (m := m) roots).filter
      fun I ↦ g ⊆ I.1.1).card =
        m * Transversal.incidenceCount roots g := by
  classical
  let base := roots.attach.product (Finset.univ : Finset (Fin m))
  have hfilter :
      (base.filter fun I ↦ g ⊆ I.1.1) =
        (roots.attach.filter fun Q ↦ g ⊆ Q.1).product Finset.univ := by
    ext I
    simp [base]
  rw [allPositiveBankIndices, Finset.filter_map, Finset.card_map]
  change (base.filter fun I ↦ g ⊆ I.1.1).card = _
  rw [hfilter]
  simp [Transversal.incidenceCount,
    card_attach_filter_subset_eq roots g, Nat.mul_comm]

theorem card_allNegativeBankIndices_through_edge
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (g : Finset (Fin n)) :
    ((allNegativeBankIndices (m := m) roots).filter
      fun I ↦ g ⊆ I.1.1).card =
        m * Transversal.incidenceCount roots g := by
  classical
  let base := roots.attach.product (Finset.univ : Finset (Fin m))
  have hfilter :
      (base.filter fun I ↦ g ⊆ I.1.1) =
        (roots.attach.filter fun Q ↦ g ⊆ Q.1).product Finset.univ := by
    ext I
    simp [base]
  rw [allNegativeBankIndices, Finset.filter_map, Finset.card_map]
  change (base.filter fun I ↦ g ⊆ I.1.1).card = _
  rw [hfilter]
  simp [Transversal.incidenceCount,
    card_attach_filter_subset_eq roots g, Nat.mul_comm]

/-- Every labelled near occurrence in the positive half, independently of
the coefficient vector later selected. -/
def allPositiveNearOccurrences
    {n k r m : ℕ} (roots : Finset (Finset (Fin n))) :
    Finset (NearOccurrence roots (2 * m) k r) :=
  (allPositiveBankIndices (m := m) roots).product Finset.univ

/-- Every labelled near occurrence in the negative half, independently of
the coefficient vector later selected. -/
def allNegativeNearOccurrences
    {n k r m : ℕ} (roots : Finset (Finset (Fin n))) :
    Finset (NearOccurrence roots (2 * m) k r) :=
  (allNegativeBankIndices (m := m) roots).product Finset.univ

theorem mem_allNegativeNearSplittingBlocks_iff
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    {B : Finset (Fin n)} :
    B ∈ allNegativeNearSplittingBlocks S ↔
      ∃ O ∈ allNegativeNearOccurrences
          (k := k) (r := r) (m := m) roots,
        nearOccurrenceBlock S O = B := by
  constructor
  · intro hB
    obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨e, _he, heB⟩ := Finset.mem_image.mp hBI
    let O : NearOccurrence roots (2 * m) k r := (I, e)
    refine ⟨O, ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hI, Finset.mem_univ e⟩
    · simpa [O, nearOccurrenceBlock] using heB
  · rintro ⟨O, hO, rfl⟩
    have hOdata := Finset.mem_product.mp hO
    apply Finset.mem_biUnion.mpr
    refine ⟨O.1, hOdata.1, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨O.2, Finset.mem_univ O.2, rfl⟩

/-- Every non-root edge of a permanently negative near block is covered by
a positive far block in the same negative-labelled splitting copy. -/
theorem exists_allPositiveSplittingBlock_through_negativeNearEdge
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (O : NearOccurrence roots (2 * m) k r)
    (hO : O ∈ allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots)
    {e : Finset (Fin n)}
    (he : e ∈ (nearOccurrenceBlock S O).powersetCard r)
    (hne : e ≠ nearOccurrenceEdge S O) :
    ∃ Q ∈ allPositiveSplittingBlocks S,
      Q ∈ (mappedPositive E
          (S.embedding O.1.1.1 O.1.1.2 O.1.2)).erase O.1.1.1 ∧
        e ∈ Q.powersetCard r := by
  classical
  let phi := S.embedding O.1.1.1 O.1.1.2 O.1.2
  have hOindex : O.1 ∈ allNegativeBankIndices (m := m) roots :=
    (Finset.mem_product.mp hO).1
  have hspecial : nearOccurrenceBlock S O ∈ mappedNegative E phi := by
    exact mappedSpecial_mem_mappedNegative E phi O.2
  have heHost : e ∈ mappedHost E phi :=
    (mappedNegative_decomp E phi).2.1 _ hspecial he
  have hcard := (mappedPositive_decomp E phi).2.2 e heHost
  have hnonempty :
      (mappedPositive E phi).filter (fun Q ↦ e ⊆ Q) |>.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨Q, hQ⟩ := hnonempty
  have hQdata := Finset.mem_filter.mp hQ
  have hecard : e.card = r := (Finset.mem_powersetCard.mp he).2
  have hQne : Q ≠ O.1.1.1 := by
    intro hQroot
    have heRoot : e ⊆ mapEdge phi E.pattern.root := by
      rw [S.root_image O.1.1.1 O.1.1.2 O.1.2]
      simpa [hQroot] using hQdata.2
    have hsub : e ⊆ nearOccurrenceEdge S O := by
      intro x hx
      have hxInter : x ∈ mappedSpecial E phi O.2 ∩
          mapEdge phi E.pattern.root := Finset.mem_inter.mpr ⟨
        (Finset.mem_powersetCard.mp he).1 hx, heRoot hx⟩
      rw [mappedSpecial_inter_mappedRoot E phi O.2] at hxInter
      exact hxInter
    apply hne
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hecard, nearOccurrenceEdge_card S O]
  refine ⟨Q, ?_, Finset.mem_erase.mpr ⟨hQne, hQdata.1⟩,
    Finset.mem_powersetCard.mpr ⟨hQdata.2, hecard⟩⟩
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨O.1, hOindex, Finset.mem_erase.mpr ⟨hQne, hQdata.1⟩⟩

/-- A positive block through a non-input edge of a negative near occurrence
comes from the positive decomposition of that same negative-labelled copy.
This is the global attribution part of the trace-separation argument: the
edge is free in the occurrence copy, so it cannot be a root edge or a free
edge of any other preallocated copy. -/
theorem allPositiveSplittingBlock_through_negativeNearEdge_sameCopy
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (O : NearOccurrence roots (2 * m) k r)
    (hO : O ∈ allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots)
    {e Q : Finset (Fin n)}
    (heO : e ∈ (nearOccurrenceBlock S O).powersetCard r)
    (hne : e ≠ nearOccurrenceEdge S O)
    (hQ : Q ∈ allPositiveSplittingBlocks S)
    (heQ : e ∈ Q.powersetCard r) :
    Q ∈ (mappedPositive E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2)).erase O.1.1.1 := by
  classical
  let I := O.1
  let φ := S.embedding I.1.1 I.1.2 I.2
  have hIfree : e ∈ imageFreeEdges E.pattern φ := by
    rcases mappedSpecial_edge_eq_or_free E φ O.2
        (by simpa [nearOccurrenceBlock, I, φ] using heO) with heq | hfree
    · exact False.elim (hne (by
        simpa [nearOccurrenceEdge, I, φ] using heq))
    · exact hfree
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · obtain ⟨I', hI', hQI'⟩ := Finset.mem_biUnion.mp hQ
    have hI'host : e ∈ mappedHost E
        (S.embedding I'.1.1 I'.1.2 I'.2) :=
      (mappedNegative_decomp E _).2.1 Q hQI' heQ
    have hecard : e.card = r := (Finset.mem_powersetCard.mp heQ).2
    have hI'notRoot :
        e ∉ (mapEdge (S.embedding I'.1.1 I'.1.2 I'.2)
          E.pattern.root).powersetCard r := by
      intro heRoot
      have heForbidden : e ∈ forbidden := by
        apply hrootForbidden
        apply Finset.mem_biUnion.mpr
        refine ⟨I'.1.1, I'.1.2, ?_⟩
        apply Finset.mem_powersetCard.mpr
        refine ⟨?_, hecard⟩
        rw [← S.root_image I'.1.1 I'.1.2 I'.2]
        exact (Finset.mem_powersetCard.mp heRoot).1
      exact Finset.disjoint_left.mp
        (S.free_disjoint_forbidden I.1.1 I.1.2 I.2)
          hIfree heForbidden
    have hI'free : e ∈ imageFreeEdges E.pattern
        (S.embedding I'.1.1 I'.1.2 I'.2) := by
      rw [← mappedHost_sdiff_root_eq_freeEdges E _]
      exact Finset.mem_sdiff.mpr ⟨hI'host, hI'notRoot⟩
    have hindex : I ≠ I' := by
      intro hEq
      subst I'
      exact Finset.disjoint_left.mp
        (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
          hI' ((Finset.mem_product.mp hO).1)
    exact False.elim (Finset.disjoint_left.mp
      (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
        (multiIndex_label_ne hindex)) hIfree hI'free)
  · obtain ⟨I', hI', hQI'⟩ := Finset.mem_biUnion.mp hQ
    have hI'free : e ∈ imageFreeEdges E.pattern
        (S.embedding I'.1.1 I'.1.2 I'.2) := by
      have hdec := mappedPositive_erase_decomp E
        (S.embedding I'.1.1 I'.1.2 I'.2)
      have hroot := S.root_image I'.1.1 I'.1.2 I'.2
      apply hdec.2.1 Q
      · simpa [hroot] using hQI'
      · exact heQ
    have hindex : I = I' := by
      by_contra hneIndex
      exact Finset.disjoint_left.mp
        (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
          (multiIndex_label_ne hneIndex)) hIfree hI'free
    subst I'
    simpa [I] using hQI'

/-- A positive splitting block cannot cover non-input edges of two distinct
negative near occurrences.  First free-edge separation identifies the
rooted copy; then the exchange's global special-trace invariant identifies
the labelled special block inside that copy. -/
theorem negativeNearOccurrences_eq_of_positiveSplittingBlock
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {O O' : NearOccurrence roots (2 * m) k r}
    (hO : O ∈ allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots)
    (hO' : O' ∈ allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots)
    {e e' Q : Finset (Fin n)}
    (heO : e ∈ (nearOccurrenceBlock S O).powersetCard r)
    (hne : e ≠ nearOccurrenceEdge S O)
    (heO' : e' ∈ (nearOccurrenceBlock S O').powersetCard r)
    (hne' : e' ≠ nearOccurrenceEdge S O')
    (hQ : Q ∈ allPositiveSplittingBlocks S)
    (heQ : e ∈ Q.powersetCard r)
    (heQ' : e' ∈ Q.powersetCard r) :
    O = O' := by
  classical
  have hQcopy :=
    allPositiveSplittingBlock_through_negativeNearEdge_sameCopy
      S hr hrootForbidden O hO heO hne hQ heQ
  have hQcopy' :=
    allPositiveSplittingBlock_through_negativeNearEdge_sameCopy
      S hr hrootForbidden O' hO' heO' hne' hQ heQ'
  have hindex : O.1 = O'.1 := by
    by_contra hneIndex
    exact Finset.disjoint_left.mp
      (mappedPositiveErase_multi_pairwise_disjoint S hrk.le hneIndex)
        hQcopy hQcopy'
  have hspecial : O.2 = O'.2 := by
    let φ := S.embedding O.1.1.1 O.1.1.2 O.1.2
    have hQpos : Q ∈ mappedPositive E φ :=
      (Finset.mem_erase.mp hQcopy).2
    have hQroot : Q ≠ mapEdge φ E.pattern.root := by
      intro hEq
      exact (Finset.mem_erase.mp hQcopy).1
        (by rw [hEq, S.root_image O.1.1.1 O.1.1.2 O.1.2])
    apply mappedPositive_special_unique E φ hQpos hQroot O.2 O'.2
    · exact ⟨e, heQ, by simpa [nearOccurrenceBlock, φ] using heO⟩
    · exact ⟨e', heQ', by
        simpa [nearOccurrenceBlock, φ, hindex] using heO'⟩
  exact Prod.ext hindex hspecial

theorem card_allPositiveNearOccurrences_fiber
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k) (g : Finset (Fin n)) (hgcard : g.card = r) :
    ((allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ nearOccurrenceEdge S O = g).card =
        m * Transversal.incidenceCount roots g := by
  calc
    ((allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ nearOccurrenceEdge S O = g).card =
        ((allPositiveBankIndices (m := m) roots).filter
          fun I ↦ g ⊆ I.1.1).card := by
      simpa [allPositiveNearOccurrences] using
        (card_nearOccurrence_fiber S
          (allPositiveBankIndices (m := m) roots) hrk hgcard)
    _ = m * Transversal.incidenceCount roots g :=
      card_allPositiveBankIndices_through_edge roots g

theorem card_allNegativeNearOccurrences_fiber
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k) (g : Finset (Fin n)) (hgcard : g.card = r) :
    ((allNegativeNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ nearOccurrenceEdge S O = g).card =
        m * Transversal.incidenceCount roots g := by
  calc
    ((allNegativeNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ nearOccurrenceEdge S O = g).card =
        ((allNegativeBankIndices (m := m) roots).filter
          fun I ↦ g ⊆ I.1.1).card := by
      simpa [allNegativeNearOccurrences] using
        (card_nearOccurrence_fiber S
          (allNegativeBankIndices (m := m) roots) hrk hgcard)
    _ = m * Transversal.incidenceCount roots g :=
      card_allNegativeBankIndices_through_edge roots g

/-- All opposite-bank near-occurrence pairs carrying the same ground
`r`-edge.  The absorber preallocates elimination gadgets for this fixed
family before a coefficient vector, and hence its matching, is known. -/
def compatibleNearOccurrencePairs
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    Finset (NearOccurrence roots (2 * m) k r ×
      NearOccurrence roots (2 * m) k r) :=
  ((allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).product
    (allNegativeNearOccurrences (k := k) (r := r) (m := m) roots)).filter
      fun X ↦ nearOccurrenceEdge S X.1 = nearOccurrenceEdge S X.2

/-- The compatible bank over one ground edge is the Cartesian product of
its positive and negative occurrence fibres.  Thus bounded input clique
multiplicity gives a fixed bound on every local routing problem. -/
theorem card_compatibleNearOccurrencePairs_fiber
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k) (g : Finset (Fin n)) (hgcard : g.card = r) :
    ((compatibleNearOccurrencePairs S).filter
      fun X ↦ nearOccurrenceEdge S X.1 = g).card =
        (m * Transversal.incidenceCount roots g) ^ 2 := by
  classical
  let pos := allPositiveNearOccurrences (k := k) (r := r) (m := m) roots
  let neg := allNegativeNearOccurrences (k := k) (r := r) (m := m) roots
  have hfiber :
      (compatibleNearOccurrencePairs S).filter
          (fun X ↦ nearOccurrenceEdge S X.1 = g) =
        (pos.filter fun O ↦ nearOccurrenceEdge S O = g) ×ˢ
          (neg.filter fun O ↦ nearOccurrenceEdge S O = g) := by
    ext X
    simp only [compatibleNearOccurrencePairs, Finset.product_eq_sprod,
      Finset.mem_filter, Finset.mem_product, pos, neg]
    constructor
    · rintro ⟨⟨⟨hpos, hneg⟩, heq⟩, hfirst⟩
      exact ⟨⟨hpos, hfirst⟩, hneg, heq.symm.trans hfirst⟩
    · rintro ⟨⟨hpos, hfirst⟩, hneg, hsecond⟩
      exact ⟨⟨⟨hpos, hneg⟩, hfirst.trans hsecond.symm⟩, hfirst⟩
  have hpos := card_nearOccurrence_fiber S
    (allPositiveBankIndices (m := m) roots) hrk hgcard
  have hneg := card_nearOccurrence_fiber S
    (allNegativeBankIndices (m := m) roots) hrk hgcard
  have hpos' :
      (pos.filter fun O ↦ nearOccurrenceEdge S O = g).card =
        m * Transversal.incidenceCount roots g := by
    calc
      (pos.filter fun O ↦ nearOccurrenceEdge S O = g).card =
          ((allPositiveBankIndices (m := m) roots).filter
            fun I ↦ g ⊆ I.1.1).card := by
        simpa [pos, allPositiveNearOccurrences] using hpos
      _ = m * Transversal.incidenceCount roots g :=
        card_allPositiveBankIndices_through_edge roots g
  have hneg' :
      (neg.filter fun O ↦ nearOccurrenceEdge S O = g).card =
        m * Transversal.incidenceCount roots g := by
    calc
      (neg.filter fun O ↦ nearOccurrenceEdge S O = g).card =
          ((allNegativeBankIndices (m := m) roots).filter
            fun I ↦ g ⊆ I.1.1).card := by
        simpa [neg, allNegativeNearOccurrences] using hneg
      _ = m * Transversal.incidenceCount roots g :=
        card_allNegativeBankIndices_through_edge roots g
  rw [hfiber]
  rw [Finset.card_product]
  rw [hpos', hneg']
  simp [pow_two]

theorem card_compatibleNearOccurrencePairs_fiber_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (g : Finset (Fin n)) :
    ((compatibleNearOccurrencePairs S).filter
      fun X ↦ nearOccurrenceEdge S X.1 = g).card ≤ (m * M) ^ 2 := by
  by_cases hgcard : g.card = r
  · rw [card_compatibleNearOccurrencePairs_fiber S hrk g hgcard]
    exact Nat.pow_le_pow_left
      (Nat.mul_le_mul_left m (hrootMultiplicity g hgcard)) 2
  · have hempty :
        (compatibleNearOccurrencePairs S).filter
          (fun X ↦ nearOccurrenceEdge S X.1 = g) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro X hX
      apply hgcard
      rw [← (Finset.mem_filter.mp hX).2]
      exact nearOccurrenceEdge_card S X.1
    simp [hempty]

/-- Once the positive occurrence of a compatible pair is fixed, only the
opposite occurrence in the same input-edge fibre remains to be chosen. -/
theorem card_compatibleNearOccurrencePairs_fixed_positive_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (O : NearOccurrence roots (2 * m) k r) :
    ((compatibleNearOccurrencePairs S).filter fun X ↦ X.1 = O).card ≤
      m * M := by
  classical
  let left := (compatibleNearOccurrencePairs S).filter fun X ↦ X.1 = O
  let right :=
    (allNegativeNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O' ↦ nearOccurrenceEdge S O' = nearOccurrenceEdge S O
  have hle : left.card ≤ right.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro X hX
      have hleft := Finset.mem_filter.mp hX
      have hcompat := Finset.mem_filter.mp hleft.1
      have hsides := Finset.mem_product.mp hcompat.1
      apply Finset.mem_filter.mpr
      exact ⟨hsides.2, by simpa [hleft.2] using hcompat.2.symm⟩
    · intro X hX Y hY hsnd
      apply Prod.ext
      · exact (Finset.mem_filter.mp hX).2.trans
          (Finset.mem_filter.mp hY).2.symm
      · exact hsnd
  have hright : right.card =
      m * Transversal.incidenceCount roots (nearOccurrenceEdge S O) := by
    simpa [right] using card_allNegativeNearOccurrences_fiber S hrk
      (nearOccurrenceEdge S O) (nearOccurrenceEdge_card S O)
  rw [hright] at hle
  exact hle.trans (Nat.mul_le_mul_left m
    (hrootMultiplicity (nearOccurrenceEdge S O)
      (nearOccurrenceEdge_card S O)))

/-- Symmetric fixed-negative fibre bound. -/
theorem card_compatibleNearOccurrencePairs_fixed_negative_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (O : NearOccurrence roots (2 * m) k r) :
    ((compatibleNearOccurrencePairs S).filter fun X ↦ X.2 = O).card ≤
      m * M := by
  classical
  let left := (compatibleNearOccurrencePairs S).filter fun X ↦ X.2 = O
  let right :=
    (allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O' ↦ nearOccurrenceEdge S O' = nearOccurrenceEdge S O
  have hle : left.card ≤ right.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro X hX
      have hleft := Finset.mem_filter.mp hX
      have hcompat := Finset.mem_filter.mp hleft.1
      have hsides := Finset.mem_product.mp hcompat.1
      apply Finset.mem_filter.mpr
      exact ⟨hsides.1, by simpa [hleft.2] using hcompat.2⟩
    · intro X hX Y hY hfst
      apply Prod.ext
      · exact hfst
      · exact (Finset.mem_filter.mp hX).2.trans
          (Finset.mem_filter.mp hY).2.symm
  have hright : right.card =
      m * Transversal.incidenceCount roots (nearOccurrenceEdge S O) := by
    simpa [right] using card_allPositiveNearOccurrences_fiber S hrk
      (nearOccurrenceEdge S O) (nearOccurrenceEdge_card S O)
  rw [hright] at hle
  exact hle.trans (Nat.mul_le_mul_left m
    (hrootMultiplicity (nearOccurrenceEdge S O)
      (nearOccurrenceEdge_card S O)))

/-- One universally compatible occurrence pair gives a valid two-clique
root for an elimination exchange. -/
def compatibleNearEliminationPair
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (X : ↥(compatibleNearOccurrencePairs S)) :
    EliminationPair n k r := by
  have hdata := Finset.mem_filter.mp X.2
  have hselection := Finset.mem_product.mp hdata.1
  have hposIndex : X.1.1.1 ∈ allPositiveBankIndices (m := m) roots :=
    (Finset.mem_product.mp hselection.1).1
  have hnegIndex : X.1.2.1 ∈ allNegativeBankIndices (m := m) roots :=
    (Finset.mem_product.mp hselection.2).1
  have hindex : X.1.1.1 ≠ X.1.2.1 := by
    intro hEq
    exact Finset.disjoint_left.mp
      (allPositiveBankIndices_disjoint_allNegativeBankIndices roots)
      hposIndex (hEq ▸ hnegIndex)
  exact
    { positive := nearOccurrenceBlock S X.1.1
      negative := nearOccurrenceBlock S X.1.2
      positive_card := nearOccurrenceBlock_card S X.1.1
      negative_card := nearOccurrenceBlock_card S X.1.2
      inter_card := mappedSpecial_multi_inter_card_of_same_edge
        S hr hrootForbidden hindex X.1.1.2 X.1.2.2 hdata.2 }

@[simp] theorem compatibleNearEliminationPair_positive
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (X : ↥(compatibleNearOccurrencePairs S)) :
    (compatibleNearEliminationPair S hr hrk hrootForbidden X).positive =
      nearOccurrenceBlock S X.1.1 := rfl

@[simp] theorem compatibleNearEliminationPair_negative
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (X : ↥(compatibleNearOccurrencePairs S)) :
    (compatibleNearEliminationPair S hr hrk hrootForbidden X).negative =
      nearOccurrenceBlock S X.1.2 := rfl

theorem compatibleNearEliminationPair_injective
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden) :
    Function.Injective
      (compatibleNearEliminationPair S hr hrk hrootForbidden) := by
  intro X X' hpair
  have hpositive := congrArg EliminationPair.positive hpair
  have hnegative := congrArg EliminationPair.negative hpair
  have hpos : X.1.1 = X'.1.1 :=
    nearOccurrenceBlock_injective S hr hrk hrootForbidden hpositive
  have hneg : X.1.2 = X'.1.2 :=
    nearOccurrenceBlock_injective S hr hrk hrootForbidden hnegative
  apply Subtype.ext
  exact Prod.ext hpos hneg

def compatibleNearEliminationPairEmbedding
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden) :
    ↥(compatibleNearOccurrencePairs S) ↪ EliminationPair n k r :=
  ⟨compatibleNearEliminationPair S hr hrk hrootForbidden,
    compatibleNearEliminationPair_injective S hr hrk hrootForbidden⟩

@[simp] theorem compatibleNearEliminationPairEmbedding_positive
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (X : ↥(compatibleNearOccurrencePairs S)) :
    ((compatibleNearEliminationPairEmbedding S hr hrk hrootForbidden) X).positive =
      nearOccurrenceBlock S X.1.1 := rfl

@[simp] theorem compatibleNearEliminationPairEmbedding_negative
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (X : ↥(compatibleNearOccurrencePairs S)) :
    ((compatibleNearEliminationPairEmbedding S hr hrk hrootForbidden) X).negative =
      nearOccurrenceBlock S X.1.2 := rfl

/-- The fixed family of every compatible first-round elimination root. -/
def compatibleNearEliminationPairs
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden) :
    Finset (EliminationPair n k r) :=
  Finset.univ.map
    (compatibleNearEliminationPairEmbedding S hr hrk hrootForbidden)

/-- If an edge of the negative root of a compatible near pair belongs to
the splitting forbidden family, then it is the common distinguished edge
and therefore lies in the positive root as well. -/
theorem compatibleNearEliminationPair_negative_edge_subset_positive_of_mem_forbidden
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (P : EliminationPair n k r)
    (hP : P ∈ compatibleNearEliminationPairs S hr hrk hrootForbidden)
    {g : Finset (Fin n)}
    (hgNegative : g ∈ P.negative.powersetCard r)
    (hgForbidden : g ∈ forbidden) :
    g ⊆ P.positive := by
  obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
  subst P
  have hcompat := (Finset.mem_filter.mp X.2).2
  have hgeq := nearOccurrenceBlock_edge_eq_distinguished_of_mem_forbidden
    S X.1.2 (by simpa using hgNegative) hgForbidden
  rw [hgeq, ← hcompat]
  exact nearOccurrenceEdge_subset_block S X.1.1

/-- Occurrence-level lower-face load of the universal compatible-pair bank. -/
def compatibleNearPairLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (J : Finset (Fin n)) : ℕ :=
  ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
    fun X ↦ J ⊆
      (compatibleNearEliminationPair S hr hrk hrootForbidden X).root).card

/-- Universal pairs through `J` for which neither constituent near block
already contains all of `J`.  Only this genuinely mixed contribution needs
a new correlation counter in the splitting random-greedy path. -/
def compatibleNearMixedPairLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (J : Finset (Fin n)) : ℕ :=
  ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
    fun X ↦
      J ⊆ (compatibleNearEliminationPair S hr hrk hrootForbidden X).root ∧
      ¬J ⊆ nearOccurrenceBlock S X.1.1 ∧
      ¬J ⊆ nearOccurrenceBlock S X.1.2).card

/-- Every genuinely mixed compatible pair forces its positive constituent
embedding to touch the face outside the prescribed root.  (The symmetric
statement is also true, but one side is enough for charging.) -/
theorem compatibleNearMixedPair_positive_touchesOutsideRoot
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (J : Finset (Fin n))
    (X : ↥(compatibleNearOccurrencePairs S))
    (hmixed :
      J ⊆ (compatibleNearEliminationPair S hr hrk
        hrootForbidden X).root ∧
      ¬J ⊆ nearOccurrenceBlock S X.1.1 ∧
      ¬J ⊆ nearOccurrenceBlock S X.1.2) :
    OutsideRootTouches E.pattern.root J
      (S.embedding X.1.1.1.1.1 X.1.1.1.1.2 X.1.1.1.2) := by
  have hcompat := Finset.mem_filter.mp X.2
  have hunion : J ⊆ nearOccurrenceBlock S X.1.2 ∪
      nearOccurrenceBlock S X.1.1 := by
    intro x hx
    have hxroot := hmixed.1 hx
    change x ∈ nearOccurrenceBlock S X.1.1 ∪
      nearOccurrenceBlock S X.1.2 at hxroot
    rcases Finset.mem_union.mp hxroot with hxpos | hxneg
    · exact Finset.mem_union_right _ hxpos
    · exact Finset.mem_union_left _ hxneg
  apply mixedSpecialFace_current_touchesOutsideRoot (E := E)
    (S.embedding X.1.2.1.1.1 X.1.2.1.1.2 X.1.2.1.2)
    (S.embedding X.1.1.1.1.1 X.1.1.1.1.2 X.1.1.1.2)
    X.1.2.2 X.1.1.2 J
  · simpa [nearOccurrenceEdge] using hcompat.2.symm
  · simpa [nearOccurrenceBlock] using hunion
  · simpa [nearOccurrenceBlock] using hmixed.2.2

/-- The mixed load of a tracked splitting bank is at most the touch count,
times the number of labelled special blocks in one copy and the bounded
opposite-edge fibre size. -/
theorem compatibleNearMixedPairLoad_le_trackedTouch
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ} {beta : Type*}
    (face : beta → Finset (Fin n)) (extraCap : beta → ℕ)
    (S : TrackedBoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C beta
      (fun b ↦ outsideRootTouchHit E.pattern.root (face b)) extraCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (b : beta) :
    compatibleNearMixedPairLoad
        S.toBoundedMultiRootedFamilyEmbeddings hr hrk hrootForbidden
        (face b) ≤
      pathHits (outsideRootTouchHit E.pattern.root (face b)) [] S.path *
        Fintype.card (RootEdge k r) * (m * M) := by
  classical
  let S0 := S.toBoundedMultiRootedFamilyEmbeddings
  let mixed : Finset ↥(compatibleNearOccurrencePairs S0) :=
    (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S0)).filter
      fun X ↦
        face b ⊆ (compatibleNearEliminationPair S0 hr hrk
          hrootForbidden X).root ∧
        ¬face b ⊆ nearOccurrenceBlock S0 X.1.1 ∧
        ¬face b ⊆ nearOccurrenceBlock S0 X.1.2
  let touchedPositive : Finset (NearOccurrence roots (2 * m) k r) :=
    (allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ outsideRootTouchHit E.pattern.root (face b) []
        (S.embedding O.1.1.1 O.1.1.2 O.1.2)
  let rel (X : ↥(compatibleNearOccurrencePairs S0))
      (O : NearOccurrence roots (2 * m) k r) : Prop := X.1.1 = O
  have hleft : ∀ X ∈ mixed,
      1 ≤ (touchedPositive.filter (rel X)).card := by
    intro X hX
    have hmixed := (Finset.mem_filter.mp hX).2
    have hcompat := Finset.mem_filter.mp X.2
    have hsides := Finset.mem_product.mp hcompat.1
    have htouch := compatibleNearMixedPair_positive_touchesOutsideRoot
      S0 hr hrk hrootForbidden (face b) X hmixed
    have htouchBool : outsideRootTouchHit E.pattern.root (face b) []
        (S.embedding X.1.1.1.1.1 X.1.1.1.1.2 X.1.1.1.2) = true :=
      (outsideRootTouchHit_eq_true_iff E.pattern.root (face b) [] _).mpr
        htouch
    exact Finset.card_pos.mpr
      ⟨X.1.1, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hsides.1, by simpa using htouchBool⟩,
          rfl⟩⟩
  have hright : ∀ O ∈ touchedPositive,
      (mixed.filter fun X ↦ rel X O).card ≤ m * M := by
    intro O hO
    have hsub : (mixed.filter fun X ↦ rel X O) ⊆
        (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S0)).filter
          fun X ↦ X.1.1 = O := by
      intro X hX
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ X, (Finset.mem_filter.mp hX).2⟩
    have hcardSubtype :
        ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S0)).filter
          fun X ↦ X.1.1 = O).card ≤
        ((compatibleNearOccurrencePairs S0).filter fun X ↦ X.1 = O).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro X hX
        exact Finset.mem_filter.mpr
          ⟨X.2, (Finset.mem_filter.mp hX).2⟩
      · intro X hX Y hY hval
        exact Subtype.ext hval
    exact (Finset.card_le_card hsub).trans
      (hcardSubtype.trans
        (card_compatibleNearOccurrencePairs_fixed_positive_le S0 hrk.le
          hrootMultiplicity O))
  have hmixedCard : mixed.card ≤ touchedPositive.card * (m * M) := by
    have hcount := Reserve.card_mul_le_card_mul_of_relation
      mixed touchedPositive rel 1 (m * M) hleft hright
    simpa using hcount
  let touchedIndices : Finset (↥roots × Fin (2 * m)) :=
    (allPositiveBankIndices (m := m) roots).filter fun I ↦
      outsideRootTouchHit E.pattern.root (face b) []
        (S.embedding I.1.1 I.1.2 I.2)
  have htouchedProduct : touchedPositive =
      touchedIndices.product (Finset.univ : Finset (RootEdge k r)) := by
    ext O
    simp [touchedPositive, touchedIndices, allPositiveNearOccurrences]
  let indexed := indexedOutsideRootTouchIndices E.pattern.root S.path (face b)
  have htouchedIndices : touchedIndices.card ≤ indexed.card := by
    apply Finset.card_le_card_of_injOn
      (fun I ↦ S.position I.1.1 I.1.2 I.2)
    · intro I hI
      have htouch := (Finset.mem_filter.mp hI).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← S.embedding_at_position I.1.1 I.1.2 I.2]
      exact htouch
    · intro I hI I' hI' hposition
      have hlabel := S.position_injective
        I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2 hposition
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hlabel
      · apply Fin.ext
        exact congrArg Prod.snd hlabel
  have htouchedCard : touchedPositive.card ≤
      pathHits (outsideRootTouchHit E.pattern.root (face b)) [] S.path *
        Fintype.card (RootEdge k r) := by
    have hindices : touchedIndices.card ≤
        pathHits (outsideRootTouchHit E.pattern.root (face b)) [] S.path :=
      htouchedIndices.trans_eq
        (card_indexedOutsideRootTouchIndices_eq_pathHits
          E.pattern.root [] S.path (face b))
    have hmul := Nat.mul_le_mul_right
      (Finset.univ : Finset (RootEdge k r)).card hindices
    rw [htouchedProduct]
    simpa using hmul
  have hscaled := Nat.mul_le_mul_right (m * M) htouchedCard
  simpa [S0, mixed, compatibleNearMixedPairLoad,
    Nat.mul_assoc] using hmixedCard.trans hscaled

/-- Counter caps immediately give a deterministic mixed-pair cap for the
finished tracked bank. -/
theorem compatibleNearMixedPairLoad_le_trackedCap
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ} {beta : Type*}
    (face : beta → Finset (Fin n)) (extraCap : beta → ℕ)
    (S : TrackedBoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C beta
      (fun b ↦ outsideRootTouchHit E.pattern.root (face b)) extraCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (b : beta) :
    compatibleNearMixedPairLoad
        S.toBoundedMultiRootedFamilyEmbeddings hr hrk hrootForbidden
        (face b) ≤
      extraCap b * Fintype.card (RootEdge k r) * (m * M) := by
  have htouch := compatibleNearMixedPairLoad_le_trackedTouch
    face extraCap S hr hrk hrootForbidden hrootMultiplicity b
  have hcap : pathHits
      (outsideRootTouchHit E.pattern.root (face b)) [] S.path ≤
      extraCap b := Nat.le_of_lt (S.extra_lt b)
  exact htouch.trans (by
    exact Nat.mul_le_mul_right (m * M)
      (Nat.mul_le_mul_right (Fintype.card (RootEdge k r)) hcap))

/-- Finite construction of the splitting bank with all codimension-one
outside-root-touch counters tracked simultaneously.  The displayed scalar
conditions are exactly the two numerator bounds and the final exponential
union bound; the asymptotic layer discharges them for the chosen path cap. -/
theorem exists_trackedSplittingBank_of_finite_bounds
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m Droot Dfixed C B : ℕ}
    [Nonempty (Fin E.v ↪ Fin n)]
    (hr : 0 < r) (hrk : r < k) (hm : 0 < m)
    (hrootUniform : ∀ Q ∈ roots, Q.card = k)
    (hforbiddenUniform : ∀ e ∈ forbidden, e.card = r)
    (Q₀ : Finset (Fin n)) (hQ₀ : Q₀ ∈ roots)
    (hrootMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree roots J ≤ Droot)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hLpos : 0 < rootedFaceLegalLowerBound E.pattern n Dfixed C)
    (hfaceBudget : faceScheduleNumeratorBound E.pattern n
      ((2 * m) * Droot) ≤ B)
    (htouchBudget : roots.card * (2 * m) *
      splittingTouchNumerator E n ≤ B)
    (hquant : (Real.exp 1 - 1) *
      ((B : ℝ) / rootedFaceLegalLowerBound E.pattern n Dfixed C) ≤
        (C : ℝ) / 2)
    (hcard : (Fintype.card
      (Sum (RelevantFaceLoadTarget E.pattern n) (SplittingFace n r)) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    Nonempty (TrackedBoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C (SplittingFace n r)
      (fun J ↦ outsideRootTouchHit E.pattern.root J.1) (fun _ ↦ C)) := by
  classical
  apply exists_trackedBoundedMultiRootedFamilyEmbeddings_of_finite_bounds
    E.pattern roots forbidden
  · intro Q hQ
    simpa using hrootUniform Q hQ
  · exact E.root_nonempty (by omega)
  · simp
    omega
  · exact hforbiddenUniform
  · exact hQ₀
  · exact hrootMax
  · exact hfixedMax
  · exact hr
  · omega
  · exact hLpos
  · intro J request history
    have htouch := card_legalEmbeddings_outsideRootTouchHit_le
      E.pattern request forbidden history J.1
    have hJcard : J.1.card = r - 1 :=
      Typicality.mem_uniformEdges.mp J.2
    simpa [splittingTouchNumerator, hJcard] using htouch
  · exact hfaceBudget
  · intro J
    simpa [splittingTouchNumerator] using htouchBudget
  · exact hquant
  · exact hcard

def compatibleNearPositiveSideLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (J : Finset (Fin n)) : ℕ :=
  ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
    fun X ↦ J ⊆ nearOccurrenceBlock S X.1.1).card

def compatibleNearNegativeSideLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (J : Finset (Fin n)) : ℕ :=
  ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
    fun X ↦ J ⊆ nearOccurrenceBlock S X.1.2).card

def allPositiveNearBlockLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (J : Finset (Fin n)) : ℕ :=
  ((allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
    fun O ↦ J ⊆ nearOccurrenceBlock S O).card

def allNegativeNearBlockLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (J : Finset (Fin n)) : ℕ :=
  ((allNegativeNearOccurrences (k := k) (r := r) (m := m) roots).filter
    fun O ↦ J ⊆ nearOccurrenceBlock S O).card

private lemma exists_edge_between_face_and_block
    {J B : Finset (Fin n)} (hr : 0 < r) (hrk : r < k)
    (hJ : J.card = r - 1) (hB : B.card = k) (hJB : J ⊆ B) :
    ∃ g ∈ B.powersetCard r, J ⊆ g := by
  have hdiffCard : (B \ J).card = k - (r - 1) := by
    rw [Finset.card_sdiff_of_subset hJB, hB, hJ]
  have hdiff : (B \ J).Nonempty := Finset.card_pos.mp (by omega)
  let x := hdiff.choose
  have hx := hdiff.choose_spec
  let g := insert x J
  have hxJ : x ∉ J := (Finset.mem_sdiff.mp hx).2
  have hgcard : g.card = r := by
    rw [Finset.card_insert_of_notMem hxJ, hJ]
    omega
  have hgB : g ⊆ B := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (Finset.mem_sdiff.mp hx).1
    · exact hJB hy
  exact ⟨g, Finset.mem_powersetCard.mpr ⟨hgB, hgcard⟩,
    Finset.subset_insert x J⟩

theorem rootBoundary_localDegree_le_incidenceCount
    {roots : Finset (Finset (Fin n))}
    (huniform : ∀ Q ∈ roots, Q.card = k)
    (J : Finset (Fin n)) :
    Reserve.localDegree (rootBoundary roots r) J ≤
      Transversal.incidenceCount roots J * 2 ^ k := by
  classical
  let left := (rootBoundary roots r).filter fun g ↦ J ⊆ g
  let right := roots.filter fun Q ↦ J ⊆ Q
  have hcount := Reserve.card_mul_le_card_mul_of_relation
    left right (fun g Q : Finset (Fin n) ↦ g ⊆ Q) 1 (2 ^ k) (by
      intro g hg
      have hgRoot := (Finset.mem_filter.mp hg).1
      obtain ⟨Q, hQ, hgQ⟩ := Finset.mem_biUnion.mp hgRoot
      have hQright : Q ∈ right := Finset.mem_filter.mpr
        ⟨hQ, (Finset.mem_filter.mp hg).2.trans
          (Finset.mem_powersetCard.mp hgQ).1⟩
      exact Finset.card_pos.mpr
        ⟨Q, Finset.mem_filter.mpr
          ⟨hQright, (Finset.mem_powersetCard.mp hgQ).1⟩⟩) (by
      intro Q hQ
      have hQroot := (Finset.mem_filter.mp hQ).1
      have hsub : (left.filter fun g ↦ g ⊆ Q) ⊆ Q.powerset := by
        intro g hg
        exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hg).2
      calc
        (left.filter fun g ↦ g ⊆ Q).card ≤ Q.powerset.card :=
          Finset.card_le_card hsub
        _ = 2 ^ k := by simp [huniform Q hQroot])
  simpa [left, right, Reserve.localDegree, Transversal.incidenceCount] using
    hcount

/-- Every near block through an `(r-1)`-face is charged either to its
distinguished input edge or to one globally separated free edge. -/
theorem nearOccurrenceBlockLoad_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (bank : Finset (↥roots × Fin (2 * m)))
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hfiber : ∀ g : Finset (Fin n), g.card = r →
      (((bank.product (Finset.univ : Finset (RootEdge k r))).filter
        fun O ↦ nearOccurrenceEdge S O = g).card) ≤ m * M)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    (((bank.product (Finset.univ : Finset (RootEdge k r))).filter
        fun O ↦ J ⊆ nearOccurrenceBlock S O).card) ≤
      (Reserve.localDegree (rootBoundary roots r) J +
          Reserve.localDegree S.freeUnion J) * (m * M + 1) := by
  classical
  let occurrences := bank.product (Finset.univ : Finset (RootEdge k r))
  let left := occurrences.filter fun O ↦ J ⊆ nearOccurrenceBlock S O
  let right := (rootBoundary roots r ∪ S.freeUnion).filter fun g ↦
    J ⊆ g ∧ g.card = r
  let rel (O : NearOccurrence roots (2 * m) k r)
      (g : Finset (Fin n)) : Prop := g ⊆ nearOccurrenceBlock S O
  have hleft : ∀ O ∈ left, 1 ≤ (right.filter (rel O)).card := by
    intro O hO
    have hJB := (Finset.mem_filter.mp hO).2
    obtain ⟨g, hgBlock, hJg⟩ := exists_edge_between_face_and_block
      hr hrk hJ (nearOccurrenceBlock_card S O) hJB
    have hgClass := mappedSpecial_edge_eq_or_free E
      (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 (by
        simpa [nearOccurrenceBlock] using hgBlock)
    have hgUnion : g ∈ rootBoundary roots r ∪ S.freeUnion := by
      rcases hgClass with hgRoot | hgFree
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨O.1.1.1, O.1.1.2, ?_⟩
        rw [hgRoot]
        exact nearOccurrenceEdge_mem_root S O
      · exact Finset.mem_union_right _
          (S.image_subset_freeUnion O.1.1.1 O.1.1.2 O.1.2 hgFree)
    have hgRight : g ∈ right := Finset.mem_filter.mpr
      ⟨hgUnion, hJg, (Finset.mem_powersetCard.mp hgBlock).2⟩
    exact Finset.card_pos.mpr
      ⟨g, Finset.mem_filter.mpr
        ⟨hgRight, (Finset.mem_powersetCard.mp hgBlock).1⟩⟩
  have hright : ∀ g ∈ right, (left.filter fun O ↦ rel O g).card ≤
      m * M + 1 := by
    intro g hg
    have hgcard : g.card = r := (Finset.mem_filter.mp hg).2.2
    let rootPart := occurrences.filter fun O ↦ nearOccurrenceEdge S O = g
    let freePart := occurrences.filter fun O ↦
      g ⊆ nearOccurrenceBlock S O ∧ nearOccurrenceEdge S O ≠ g
    have hfreeCard : freePart.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro O hO O' hO'
      have hOdata := Finset.mem_filter.mp hO
      have hO'data := Finset.mem_filter.mp hO'
      have hgO : g ∈ (nearOccurrenceBlock S O).powersetCard r :=
        Finset.mem_powersetCard.mpr ⟨hOdata.2.1, hgcard⟩
      have hgO' : g ∈ (nearOccurrenceBlock S O').powersetCard r :=
        Finset.mem_powersetCard.mpr ⟨hO'data.2.1, hgcard⟩
      have hfreeO : g ∈ imageFreeEdges E.pattern
          (S.embedding O.1.1.1 O.1.1.2 O.1.2) := by
        rcases mappedSpecial_edge_eq_or_free E
            (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2 (by
              simpa [nearOccurrenceBlock] using hgO) with heq | hfree
        · exact False.elim (hOdata.2.2 (by
            simpa [nearOccurrenceEdge] using heq.symm))
        · exact hfree
      have hfreeO' : g ∈ imageFreeEdges E.pattern
          (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) := by
        rcases mappedSpecial_edge_eq_or_free E
            (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2 (by
              simpa [nearOccurrenceBlock] using hgO') with heq | hfree
        · exact False.elim (hO'data.2.2 (by
            simpa [nearOccurrenceEdge] using heq.symm))
        · exact hfree
      by_cases hindex : O.1 = O'.1
      · have hB : nearOccurrenceBlock S O ∈ mappedNegative E
            (S.embedding O.1.1.1 O.1.1.2 O.1.2) := by
          exact mappedSpecial_mem_mappedNegative E _ O.2
        have hB' : nearOccurrenceBlock S O' ∈ mappedNegative E
            (S.embedding O.1.1.1 O.1.1.2 O.1.2) := by
          simpa [nearOccurrenceBlock, hindex] using
            (mappedSpecial_mem_mappedNegative E
              (S.embedding O'.1.1.1 O'.1.1.2 O'.1.2) O'.2)
        have hblocks : nearOccurrenceBlock S O = nearOccurrenceBlock S O' :=
          (mappedNegative_decomp E
            (S.embedding O.1.1.1 O.1.1.2 O.1.2)).blocks_eq_of_common_edge
              hB hB' hgO hgO'
        exact nearOccurrenceBlock_injective S hr hrk hrootForbidden hblocks
      · exact False.elim (Finset.disjoint_left.mp
          (S.free_pairwise O.1.1.1 O.1.1.2 O.1.2
            O'.1.1.1 O'.1.1.2 O'.1.2 (multiIndex_label_ne hindex))
          hfreeO hfreeO')
    have hsubset : (left.filter fun O ↦ rel O g) ⊆
        rootPart ∪ freePart := by
      intro O hO
      have hOleft := Finset.mem_filter.mp hO
      by_cases hedge : nearOccurrenceEdge S O = g
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hOleft.1).1, hedge⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hOleft.1).1, hOleft.2, hedge⟩)
    calc
      (left.filter fun O ↦ rel O g).card ≤ (rootPart ∪ freePart).card :=
        Finset.card_le_card hsubset
      _ ≤ rootPart.card + freePart.card := Finset.card_union_le _ _
      _ ≤ m * M + 1 := Nat.add_le_add (by
          simpa [rootPart, occurrences] using hfiber g hgcard) hfreeCard
  have hcount := Reserve.card_mul_le_card_mul_of_relation
    left right rel 1 (m * M + 1) hleft hright
  have hrightCard : right.card ≤
      Reserve.localDegree (rootBoundary roots r) J +
        Reserve.localDegree S.freeUnion J := by
    let rootSide := (rootBoundary roots r).filter fun g ↦ J ⊆ g
    let freeSide := S.freeUnion.filter fun g ↦ J ⊆ g
    have hsub : right ⊆ rootSide ∪ freeSide := by
      intro g hg
      have hgm := Finset.mem_filter.mp hg
      rcases Finset.mem_union.mp hgm.1 with hgRoot | hgFree
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hgRoot, hgm.2.1⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hgFree, hgm.2.1⟩)
    exact (Finset.card_le_card hsub).trans (by
      simpa [rootSide, freeSide, Reserve.localDegree] using
        (Finset.card_union_le rootSide freeSide))
  have hmul := Nat.mul_le_mul_right (m * M + 1) hrightCard
  simpa [left, occurrences] using hcount.trans hmul

theorem allPositiveNearBlockLoad_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    allPositiveNearBlockLoad S J ≤
      (Reserve.localDegree (rootBoundary roots r) J +
          Reserve.localDegree S.freeUnion J) * (m * M + 1) := by
  apply nearOccurrenceBlockLoad_le S
    (allPositiveBankIndices (m := m) roots) hr hrk hrootForbidden
  · intro g hgcard
    rw [show
      (((allPositiveBankIndices (m := m) roots).product
          (Finset.univ : Finset (RootEdge k r))).filter
        fun O ↦ nearOccurrenceEdge S O = g).card =
          m * Transversal.incidenceCount roots g by
      simpa [allPositiveNearOccurrences] using
        card_allPositiveNearOccurrences_fiber S hrk.le g hgcard]
    exact Nat.mul_le_mul_left m (hrootMultiplicity g hgcard)
  · exact hJ

theorem allNegativeNearBlockLoad_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    allNegativeNearBlockLoad S J ≤
      (Reserve.localDegree (rootBoundary roots r) J +
          Reserve.localDegree S.freeUnion J) * (m * M + 1) := by
  apply nearOccurrenceBlockLoad_le S
    (allNegativeBankIndices (m := m) roots) hr hrk hrootForbidden
  · intro g hgcard
    rw [show
      (((allNegativeBankIndices (m := m) roots).product
          (Finset.univ : Finset (RootEdge k r))).filter
        fun O ↦ nearOccurrenceEdge S O = g).card =
          m * Transversal.incidenceCount roots g by
      simpa [allNegativeNearOccurrences] using
        card_allNegativeNearOccurrences_fiber S hrk.le g hgcard]
    exact Nat.mul_le_mul_left m (hrootMultiplicity g hgcard)
  · exact hJ

theorem compatibleNearPositiveSideLoad_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (J : Finset (Fin n)) :
    compatibleNearPositiveSideLoad S J ≤
      allPositiveNearBlockLoad S J * (m * M + 1) := by
  classical
  let side :=
    (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
      fun X ↦ J ⊆ nearOccurrenceBlock S X.1.1
  let posJ :=
    (allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ J ⊆ nearOccurrenceBlock S O
  let negFiber (g : Finset (Fin n)) :=
    (allNegativeNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O' ↦ nearOccurrenceEdge S O' = g
  have hnegFiber (g : Finset (Fin n)) : (negFiber g).card ≤ m * M := by
    by_cases hgcard : g.card = r
    · rw [show (negFiber g).card =
          m * Transversal.incidenceCount roots g by
        simpa [negFiber] using card_allNegativeNearOccurrences_fiber S hrk
          g hgcard]
      exact Nat.mul_le_mul_left m (hrootMultiplicity g hgcard)
    · have hempty : negFiber g = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro O hO
        apply hgcard
        rw [← (Finset.mem_filter.mp hO).2]
        exact nearOccurrenceEdge_card S O
      simp [hempty]
  let fiberEmbedding (g : Finset (Fin n)) :
      ↥(negFiber g) ↪ Fin (m * M) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa using hnegFiber g))
  let fiberCode (g : Finset (Fin n))
      (O : NearOccurrence roots (2 * m) k r) : Fin (m * M + 1) :=
    if hO : O ∈ negFiber g then
      Fin.castLE (Nat.le_add_right (m * M) 1) (fiberEmbedding g ⟨O, hO⟩)
    else
      ⟨m * M, Nat.lt_add_one _⟩
  have hfiberCode {g : Finset (Fin n)}
      {O O' : NearOccurrence roots (2 * m) k r}
      (hO : O ∈ negFiber g) (hO' : O' ∈ negFiber g)
      (hcode : fiberCode g O = fiberCode g O') : O = O' := by
    have hemb : fiberEmbedding g ⟨O, hO⟩ = fiberEmbedding g ⟨O', hO'⟩ := by
      apply Fin.ext
      have hval := congrArg Fin.val hcode
      simpa [fiberCode, hO, hO'] using hval
    exact congrArg Subtype.val ((fiberEmbedding g).injective hemb)
  let route (X : ↥side) : ↥posJ × Fin (m * M + 1) := by
    have hcompat := Finset.mem_filter.mp X.1.2
    have hsides := Finset.mem_product.mp hcompat.1
    have hside := (Finset.mem_filter.mp X.2).2
    let Opos : ↥posJ :=
      ⟨X.1.1.1, Finset.mem_filter.mpr ⟨hsides.1, hside⟩⟩
    have hnegMem : X.1.1.2 ∈ negFiber (nearOccurrenceEdge S Opos.1) := by
      apply Finset.mem_filter.mpr
      exact ⟨hsides.2, hcompat.2.symm⟩
    exact (Opos, fiberCode (nearOccurrenceEdge S Opos.1) X.1.1.2)
  have hroute : Function.Injective route := by
    intro X Y hXY
    have hpos : X.1.1.1 = Y.1.1.1 := by
      exact congrArg (fun z : ↥posJ × Fin (m * M + 1) ↦ z.1.1) hXY
    have hedge : nearOccurrenceEdge S X.1.1.1 =
        nearOccurrenceEdge S Y.1.1.1 := congrArg (nearOccurrenceEdge S) hpos
    have hneg : X.1.1.2 = Y.1.1.2 := by
      have hsnd := congrArg (fun z : ↥posJ × Fin (m * M + 1) ↦ z.2) hXY
      dsimp only [route] at hsnd
      rw [← hedge] at hsnd
      apply hfiberCode
      · have hcompat := Finset.mem_filter.mp X.1.2
        have hsides := Finset.mem_product.mp hcompat.1
        exact Finset.mem_filter.mpr ⟨hsides.2, hcompat.2.symm⟩
      · have hcompat := Finset.mem_filter.mp Y.1.2
        have hsides := Finset.mem_product.mp hcompat.1
        exact Finset.mem_filter.mpr
          ⟨hsides.2, by simpa [hpos] using hcompat.2.symm⟩
      · exact hsnd
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hpos hneg
  have hcard := Fintype.card_le_of_injective route hroute
  have hcard' : side.card ≤ posJ.card * (m * M + 1) := by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hcard
  simpa [side, posJ, compatibleNearPositiveSideLoad,
    allPositiveNearBlockLoad] using hcard'

theorem compatibleNearNegativeSideLoad_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (J : Finset (Fin n)) :
    compatibleNearNegativeSideLoad S J ≤
      allNegativeNearBlockLoad S J * (m * M + 1) := by
  classical
  let side :=
    (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
      fun X ↦ J ⊆ nearOccurrenceBlock S X.1.2
  let negJ :=
    (allNegativeNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ J ⊆ nearOccurrenceBlock S O
  let posFiber (g : Finset (Fin n)) :=
    (allPositiveNearOccurrences (k := k) (r := r) (m := m) roots).filter
      fun O ↦ nearOccurrenceEdge S O = g
  have hposFiber (g : Finset (Fin n)) : (posFiber g).card ≤ m * M := by
    by_cases hgcard : g.card = r
    · rw [show (posFiber g).card =
          m * Transversal.incidenceCount roots g by
        simpa [posFiber] using card_allPositiveNearOccurrences_fiber S hrk
          g hgcard]
      exact Nat.mul_le_mul_left m (hrootMultiplicity g hgcard)
    · have hempty : posFiber g = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro O hO
        apply hgcard
        rw [← (Finset.mem_filter.mp hO).2]
        exact nearOccurrenceEdge_card S O
      simp [hempty]
  let fiberEmbedding (g : Finset (Fin n)) :
      ↥(posFiber g) ↪ Fin (m * M) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa using hposFiber g))
  let fiberCode (g : Finset (Fin n))
      (O : NearOccurrence roots (2 * m) k r) : Fin (m * M + 1) :=
    if hO : O ∈ posFiber g then
      Fin.castLE (Nat.le_add_right (m * M) 1) (fiberEmbedding g ⟨O, hO⟩)
    else
      ⟨m * M, Nat.lt_add_one _⟩
  have hfiberCode {g : Finset (Fin n)}
      {O O' : NearOccurrence roots (2 * m) k r}
      (hO : O ∈ posFiber g) (hO' : O' ∈ posFiber g)
      (hcode : fiberCode g O = fiberCode g O') : O = O' := by
    have hemb : fiberEmbedding g ⟨O, hO⟩ = fiberEmbedding g ⟨O', hO'⟩ := by
      apply Fin.ext
      have hval := congrArg Fin.val hcode
      simpa [fiberCode, hO, hO'] using hval
    exact congrArg Subtype.val ((fiberEmbedding g).injective hemb)
  let route (X : ↥side) : ↥negJ × Fin (m * M + 1) := by
    have hcompat := Finset.mem_filter.mp X.1.2
    have hsides := Finset.mem_product.mp hcompat.1
    have hside := (Finset.mem_filter.mp X.2).2
    let Oneg : ↥negJ :=
      ⟨X.1.1.2, Finset.mem_filter.mpr ⟨hsides.2, hside⟩⟩
    exact (Oneg, fiberCode (nearOccurrenceEdge S Oneg.1) X.1.1.1)
  have hroute : Function.Injective route := by
    intro X Y hXY
    have hneg : X.1.1.2 = Y.1.1.2 := by
      exact congrArg (fun z : ↥negJ × Fin (m * M + 1) ↦ z.1.1) hXY
    have hedge : nearOccurrenceEdge S X.1.1.2 =
        nearOccurrenceEdge S Y.1.1.2 := congrArg (nearOccurrenceEdge S) hneg
    have hpos : X.1.1.1 = Y.1.1.1 := by
      have hsnd := congrArg (fun z : ↥negJ × Fin (m * M + 1) ↦ z.2) hXY
      dsimp only [route] at hsnd
      rw [← hedge] at hsnd
      apply hfiberCode
      · have hcompat := Finset.mem_filter.mp X.1.2
        have hsides := Finset.mem_product.mp hcompat.1
        exact Finset.mem_filter.mpr ⟨hsides.1, hcompat.2⟩
      · have hcompat := Finset.mem_filter.mp Y.1.2
        have hsides := Finset.mem_product.mp hcompat.1
        exact Finset.mem_filter.mpr
          ⟨hsides.1, by simpa [hneg] using hcompat.2⟩
      · exact hsnd
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hpos hneg
  have hcard := Fintype.card_le_of_injective route hroute
  have hcard' : side.card ≤ negJ.card * (m * M + 1) := by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hcard
  simpa [side, negJ, compatibleNearNegativeSideLoad,
    allNegativeNearBlockLoad] using hcard'

/-- Combined quantitative bound for the two prescribed-side schedules of
the universal first elimination bank. -/
theorem compatibleNearSideLoads_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    compatibleNearPositiveSideLoad S J +
        compatibleNearNegativeSideLoad S J ≤
      2 * ((m * M + 1) * (m * M + 1)) *
        (Reserve.localDegree (rootBoundary roots r) J +
          Reserve.localDegree S.freeUnion J) := by
  let D := Reserve.localDegree (rootBoundary roots r) J +
    Reserve.localDegree S.freeUnion J
  let F := m * M + 1
  have hposBlock : allPositiveNearBlockLoad S J ≤ D * F := by
    simpa [D, F] using allPositiveNearBlockLoad_le S hr hrk
      hrootForbidden hrootMultiplicity J hJ
  have hnegBlock : allNegativeNearBlockLoad S J ≤ D * F := by
    simpa [D, F] using allNegativeNearBlockLoad_le S hr hrk
      hrootForbidden hrootMultiplicity J hJ
  have hpos : compatibleNearPositiveSideLoad S J ≤ D * F * F :=
    (compatibleNearPositiveSideLoad_le S hrk.le hrootMultiplicity J).trans
      (Nat.mul_le_mul_right F hposBlock)
  have hneg : compatibleNearNegativeSideLoad S J ≤ D * F * F :=
    (compatibleNearNegativeSideLoad_le S hrk.le hrootMultiplicity J).trans
      (Nat.mul_le_mul_right F hnegBlock)
  calc
    compatibleNearPositiveSideLoad S J +
        compatibleNearNegativeSideLoad S J ≤
      D * F * F + D * F * F := Nat.add_le_add hpos hneg
    _ = 2 * ((m * M + 1) * (m * M + 1)) *
        (Reserve.localDegree (rootBoundary roots r) J +
          Reserve.localDegree S.freeUnion J) := by
      dsimp only [D, F]
      ring

theorem compatibleNearPairLoad_le_mixed_add_sides
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (J : Finset (Fin n)) :
    compatibleNearPairLoad S hr hrk hrootForbidden J ≤
      compatibleNearMixedPairLoad S hr hrk hrootForbidden J +
        compatibleNearPositiveSideLoad S J +
          compatibleNearNegativeSideLoad S J := by
  classical
  let U : Finset ↥(compatibleNearOccurrencePairs S) := Finset.univ
  let all := U.filter fun X ↦
    J ⊆ (compatibleNearEliminationPair S hr hrk hrootForbidden X).root
  let mixed := U.filter fun X ↦
    J ⊆ (compatibleNearEliminationPair S hr hrk hrootForbidden X).root ∧
      ¬J ⊆ nearOccurrenceBlock S X.1.1 ∧
      ¬J ⊆ nearOccurrenceBlock S X.1.2
  let pos := U.filter fun X ↦ J ⊆ nearOccurrenceBlock S X.1.1
  let neg := U.filter fun X ↦ J ⊆ nearOccurrenceBlock S X.1.2
  have hsubset : all ⊆ mixed ∪ (pos ∪ neg) := by
    intro X hX
    have hroot := (Finset.mem_filter.mp hX).2
    by_cases hp : J ⊆ nearOccurrenceBlock S X.1.1
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ X, hp⟩))
    · by_cases hn : J ⊆ nearOccurrenceBlock S X.1.2
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ X, hn⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ X, hroot, hp, hn⟩)
  calc
    compatibleNearPairLoad S hr hrk hrootForbidden J = all.card := rfl
    _ ≤ (mixed ∪ (pos ∪ neg)).card := Finset.card_le_card hsubset
    _ ≤ mixed.card + (pos ∪ neg).card := Finset.card_union_le _ _
    _ ≤ mixed.card + (pos.card + neg.card) :=
      Nat.add_le_add_left (Finset.card_union_le pos neg) _
    _ = compatibleNearMixedPairLoad S hr hrk hrootForbidden J +
        compatibleNearPositiveSideLoad S J +
          compatibleNearNegativeSideLoad S J := by
      simp [mixed, pos, neg, U, compatibleNearMixedPairLoad,
        compatibleNearPositiveSideLoad, compatibleNearNegativeSideLoad,
        Nat.add_assoc]

/-- After the existing rooted degree estimates are applied, the only new
counter needed for the universal first elimination bank is the mixed-face
load. -/
theorem compatibleNearPairLoad_le_mixed_add_structural
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    compatibleNearPairLoad S hr hrk hrootForbidden J ≤
      compatibleNearMixedPairLoad S hr hrk hrootForbidden J +
        2 * ((Reserve.localDegree (rootBoundary roots r) J +
              Reserve.localDegree S.freeUnion J) *
            (m * M + 1) * (m * M + 1)) := by
  let D := Reserve.localDegree (rootBoundary roots r) J +
    Reserve.localDegree S.freeUnion J
  let F := m * M + 1
  have hposBlock : allPositiveNearBlockLoad S J ≤ D * F := by
    simpa [D, F] using allPositiveNearBlockLoad_le S hr hrk
      hrootForbidden hrootMultiplicity J hJ
  have hnegBlock : allNegativeNearBlockLoad S J ≤ D * F := by
    simpa [D, F] using allNegativeNearBlockLoad_le S hr hrk
      hrootForbidden hrootMultiplicity J hJ
  have hpos : compatibleNearPositiveSideLoad S J ≤ D * F * F :=
    (compatibleNearPositiveSideLoad_le S hrk.le hrootMultiplicity J).trans
      (Nat.mul_le_mul_right F hposBlock)
  have hneg : compatibleNearNegativeSideLoad S J ≤ D * F * F :=
    (compatibleNearNegativeSideLoad_le S hrk.le hrootMultiplicity J).trans
      (Nat.mul_le_mul_right F hnegBlock)
  have hall := compatibleNearPairLoad_le_mixed_add_sides S hr hrk
    hrootForbidden J
  dsimp only [D, F] at hpos hneg ⊢
  omega

theorem compatibleNearPairLoad_le_mixed_add_caps
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M D : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (huniform : ∀ Q ∈ roots, Q.card = k)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (hinputDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Transversal.incidenceCount roots J ≤ D)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    compatibleNearPairLoad S hr hrk hrootForbidden J ≤
      compatibleNearMixedPairLoad S hr hrk hrootForbidden J +
        2 * ((D * 2 ^ k + E.pattern.freeEdges.card * C) *
            (m * M + 1) * (m * M + 1)) := by
  have hrootDegree : Reserve.localDegree (rootBoundary roots r) J ≤
      D * 2 ^ k :=
    (rootBoundary_localDegree_le_incidenceCount huniform J).trans
      (Nat.mul_le_mul_right (2 ^ k) (hinputDegree J hJ))
  have hfreeDegree : Reserve.localDegree S.freeUnion J ≤
      E.pattern.freeEdges.card * C := S.free_degree_le J hJ
  have hsum : Reserve.localDegree (rootBoundary roots r) J +
      Reserve.localDegree S.freeUnion J ≤
        D * 2 ^ k + E.pattern.freeEdges.card * C :=
    Nat.add_le_add hrootDegree hfreeDegree
  have hstruct := compatibleNearPairLoad_le_mixed_add_structural S hr hrk
    hrootForbidden hrootMultiplicity J hJ
  have hscaled := Nat.mul_le_mul_left 2
    (Nat.mul_le_mul_right (m * M + 1)
      (Nat.mul_le_mul_right (m * M + 1) hsum))
  exact hstruct.trans (Nat.add_le_add_left hscaled _)

theorem compatibleNearPairRootDegree_le_load
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (J : Finset (Fin n)) :
    Reserve.localDegree
        ((compatibleNearEliminationPairs S hr hrk hrootForbidden).image
          EliminationPair.root) J ≤
      compatibleNearPairLoad S hr hrk hrootForbidden J := by
  classical
  let pairEmb :=
    compatibleNearEliminationPairEmbedding S hr hrk hrootForbidden
  let rootMap : ↥(compatibleNearOccurrencePairs S) → Finset (Fin n) :=
    fun X ↦ (pairEmb X).root
  have hrootSet :
      (compatibleNearEliminationPairs S hr hrk hrootForbidden).image
          EliminationPair.root =
        (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).image
          rootMap := by
    ext Q
    simp [compatibleNearEliminationPairs, pairEmb, rootMap,
      compatibleNearEliminationPairEmbedding]
  have hsubset :
      (((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).image
          rootMap).filter fun Q ↦ J ⊆ Q) ⊆
        (((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ J ⊆ rootMap X).image rootMap) := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    obtain ⟨X, _hX, rfl⟩ := Finset.mem_image.mp hQdata.1
    exact Finset.mem_image.mpr
      ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ X, hQdata.2⟩, rfl⟩
  calc
    Reserve.localDegree
        ((compatibleNearEliminationPairs S hr hrk hrootForbidden).image
          EliminationPair.root) J =
        (((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).image
          rootMap).filter fun Q ↦ J ⊆ Q).card := by
      rw [hrootSet]
      rfl
    _ ≤ (((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ J ⊆ rootMap X).image rootMap).card :=
      Finset.card_le_card hsubset
    _ ≤ ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ J ⊆ rootMap X).card := Finset.card_image_le
    _ = compatibleNearPairLoad S hr hrk hrootForbidden J := by rfl

/-- The set-degree of the two prescribed sides is bounded by the two
occurrence-level side loads.  Passing from occurrences to a set of blocks
can only decrease cardinality. -/
theorem compatibleNearEliminationPairSides_degree_le_sideLoads
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (J : Finset (Fin n)) :
    Reserve.localDegree
        (eliminationPairSides
          (compatibleNearEliminationPairs S hr hrk hrootForbidden)) J ≤
      compatibleNearPositiveSideLoad S J +
        compatibleNearNegativeSideLoad S J := by
  classical
  let occurrences : Finset ↥(compatibleNearOccurrencePairs S) := Finset.univ
  let posBlocks := occurrences.image fun X ↦ nearOccurrenceBlock S X.1.1
  let negBlocks := occurrences.image fun X ↦ nearOccurrenceBlock S X.1.2
  have hsideSub : eliminationPairSides
      (compatibleNearEliminationPairs S hr hrk hrootForbidden) ⊆
        posBlocks ∪ negBlocks := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨X, Finset.mem_univ X, ?_⟩
      rw [← hXP]
      exact compatibleNearEliminationPairEmbedding_positive
        S hr hrk hrootForbidden X
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨X, Finset.mem_univ X, ?_⟩
      rw [← hXP]
      exact compatibleNearEliminationPairEmbedding_negative
        S hr hrk hrootForbidden X
  let posJ := occurrences.filter fun X ↦ J ⊆ nearOccurrenceBlock S X.1.1
  let negJ := occurrences.filter fun X ↦ J ⊆ nearOccurrenceBlock S X.1.2
  have hpos : Reserve.localDegree posBlocks J ≤ posJ.card := by
    let filtered := posBlocks.filter fun Q ↦ J ⊆ Q
    have hsub : filtered ⊆ posJ.image (fun X ↦ nearOccurrenceBlock S X.1.1) := by
      intro Q hQ
      have hQdata := Finset.mem_filter.mp hQ
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hQdata.1
      exact Finset.mem_image.mpr
        ⟨X, Finset.mem_filter.mpr ⟨hX, hQdata.2⟩, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hneg : Reserve.localDegree negBlocks J ≤ negJ.card := by
    let filtered := negBlocks.filter fun Q ↦ J ⊆ Q
    have hsub : filtered ⊆ negJ.image (fun X ↦ nearOccurrenceBlock S X.1.2) := by
      intro Q hQ
      have hQdata := Finset.mem_filter.mp hQ
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hQdata.1
      exact Finset.mem_image.mpr
        ⟨X, Finset.mem_filter.mpr ⟨hX, hQdata.2⟩, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hdegreeSub : Reserve.localDegree
      (eliminationPairSides
        (compatibleNearEliminationPairs S hr hrk hrootForbidden)) J ≤
      Reserve.localDegree (posBlocks ∪ negBlocks) J := by
    apply Finset.card_le_card
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr ⟨hsideSub hQdata.1, hQdata.2⟩
  have hunion : Reserve.localDegree (posBlocks ∪ negBlocks) J ≤
      Reserve.localDegree posBlocks J + Reserve.localDegree negBlocks J := by
    let allJ := (posBlocks ∪ negBlocks).filter fun Q ↦ J ⊆ Q
    let posJ' := posBlocks.filter fun Q ↦ J ⊆ Q
    let negJ' := negBlocks.filter fun Q ↦ J ⊆ Q
    have hsub : allJ ⊆ posJ' ∪ negJ' := by
      intro Q hQ
      have hQdata := Finset.mem_filter.mp hQ
      rcases Finset.mem_union.mp hQdata.1 with hQpos | hQneg
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hQpos, hQdata.2⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hQneg, hQdata.2⟩)
    exact (Finset.card_le_card hsub).trans (by
      simpa [allJ, posJ', negJ', Reserve.localDegree] using
        Finset.card_union_le posJ' negJ')
  exact hdegreeSub.trans (hunion.trans (by
    simpa [posJ, negJ, compatibleNearPositiveSideLoad,
      compatibleNearNegativeSideLoad, occurrences] using
        Nat.add_le_add hpos hneg))

/-- Every prescribed edge of a compatible near-elimination pair is either
an input-root edge or a free edge already charged to the splitting
allocator. -/
theorem compatibleNearEliminationPairSideBoundary_subset_rootBoundary_union_freeUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden) :
    eliminationPairSideBoundary
        (compatibleNearEliminationPairs S hr hrk hrootForbidden) ⊆
      rootBoundary roots r ∪ S.freeUnion := by
  classical
  have hoccurrence (O : NearOccurrence roots (2 * m) k r)
      {g : Finset (Fin n)}
      (hg : g ∈ (nearOccurrenceBlock S O).powersetCard r) :
      g ∈ rootBoundary roots r ∪ S.freeUnion := by
    have hspecial : nearOccurrenceBlock S O ∈
        mappedNegative E (S.embedding O.1.1.1 O.1.1.2 O.1.2) := by
      exact mappedSpecial_mem_mappedNegative E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) O.2
    have hhost : g ∈ mappedHost E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) :=
      (mappedNegative_decomp E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2)).2.1
          (nearOccurrenceBlock S O) hspecial hg
    rcases mem_mappedRootBoundary_or_imageFreeEdges E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) hhost with hroot | hfree
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨O.1.1.1, O.1.1.2, ?_⟩
      simpa [S.root_image O.1.1.1 O.1.1.2 O.1.2] using hroot
    · exact Finset.mem_union_right _
        (S.image_subset_freeUnion O.1.1.1 O.1.1.2 O.1.2 hfree)
  intro g hg
  obtain ⟨Q, hQ, hgQ⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
    have hpos := congrArg EliminationPair.positive hXP
    rw [compatibleNearEliminationPairEmbedding_positive] at hpos
    rw [← hpos] at hgQ
    exact hoccurrence X.1.1 hgQ
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
    have hneg := congrArg EliminationPair.negative hXP
    rw [compatibleNearEliminationPairEmbedding_negative] at hneg
    rw [← hneg] at hgQ
    exact hoccurrence X.1.2 hgQ

/-- A fixed positive block occurs in only the opposite-side fibre over its
unique near occurrence. -/
theorem compatibleNearEliminationPairs_fixed_positive_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (Q : Finset (Fin n)) :
    ((compatibleNearEliminationPairs S hr hrk hrootForbidden).filter
      fun P ↦ P.positive = Q).card ≤ m * M := by
  classical
  let occurrenceFiber : Finset ↥(compatibleNearOccurrencePairs S) :=
    (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter fun X ↦
      nearOccurrenceBlock S X.1.1 = Q
  have hpairEq :
      ((compatibleNearEliminationPairs S hr hrk hrootForbidden).filter
        fun P ↦ P.positive = Q).card = occurrenceFiber.card := by
    rw [compatibleNearEliminationPairs, Finset.filter_map, Finset.card_map]
    apply congrArg Finset.card
    ext X
    simp only [Finset.mem_filter, Finset.mem_attach, occurrenceFiber,
      Finset.mem_univ, true_and, Function.comp_apply]
    rw [compatibleNearEliminationPairEmbedding_positive
      S hr hrk hrootForbidden X]
  by_cases hfiber : occurrenceFiber = ∅
  · simp [hpairEq, hfiber]
  · obtain ⟨X₀, hX₀⟩ := Finset.nonempty_iff_ne_empty.mpr hfiber
    have hsub : occurrenceFiber ⊆
        (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ X.1.1 = X₀.1.1 := by
      intro X hX
      have hXdata := Finset.mem_filter.mp hX
      have hX₀data := Finset.mem_filter.mp hX₀
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ X, ?_⟩
      exact nearOccurrenceBlock_injective S hr hrk hrootForbidden
        (hXdata.2.trans hX₀data.2.symm)
    have hfixed :
        ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ X.1.1 = X₀.1.1).card ≤
        ((compatibleNearOccurrencePairs S).filter
          fun X ↦ X.1 = X₀.1.1).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro X hX
        exact Finset.mem_filter.mpr
          ⟨X.2, (Finset.mem_filter.mp hX).2⟩
      · intro X hX Y hY hEq
        exact Subtype.ext hEq
    rw [hpairEq]
    exact ((Finset.card_le_card hsub).trans hfixed).trans
      (card_compatibleNearOccurrencePairs_fixed_positive_le S hrk.le
        hrootMultiplicity X₀.1.1)

/-- Symmetric fixed-negative fibre bound for the set of elimination pairs. -/
theorem compatibleNearEliminationPairs_fixed_negative_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C M : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
      Transversal.incidenceCount roots g ≤ M)
    (Q : Finset (Fin n)) :
    ((compatibleNearEliminationPairs S hr hrk hrootForbidden).filter
      fun P ↦ P.negative = Q).card ≤ m * M := by
  classical
  let occurrenceFiber : Finset ↥(compatibleNearOccurrencePairs S) :=
    (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter fun X ↦
      nearOccurrenceBlock S X.1.2 = Q
  have hpairEq :
      ((compatibleNearEliminationPairs S hr hrk hrootForbidden).filter
        fun P ↦ P.negative = Q).card = occurrenceFiber.card := by
    rw [compatibleNearEliminationPairs, Finset.filter_map, Finset.card_map]
    apply congrArg Finset.card
    ext X
    simp only [Finset.mem_filter, Finset.mem_attach, occurrenceFiber,
      Finset.mem_univ, true_and, Function.comp_apply]
    rw [compatibleNearEliminationPairEmbedding_negative
      S hr hrk hrootForbidden X]
  by_cases hfiber : occurrenceFiber = ∅
  · simp [hpairEq, hfiber]
  · obtain ⟨X₀, hX₀⟩ := Finset.nonempty_iff_ne_empty.mpr hfiber
    have hsub : occurrenceFiber ⊆
        (Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ X.1.2 = X₀.1.2 := by
      intro X hX
      have hXdata := Finset.mem_filter.mp hX
      have hX₀data := Finset.mem_filter.mp hX₀
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ X, ?_⟩
      exact nearOccurrenceBlock_injective S hr hrk hrootForbidden
        (hXdata.2.trans hX₀data.2.symm)
    have hfixed :
        ((Finset.univ : Finset ↥(compatibleNearOccurrencePairs S)).filter
          fun X ↦ X.1.2 = X₀.1.2).card ≤
        ((compatibleNearOccurrencePairs S).filter
          fun X ↦ X.2 = X₀.1.2).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro X hX
        exact Finset.mem_filter.mpr
          ⟨X.2, (Finset.mem_filter.mp hX).2⟩
      · intro X hX Y hY hEq
        exact Subtype.ext hEq
    rw [hpairEq]
    exact ((Finset.card_le_card hsub).trans hfixed).trans
      (card_compatibleNearOccurrencePairs_fixed_negative_le S hrk.le
        hrootMultiplicity X₀.1.2)

theorem compatibleNearPairRoots_powerBounded_of_load
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C d : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (hload : ∀ J : Finset (Fin n), J.card = r - 1 →
      (compatibleNearPairLoad S hr hrk hrootForbidden J) ^ d ≤
        n ^ (d - 1)) :
    ∀ J : Finset (Fin n), J.card = r - 1 →
      (Reserve.localDegree
        ((compatibleNearEliminationPairs S hr hrk hrootForbidden).image
          EliminationPair.root) J) ^ d ≤ n ^ (d - 1) := by
  intro J hJ
  exact (Nat.pow_le_pow_left
    (compatibleNearPairRootDegree_le_load S hr hrk hrootForbidden J) d).trans
      (hload J hJ)

/-- Once the two side schedules have the required power bound, the generic
rooted theorem places the whole fixed first-round bank.  No bound on mixed
subsets of the union of the two prescribed cliques is needed. -/
theorem eventually_exists_compatibleNearEliminationEmbeddings_twoScale
    {dInput dPath : ℕ}
    (E : RelabeledFullExchange k r) (hr : 0 < r) (hrk : r < k)
    (e₀ : RootEdge k r) (htrace : E.SpecialTraceIsolated e₀)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath) (m M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots splitForbidden : Finset (Finset (Fin n)))
        (splitCap : ℕ)
        (S : BoundedMultiRootedFamilyEmbeddings
          E.pattern roots splitForbidden (2 * m) splitCap)
        (hrootForbidden : rootBoundary roots r ⊆ splitForbidden)
        (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
          Transversal.incidenceCount roots g ≤ M)
        (eliminationForbidden : Finset (Finset (Fin n))),
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (compatibleNearPositiveSideLoad S J +
          compatibleNearNegativeSideLoad S J) ^ dInput ≤
            n ^ (dInput - 1)) →
      (∀ g ∈ eliminationForbidden, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree eliminationForbidden J) ^ dInput ≤
          n ^ (dInput - 1)) →
      Nonempty (BoundedEliminationPairEmbeddings E e₀
        (compatibleNearEliminationPairs S hr hrk hrootForbidden)
        eliminationForbidden
        (scaledDecoderPathCap (m * M + 1) E.v r dPath n)) := by
  have hplace :=
    eventually_exists_boundedEliminationPairEmbeddings_twoScale
      E hr hrk e₀ htrace hdInput hdPath hgap
        (m * M + 1) (by omega)
  filter_upwards [hplace] with n hplace
  intro roots splitForbidden splitCap S hrootForbidden hrootMultiplicity
    eliminationForbidden hload hforbiddenUniform hforbiddenDegree
  exact hplace (compatibleNearEliminationPairs S hr hrk hrootForbidden)
    eliminationForbidden
    (fun Q ↦ (compatibleNearEliminationPairs_fixed_positive_le S hr hrk
      hrootForbidden hrootMultiplicity Q).trans (Nat.le_add_right _ 1))
    (fun Q ↦ (compatibleNearEliminationPairs_fixed_negative_le S hr hrk
      hrootForbidden hrootMultiplicity Q).trans (Nat.le_add_right _ 1))
    (fun J hJ ↦ (Nat.pow_le_pow_left
      (compatibleNearEliminationPairSides_degree_le_sideLoads
        S hr hrk hrootForbidden J) dInput).trans (hload J hJ))
    hforbiddenUniform hforbiddenDegree

/-- Equal-denominator compatibility wrapper. -/
theorem eventually_exists_compatibleNearEliminationEmbeddings
    (E : RelabeledFullExchange k r) (hr : 0 < r) (hrk : r < k)
    (e₀ : RootEdge k r) (htrace : E.SpecialTraceIsolated e₀)
    (hd : 0 < d) (m M : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots splitForbidden : Finset (Finset (Fin n)))
        (splitCap : ℕ)
        (S : BoundedMultiRootedFamilyEmbeddings
          E.pattern roots splitForbidden (2 * m) splitCap)
        (hrootForbidden : rootBoundary roots r ⊆ splitForbidden)
        (hrootMultiplicity : ∀ g : Finset (Fin n), g.card = r →
          Transversal.incidenceCount roots g ≤ M)
        (eliminationForbidden : Finset (Finset (Fin n))),
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (compatibleNearPositiveSideLoad S J +
          compatibleNearNegativeSideLoad S J) ^ d ≤ n ^ (d - 1)) →
      (∀ g ∈ eliminationForbidden, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree eliminationForbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedEliminationPairEmbeddings E e₀
        (compatibleNearEliminationPairs S hr hrk hrootForbidden)
        eliminationForbidden
        (scaledDecoderPathCap (m * M + 1) E.v r d n)) := by
  simpa using
    (eventually_exists_compatibleNearEliminationEmbeddings_twoScale
      E hr hrk e₀ htrace hd hd (by omega) m M)

/-- A matched opposite-sign pair of near occurrences is a valid root for
one elimination exchange. -/
def matchedNearEliminationPair
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    (O : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)) :
    EliminationPair n k r := by
  have hposIndex : (f O).1.1 ∈ positiveBankSelection (m := m) roots θ :=
    (Finset.mem_product.mp (f O).2).1
  have hnegIndex : O.1.1 ∈ negativeBankSelection (m := m) roots θ :=
    (Finset.mem_product.mp O.2).1
  have hindex : (f O).1.1 ≠ O.1.1 := by
    intro hEq
    exact Finset.disjoint_left.mp
      (positiveBankSelection_disjoint_negativeBankSelection roots θ)
      hposIndex (hEq ▸ hnegIndex)
  exact
    { positive := nearOccurrenceBlock S (f O).1
      negative := nearOccurrenceBlock S O.1
      positive_card := nearOccurrenceBlock_card S (f O).1
      negative_card := nearOccurrenceBlock_card S O.1
      inter_card := mappedSpecial_multi_inter_card_of_same_edge
        S hr hrootForbidden hindex (f O).1.2 O.1.2 (hf O) }

theorem matchedNearEliminationPair_injective
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    Function.Injective
      (matchedNearEliminationPair S hr hrk hrootForbidden θ f hf) := by
  intro O O' hpair
  have hnegative := congrArg EliminationPair.negative hpair
  apply Subtype.ext
  exact nearOccurrenceBlock_injective S hr hrk hrootForbidden hnegative

def matchedNearEliminationPairEmbedding
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      EliminationPair n k r :=
  ⟨matchedNearEliminationPair S hr hrk hrootForbidden θ f hf,
    matchedNearEliminationPair_injective S hr hrk hrootForbidden θ f hf⟩

def matchedNearEliminationPairs
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    Finset (EliminationPair n k r) :=
  Finset.univ.map
    (matchedNearEliminationPairEmbedding S hr hrk hrootForbidden θ f hf)

/-- Every coefficient-dependent matched pair belongs to the fixed
coefficient-independent compatible preallocation. -/
theorem matchedNearEliminationPairs_subset_compatible
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf ⊆
      compatibleNearEliminationPairs S hr hrk hrootForbidden := by
  intro P hP
  obtain ⟨O, _hO, hOP⟩ := Finset.mem_map.mp hP
  let Xval : NearOccurrence roots (2 * m) k r ×
      NearOccurrence roots (2 * m) k r := ((f O).1, O.1)
  have hXval : Xval ∈ compatibleNearOccurrencePairs S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hf O⟩
    · apply Finset.mem_product.mpr
      exact ⟨positiveBankSelection_subset_allPositiveBankIndices roots θ
        (Finset.mem_product.mp (f O).2).1,
        (Finset.mem_product.mp (f O).2).2⟩
    · apply Finset.mem_product.mpr
      exact ⟨negativeBankSelection_subset_allNegativeBankIndices roots θ
        (Finset.mem_product.mp O.2).1,
        (Finset.mem_product.mp O.2).2⟩
  let X : ↥(compatibleNearOccurrencePairs S) := ⟨Xval, hXval⟩
  apply Finset.mem_map.mpr
  refine ⟨X, Finset.mem_univ X, ?_⟩
  calc
    compatibleNearEliminationPair S hr hrk hrootForbidden X =
        matchedNearEliminationPair S hr hrk hrootForbidden θ f hf O := by
      apply EliminationPair.ext <;> rfl
    _ = P := hOP

/-- The number of matched elimination roots containing a prescribed face,
counted before quotienting equal root unions.  This is the load controlled
by the random fibrewise matching in the source proof. -/
def matchedNearPairLoad
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    (J : Finset (Fin n)) : ℕ :=
  ((Finset.univ : Finset
      ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).filter
    fun O ↦ J ⊆
      (matchedNearEliminationPair S hr hrk hrootForbidden θ f hf O).root).card

/-- Taking an image can only decrease a face load.  In particular the
root-family degree needed by the elimination placement theorem is bounded
by the occurrence-level matching load above. -/
theorem matchedNearPairRootDegree_le_load
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    (J : Finset (Fin n)) :
    Reserve.localDegree
        ((matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).image
          EliminationPair.root) J ≤
      matchedNearPairLoad S hr hrk hrootForbidden θ f hf J := by
  classical
  let pairEmb :=
    matchedNearEliminationPairEmbedding S hr hrk hrootForbidden θ f hf
  let rootMap :
      ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) →
        Finset (Fin n) := fun O ↦ (pairEmb O).root
  have hrootSet :
      (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).image
          EliminationPair.root =
        (Finset.univ : Finset
          ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).image
            rootMap := by
    ext Q
    simp [matchedNearEliminationPairs, pairEmb, rootMap,
      matchedNearEliminationPairEmbedding]
  have hsubset :
      (((Finset.univ : Finset
          ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).image
            rootMap).filter fun Q ↦ J ⊆ Q) ⊆
        (((Finset.univ : Finset
          ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).filter
            fun O ↦ J ⊆ rootMap O).image rootMap) := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    obtain ⟨O, _hO, rfl⟩ := Finset.mem_image.mp hQdata.1
    exact Finset.mem_image.mpr
      ⟨O, Finset.mem_filter.mpr ⟨Finset.mem_univ O, hQdata.2⟩, rfl⟩
  calc
    Reserve.localDegree
        ((matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).image
          EliminationPair.root) J =
        (((Finset.univ : Finset
          ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).image
            rootMap).filter fun Q ↦ J ⊆ Q).card := by
      rw [hrootSet]
      rfl
    _ ≤ (((Finset.univ : Finset
          ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).filter
            fun O ↦ J ⊆ rootMap O).image rootMap).card :=
      Finset.card_le_card hsubset
    _ ≤ ((Finset.univ : Finset
          ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ)).filter
            fun O ↦ J ⊆ rootMap O).card := Finset.card_image_le
    _ = matchedNearPairLoad S hr hrk hrootForbidden θ f hf J := by
      rfl

/-- A power bound for the occurrence-level matching load is exactly the
quantitative input required to place all first-round elimination gadgets. -/
theorem matchedNearPairRoots_powerBounded_of_load
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C d : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    (hload : ∀ J : Finset (Fin n), J.card = r - 1 →
      (matchedNearPairLoad S hr hrk hrootForbidden θ f hf J) ^ d ≤
        n ^ (d - 1)) :
    ∀ J : Finset (Fin n), J.card = r - 1 →
      (Reserve.localDegree
        ((matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).image
          EliminationPair.root) J) ^ d ≤ n ^ (d - 1) := by
  intro J hJ
  exact (Nat.pow_le_pow_left
    (matchedNearPairRootDegree_le_load S hr hrk hrootForbidden θ f hf J) d).trans
      (hload J hJ)

def matchedNearPositiveBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    Finset (Finset (Fin n)) :=
  (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).image
    EliminationPair.positive

theorem matchedNearPairs_negative_image
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).image
        EliminationPair.negative =
      selectedBankNegativeNearBlocks S θ := by
  classical
  ext B
  constructor
  · intro hB
    obtain ⟨P, hP, hPB⟩ := Finset.mem_image.mp hB
    obtain ⟨O, hO, hOP⟩ := Finset.mem_map.mp hP
    subst P
    change nearOccurrenceBlock S O.1 = B at hPB
    subst B
    apply Finset.mem_biUnion.mpr
    exact ⟨O.1.1, (Finset.mem_product.mp O.2).1,
      Finset.mem_image.mpr ⟨O.1.2, Finset.mem_univ _, rfl⟩⟩
  · intro hB
    obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨e, _he, heB⟩ := Finset.mem_image.mp hBI
    let O : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) :=
      ⟨(I, e), Finset.mem_product.mpr ⟨hI, Finset.mem_univ _⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨matchedNearEliminationPair S hr hrk hrootForbidden θ f hf O,
      ?_, ?_⟩
    · apply Finset.mem_map.mpr
      exact ⟨O, Finset.mem_univ _, rfl⟩
    · simpa [matchedNearEliminationPair, nearOccurrenceBlock, O] using heB

theorem matchedNearPositiveBlocks_subset_selected
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    matchedNearPositiveBlocks S hr hrk hrootForbidden θ f hf ⊆
      selectedBankPositiveNearBlocks S θ := by
  intro B hB
  obtain ⟨P, hP, hPB⟩ := Finset.mem_image.mp hB
  obtain ⟨O, hO, hOP⟩ := Finset.mem_map.mp hP
  subst P
  change nearOccurrenceBlock S (f O).1 = B at hPB
  subst B
  apply Finset.mem_biUnion.mpr
  exact ⟨(f O).1.1, (Finset.mem_product.mp (f O).2).1,
    Finset.mem_image.mpr ⟨(f O).1.2, Finset.mem_univ _, rfl⟩⟩

theorem matchedNearPairs_positive_injOn
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    Set.InjOn EliminationPair.positive
      (↑(matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf) :
        Set (EliminationPair n k r)) := by
  intro P hP P' hP' hpositive
  obtain ⟨O, _hO, hOP⟩ := Finset.mem_map.mp hP
  obtain ⟨O', _hO', hO'P'⟩ := Finset.mem_map.mp hP'
  subst P
  subst P'
  have hblocks : nearOccurrenceBlock S (f O).1 =
      nearOccurrenceBlock S (f O').1 := by
    exact hpositive
  have hvals := nearOccurrenceBlock_injective S hr hrk hrootForbidden hblocks
  have hsub : f O = f O' := Subtype.ext hvals
  have hOO' := f.injective hsub
  subst O'
  rfl

theorem matchedNearPairs_negative_injOn
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    Set.InjOn EliminationPair.negative
      (↑(matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf) :
        Set (EliminationPair n k r)) := by
  intro P hP P' hP' hnegative
  obtain ⟨O, _hO, hOP⟩ := Finset.mem_map.mp hP
  obtain ⟨O', _hO', hO'P'⟩ := Finset.mem_map.mp hP'
  subst P
  subst P'
  have hvals := nearOccurrenceBlock_injective S hr hrk hrootForbidden hnegative
  have hOO' : O = O' := Subtype.ext hvals
  subst O'
  rfl

/-- The matched pair sum is exactly the incidence difference between the
used positive near blocks and all selected negative near blocks. -/
theorem matchedNearPairs_signed_sum
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    (g : Finset (Fin n)) :
    ∑ P ∈ (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).attach,
        ((if g ⊆ P.1.positive then (1 : ℤ) else 0) -
          (if g ⊆ P.1.negative then (1 : ℤ) else 0)) =
      (Transversal.incidenceCount
          (matchedNearPositiveBlocks S hr hrk hrootForbidden θ f hf) g : ℤ) -
      (Transversal.incidenceCount
          (selectedBankNegativeNearBlocks S θ) g : ℤ) := by
  classical
  let pairs := matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf
  have hposNat := incidenceCount_image_of_injective pairs
    EliminationPair.positive
    (matchedNearPairs_positive_injOn S hr hrk hrootForbidden θ f hf) g
  have hnegNat := incidenceCount_image_of_injective pairs
    EliminationPair.negative
    (matchedNearPairs_negative_injOn S hr hrk hrootForbidden θ f hf) g
  have hposInt :
      (Transversal.incidenceCount (pairs.image EliminationPair.positive) g : ℤ) =
        ∑ P ∈ pairs, if g ⊆ P.positive then (1 : ℤ) else 0 := by
    exact_mod_cast hposNat
  have hnegInt :
      (Transversal.incidenceCount (pairs.image EliminationPair.negative) g : ℤ) =
        ∑ P ∈ pairs, if g ⊆ P.negative then (1 : ℤ) else 0 := by
    exact_mod_cast hnegNat
  calc
    (∑ P ∈ (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf).attach,
        ((if g ⊆ P.1.positive then (1 : ℤ) else 0) -
          (if g ⊆ P.1.negative then (1 : ℤ) else 0))) =
        ∑ P ∈ pairs,
          ((if g ⊆ P.positive then (1 : ℤ) else 0) -
            (if g ⊆ P.negative then (1 : ℤ) else 0)) := by
      simpa [pairs] using Finset.sum_attach pairs (fun P ↦
        (if g ⊆ P.positive then (1 : ℤ) else 0) -
          (if g ⊆ P.negative then (1 : ℤ) else 0))
    _ = (∑ P ∈ pairs, if g ⊆ P.positive then (1 : ℤ) else 0) -
        ∑ P ∈ pairs, if g ⊆ P.negative then (1 : ℤ) else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (Transversal.incidenceCount
          (matchedNearPositiveBlocks S hr hrk hrootForbidden θ f hf) g : ℤ) -
        (Transversal.incidenceCount
          (selectedBankNegativeNearBlocks S θ) g : ℤ) := by
      rw [← hposInt, ← hnegInt]
      simp [pairs, matchedNearPositiveBlocks,
        matchedNearPairs_negative_image S hr hrk hrootForbidden θ f hf]

/-- The matched family satisfies the source-accurate separation premise of
the first elimination round: common edges of distinct prescribed negative
cliques are their common distinguished input edge, hence lie in both
prescribed positive cliques. -/
theorem matchedNearPairs_common_in_positive
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1) :
    ∀ P ∈ matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf,
      ∀ P' ∈ matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf,
        P ≠ P' → ∀ g ∈ P.negative.powersetCard r,
          g ∈ P'.negative.powersetCard r →
            g ⊆ P.positive ∧ g ⊆ P'.positive := by
  intro P hP P' hP' hPP' g hg hg'
  obtain ⟨O, _hO, hOP⟩ := Finset.mem_map.mp hP
  obtain ⟨O', _hO', hO'P'⟩ := Finset.mem_map.mp hP'
  subst P
  subst P'
  have hOO' : O ≠ O' := by
    intro hEq
    subst O'
    exact hPP' rfl
  change g ∈ (nearOccurrenceBlock S O.1).powersetCard r at hg
  change g ∈ (nearOccurrenceBlock S O'.1).powersetCard r at hg'
  have hcommon := nearOccurrence_common_edge_eq S hr hrk hrootForbidden
    (fun hval ↦ hOO' (Subtype.ext hval)) hg hg'
  constructor
  · change g ⊆ nearOccurrenceBlock S (f O).1
    rw [hcommon.1, ← hf O]
    exact nearOccurrenceEdge_subset_block S (f O).1
  · change g ⊆ nearOccurrenceBlock S (f O').1
    rw [hcommon.1, hcommon.2, ← hf O']
    exact nearOccurrenceEdge_subset_block S (f O').1

/-- Execute the complete first elimination round for the matched near
family.  The output has the exact matched signed boundary and its negative
part is already an edge-disjoint decomposition. -/
theorem matchedNearEliminationRound
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ splitForbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (T : BoundedEliminationPairEmbeddings E e₀
      (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf)
      eliminationForbidden eliminationCap)
    (heliminationRootForbidden :
      eliminationPairSideBoundary
        (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf) ⊆
          eliminationForbidden) :
    Disjoint (allEliminationPositiveOnly T)
        (allEliminationNegativeOnly T) ∧
      IsUniformDecomposition (allEliminationNegativeOnlyHost T)
        (allEliminationNegativeOnly T) k r ∧
      ∀ g : Finset (Fin n), g.card = r →
        (Transversal.incidenceCount (allEliminationPositiveOnly T) g : ℤ) -
            (Transversal.incidenceCount (allEliminationNegativeOnly T) g : ℤ) =
          (Transversal.incidenceCount
            (matchedNearPositiveBlocks S hr hrk hrootForbidden θ f hf) g : ℤ) -
            (Transversal.incidenceCount
              (selectedBankNegativeNearBlocks S θ) g : ℤ) := by
  have hround := allEliminationOnly_round_of_common_in_positive T hr hrk
    heliminationRootForbidden
    (matchedNearPairs_common_in_positive S hr hrk hrootForbidden θ f hf)
  refine ⟨hround.1, hround.2.1, ?_⟩
  intro g hg
  rw [hround.2.2 g hg]
  exact matchedNearPairs_signed_sum S hr hrk hrootForbidden θ f hf g

/-- Execute a coefficient-dependent matching by restricting the genuinely
fixed compatible-pair preallocation. -/
theorem matchedNearEliminationRound_of_compatibleBank
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ splitForbidden)
    (θ : Finset (Fin n) → ℤ)
    (f : ↥(negativeNearOccurrences (k := k) (r := r) (m := m) roots θ) ↪
      ↥(positiveNearOccurrences (k := k) (r := r) (m := m) roots θ))
    (hf : ∀ O, nearOccurrenceEdge S (f O).1 = nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      eliminationPairSideBoundary
        (compatibleNearEliminationPairs S hr hrk hrootForbidden) ⊆
          eliminationForbidden) :
    let T := U.restrict
      (matchedNearEliminationPairs_subset_compatible S hr hrk
        hrootForbidden θ f hf)
    Disjoint (allEliminationPositiveOnly T)
        (allEliminationNegativeOnly T) ∧
      IsUniformDecomposition (allEliminationNegativeOnlyHost T)
        (allEliminationNegativeOnly T) k r ∧
      ∀ g : Finset (Fin n), g.card = r →
        (Transversal.incidenceCount (allEliminationPositiveOnly T) g : ℤ) -
            (Transversal.incidenceCount (allEliminationNegativeOnly T) g : ℤ) =
          (Transversal.incidenceCount
            (matchedNearPositiveBlocks S hr hrk hrootForbidden θ f hf) g : ℤ) -
            (Transversal.incidenceCount
              (selectedBankNegativeNearBlocks S θ) g : ℤ) := by
  let hsub := matchedNearEliminationPairs_subset_compatible S hr hrk
    hrootForbidden θ f hf
  let T := U.restrict hsub
  have hselectedRootForbidden :
      eliminationPairSideBoundary
        (matchedNearEliminationPairs S hr hrk hrootForbidden θ f hf) ⊆
          eliminationForbidden :=
    (eliminationPairSideBoundary_mono hsub).trans huniversalRootForbidden
  exact matchedNearEliminationRound S hr hrk hrootForbidden θ f hf T
    hselectedRootForbidden

end

end Erdos722.NearPairing

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
import ErdosProblems.Erdos722.NearPairing
import Mathlib

set_option relaxedAutoImplicit true

/-!
# The fixed further-elimination bank

After the first elimination round, a negative output block is called bad
when it shares an `r`-edge with a negative near splitting block.  Keevash's
splitting geometry gives every bad block a unique positive far splitting
block through its bad edge.  This file records the coefficient-independent
finite construction that turns those unique partners into the roots of the
second elimination round.

The definitions below deliberately take the existence and uniqueness of the
positive partner as hypotheses.  The geometric specialization to the fixed
splitting and first-elimination banks is proved separately; the finite facts
here do not depend on how those banks were embedded.
-/

namespace Erdos722.FurtherElimination

open Finset
open Erdos722.Transversal
open Erdos722.Reserve
open Erdos722.ExchangeEliminationEmbedding

noncomputable section

variable {n k r : ℕ}

/-- First-round negative output blocks which meet the permanently negative
near bank in an entire `r`-edge. -/
def badEliminationBlocks (r : ℕ)
    (firstNegative negativeNear : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  firstNegative.filter fun B ↦
    ∃ e ∈ B.powersetCard r, ∃ N ∈ negativeNear, e ⊆ N

@[simp] theorem mem_badEliminationBlocks
    {B : Finset (Fin n)} :
    B ∈ badEliminationBlocks r firstNegative negativeNear ↔
      B ∈ firstNegative ∧
        ∃ e ∈ B.powersetCard r, ∃ N ∈ negativeNear, e ⊆ N := by
  simp [badEliminationBlocks]

theorem badEliminationBlocks_subset_firstNegative :
    badEliminationBlocks r firstNegative negativeNear ⊆ firstNegative := by
  exact Finset.filter_subset _ _

theorem badEliminationBlocks_mono_first
    {firstNegative firstNegative' negativeNear :
      Finset (Finset (Fin n))}
    (hsub : firstNegative ⊆ firstNegative') :
    badEliminationBlocks r firstNegative negativeNear ⊆
      badEliminationBlocks r firstNegative' negativeNear := by
  intro B hB
  have hm := mem_badEliminationBlocks.mp hB
  exact mem_badEliminationBlocks.mpr ⟨hsub hm.1, hm.2⟩

/-- If two finite sets have one common `r`-edge and every common `r`-edge
is that edge, their intersection has exactly `r` vertices. -/
theorem inter_card_eq_of_unique_common_edge
    (hr : 0 < r) {A B e : Finset (Fin n)}
    (heA : e ∈ A.powersetCard r) (heB : e ∈ B.powersetCard r)
    (hunique : ∀ g ∈ (A ∩ B).powersetCard r, g = e) :
    (A ∩ B).card = r := by
  have heInter : e ∈ (A ∩ B).powersetCard r := by
    have heAdata := Finset.mem_powersetCard.mp heA
    have heBdata := Finset.mem_powersetCard.mp heB
    exact Finset.mem_powersetCard.mpr
      ⟨fun x hx ↦ Finset.mem_inter.mpr ⟨heAdata.1 hx, heBdata.1 hx⟩,
        heAdata.2⟩
  have hsingle : (A ∩ B).powersetCard r = {e} := by
    ext g
    constructor
    · intro hg
      simpa [hunique g hg]
    · intro hg
      have hge : g = e := Finset.mem_singleton.mp hg
      subst g
      exact heInter
  have hchoose : Nat.choose (A ∩ B).card r = 1 := by
    rw [← Finset.card_powersetCard, hsingle]
    simp
  rcases Nat.choose_eq_one_iff.mp hchoose with hrzero | hinter
  · omega
  · exact hinter

/-- A positive partner for every bad negative block.  In the application the
partner is the unique positive far splitting block through the bad edge. -/
def HasFurtherPartners (n k r : ℕ)
    (bad positive : Finset (Finset (Fin n))) : Prop :=
  ∀ B ∈ bad, ∃ P ∈ positive,
    P.card = k ∧ B.card = k ∧ (P ∩ B).card = r

/-- The canonical partner chosen from a proof of `HasFurtherPartners`. -/
noncomputable def furtherPositivePartner
    (hpartner : HasFurtherPartners n k r bad positive)
    (B : ↑bad) : Finset (Fin n) :=
  Classical.choose (hpartner B.1 B.2)

theorem furtherPositivePartner_mem
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    furtherPositivePartner hpartner B ∈ positive :=
  (Classical.choose_spec (hpartner B.1 B.2)).1

theorem furtherPositivePartner_card
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    (furtherPositivePartner hpartner B).card = k :=
  (Classical.choose_spec (hpartner B.1 B.2)).2.1

theorem furtherNegativeBlock_card
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    B.1.card = k :=
  (Classical.choose_spec (hpartner B.1 B.2)).2.2.1

theorem furtherPartner_inter_card
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    (furtherPositivePartner hpartner B ∩ B.1).card = r :=
  (Classical.choose_spec (hpartner B.1 B.2)).2.2.2

/-- The ordered positive/negative root used to remove one bad block. -/
def furtherEliminationPair
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    EliminationPair n k r where
  positive := furtherPositivePartner hpartner B
  negative := B.1
  positive_card := furtherPositivePartner_card hpartner B
  negative_card := furtherNegativeBlock_card hpartner B
  inter_card := furtherPartner_inter_card hpartner B

@[simp] theorem furtherEliminationPair_positive
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    (furtherEliminationPair hpartner B).positive =
      furtherPositivePartner hpartner B := rfl

@[simp] theorem furtherEliminationPair_negative
    (hpartner : HasFurtherPartners n k r bad positive) (B : ↑bad) :
    (furtherEliminationPair hpartner B).negative = B.1 := rfl

theorem furtherEliminationPair_injective
    (hpartner : HasFurtherPartners n k r bad positive) :
    Function.Injective (furtherEliminationPair hpartner) := by
  intro B B' h
  apply Subtype.ext
  exact congrArg EliminationPair.negative h

def furtherEliminationPairEmbedding
    (hpartner : HasFurtherPartners n k r bad positive) :
    ↑bad ↪ EliminationPair n k r :=
  ⟨furtherEliminationPair hpartner,
    furtherEliminationPair_injective hpartner⟩

/-- The fixed family of all roots needed by the further-elimination round. -/
def furtherEliminationPairs
    (hpartner : HasFurtherPartners n k r bad positive) :
    Finset (EliminationPair n k r) :=
  bad.attach.map (furtherEliminationPairEmbedding hpartner)

theorem mem_furtherEliminationPairs_iff
    (hpartner : HasFurtherPartners n k r bad positive)
    {P : EliminationPair n k r} :
    P ∈ furtherEliminationPairs hpartner ↔
      ∃ B : ↑bad, furtherEliminationPair hpartner B = P := by
  constructor
  · intro hP
    obtain ⟨B, _hB, hBP⟩ := Finset.mem_map.mp hP
    exact ⟨B, hBP⟩
  · rintro ⟨B, hBP⟩
    apply Finset.mem_map.mpr
    exact ⟨B, Finset.mem_attach _ _, hBP⟩

theorem furtherEliminationPairs_negative_mem
    (hpartner : HasFurtherPartners n k r bad positive)
    {P : EliminationPair n k r}
    (hP : P ∈ furtherEliminationPairs hpartner) :
    P.negative ∈ bad := by
  obtain ⟨B, hBP⟩ := (mem_furtherEliminationPairs_iff hpartner).mp hP
  subst P
  exact B.2

theorem furtherEliminationPairs_positive_mem
    (hpartner : HasFurtherPartners n k r bad positive)
    {P : EliminationPair n k r}
    (hP : P ∈ furtherEliminationPairs hpartner) :
    P.positive ∈ positive := by
  obtain ⟨B, hBP⟩ := (mem_furtherEliminationPairs_iff hpartner).mp hP
  subst P
  exact furtherPositivePartner_mem hpartner B

/-- The sides of the second-round roots use no blocks beyond the two fixed
input banks. -/
theorem eliminationPairSides_further_subset
    (hpartner : HasFurtherPartners n k r bad positive) :
    eliminationPairSides (furtherEliminationPairs hpartner) ⊆
      positive ∪ bad := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact Finset.mem_union_left _
      (furtherEliminationPairs_positive_mem hpartner hP)
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact Finset.mem_union_right _
      (furtherEliminationPairs_negative_mem hpartner hP)

/-- Boundary version of `eliminationPairSides_further_subset`: every
prescribed second-round root edge already occurs in either the fixed
positive bank or the fixed bad-negative bank. -/
theorem eliminationPairSideBoundary_further_subset
    (hpartner : HasFurtherPartners n k r bad positive) :
    eliminationPairSideBoundary (furtherEliminationPairs hpartner) ⊆
      (positive.biUnion fun Q ↦ Q.powersetCard r) ∪
        (bad.biUnion fun Q ↦ Q.powersetCard r) := by
  intro g hg
  obtain ⟨Q, hQ, hgQ⟩ := Finset.mem_biUnion.mp hg
  have hQbank := eliminationPairSides_further_subset hpartner hQ
  rcases Finset.mem_union.mp hQbank with hQpos | hQbad
  · exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨Q, hQpos, hgQ⟩)
  · exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨Q, hQbad, hgQ⟩)

/-- Lower-face load of the second-round side family is bounded by the sum
of the loads of the fixed positive and bad-negative block banks. -/
theorem localDegree_eliminationPairSides_further_le
    (hpartner : HasFurtherPartners n k r bad positive)
    (J : Finset (Fin n)) :
    Reserve.localDegree
        (eliminationPairSides (furtherEliminationPairs hpartner)) J ≤
      Reserve.localDegree positive J + Reserve.localDegree bad J := by
  have hsub := eliminationPairSides_further_subset hpartner
  unfold Reserve.localDegree
  calc
    ((eliminationPairSides (furtherEliminationPairs hpartner)).filter
        fun Q ↦ J ⊆ Q).card ≤
        ((positive ∪ bad).filter fun Q ↦ J ⊆ Q).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    _ ≤ (positive.filter fun Q ↦ J ⊆ Q).card +
        (bad.filter fun Q ↦ J ⊆ Q).card := by
      rw [Finset.filter_union]
      exact Finset.card_union_le _ _

/-- A fixed negative side occurs in at most one second-round root. -/
theorem card_furtherEliminationPairs_fixed_negative_le_one
    (hpartner : HasFurtherPartners n k r bad positive)
    (Q : Finset (Fin n)) :
    ((furtherEliminationPairs hpartner).filter
      fun P ↦ P.negative = Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro P hP P' hP'
  have hneg : P.negative = P'.negative :=
    (Finset.mem_filter.mp hP).2.trans
      (Finset.mem_filter.mp hP').2.symm
  obtain ⟨B, hBP⟩ :=
    (mem_furtherEliminationPairs_iff hpartner).mp
      (Finset.mem_filter.mp hP).1
  obtain ⟨B', hB'P'⟩ :=
    (mem_furtherEliminationPairs_iff hpartner).mp
      (Finset.mem_filter.mp hP').1
  subst P
  subst P'
  have hBB' : B = B' := Subtype.ext hneg
  subst B'
  rfl

/-- A supplied partner-fibre bound is exactly the positive-side fibre bound
needed by the rooted elimination placement theorem. -/
theorem card_furtherEliminationPairs_fixed_positive_le
    (hpartner : HasFurtherPartners n k r bad positive)
    (M : ℕ)
    (hfiber : ∀ Q : Finset (Fin n),
      ((bad.attach).filter fun B ↦
        furtherPositivePartner hpartner B = Q).card ≤ M)
    (Q : Finset (Fin n)) :
    ((furtherEliminationPairs hpartner).filter
      fun P ↦ P.positive = Q).card ≤ M := by
  let source := bad.attach.filter fun B ↦
    furtherPositivePartner hpartner B = Q
  let target := (furtherEliminationPairs hpartner).filter fun P ↦
    P.positive = Q
  have heq : target = source.map (furtherEliminationPairEmbedding hpartner) := by
    ext P
    simp only [target, source, Finset.mem_filter,
      furtherEliminationPairs, Finset.mem_map]
    constructor
    · rintro ⟨hP, hpos⟩
      obtain ⟨B, _hB, rfl⟩ := hP
      exact ⟨B, ⟨Finset.mem_attach _ _, hpos⟩, rfl⟩
    · rintro ⟨B, ⟨hB, hpos⟩, rfl⟩
      exact ⟨⟨B, Finset.mem_attach _ _, rfl⟩, hpos⟩
  change target.card ≤ M
  rw [heq, Finset.card_map]
  exact hfiber Q

/-- The common-edge condition required for the aggregate negative
decomposition transfers directly from bad blocks to the corresponding
second-round roots. -/
theorem furtherEliminationPairs_common_in_positive
    (hpartner : HasFurtherPartners n k r bad positive)
    (hcommon : ∀ B : ↑bad, ∀ B' : ↑bad, B ≠ B' →
      ∀ g ∈ B.1.powersetCard r, g ∈ B'.1.powersetCard r →
        g ⊆ furtherPositivePartner hpartner B ∧
          g ⊆ furtherPositivePartner hpartner B') :
    ∀ P ∈ furtherEliminationPairs hpartner,
      ∀ P' ∈ furtherEliminationPairs hpartner, P ≠ P' →
        ∀ g ∈ P.negative.powersetCard r,
          g ∈ P'.negative.powersetCard r →
            g ⊆ P.positive ∧ g ⊆ P'.positive := by
  intro P hP P' hP' hPP' g hg hg'
  obtain ⟨B, hBP⟩ := (mem_furtherEliminationPairs_iff hpartner).mp hP
  obtain ⟨B', hB'P'⟩ :=
    (mem_furtherEliminationPairs_iff hpartner).mp hP'
  subst P
  subst P'
  apply hcommon B B'
  · intro hBB'
    subst B'
    exact hPP' rfl
  · exact hg
  · exact hg'

/-- Source-facing placement wrapper for the fixed second-round bank.  The
only geometric inputs left to an application are the positive-partner fibre
bound and the combined side degree; trace isolation then supplies every
root-part schedule required by the generic elimination embedding theorem. -/
theorem eventually_exists_boundedFurtherEliminationEmbeddings_twoScale
    {dInput dPath : ℕ}
    (E : ExchangePattern.RelabeledFullExchange k r)
    (hr : 0 < r) (hrk : r < k)
    (e₀ : Exchange.RootEdge k r)
    (htrace : E.SpecialTraceIsolated e₀)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath) (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (bad positive : Finset (Finset (Fin n)))
        (hpartner : HasFurtherPartners n k r bad positive)
        (forbidden : Finset (Finset (Fin n))),
      (∀ Q : Finset (Fin n),
        ((bad.attach).filter fun B ↦
          furtherPositivePartner hpartner B = Q).card ≤ M) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree positive J +
          Reserve.localDegree bad J) ^ dInput ≤
            n ^ (dInput - 1)) →
      (∀ g ∈ forbidden, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ dInput ≤
          n ^ (dInput - 1)) →
      Nonempty (BoundedEliminationPairEmbeddings E e₀
        (furtherEliminationPairs hpartner) forbidden
        (RootedFamilyAsymptotic.scaledDecoderPathCap M E.v r dPath n)) := by
  have hplace :=
    eventually_exists_boundedEliminationPairEmbeddings_twoScale
      E hr hrk e₀ htrace hdInput hdPath hgap M hM
  filter_upwards [hplace] with n hplace
  intro bad positive hpartner forbidden hfiber hside
    hforbiddenUniform hforbiddenDegree
  apply hplace (furtherEliminationPairs hpartner) forbidden
  · exact card_furtherEliminationPairs_fixed_positive_le
      hpartner M hfiber
  · intro Q
    exact (card_furtherEliminationPairs_fixed_negative_le_one
      hpartner Q).trans hM
  · intro J hJ
    exact (Nat.pow_le_pow_left
      (localDegree_eliminationPairSides_further_le hpartner J) dInput).trans
        (hside J hJ)
  · exact hforbiddenUniform
  · exact hforbiddenDegree

/-- Equal-denominator compatibility wrapper. -/
theorem eventually_exists_boundedFurtherEliminationEmbeddings
    (E : ExchangePattern.RelabeledFullExchange k r)
    (hr : 0 < r) (hrk : r < k)
    (e₀ : Exchange.RootEdge k r)
    (htrace : E.SpecialTraceIsolated e₀)
    (hd : 0 < d) (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (bad positive : Finset (Finset (Fin n)))
        (hpartner : HasFurtherPartners n k r bad positive)
        (forbidden : Finset (Finset (Fin n))),
      (∀ Q : Finset (Fin n),
        ((bad.attach).filter fun B ↦
          furtherPositivePartner hpartner B = Q).card ≤ M) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree positive J +
          Reserve.localDegree bad J) ^ d ≤ n ^ (d - 1)) →
      (∀ g ∈ forbidden, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedEliminationPairEmbeddings E e₀
        (furtherEliminationPairs hpartner) forbidden
        (RootedFamilyAsymptotic.scaledDecoderPathCap M E.v r d n)) := by
  simpa using
    (eventually_exists_boundedFurtherEliminationEmbeddings_twoScale
      E hr hrk e₀ htrace hd hd (by omega) M hM)

/-! ## Specialization to the splitting and first-elimination banks -/

/-- The coefficient-independent family of all bad first-round outputs. -/
def universalBadEliminationBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  badEliminationBlocks r (allEliminationNegativeOnly U)
    (NearPairing.allNegativeNearSplittingBlocks S)

/-- Every edge of a universal bad first-round output is charged to the
first elimination bank's prescribed side boundary or its actual free host. -/
theorem universalBadEliminationBlocks_boundary_subset_allocatorHost
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    (universalBadEliminationBlocks S hr hrk hrootForbidden U).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      eliminationPairSideBoundary
          (NearPairing.compatibleNearEliminationPairs S hr hrk
            hrootForbidden) ∪ U.freeUnion := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  apply allEliminationNegativeOnly_edge_mem_sideBoundary_union_freeUnion
    U (badEliminationBlocks_subset_firstNegative hB) hgB

/-- Universal first-round negative outputs which do not collide with a
permanent negative near splitting block. -/
def universalGoodEliminationBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  allEliminationNegativeOnly U \
    universalBadEliminationBlocks S hr hrk hrootForbidden U

/-- Bad outputs actually present after restricting the first-round bank to a
coefficient-dependent near matching. -/
def selectedBadEliminationBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  badEliminationBlocks r
    (allEliminationNegativeOnly (U.restrict hsub))
    (NearPairing.allNegativeNearSplittingBlocks S)

theorem selectedBadEliminationBlocks_subset_universal
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    selectedBadEliminationBlocks S hr hrk hrootForbidden theta f hf U ⊆
      universalBadEliminationBlocks S hr hrk hrootForbidden U := by
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  exact badEliminationBlocks_mono_first
    (allEliminationNegativeOnly_restrict_subset U hsub)

/-- A collision edge of a first-round negative output cannot lie in the
free part of its elimination copy, because that free part was chosen away
from every earlier negative near clique.  It must therefore lie in the
prescribed negative root side. -/
theorem badEdge_mem_firstNegativeRoot
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {eliminationForbidden : Finset (Finset (Fin n))} {C : ℕ}
    (U : BoundedEliminationPairEmbeddings E e₀ pairs
      eliminationForbidden C)
    {negativeNear : Finset (Finset (Fin n))}
    (hnearForbidden :
      negativeNear.biUnion (fun N ↦ N.powersetCard r) ⊆
        eliminationForbidden)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B e N : Finset (Fin n)}
    (hB : B ∈ eliminationNegativeOnly U P hP)
    (heB : e ∈ B.powersetCard r)
    (hN : N ∈ negativeNear) (heN : e ⊆ N) :
    e ∈ P.negative.powersetCard r := by
  have hBrem : B ∈ eliminationNegativeRemainder U P hP :=
    (Finset.mem_sdiff.mp hB).1
  have heHost : e ∈
      RootedEmbedding.imageFreeEdges E.pattern (U.embedding P hP) :=
    (eliminationNegativeRemainder_decomp U P hP).2.1 B hBrem heB
  rcases mem_negativeEdges_or_eliminationFreeEdges U
      (RelabeledFullExchange.isSpecialIsolated E e₀) P hP heHost with
    heNeg | heFree
  · exact heNeg
  · exfalso
    have hecard : e.card = r := (Finset.mem_powersetCard.mp heB).2
    have heNearBoundary : e ∈
        negativeNear.biUnion (fun Q ↦ Q.powersetCard r) := by
      apply Finset.mem_biUnion.mpr
      exact ⟨N, hN, Finset.mem_powersetCard.mpr ⟨heN, hecard⟩⟩
    exact Finset.disjoint_left.mp (U.free_disjoint_forbidden P hP)
      heFree (hnearForbidden heNearBoundary)

/-- A block remaining on the negative side of an elimination exchange
cannot contain an `r`-edge of the prescribed positive root: that root is the
unique positive-decomposition block through each of its edges. -/
theorem eliminationNegativeOnly_edge_not_subset_positive
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (U : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B e : Finset (Fin n)}
    (hB : B ∈ eliminationNegativeOnly U P hP)
    (heB : e ∈ B.powersetCard r) :
    ¬e ⊆ P.positive := by
  intro hePos
  have hBdata := Finset.mem_erase.mp
    (show B ∈ eliminationNegativeRemainder U P hP from
      (Finset.mem_sdiff.mp hB).1)
  have hBmem : B ∈ ExchangeEmbedding.mappedPositive E
      (U.embedding P hP) := hBdata.2
  have hPosmem : P.positive ∈ ExchangeEmbedding.mappedPositive E
      (U.embedding P hP) := by
    simpa [U.maps_positive P hP] using
      ExchangeEmbedding.mappedRoot_mem_mappedPositive E (U.embedding P hP)
  have hecard : e.card = r := (Finset.mem_powersetCard.mp heB).2
  have hePosmem : e ∈ P.positive.powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨hePos, hecard⟩
  have hEq := (ExchangeEmbedding.mappedPositive_decomp E
    (U.embedding P hP)).blocks_eq_of_common_edge
      hBmem hPosmem heB hePosmem
  exact hBdata.1 hEq

/-- An `r`-edge of a negative first-round output which belongs to the
forbidden bank must lie in the prescribed negative root. -/
theorem eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (U : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B g : Finset (Fin n)}
    (hB : B ∈ eliminationNegativeOnly U P hP)
    (hgB : g ∈ B.powersetCard r) (hgForbidden : g ∈ forbidden) :
    g ∈ P.negative.powersetCard r := by
  have hBrem : B ∈ eliminationNegativeRemainder U P hP :=
    (Finset.mem_sdiff.mp hB).1
  have hgHost : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (U.embedding P hP) :=
    (eliminationNegativeRemainder_decomp U P hP).2.1 B hBrem hgB
  rcases mem_negativeEdges_or_eliminationFreeEdges U
      (RelabeledFullExchange.isSpecialIsolated E e₀) P hP hgHost with
    hgNeg | hgFree
  · exact hgNeg
  · exact (Finset.disjoint_left.mp (U.free_disjoint_forbidden P hP)
      hgFree hgForbidden).elim

/-- The distance-refined full exchange makes every first-round negative
output meet the prescribed negative root in at most `r` vertices. -/
theorem eliminationNegativeOnly_inter_negative_card_le
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (hbound : E.SpecialPositiveInterBounded e₀)
    (U : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B : Finset (Fin n)}
    (hB : B ∈ eliminationNegativeOnly U P hP) :
    (B ∩ P.negative).card ≤ r := by
  have hBrem : B ∈ eliminationNegativeRemainder U P hP :=
    (Finset.mem_sdiff.mp hB).1
  have hBmap : B ∈ ExchangeEmbedding.mappedPositive E
      (U.embedding P hP) := (Finset.mem_erase.mp hBrem).2
  obtain ⟨B₀, hB₀, hB₀map⟩ := mem_mapFamily.mp hBmap
  have hlocal := hbound B₀ hB₀
  rw [← U.maps_negative P hP, ← hB₀map]
  simpa [ExchangeEmbedding.mappedSpecial, RootedEmbedding.mapEdge,
    ← Finset.map_inter] using hlocal

/-- Every universal bad first-round block has a positive far splitting
partner through its bad edge.  This is the existence half of Keevash's
unique-partner assertion; the exact-intersection half is isolated below. -/
theorem exists_positiveSplittingPartner_commonEdge
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hnearForbidden :
      (NearPairing.allNegativeNearSplittingBlocks S).biUnion
          (fun N ↦ N.powersetCard r) ⊆ eliminationForbidden)
    {B : Finset (Fin n)}
    (hB : B ∈ universalBadEliminationBlocks S hr hrk hrootForbidden U) :
    ∃ Q ∈ NearPairing.allPositiveSplittingBlocks S,
      ∃ e ∈ B.powersetCard r, e ∈ Q.powersetCard r := by
  have hbad := mem_badEliminationBlocks.mp hB
  obtain ⟨e, heB, N, hN, heN⟩ := hbad.2
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hbad.1
  have hP : P.1 ∈ NearPairing.compatibleNearEliminationPairs S hr hrk
      hrootForbidden := P.2
  obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
  let O : NearPairing.NearOccurrence roots (2 * m) k r := X.1.2
  have hO : O ∈ NearPairing.allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots := by
    exact (Finset.mem_product.mp (Finset.mem_filter.mp X.2).1).2
  have heNeg : e ∈ P.1.negative.powersetCard r :=
    badEdge_mem_firstNegativeRoot U hnearForbidden P.1 P.2 hBP heB hN heN
  have hPnegative : P.1.negative = NearPairing.nearOccurrenceBlock S O := by
    rw [← hXP]
    rfl
  have heO : e ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
    rw [← hPnegative]
    exact heNeg
  have hene : e ≠ NearPairing.nearOccurrenceEdge S O := by
    intro heq
    have hnot := eliminationNegativeOnly_edge_not_subset_positive
      U P.1 P.2 hBP heB
    apply hnot
    rw [heq, ← hXP]
    change NearPairing.nearOccurrenceEdge S X.1.2 ⊆
      NearPairing.nearOccurrenceBlock S X.1.1
    have hcompat := (Finset.mem_filter.mp X.2).2
    rw [← hcompat]
    exact NearPairing.nearOccurrenceEdge_subset_block S X.1.1
  obtain ⟨Q, hQ, _hQsameCopy, heQ⟩ :=
    NearPairing.exists_allPositiveSplittingBlock_through_negativeNearEdge
      S O hO heO hene
  exact ⟨Q, hQ, e, heB, heQ⟩

/-- The concrete splitting and first-elimination banks satisfy the partner
hypothesis required for the second elimination round. -/
theorem hasFurtherPartners_universalBadEliminationBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hbound : E.SpecialPositiveInterBounded e₀)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hnearForbidden :
      (NearPairing.allNegativeNearSplittingBlocks S).biUnion
          (fun N ↦ N.powersetCard r) ⊆ eliminationForbidden)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden) :
    HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S) := by
  intro B hB
  have hbad := mem_badEliminationBlocks.mp hB
  obtain ⟨e, heB, N, hN, heN⟩ := hbad.2
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hbad.1
  have hP : P.1 ∈ NearPairing.compatibleNearEliminationPairs S hr hrk
      hrootForbidden := P.2
  obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp hP
  let O : NearPairing.NearOccurrence roots (2 * m) k r := X.1.2
  have hO : O ∈ NearPairing.allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots := by
    exact (Finset.mem_product.mp (Finset.mem_filter.mp X.2).1).2
  have heNeg : e ∈ P.1.negative.powersetCard r :=
    badEdge_mem_firstNegativeRoot U hnearForbidden P.1 P.2 hBP heB hN heN
  have hPnegative : P.1.negative = NearPairing.nearOccurrenceBlock S O := by
    rw [← hXP]
    rfl
  have heO : e ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
    rw [← hPnegative]
    exact heNeg
  have hene : e ≠ NearPairing.nearOccurrenceEdge S O := by
    intro heq
    have hnot := eliminationNegativeOnly_edge_not_subset_positive
      U P.1 P.2 hBP heB
    apply hnot
    rw [heq, ← hXP]
    change NearPairing.nearOccurrenceEdge S X.1.2 ⊆
      NearPairing.nearOccurrenceBlock S X.1.1
    have hcompat := (Finset.mem_filter.mp X.2).2
    rw [← hcompat]
    exact NearPairing.nearOccurrenceEdge_subset_block S X.1.1
  obtain ⟨Q, hQ, _hQsameCopy, heQ⟩ :=
    NearPairing.exists_allPositiveSplittingBlock_through_negativeNearEdge
      S O hO heO hene
  refine ⟨Q, hQ, NearPairing.allPositiveSplittingBlocks_uniform S hQ,
    (eliminationNegativeOnly_decomp U P.1 P.2).1 B hBP, ?_⟩
  apply inter_card_eq_of_unique_common_edge hr heQ heB
  intro g hg
  have hgdata := Finset.mem_powersetCard.mp hg
  have hgQ : g ∈ Q.powersetCard r :=
    Finset.mem_powersetCard.mpr
      ⟨hgdata.1.trans Finset.inter_subset_left, hgdata.2⟩
  have hgB : g ∈ B.powersetCard r :=
    Finset.mem_powersetCard.mpr
      ⟨hgdata.1.trans Finset.inter_subset_right, hgdata.2⟩
  have hgForbidden : g ∈ eliminationForbidden := by
    apply hpositiveForbidden
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, hgQ⟩
  have hgNeg : g ∈ P.1.negative.powersetCard r :=
    eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
      U P.1 P.2 hBP hgB hgForbidden
  have heInter : e ⊆ B ∩ P.1.negative := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_powersetCard.mp heB).1 hx,
        (Finset.mem_powersetCard.mp heNeg).1 hx⟩
  have hInterEq : e = B ∩ P.1.negative := by
    apply Finset.eq_of_subset_of_card_le heInter
    simpa [(Finset.mem_powersetCard.mp heB).2] using
      (eliminationNegativeOnly_inter_negative_card_le hbound
        U P.1 P.2 hBP)
  have hgSub : g ⊆ e := by
    rw [hInterEq]
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_powersetCard.mp hgB).1 hx,
        (Finset.mem_powersetCard.mp hgNeg).1 hx⟩
  apply Finset.eq_of_subset_of_card_le hgSub
  rw [(Finset.mem_powersetCard.mp heB).2, hgdata.2]

/-- For a coefficient-dependent first-round matching, distinct selected bad
blocks use distinct positive splitting partners.  The proof is the exact
Step 5 argument: the partner intersection is a forbidden edge, hence lies
in the selected negative near root; global trace separation identifies that
near occurrence, and the selected first-round negative decomposition then
identifies the bad output block itself. -/
theorem furtherPositivePartner_injOn_selectedBadEliminationBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S)) :
    Set.InjOn
      (fun B : ↑(universalBadEliminationBlocks S hr hrk hrootForbidden U) ↦
        furtherPositivePartner hpartner B)
      {B | B.1 ∈ selectedBadEliminationBlocks S hr hrk hrootForbidden
        theta f hf U} := by
  classical
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  let T := U.restrict hsub
  let selectedBad := selectedBadEliminationBlocks S hr hrk hrootForbidden
    theta f hf U
  let bad := universalBadEliminationBlocks S hr hrk hrootForbidden U
  have sourceData (A : ↑bad) (hAsel : A.1 ∈ selectedBad) :
      ∃ O : NearPairing.NearOccurrence roots (2 * m) k r,
        O ∈ NearPairing.allNegativeNearOccurrences
          (k := k) (r := r) (m := m) roots ∧
        ∃ g : Finset (Fin n),
          g = furtherPositivePartner hpartner A ∩ A.1 ∧
          g ∈ A.1.powersetCard r ∧
          g ∈ (furtherPositivePartner hpartner A).powersetCard r ∧
          g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r ∧
          g ≠ NearPairing.nearOccurrenceEdge S O ∧
          A.1 ∈ allEliminationNegativeOnly T := by
    have hAsel' : A.1 ∈ badEliminationBlocks r
        (allEliminationNegativeOnly T)
        (NearPairing.allNegativeNearSplittingBlocks S) := by
      simpa [selectedBad, selectedBadEliminationBlocks, T, hsub] using hAsel
    have hAout := (mem_badEliminationBlocks.mp hAsel').1
    obtain ⟨P, _hPattach, hAP⟩ := Finset.mem_biUnion.mp hAout
    obtain ⟨Osub, _hOsub, hOP⟩ := Finset.mem_map.mp P.2
    let O : NearPairing.NearOccurrence roots (2 * m) k r := Osub.1
    have hOall : O ∈ NearPairing.allNegativeNearOccurrences
        (k := k) (r := r) (m := m) roots := by
      apply Finset.mem_product.mpr
      exact ⟨NearPairing.negativeBankSelection_subset_allNegativeBankIndices
        roots theta (Finset.mem_product.mp Osub.2).1,
        (Finset.mem_product.mp Osub.2).2⟩
    let Q := furtherPositivePartner hpartner A
    let g := Q ∩ A.1
    have hgcard : g.card = r := by
      exact furtherPartner_inter_card hpartner A
    have hgA : g ∈ A.1.powersetCard r :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hgcard⟩
    have hgQ : g ∈ Q.powersetCard r :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hgcard⟩
    have hQmem : Q ∈ NearPairing.allPositiveSplittingBlocks S :=
      furtherPositivePartner_mem hpartner A
    have hgForbidden : g ∈ eliminationForbidden := by
      apply hpositiveForbidden
      exact Finset.mem_biUnion.mpr ⟨Q, hQmem, hgQ⟩
    have hgNeg : g ∈ P.1.negative.powersetCard r :=
      eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
        T P.1 P.2 hAP hgA hgForbidden
    have hPnegative : P.1.negative =
        NearPairing.nearOccurrenceBlock S O := by
      rw [← hOP]
      rfl
    have hgO : g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
      rw [← hPnegative]
      exact hgNeg
    have hgne : g ≠ NearPairing.nearOccurrenceEdge S O := by
      intro heq
      have hnot := eliminationNegativeOnly_edge_not_subset_positive
        T P.1 P.2 hAP hgA
      apply hnot
      rw [heq, ← hOP]
      change NearPairing.nearOccurrenceEdge S Osub.1 ⊆
        NearPairing.nearOccurrenceBlock S (f Osub).1
      rw [← hf Osub]
      exact NearPairing.nearOccurrenceEdge_subset_block S (f Osub).1
    exact ⟨O, hOall, g, rfl, hgA, hgQ, hgO, hgne, hAout⟩
  intro A hAsel A' hA'sel hpartnerEq
  have hAsel' : A.1 ∈ selectedBad := by
    simpa [selectedBad] using hAsel
  have hA'sel' : A'.1 ∈ selectedBad := by
    simpa [selectedBad] using hA'sel
  obtain ⟨O, hO, g, hgdef, hgA, hgQ, hgO, hgne, hAout⟩ :=
    sourceData A hAsel'
  obtain ⟨O', hO', g', hg'def, hg'A', hg'Q', hg'O', hgne', hA'out⟩ :=
    sourceData A' hA'sel'
  have hQmem : furtherPositivePartner hpartner A ∈
      NearPairing.allPositiveSplittingBlocks S :=
    furtherPositivePartner_mem hpartner A
  have hg'Q : g' ∈ (furtherPositivePartner hpartner A).powersetCard r := by
    simpa only [hpartnerEq] using hg'Q'
  have hOO' : O = O' :=
    NearPairing.negativeNearOccurrences_eq_of_positiveSplittingBlock
      S hr hrk hrootForbidden hO hO' hgO hgne hg'O' hgne'
        hQmem hgQ hg'Q
  have hQcopy :=
    NearPairing.allPositiveSplittingBlock_through_negativeNearEdge_sameCopy
      S hr hrootForbidden O hO hgO hgne hQmem hgQ
  have hQpos : furtherPositivePartner hpartner A ∈
      ExchangeEmbedding.mappedPositive E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2) :=
    (Finset.mem_erase.mp hQcopy).2
  have hinterBound :
      (furtherPositivePartner hpartner A ∩
        NearPairing.nearOccurrenceBlock S O).card ≤ r := by
    simpa [NearPairing.nearOccurrenceBlock] using
      ExchangeEmbedding.mappedPositive_inter_mappedSpecial_card_le
        E (S.embedding O.1.1.1 O.1.1.2 O.1.2) hQpos O.2
  have hgInter : g ⊆ furtherPositivePartner hpartner A ∩
      NearPairing.nearOccurrenceBlock S O := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_powersetCard.mp hgQ).1 hx,
        (Finset.mem_powersetCard.mp hgO).1 hx⟩
  have hg'Inter : g' ⊆ furtherPositivePartner hpartner A ∩
      NearPairing.nearOccurrenceBlock S O := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_powersetCard.mp hg'Q).1 hx,
        (by simpa only [hOO'] using
          ((Finset.mem_powersetCard.mp hg'O').1 hx))⟩
  have hgEq : g = furtherPositivePartner hpartner A ∩
      NearPairing.nearOccurrenceBlock S O := by
    apply Finset.eq_of_subset_of_card_le hgInter
    simpa [(Finset.mem_powersetCard.mp hgQ).2] using hinterBound
  have hg'Eq : g' = furtherPositivePartner hpartner A ∩
      NearPairing.nearOccurrenceBlock S O := by
    apply Finset.eq_of_subset_of_card_le hg'Inter
    simpa [(Finset.mem_powersetCard.mp hg'Q).2] using hinterBound
  have hgg' : g = g' := hgEq.trans hg'Eq.symm
  have hfirstDecomp : IsUniformDecomposition
      (allEliminationNegativeOnlyHost T)
      (allEliminationNegativeOnly T) k r := by
    exact (NearPairing.matchedNearEliminationRound_of_compatibleBank
      S hr hrk hrootForbidden theta f hf U huniversalRootForbidden).2.1
  apply Subtype.ext
  exact hfirstDecomp.blocks_eq_of_common_edge hAout hA'out hgA
    (by simpa [hgg'] using hg'A')

/-- Common edges of distinct universal bad first-round outputs lie in both
chosen positive splitting partners.  This is the fixed-bank premise needed
to place every possible second-round elimination gadget before the
coefficient vector is known. -/
theorem universalBadEliminationBlocks_common_in_positivePartner
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hbound : E.SpecialPositiveInterBounded e₀)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S)) :
    ∀ B : ↑(universalBadEliminationBlocks S hr hrk hrootForbidden U),
      ∀ B' : ↑(universalBadEliminationBlocks S hr hrk hrootForbidden U),
        B ≠ B' → ∀ g ∈ B.1.powersetCard r, g ∈ B'.1.powersetCard r →
          g ⊆ furtherPositivePartner hpartner B ∧
            g ⊆ furtherPositivePartner hpartner B' := by
  classical
  intro B B' hBB' g hgB hgB'
  have hBbad := mem_badEliminationBlocks.mp B.2
  have hB'bad := mem_badEliminationBlocks.mp B'.2
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hBbad.1
  obtain ⟨P', _hP'attach, hB'P'⟩ := Finset.mem_biUnion.mp hB'bad.1
  have hPP' : P.1 ≠ P'.1 := by
    intro hEq
    have hB'P : B'.1 ∈ eliminationNegativeOnly U P.1 P.2 := by
      simpa [hEq] using hB'P'
    have hblocks := (eliminationNegativeOnly_decomp U P.1 P.2).blocks_eq_of_common_edge
      hBP hB'P hgB hgB'
    exact hBB' (Subtype.ext hblocks)
  have hgHostP : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (U.embedding P.1 P.2) :=
    (eliminationNegativeRemainder_decomp U P.1 P.2).2.1 B.1
      (Finset.mem_sdiff.mp hBP).1 hgB
  have hgHostP' : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (U.embedding P'.1 P'.2) :=
    (eliminationNegativeRemainder_decomp U P'.1 P'.2).2.1 B'.1
      (Finset.mem_sdiff.mp hB'P').1 hgB'
  have forbidden_of_negative (R : EliminationPair n k r)
      (hR : R ∈ NearPairing.compatibleNearEliminationPairs S hr hrk
        hrootForbidden) {a : Finset (Fin n)}
      (ha : a ∈ R.negative.powersetCard r) : a ∈ eliminationForbidden := by
    apply huniversalRootForbidden
    exact Finset.mem_biUnion.mpr ⟨R.negative, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨R, hR, rfl⟩), ha⟩
  have hgNegPair : g ∈ P.1.negative.powersetCard r ∧
      g ∈ P'.1.negative.powersetCard r := by
    rcases mem_negativeEdges_or_eliminationFreeEdges U
        (RelabeledFullExchange.isSpecialIsolated E e₀)
        P.1 P.2 hgHostP with hgNeg | hgFree <;>
      rcases mem_negativeEdges_or_eliminationFreeEdges U
        (RelabeledFullExchange.isSpecialIsolated E e₀)
        P'.1 P'.2 hgHostP' with hgNeg' | hgFree'
    · exact ⟨hgNeg, hgNeg'⟩
    · exact False.elim (Finset.disjoint_left.mp
        (U.free_disjoint_forbidden P'.1 P'.2) hgFree'
          (forbidden_of_negative P.1 P.2 hgNeg))
    · exact False.elim (Finset.disjoint_left.mp
        (U.free_disjoint_forbidden P.1 P.2) hgFree
          (forbidden_of_negative P'.1 P'.2 hgNeg'))
    · exact False.elim (Finset.disjoint_left.mp
        (U.free_pairwise P.1 P.2 P'.1 P'.2 hPP') hgFree hgFree')
  obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp P.2
  obtain ⟨X', _hX', hX'P'⟩ := Finset.mem_map.mp P'.2
  let O : NearPairing.NearOccurrence roots (2 * m) k r := X.1.2
  let O' : NearPairing.NearOccurrence roots (2 * m) k r := X'.1.2
  have hgO : g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
    have h := hgNegPair.1
    rw [← hXP] at h
    simpa [O] using h
  have hgO' : g ∈ (NearPairing.nearOccurrenceBlock S O').powersetCard r := by
    have h := hgNegPair.2
    rw [← hX'P'] at h
    simpa [O'] using h
  have hOO' : O = O' := by
    by_contra hne
    have hcommon := NearPairing.nearOccurrence_common_edge_eq
      S hr hrk hrootForbidden hne hgO hgO'
    have hnot := eliminationNegativeOnly_edge_not_subset_positive
      U P.1 P.2 hBP hgB
    apply hnot
    rw [← hXP]
    change g ⊆ NearPairing.nearOccurrenceBlock S X.1.1
    rw [hcommon.1, ← (Finset.mem_filter.mp X.2).2]
    exact NearPairing.nearOccurrenceEdge_subset_block S X.1.1
  have partner_covers
      (A : ↑(universalBadEliminationBlocks S hr hrk hrootForbidden U))
      (R : EliminationPair n k r)
      (hR : R ∈ NearPairing.compatibleNearEliminationPairs S hr hrk
        hrootForbidden)
      (hAR : A.1 ∈ eliminationNegativeOnly U R hR)
      (hgA : g ∈ A.1.powersetCard r)
      (hgNeg : g ∈ R.negative.powersetCard r) :
      g ⊆ furtherPositivePartner hpartner A := by
    let Q := furtherPositivePartner hpartner A
    let e := Q ∩ A.1
    have hecard : e.card = r := furtherPartner_inter_card hpartner A
    have heA : e ∈ A.1.powersetCard r :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hecard⟩
    have heQ : e ∈ Q.powersetCard r :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hecard⟩
    have hQmem : Q ∈ NearPairing.allPositiveSplittingBlocks S :=
      furtherPositivePartner_mem hpartner A
    have heForbidden : e ∈ eliminationForbidden := by
      apply hpositiveForbidden
      exact Finset.mem_biUnion.mpr ⟨Q, hQmem, heQ⟩
    have heNeg : e ∈ R.negative.powersetCard r :=
      eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
        U R hR hAR heA heForbidden
    have hinterBound : (A.1 ∩ R.negative).card ≤ r :=
      eliminationNegativeOnly_inter_negative_card_le hbound U R hR hAR
    have heInter : e ⊆ A.1 ∩ R.negative := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp heA).1 hx,
          (Finset.mem_powersetCard.mp heNeg).1 hx⟩
    have hgInter : g ⊆ A.1 ∩ R.negative := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp hgA).1 hx,
          (Finset.mem_powersetCard.mp hgNeg).1 hx⟩
    have heEq : e = A.1 ∩ R.negative := by
      apply Finset.eq_of_subset_of_card_le heInter
      simpa [hecard] using hinterBound
    have hgEq : g = A.1 ∩ R.negative := by
      apply Finset.eq_of_subset_of_card_le hgInter
      simpa [(Finset.mem_powersetCard.mp hgA).2] using hinterBound
    rw [hgEq, ← heEq]
    exact (Finset.mem_powersetCard.mp heQ).1
  constructor
  · exact partner_covers B P.1 P.2 hBP hgB hgNegPair.1
  · exact partner_covers B' P'.1 P'.2 hB'P' hgB' hgNegPair.2

/-- Distinct universal first-round negative outputs can share an edge only
when both collide with the same permanent negative near block. -/
theorem common_edge_universalFirstElimination_mem_bad
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    {B B' g : Finset (Fin n)}
    (hB : B ∈ allEliminationNegativeOnly U)
    (hB' : B' ∈ allEliminationNegativeOnly U)
    (hne : B ≠ B')
    (hgB : g ∈ B.powersetCard r) (hgB' : g ∈ B'.powersetCard r) :
    B ∈ universalBadEliminationBlocks S hr hrk hrootForbidden U ∧
      B' ∈ universalBadEliminationBlocks S hr hrk hrootForbidden U := by
  classical
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  obtain ⟨P', _hP'attach, hB'P'⟩ := Finset.mem_biUnion.mp hB'
  have hPP' : P.1 ≠ P'.1 := by
    intro hEq
    have hB'P : B' ∈ eliminationNegativeOnly U P.1 P.2 := by
      simpa [hEq] using hB'P'
    exact hne ((eliminationNegativeOnly_decomp U P.1 P.2).blocks_eq_of_common_edge
      hBP hB'P hgB hgB')
  have hgHostP : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (U.embedding P.1 P.2) :=
    (eliminationNegativeRemainder_decomp U P.1 P.2).2.1 B
      (Finset.mem_sdiff.mp hBP).1 hgB
  have hgHostP' : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (U.embedding P'.1 P'.2) :=
    (eliminationNegativeRemainder_decomp U P'.1 P'.2).2.1 B'
      (Finset.mem_sdiff.mp hB'P').1 hgB'
  have forbidden_of_negative (R : EliminationPair n k r)
      (hR : R ∈ NearPairing.compatibleNearEliminationPairs S hr hrk
        hrootForbidden) {a : Finset (Fin n)}
      (ha : a ∈ R.negative.powersetCard r) : a ∈ eliminationForbidden := by
    apply huniversalRootForbidden
    exact Finset.mem_biUnion.mpr ⟨R.negative, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨R, hR, rfl⟩), ha⟩
  have hgNegPair : g ∈ P.1.negative.powersetCard r ∧
      g ∈ P'.1.negative.powersetCard r := by
    rcases mem_negativeEdges_or_eliminationFreeEdges U
        (RelabeledFullExchange.isSpecialIsolated E e₀)
        P.1 P.2 hgHostP with hgNeg | hgFree <;>
      rcases mem_negativeEdges_or_eliminationFreeEdges U
        (RelabeledFullExchange.isSpecialIsolated E e₀)
        P'.1 P'.2 hgHostP' with hgNeg' | hgFree'
    · exact ⟨hgNeg, hgNeg'⟩
    · exact False.elim (Finset.disjoint_left.mp
        (U.free_disjoint_forbidden P'.1 P'.2) hgFree'
          (forbidden_of_negative P.1 P.2 hgNeg))
    · exact False.elim (Finset.disjoint_left.mp
        (U.free_disjoint_forbidden P.1 P.2) hgFree
          (forbidden_of_negative P'.1 P'.2 hgNeg'))
    · exact False.elim (Finset.disjoint_left.mp
        (U.free_pairwise P.1 P.2 P'.1 P'.2 hPP') hgFree hgFree')
  obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp P.2
  obtain ⟨X', _hX', hX'P'⟩ := Finset.mem_map.mp P'.2
  let O : NearPairing.NearOccurrence roots (2 * m) k r := X.1.2
  let O' : NearPairing.NearOccurrence roots (2 * m) k r := X'.1.2
  have hOall : O ∈ NearPairing.allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots :=
    (Finset.mem_product.mp (Finset.mem_filter.mp X.2).1).2
  have hgO : g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
    have h := hgNegPair.1
    rw [← hXP] at h
    simpa [O] using h
  have hgO' : g ∈ (NearPairing.nearOccurrenceBlock S O').powersetCard r := by
    have h := hgNegPair.2
    rw [← hX'P'] at h
    simpa [O'] using h
  have hOO' : O = O' := by
    by_contra hneO
    have hcommon := NearPairing.nearOccurrence_common_edge_eq
      S hr hrk hrootForbidden hneO hgO hgO'
    have hnot := eliminationNegativeOnly_edge_not_subset_positive
      U P.1 P.2 hBP hgB
    apply hnot
    rw [← hXP]
    change g ⊆ NearPairing.nearOccurrenceBlock S X.1.1
    rw [hcommon.1, ← (Finset.mem_filter.mp X.2).2]
    exact NearPairing.nearOccurrenceEdge_subset_block S X.1.1
  have hNear : NearPairing.nearOccurrenceBlock S O ∈
      NearPairing.allNegativeNearSplittingBlocks S :=
    (NearPairing.mem_allNegativeNearSplittingBlocks_iff S).mpr
      ⟨O, hOall, rfl⟩
  constructor
  · apply mem_badEliminationBlocks.mpr
    exact ⟨hB, g, hgB, NearPairing.nearOccurrenceBlock S O,
      hNear, (Finset.mem_powersetCard.mp hgO).1⟩
  · apply mem_badEliminationBlocks.mpr
    exact ⟨hB', g, hgB', NearPairing.nearOccurrenceBlock S O,
      hNear, (Finset.mem_powersetCard.mp hgO').1.trans_eq
        (congrArg (NearPairing.nearOccurrenceBlock S) hOO'.symm)⟩

theorem universalGoodEliminationBlocks_uniform
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    {B : Finset (Fin n)}
    (hB : B ∈ universalGoodEliminationBlocks S hr hrk hrootForbidden U) :
    B.card = k := by
  have hBall : B ∈ allEliminationNegativeOnly U :=
    (Finset.mem_sdiff.mp hB).1
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hBall
  exact (eliminationNegativeOnly_decomp U P.1 P.2).1 B hBP

theorem universalGoodEliminationBlocks_pairwise_edgeDisjoint
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    {B B' : Finset (Fin n)}
    (hB : B ∈ universalGoodEliminationBlocks S hr hrk hrootForbidden U)
    (hB' : B' ∈ universalGoodEliminationBlocks S hr hrk hrootForbidden U)
    (hne : B ≠ B') :
    Disjoint (B.powersetCard r) (B'.powersetCard r) := by
  apply Finset.disjoint_left.mpr
  intro g hgB hgB'
  have hbad := common_edge_universalFirstElimination_mem_bad
    S hr hrk hrootForbidden U huniversalRootForbidden
      (Finset.mem_sdiff.mp hB).1 (Finset.mem_sdiff.mp hB').1 hne hgB hgB'
  exact (Finset.mem_sdiff.mp hB).2 hbad.1

theorem universalGoodEliminationBlocks_decomp
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden) :
    IsUniformDecomposition
      ((universalGoodEliminationBlocks S hr hrk hrootForbidden U).biUnion
        (fun B ↦ B.powersetCard r))
      (universalGoodEliminationBlocks S hr hrk hrootForbidden U) k r := by
  apply IsUniformDecomposition.of_pairwise_powersetCard
  · exact fun B hB ↦ universalGoodEliminationBlocks_uniform
      S hr hrk hrootForbidden U hB
  · exact fun B hB B' hB' hne ↦
      universalGoodEliminationBlocks_pairwise_edgeDisjoint
        S hr hrk hrootForbidden U huniversalRootForbidden hB hB' hne

/-- The permanent far splitting bank and the good universal first-round
outputs have disjoint edge boundaries. -/
theorem negativeFarSplitting_edgeDisjoint_universalGood
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    {F B : Finset (Fin n)}
    (hF : F ∈ NearPairing.allNegativeFarSplittingBlocks S)
    (hB : B ∈ universalGoodEliminationBlocks S hr hrk hrootForbidden U) :
    Disjoint (F.powersetCard r) (B.powersetCard r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro g hgF hgB
  have hBall : B ∈ allEliminationNegativeOnly U :=
    (Finset.mem_sdiff.mp hB).1
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hBall
  have hgHost : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (U.embedding P.1 P.2) :=
    (eliminationNegativeRemainder_decomp U P.1 P.2).2.1 B
      (Finset.mem_sdiff.mp hBP).1 hgB
  rcases mem_negativeEdges_or_eliminationFreeEdges U
      (RelabeledFullExchange.isSpecialIsolated E e₀)
      P.1 P.2 hgHost with hgNeg | hgFree
  · obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp P.2
    let O : NearPairing.NearOccurrence roots (2 * m) k r := X.1.2
    have hOall : O ∈ NearPairing.allNegativeNearOccurrences
        (k := k) (r := r) (m := m) roots :=
      (Finset.mem_product.mp (Finset.mem_filter.mp X.2).1).2
    have hN : NearPairing.nearOccurrenceBlock S O ∈
        NearPairing.allNegativeNearSplittingBlocks S :=
      (NearPairing.mem_allNegativeNearSplittingBlocks_iff S).mpr
        ⟨O, hOall, rfl⟩
    have hgN : g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
      have h := hgNeg
      rw [← hXP] at h
      simpa [O] using h
    exact Finset.disjoint_left.mp
      (NearPairing.allNegativeFarSplittingBlocks_edgeDisjoint_negativeNear
        S hrootForbidden hF hN) hgF hgN
  · have hgForbidden : g ∈ eliminationForbidden := by
      apply hfarForbidden
      exact Finset.mem_biUnion.mpr ⟨F, hF, hgF⟩
    exact Finset.disjoint_left.mp (U.free_disjoint_forbidden P.1 P.2)
      hgFree hgForbidden

/-- The fixed negative bank before the second elimination round. -/
def preFurtherNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  NearPairing.allNegativeFarSplittingBlocks S ∪
    universalGoodEliminationBlocks S hr hrk hrootForbidden U

theorem preFurtherNegativeBlocks_decomp
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden) :
    IsUniformDecomposition
      ((preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
        (fun B ↦ B.powersetCard r))
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U) k r := by
  apply IsUniformDecomposition.of_pairwise_powersetCard
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · exact NearPairing.allNegativeFarSplittingBlocks_uniform S hB
    · exact universalGoodEliminationBlocks_uniform
        S hr hrk hrootForbidden U hB
  · intro B hB B' hB' hne
    rcases Finset.mem_union.mp hB with hB | hB <;>
      rcases Finset.mem_union.mp hB' with hB' | hB'
    · exact NearPairing.allNegativeFarSplittingBlocks_pairwise_edgeDisjoint
        S hr hrk hB hB' hne
    · exact negativeFarSplitting_edgeDisjoint_universalGood
        S hr hrk hrootForbidden U hfarForbidden hB hB'
    · exact (negativeFarSplitting_edgeDisjoint_universalGood
        S hr hrk hrootForbidden U hfarForbidden hB' hB).symm
    · exact universalGoodEliminationBlocks_pairwise_edgeDisjoint
        S hr hrk hrootForbidden U huniversalRootForbidden hB hB' hne

/-- Every universal bad first-round root is edge-disjoint from the fixed
far-plus-good negative prefix. -/
theorem universalBad_edgeDisjoint_preFurtherNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    {A F : Finset (Fin n)}
    (hA : A ∈ universalBadEliminationBlocks S hr hrk hrootForbidden U)
    (hF : F ∈ preFurtherNegativeBlocks S hr hrk hrootForbidden U) :
    Disjoint (A.powersetCard r) (F.powersetCard r) := by
  classical
  rcases Finset.mem_union.mp hF with hF | hF
  · apply Finset.disjoint_left.mpr
    intro g hgA hgF
    have hAall := (mem_badEliminationBlocks.mp hA).1
    obtain ⟨P, _hPattach, hAP⟩ := Finset.mem_biUnion.mp hAall
    have hgHost : g ∈ RootedEmbedding.imageFreeEdges E.pattern
        (U.embedding P.1 P.2) :=
      (eliminationNegativeRemainder_decomp U P.1 P.2).2.1 A
        (Finset.mem_sdiff.mp hAP).1 hgA
    rcases mem_negativeEdges_or_eliminationFreeEdges U
        (RelabeledFullExchange.isSpecialIsolated E e₀)
        P.1 P.2 hgHost with hgNeg | hgFree
    · obtain ⟨X, _hX, hXP⟩ := Finset.mem_map.mp P.2
      let O : NearPairing.NearOccurrence roots (2 * m) k r := X.1.2
      have hOall : O ∈ NearPairing.allNegativeNearOccurrences
          (k := k) (r := r) (m := m) roots :=
        (Finset.mem_product.mp (Finset.mem_filter.mp X.2).1).2
      have hN : NearPairing.nearOccurrenceBlock S O ∈
          NearPairing.allNegativeNearSplittingBlocks S :=
        (NearPairing.mem_allNegativeNearSplittingBlocks_iff S).mpr
          ⟨O, hOall, rfl⟩
      have hgN : g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
        have h := hgNeg
        rw [← hXP] at h
        simpa [O] using h
      exact Finset.disjoint_left.mp
        (NearPairing.allNegativeFarSplittingBlocks_edgeDisjoint_negativeNear
          S hrootForbidden hF hN) hgF hgN
    · have hgForbidden : g ∈ eliminationForbidden := by
        apply hfarForbidden
        exact Finset.mem_biUnion.mpr ⟨F, hF, hgF⟩
      exact Finset.disjoint_left.mp (U.free_disjoint_forbidden P.1 P.2)
        hgFree hgForbidden
  · apply Finset.disjoint_left.mpr
    intro g hgA hgF
    have hFall := (Finset.mem_sdiff.mp hF).1
    by_cases hEq : A = F
    · subst F
      exact (Finset.mem_sdiff.mp hF).2 hA
    · have hboth := common_edge_universalFirstElimination_mem_bad
        S hr hrk hrootForbidden U huniversalRootForbidden
          (mem_badEliminationBlocks.mp hA).1 hFall hEq hgA hgF
      exact (Finset.mem_sdiff.mp hF).2 hboth.2

/-- The fixed final negative bank, including every universally preallocated
second-round output. -/
def finalNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    Finset (Finset (Fin n)) :=
  preFurtherNegativeBlocks S hr hrk hrootForbidden U ∪
    allEliminationNegativeOnly V

/-- Support audit for the fixed prefix after the first elimination round. -/
theorem preFurtherNegativeBlocks_boundary_subset_allocatorHosts
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      S.freeUnion ∪
        (eliminationPairSideBoundary
          (NearPairing.compatibleNearEliminationPairs S hr hrk
            hrootForbidden) ∪ U.freeUnion) := by
  let firstHost := eliminationPairSideBoundary
      (NearPairing.compatibleNearEliminationPairs S hr hrk
        hrootForbidden) ∪ U.freeUnion
  change (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
      (fun B ↦ B.powersetCard r) ⊆
    S.freeUnion ∪ firstHost
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_union.mp hB with hBfar | hBgood
  · exact Finset.mem_union_left _
      (NearPairing.cliqueBoundarySupport_allNegativeFarSplittingBlocks_subset_freeUnion
        S (Finset.mem_biUnion.mpr ⟨B, hBfar, hgB⟩))
  · exact Finset.mem_union_right _
      (ExchangeEliminationEmbedding.allEliminationNegativeOnly_edge_mem_sideBoundary_union_freeUnion
        (E := E) (e₀ := e₀)
        (pairs := NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden)
        (forbidden := eliminationForbidden) (C := eliminationCap)
        U (Finset.mem_sdiff.mp hBgood).1 hgB)

/-- The first elimination round creates no negative boundary edge in a
prescribed source family already forbidden to both the splitting and
elimination allocators.  If such an edge existed, the elimination geometry
would put it in the negative near root; splitting trace isolation would
then identify it with the common distinguished edge, which is contained in
the positive root, contradicting the negative-only property. -/
theorem allFirstEliminationNegativeOnly_boundary_disjoint_source
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (source : Finset (Finset (Fin n)))
    (hsourceSplit : source ⊆ splitForbidden)
    (hsourceElimination : source ⊆ eliminationForbidden) :
    Disjoint
      ((allEliminationNegativeOnly U).biUnion
        (fun B ↦ B.powersetCard r)) source := by
  rw [Finset.disjoint_left]
  intro g hg hgSource
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  have hgNegative : g ∈ P.1.negative.powersetCard r :=
    eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
      U P.1 P.2 hBP hgB (hsourceElimination hgSource)
  have hgPositive : g ⊆ P.1.positive :=
    NearPairing.compatibleNearEliminationPair_negative_edge_subset_positive_of_mem_forbidden
      S hr hrk hrootForbidden P.1 P.2 hgNegative
        (hsourceSplit hgSource)
  exact (eliminationNegativeOnly_edge_not_subset_positive
    U P.1 P.2 hBP hgB) hgPositive

/-- The far-plus-good prefix of the final negative bank avoids the same
source family.  Far blocks use only splitting free edges, while every good
block is a first-round negative-only output. -/
theorem preFurtherNegativeBlocks_boundary_disjoint_source
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (source : Finset (Finset (Fin n)))
    (hsourceSplit : source ⊆ splitForbidden)
    (hsourceElimination : source ⊆ eliminationForbidden) :
    Disjoint
      ((preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
        (fun B ↦ B.powersetCard r)) source := by
  rw [Finset.disjoint_left]
  intro g hg hgSource
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_union.mp hB with hBfar | hBgood
  · have hgFree :=
      NearPairing.cliqueBoundarySupport_allNegativeFarSplittingBlocks_subset_freeUnion
        S (Finset.mem_biUnion.mpr ⟨B, hBfar, hgB⟩)
    exact Finset.disjoint_left.mp S.freeUnion_disjoint_forbidden
      hgFree (hsourceSplit hgSource)
  · have hfirst := allFirstEliminationNegativeOnly_boundary_disjoint_source
      S hr hrk hrootForbidden U source hsourceSplit hsourceElimination
    apply Finset.disjoint_left.mp hfirst
    · exact Finset.mem_biUnion.mpr
        ⟨B, (Finset.mem_sdiff.mp hBgood).1, hgB⟩
    · exact hgSource

/-- The complete two-round negative bank avoids every source family put in
all three allocator forbidden sets.  In the second round a forbidden output
edge is forced into a bad negative root; those bad roots are first-round
negative outputs and have already been shown to avoid the source. -/
theorem finalNegativeBlocks_boundary_disjoint_source
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (source : Finset (Finset (Fin n)))
    (hsourceSplit : source ⊆ splitForbidden)
    (hsourceElimination : source ⊆ eliminationForbidden)
    (hsourceFurther : source ⊆ furtherForbidden) :
    Disjoint
      ((finalNegativeBlocks S hr hrk hrootForbidden U hpartner V).biUnion
        (fun B ↦ B.powersetCard r)) source := by
  rw [Finset.disjoint_left]
  intro g hg hgSource
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_union.mp hB with hBprefix | hBsecond
  · have hprefix := preFurtherNegativeBlocks_boundary_disjoint_source
      S hr hrk hrootForbidden U source hsourceSplit hsourceElimination
    exact Finset.disjoint_left.mp hprefix
      (Finset.mem_biUnion.mpr ⟨B, hBprefix, hgB⟩) hgSource
  · obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hBsecond
    have hgNegative : g ∈ P.1.negative.powersetCard r :=
      eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
        V P.1 P.2 hBP hgB (hsourceFurther hgSource)
    have hPbad : P.1.negative ∈
        universalBadEliminationBlocks S hr hrk hrootForbidden U :=
      furtherEliminationPairs_negative_mem hpartner P.2
    have hPfirst : P.1.negative ∈ allEliminationNegativeOnly U :=
      badEliminationBlocks_subset_firstNegative hPbad
    have hfirst := allFirstEliminationNegativeOnly_boundary_disjoint_source
      S hr hrk hrootForbidden U source hsourceSplit hsourceElimination
    exact Finset.disjoint_left.mp hfirst
      (Finset.mem_biUnion.mpr ⟨P.1.negative, hPfirst, hgNegative⟩)
      hgSource

/-- Quantitative support audit for the fixed final negative bank.  Every
edge is charged either to the splitting allocator, to a prescribed pair
root from one of the two rounds, or to the corresponding elimination
allocator's free-edge union. -/
theorem finalNegativeBlocks_boundary_subset_allocatorHosts
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    (finalNegativeBlocks S hr hrk hrootForbidden U hpartner V).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      S.freeUnion ∪
        (eliminationPairSideBoundary
            (NearPairing.compatibleNearEliminationPairs S hr hrk
              hrootForbidden) ∪ U.freeUnion) ∪
        (eliminationPairSideBoundary (furtherEliminationPairs hpartner) ∪
          V.freeUnion) := by
  let firstHost := S.freeUnion ∪
    (eliminationPairSideBoundary
      (NearPairing.compatibleNearEliminationPairs S hr hrk
        hrootForbidden) ∪ U.freeUnion)
  let secondHost := eliminationPairSideBoundary
      (furtherEliminationPairs hpartner) ∪
        V.freeUnion
  have hprefix := preFurtherNegativeBlocks_boundary_subset_allocatorHosts
    S hr hrk hrootForbidden U
  change (finalNegativeBlocks S hr hrk hrootForbidden U hpartner V).biUnion
      (fun B ↦ B.powersetCard r) ⊆ firstHost ∪ secondHost
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  change B ∈ preFurtherNegativeBlocks S hr hrk hrootForbidden U ∪
      allEliminationNegativeOnly V at hB
  rcases Finset.mem_union.mp hB with hBprefix | hBV
  · apply Finset.mem_union_left
    exact hprefix (Finset.mem_biUnion.mpr ⟨B, hBprefix, hgB⟩)
  · apply Finset.mem_union_right
    exact ExchangeEliminationEmbedding.allEliminationNegativeOnly_edge_mem_sideBoundary_union_freeUnion
      (E := E) (e₀ := e₀) (pairs := furtherEliminationPairs hpartner)
      (forbidden := furtherForbidden) (C := furtherCap) V hBV hgB

/-- The final negative boundary is disjoint from any family avoided by all
five components in its allocator-host support audit. -/
theorem finalNegativeBlocks_boundary_disjoint_of_allocatorHosts
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (reserve : Finset (Finset (Fin n)))
    (hS : Disjoint S.freeUnion reserve)
    (hfirstSide : Disjoint
      (eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden)) reserve)
    (hU : Disjoint U.freeUnion reserve)
    (hsecondSide : Disjoint
      (eliminationPairSideBoundary (furtherEliminationPairs hpartner))
        reserve)
    (hV : Disjoint V.freeUnion reserve) :
    Disjoint
      ((finalNegativeBlocks S hr hrk hrootForbidden U hpartner V).biUnion
        (fun B ↦ B.powersetCard r)) reserve := by
  rw [Finset.disjoint_left]
  intro g hg hgR
  have hsupport := finalNegativeBlocks_boundary_subset_allocatorHosts
    S hr hrk hrootForbidden U hpartner V hg
  rcases Finset.mem_union.mp hsupport with hfirst | hsecond
  · rcases Finset.mem_union.mp hfirst with hgS | hrest
    · exact Finset.disjoint_left.mp hS hgS hgR
    · rcases Finset.mem_union.mp hrest with hgSide | hgU
      · exact Finset.disjoint_left.mp hfirstSide hgSide hgR
      · exact Finset.disjoint_left.mp hU hgU hgR
  · rcases Finset.mem_union.mp hsecond with hgSide | hgV
    · exact Finset.disjoint_left.mp hsecondSide hgSide hgR
    · exact Finset.disjoint_left.mp hV hgV hgR

/-- Collapse the five-part allocator-host audit when the four earlier
components have all been included in one later forbidden host. -/
theorem finalNegativeBlocks_boundary_subset_forbidden_union_free
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (hS : S.freeUnion ⊆ furtherForbidden)
    (hfirstSide : eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆ furtherForbidden)
    (hU : U.freeUnion ⊆ furtherForbidden)
    (hsecondSide : eliminationPairSideBoundary
        (furtherEliminationPairs hpartner) ⊆ furtherForbidden) :
    (finalNegativeBlocks S hr hrk hrootForbidden U hpartner V).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      furtherForbidden ∪ V.freeUnion := by
  intro g hg
  have hsupport := finalNegativeBlocks_boundary_subset_allocatorHosts
    S hr hrk hrootForbidden U hpartner V hg
  rcases Finset.mem_union.mp hsupport with hfirst | hsecond
  · apply Finset.mem_union_left
    rcases Finset.mem_union.mp hfirst with hgS | hrest
    · exact hS hgS
    · rcases Finset.mem_union.mp hrest with hgSide | hgU
      · exact hfirstSide hgSide
      · exact hU hgU
  · rcases Finset.mem_union.mp hsecond with hgSide | hgV
    · exact Finset.mem_union_left _ (hsecondSide hgSide)
    · exact Finset.mem_union_right _ hgV

theorem preFurtherNegativeBlocks_edgeDisjoint_furtherOutputs
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (hprefixForbidden :
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden)
    {F B : Finset (Fin n)}
    (hF : F ∈ preFurtherNegativeBlocks S hr hrk hrootForbidden U)
    (hB : B ∈ allEliminationNegativeOnly V) :
    Disjoint (F.powersetCard r) (B.powersetCard r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro g hgF hgB
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  have hgHost : g ∈ RootedEmbedding.imageFreeEdges E.pattern
      (V.embedding P.1 P.2) :=
    (eliminationNegativeRemainder_decomp V P.1 P.2).2.1 B
      (Finset.mem_sdiff.mp hBP).1 hgB
  rcases mem_negativeEdges_or_eliminationFreeEdges V
      (RelabeledFullExchange.isSpecialIsolated E e₀)
      P.1 P.2 hgHost with hgNeg | hgFree
  · obtain ⟨A, hAP⟩ :=
      (mem_furtherEliminationPairs_iff hpartner).mp P.2
    have hPnegative : P.1.negative = A.1 := by
      rw [← hAP]
      rfl
    have hgA : g ∈ A.1.powersetCard r := by
      rw [← hPnegative]
      exact hgNeg
    exact Finset.disjoint_left.mp
      (universalBad_edgeDisjoint_preFurtherNegativeBlocks
        S hr hrk hrootForbidden U huniversalRootForbidden hfarForbidden
          A.2 hF).symm hgF hgA
  · have hgForbidden : g ∈ furtherForbidden := by
      apply hprefixForbidden
      exact Finset.mem_biUnion.mpr ⟨F, hF, hgF⟩
    exact Finset.disjoint_left.mp (V.free_disjoint_forbidden P.1 P.2)
      hgFree hgForbidden

/-- Pointwise form of the prefix/second-round separation, packaged once so
later aggregate decomposition proofs do not repeatedly elaborate the full
dependent allocator signature. -/
theorem preFurtherNegativeBlocks_cross_furtherOutputs
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆ eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (hprefixForbidden :
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden) :
    ∀ F ∈ preFurtherNegativeBlocks S hr hrk hrootForbidden U,
      ∀ B ∈ allEliminationNegativeOnly V,
        ∀ g, g ∈ F.powersetCard r → g ∈ B.powersetCard r → False := by
  intro F hF B hB g hgF hgB
  exact Finset.disjoint_left.mp
    (preFurtherNegativeBlocks_edgeDisjoint_furtherOutputs
      S hr hrk hrootForbidden U huniversalRootForbidden hfarForbidden
        hpartner V hprefixForbidden hF hB) hgF hgB

/-- The complete coefficient-independent negative bank is an edge-disjoint
`k`-clique decomposition. -/
theorem finalNegativeBlocks_decomp
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hbound : E.SpecialPositiveInterBounded e₀)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (hfurtherRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (furtherEliminationPairs hpartner) ⊆
          furtherForbidden)
    (hprefixForbidden :
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden) :
    IsUniformDecomposition
      ((finalNegativeBlocks S hr hrk hrootForbidden U hpartner V).biUnion
        (fun B ↦ B.powersetCard r))
      (finalNegativeBlocks S hr hrk hrootForbidden U hpartner V) k r := by
  have hprefix := preFurtherNegativeBlocks_decomp
    S hr hrk hrootForbidden U huniversalRootForbidden hfarForbidden
  have hcommon := universalBadEliminationBlocks_common_in_positivePartner
    S hr hrk hbound hrootForbidden U hpositiveForbidden
      huniversalRootForbidden hpartner
  have hV : IsUniformDecomposition
      (allEliminationNegativeOnlyHost V)
      (allEliminationNegativeOnly V) k r :=
    allEliminationNegativeOnly_decomp_of_common_in_positive V hrk.le
      hfurtherRootForbidden
        (furtherEliminationPairs_common_in_positive hpartner hcommon)
  have hVhostUniform : ∀ g ∈ allEliminationNegativeOnlyHost V,
      g.card = r := by
    intro g hg
    obtain ⟨P, _hPattach, hgP⟩ := Finset.mem_biUnion.mp hg
    exact RootedEmbedding.imageFreeEdges_uniform E.pattern (V.embedding P.1 P.2)
      (Finset.mem_sdiff.mp hgP).1
  have hVcanonical : IsUniformDecomposition
      ((allEliminationNegativeOnly V).biUnion
        (fun B ↦ B.powersetCard r))
      (allEliminationNegativeOnly V) k r := by
    rw [← hV.host_eq_biUnion hVhostUniform]
    exact hV
  have hcross := preFurtherNegativeBlocks_cross_furtherOutputs
    S hr hrk hrootForbidden U huniversalRootForbidden hfarForbidden
      hpartner V hprefixForbidden
  simpa [finalNegativeBlocks] using
    hprefix.union_canonical hVcanonical hcross hrk.le

/-! ## Coefficient-dependent restriction of the fixed bank -/

/-- Generic signed replacement algebra used by both elimination rounds. -/
theorem signedIncidence_replace
    (positive negative positiveRoots negativeRoots
      outputPositive outputNegative : Finset (Finset (Fin n)))
    (hpositiveRoots : positiveRoots ⊆ positive)
    (hnegativeRoots : negativeRoots ⊆ negative)
    (hpositiveDisjoint : Disjoint (positive \ positiveRoots) outputPositive)
    (hnegativeDisjoint : Disjoint (negative \ negativeRoots) outputNegative)
    (hround : ∀ g : Finset (Fin n), g.card = r →
      (incidenceCount outputPositive g : ℤ) -
          (incidenceCount outputNegative g : ℤ) =
        (incidenceCount positiveRoots g : ℤ) -
          (incidenceCount negativeRoots g : ℤ))
    (g : Finset (Fin n)) (hg : g.card = r) :
    (incidenceCount
        ((positive \ positiveRoots) ∪ outputPositive) g : ℤ) -
        (incidenceCount
          ((negative \ negativeRoots) ∪ outputNegative) g : ℤ) =
      (incidenceCount positive g : ℤ) -
        (incidenceCount negative g : ℤ) := by
  have hposLe : incidenceCount positiveRoots g ≤
      incidenceCount positive g :=
    Finset.card_le_card (Finset.filter_subset_filter _ hpositiveRoots)
  have hnegLe : incidenceCount negativeRoots g ≤
      incidenceCount negative g :=
    Finset.card_le_card (Finset.filter_subset_filter _ hnegativeRoots)
  rw [ExchangeEmbedding.incidenceCount_union_of_disjoint
      hpositiveDisjoint,
    ExchangeEmbedding.incidenceCount_union_of_disjoint hnegativeDisjoint,
    incidenceCount_sdiff hpositiveRoots g,
    incidenceCount_sdiff hnegativeRoots g]
  push_cast [Nat.cast_sub hposLe, Nat.cast_sub hnegLe]
  have hr := hround g hg
  omega

/-- Positive family after the matched near cliques have been removed from
the selected splitting trade and the first elimination remainders inserted. -/
def firstRoundPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  (ExchangeEmbedding.selectedBankPositiveBlocks S theta \
      NearPairing.matchedNearPositiveBlocks S hr hrk hrootForbidden
        theta f hf) ∪
    allEliminationPositiveOnly (U.restrict hsub)

/-- Negative family after the first elimination round.  The near splitting
cliques have disappeared, so only the selected far splitting cliques and
the first-round negative remainders remain. -/
def firstRoundNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  ExchangeEmbedding.selectedBankFarNegativeBlocks S theta ∪
    allEliminationNegativeOnly (U.restrict hsub)

/-- The first replacement round preserves the signed splitting boundary.
This is the complete finite algebra behind Step 4: the two disjointness
hypotheses are discharged from the fixed forbidden-edge bank, not assumed
for a coefficient-dependent placement. -/
theorem firstRoundBlocks_signedIncidence
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (g : Finset (Fin n)) (hg : g.card = r) :
    (incidenceCount
        (firstRoundPositiveBlocks S hr hrk hrootForbidden theta f hf U) g : ℤ) -
      (incidenceCount
        (firstRoundNegativeBlocks S hr hrk hrootForbidden theta f hf U) g : ℤ) =
      (incidenceCount
        (ExchangeEmbedding.selectedBankPositiveBlocks S theta) g : ℤ) -
      (incidenceCount
        (ExchangeEmbedding.selectedBankNegativeBlocks S theta) g : ℤ) := by
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  let T := U.restrict hsub
  let positiveRoots := NearPairing.matchedNearPositiveBlocks S hr hrk
    hrootForbidden theta f hf
  let negativeRoots := ExchangeEmbedding.selectedBankNegativeNearBlocks S theta
  have hpositiveRoots : positiveRoots ⊆
      ExchangeEmbedding.selectedBankPositiveBlocks S theta := by
    exact (NearPairing.matchedNearPositiveBlocks_subset_selected
      S hr hrk hrootForbidden theta f hf).trans
        (ExchangeEmbedding.selectedBankPositiveNearBlocks_subset S theta)
  have hnegativeRoots : negativeRoots ⊆
      ExchangeEmbedding.selectedBankNegativeBlocks S theta := by
    exact ExchangeEmbedding.selectedBankNegativeNearBlocks_subset S theta
  have hselectedPositiveForbidden :
      (ExchangeEmbedding.selectedBankPositiveBlocks S theta).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden := by
    intro e he
    apply hpositiveForbidden
    obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr
      ⟨B, NearPairing.selectedBankPositiveBlocks_subset_allPositiveSplittingBlocks
        S theta hB, heB⟩
  have hselectedFarForbidden :
      (ExchangeEmbedding.selectedBankFarNegativeBlocks S theta).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden := by
    intro e he
    apply hfarForbidden
    obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr
      ⟨B,
        NearPairing.selectedBankFarNegativeBlocks_subset_allNegativeFarSplittingBlocks
          S theta hB,
        heB⟩
  have hpositiveDisjoint : Disjoint
      (ExchangeEmbedding.selectedBankPositiveBlocks S theta \ positiveRoots)
      (allEliminationPositiveOnly T) := by
    exact (allEliminationPositiveOnly_disjoint_forbiddenFamily T hr hrk
      (ExchangeEmbedding.selectedBankPositiveBlocks S theta)
      hselectedPositiveForbidden).symm.mono Finset.sdiff_subset (fun _ h ↦ h)
  have hnegativeDisjoint : Disjoint
      (ExchangeEmbedding.selectedBankNegativeBlocks S theta \ negativeRoots)
      (allEliminationNegativeOnly T) := by
    have heq : ExchangeEmbedding.selectedBankNegativeBlocks S theta \
        negativeRoots =
        ExchangeEmbedding.selectedBankFarNegativeBlocks S theta := by
      simpa [negativeRoots] using
        NearPairing.selectedBankNegativeBlocks_sdiff_near_eq_far
          S hr hrk hrootForbidden theta
    rw [heq]
    exact (allEliminationNegativeOnly_disjoint_forbiddenFamily T hr hrk
      (ExchangeEmbedding.selectedBankFarNegativeBlocks S theta)
      hselectedFarForbidden).symm
  have hround :=
    (NearPairing.matchedNearEliminationRound_of_compatibleBank
      S hr hrk hrootForbidden theta f hf U huniversalRootForbidden).2.2
  have h := signedIncidence_replace
    (ExchangeEmbedding.selectedBankPositiveBlocks S theta)
    (ExchangeEmbedding.selectedBankNegativeBlocks S theta)
    positiveRoots negativeRoots
    (allEliminationPositiveOnly T) (allEliminationNegativeOnly T)
    hpositiveRoots hnegativeRoots hpositiveDisjoint hnegativeDisjoint
    hround g hg
  simpa [firstRoundPositiveBlocks, firstRoundNegativeBlocks, hsub, T,
    positiveRoots, negativeRoots,
    NearPairing.selectedBankNegativeBlocks_sdiff_near_eq_far
      S hr hrk hrootForbidden theta] using h

/-- Every selected bad output really is present on the negative side after
the first replacement round. -/
theorem selectedBadEliminationBlocks_subset_firstRoundNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    selectedBadEliminationBlocks S hr hrk hrootForbidden theta f hf U ⊆
      firstRoundNegativeBlocks S hr hrk hrootForbidden theta f hf U := by
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  intro B hB
  apply Finset.mem_union_right
  have hB' : B ∈ badEliminationBlocks r
      (allEliminationNegativeOnly (U.restrict hsub))
      (NearPairing.allNegativeNearSplittingBlocks S) := by
    simpa [selectedBadEliminationBlocks, hsub] using hB
  simpa [firstRoundNegativeBlocks, hsub] using
    (mem_badEliminationBlocks.mp hB').1

/-- The positive splitting partner of a selected bad first-round block was
forced into the selected negative-labelled half of the splitting bank and
was not one of the matched positive near roots.  Consequently it is still
present on the positive side after the first round. -/
theorem furtherPositivePartner_mem_firstRoundPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    (A : ↑(universalBadEliminationBlocks S hr hrk hrootForbidden U))
    (hAsel : A.1 ∈ selectedBadEliminationBlocks S hr hrk
      hrootForbidden theta f hf U) :
    furtherPositivePartner hpartner A ∈
      firstRoundPositiveBlocks S hr hrk hrootForbidden theta f hf U := by
  classical
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  let T := U.restrict hsub
  have hAsel' : A.1 ∈ badEliminationBlocks r
      (allEliminationNegativeOnly T)
      (NearPairing.allNegativeNearSplittingBlocks S) := by
    simpa [selectedBadEliminationBlocks, T, hsub] using hAsel
  have hAout := (mem_badEliminationBlocks.mp hAsel').1
  obtain ⟨P, _hPattach, hAP⟩ := Finset.mem_biUnion.mp hAout
  obtain ⟨Osub, _hOsub, hOP⟩ := Finset.mem_map.mp P.2
  let O : NearPairing.NearOccurrence roots (2 * m) k r := Osub.1
  have hOselected : O.1 ∈
      ExchangeEmbedding.negativeBankSelection (m := m) roots theta := by
    exact (Finset.mem_product.mp Osub.2).1
  have hOall : O ∈ NearPairing.allNegativeNearOccurrences
      (k := k) (r := r) (m := m) roots := by
    apply Finset.mem_product.mpr
    exact ⟨NearPairing.negativeBankSelection_subset_allNegativeBankIndices
      roots theta hOselected, (Finset.mem_product.mp Osub.2).2⟩
  let Q := furtherPositivePartner hpartner A
  let g := Q ∩ A.1
  have hgcard : g.card = r := furtherPartner_inter_card hpartner A
  have hgA : g ∈ A.1.powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hgcard⟩
  have hgQ : g ∈ Q.powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hgcard⟩
  have hQall : Q ∈ NearPairing.allPositiveSplittingBlocks S :=
    furtherPositivePartner_mem hpartner A
  have hgForbidden : g ∈ eliminationForbidden := by
    apply hpositiveForbidden
    exact Finset.mem_biUnion.mpr ⟨Q, hQall, hgQ⟩
  have hgNeg : g ∈ P.1.negative.powersetCard r :=
    eliminationNegativeOnly_edge_mem_negativeRoot_of_mem_forbidden
      T P.1 P.2 hAP hgA hgForbidden
  have hPnegative : P.1.negative =
      NearPairing.nearOccurrenceBlock S O := by
    rw [← hOP]
    rfl
  have hgO : g ∈ (NearPairing.nearOccurrenceBlock S O).powersetCard r := by
    rw [← hPnegative]
    exact hgNeg
  have hgne : g ≠ NearPairing.nearOccurrenceEdge S O := by
    intro heq
    have hnot := eliminationNegativeOnly_edge_not_subset_positive
      T P.1 P.2 hAP hgA
    apply hnot
    rw [heq, ← hOP]
    change NearPairing.nearOccurrenceEdge S Osub.1 ⊆
      NearPairing.nearOccurrenceBlock S (f Osub).1
    rw [← hf Osub]
    exact NearPairing.nearOccurrenceEdge_subset_block S (f Osub).1
  have hQcopy : Q ∈
      (ExchangeEmbedding.mappedPositive E
        (S.embedding O.1.1.1 O.1.1.2 O.1.2)).erase O.1.1.1 :=
    NearPairing.allPositiveSplittingBlock_through_negativeNearEdge_sameCopy
      S hr hrootForbidden O hOall hgO hgne hQall hgQ
  have hQselected : Q ∈
      ExchangeEmbedding.selectedBankPositiveBlocks S theta := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨O.1, hOselected, hQcopy⟩
  have hQnotMatched : Q ∉ NearPairing.matchedNearPositiveBlocks S hr hrk
      hrootForbidden theta f hf := by
    intro hQmatched
    have hQnear := NearPairing.matchedNearPositiveBlocks_subset_selected
      S hr hrk hrootForbidden theta f hf hQmatched
    obtain ⟨I, hI, hQI⟩ := Finset.mem_biUnion.mp hQnear
    have hQleft : Q ∈
        (ExchangeEmbedding.positiveBankSelection (m := m) roots theta).biUnion
          (fun J ↦ ExchangeEmbedding.mappedNegative E
            (S.embedding J.1.1 J.1.2 J.2)) := by
      exact Finset.mem_biUnion.mpr
        ⟨I, hI,
          ExchangeEmbedding.mappedNearNegative_subset_mappedNegative E _ hQI⟩
    have hQright : Q ∈
        (ExchangeEmbedding.negativeBankSelection (m := m) roots theta).biUnion
          (fun J ↦ (ExchangeEmbedding.mappedPositive E
            (S.embedding J.1.1 J.1.2 J.2)).erase J.1.1) := by
      exact Finset.mem_biUnion.mpr ⟨O.1, hOselected, hQcopy⟩
    exact Finset.disjoint_left.mp
      (ExchangeEmbedding.selectedBankPositive_cross_disjoint
        S hr hrk hrootForbidden theta) hQleft hQright
  apply Finset.mem_union_left
  exact Finset.mem_sdiff.mpr ⟨hQselected, hQnotMatched⟩

/-- Coefficient-independent positive family present before the second
elimination round. -/
def preFurtherPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    Finset (Finset (Fin n)) :=
  NearPairing.allPositiveSplittingBlocks S ∪ allEliminationPositiveOnly U

theorem firstRoundPositiveBlocks_subset_preFurtherPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    firstRoundPositiveBlocks S hr hrk hrootForbidden theta f hf U ⊆
      preFurtherPositiveBlocks S hr hrk hrootForbidden U := by
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  intro B hB
  rcases Finset.mem_union.mp hB with hB | hB
  · exact Finset.mem_union_left _
      (NearPairing.selectedBankPositiveBlocks_subset_allPositiveSplittingBlocks
        S theta (Finset.mem_sdiff.mp hB).1)
  · exact Finset.mem_union_right _
      (allEliminationPositiveOnly_restrict_subset U hsub hB)

/-- After the selected bad outputs are removed, every remaining first-round
negative block belongs to the fixed far-plus-good prefix. -/
theorem firstRoundNegativeBlocks_sdiff_selectedBad_subset_preFurtherNegative
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap) :
    firstRoundNegativeBlocks S hr hrk hrootForbidden theta f hf U \
        selectedBadEliminationBlocks S hr hrk hrootForbidden theta f hf U ⊆
      preFurtherNegativeBlocks S hr hrk hrootForbidden U := by
  let hsub := NearPairing.matchedNearEliminationPairs_subset_compatible
    S hr hrk hrootForbidden theta f hf
  let T := U.restrict hsub
  intro B hB
  have hBdata := Finset.mem_sdiff.mp hB
  rcases Finset.mem_union.mp hBdata.1 with hBfar | hBout
  · exact Finset.mem_union_left _
      (NearPairing.selectedBankFarNegativeBlocks_subset_allNegativeFarSplittingBlocks
        S theta hBfar)
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨allEliminationNegativeOnly_restrict_subset U hsub hBout, ?_⟩
    intro hBbad
    have hBselected : B ∈ selectedBadEliminationBlocks S hr hrk
        hrootForbidden theta f hf U := by
      have hcollision := (mem_badEliminationBlocks.mp hBbad).2
      have hselected' : B ∈ badEliminationBlocks r
          (allEliminationNegativeOnly T)
          (NearPairing.allNegativeNearSplittingBlocks S) :=
        mem_badEliminationBlocks.mpr ⟨hBout, hcollision⟩
      simpa [selectedBadEliminationBlocks, T, hsub] using hselected'
    exact hBdata.2 hBselected

/-- Restrict the permanent second-round bank to precisely those bad
negative blocks which actually occur for the current coefficient vector. -/
def selectedFurtherEliminationPairs
    (hpartner : HasFurtherPartners n k r bad positive)
    (selectedBad : Finset (Finset (Fin n))) :
    Finset (EliminationPair n k r) :=
  (furtherEliminationPairs hpartner).filter fun P ↦
    P.negative ∈ selectedBad

theorem selectedFurtherEliminationPairs_subset
    (hpartner : HasFurtherPartners n k r bad positive)
    (selectedBad : Finset (Finset (Fin n))) :
    selectedFurtherEliminationPairs hpartner selectedBad ⊆
      furtherEliminationPairs hpartner :=
  Finset.filter_subset _ _

/-- Every selected second-round negative root is exactly a selected bad
block, and every selected bad block occurs once. -/
theorem image_negative_selectedFurtherEliminationPairs
    (hpartner : HasFurtherPartners n k r bad positive)
    (selectedBad : Finset (Finset (Fin n)))
    (hselected : selectedBad ⊆ bad) :
    (selectedFurtherEliminationPairs hpartner selectedBad).image
        EliminationPair.negative = selectedBad := by
  ext B
  constructor
  · intro hB
    obtain ⟨P, hP, hPB⟩ := Finset.mem_image.mp hB
    subst B
    exact (Finset.mem_filter.mp hP).2
  · intro hB
    let Bsub : ↑bad := ⟨B, hselected hB⟩
    let P := furtherEliminationPair hpartner Bsub
    apply Finset.mem_image.mpr
    refine ⟨P, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_furtherEliminationPairs_iff hpartner).mpr ⟨Bsub, rfl⟩
    · exact hB

theorem image_positive_selectedFurtherEliminationPairs_subset
    (hpartner : HasFurtherPartners n k r bad positive)
    (selectedBad : Finset (Finset (Fin n))) :
    (selectedFurtherEliminationPairs hpartner selectedBad).image
        EliminationPair.positive ⊆ positive := by
  intro P hP
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hP
  exact furtherEliminationPairs_positive_mem hpartner
    (selectedFurtherEliminationPairs_subset hpartner selectedBad hX)

/-- If no two selected bad blocks use the same partner, summing the roots of
the restricted pair family is exactly the incidence difference of the two
root images.  This is the coefficient-dependent uniqueness used in Step 5. -/
theorem selectedFurtherPairs_signed_sum
    (hpartner : HasFurtherPartners n k r bad positive)
    (selectedBad : Finset (Finset (Fin n)))
    (hinjective : Set.InjOn
      (fun B : ↑bad ↦ furtherPositivePartner hpartner B)
      {B | B.1 ∈ selectedBad})
    (g : Finset (Fin n)) :
    (∑ P ∈ (selectedFurtherEliminationPairs hpartner selectedBad).attach,
        ((if g ⊆ P.1.positive then (1 : ℤ) else 0) -
          (if g ⊆ P.1.negative then (1 : ℤ) else 0))) =
      (incidenceCount
        ((selectedFurtherEliminationPairs hpartner selectedBad).image
          EliminationPair.positive) g : ℤ) -
      (incidenceCount
          ((selectedFurtherEliminationPairs hpartner selectedBad).image
            EliminationPair.negative) g : ℤ) := by
  classical
  let pairs := selectedFurtherEliminationPairs hpartner selectedBad
  have hposInj : Set.InjOn EliminationPair.positive
      (↑pairs : Set (EliminationPair n k r)) := by
    intro P hP P' hP' hEq
    have hPmem : P ∈ furtherEliminationPairs hpartner :=
      selectedFurtherEliminationPairs_subset hpartner selectedBad hP
    have hP'mem : P' ∈ furtherEliminationPairs hpartner :=
      selectedFurtherEliminationPairs_subset hpartner selectedBad hP'
    obtain ⟨B, hBP⟩ :=
      (mem_furtherEliminationPairs_iff hpartner).mp hPmem
    obtain ⟨B', hB'P'⟩ :=
      (mem_furtherEliminationPairs_iff hpartner).mp hP'mem
    subst P
    subst P'
    have hBsel : B.1 ∈ selectedBad := (Finset.mem_filter.mp hP).2
    have hB'sel : B'.1 ∈ selectedBad := (Finset.mem_filter.mp hP').2
    have hBB' : B = B' := hinjective hBsel hB'sel hEq
    subst B'
    rfl
  have hnegInj : Set.InjOn EliminationPair.negative
      (↑pairs : Set (EliminationPair n k r)) := by
    intro P hP P' hP' hEq
    have hPmem : P ∈ furtherEliminationPairs hpartner :=
      selectedFurtherEliminationPairs_subset hpartner selectedBad hP
    have hP'mem : P' ∈ furtherEliminationPairs hpartner :=
      selectedFurtherEliminationPairs_subset hpartner selectedBad hP'
    obtain ⟨B, hBP⟩ :=
      (mem_furtherEliminationPairs_iff hpartner).mp hPmem
    obtain ⟨B', hB'P'⟩ :=
      (mem_furtherEliminationPairs_iff hpartner).mp hP'mem
    subst P
    subst P'
    have hBB' : B = B' := Subtype.ext hEq
    subst B'
    rfl
  rw [NearPairing.incidenceCount_image_of_injective pairs
      EliminationPair.positive
      hposInj g,
    NearPairing.incidenceCount_image_of_injective pairs
      EliminationPair.negative
      hnegInj g]
  push_cast
  rw [← Finset.sum_sub_distrib]
  simpa using Finset.sum_attach pairs (fun P ↦
    (if g ⊆ P.positive then (1 : ℤ) else 0) -
      (if g ⊆ P.negative then (1 : ℤ) else 0))

/-- Execute a coefficient-dependent second round by restricting the fixed
further-elimination bank.  The signed output replaces exactly the selected
positive partners and selected bad negative blocks. -/
theorem selectedFurtherEliminationRound_of_fixedBank
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {bad positive : Finset (Finset (Fin n))}
    (hpartner : HasFurtherPartners n k r bad positive)
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (furtherEliminationPairs hpartner) ⊆
          forbidden)
    (hcommon : ∀ B : ↑bad, ∀ B' : ↑bad, B ≠ B' →
      ∀ g ∈ B.1.powersetCard r, g ∈ B'.1.powersetCard r →
        g ⊆ furtherPositivePartner hpartner B ∧
          g ⊆ furtherPositivePartner hpartner B')
    (selectedBad : Finset (Finset (Fin n)))
    (hselected : selectedBad ⊆ bad)
    (hinjective : Set.InjOn
      (fun B : ↑bad ↦ furtherPositivePartner hpartner B)
      {B | B.1 ∈ selectedBad}) :
    let selectedPairs := selectedFurtherEliminationPairs hpartner selectedBad
    let W := V.restrict
      (selectedFurtherEliminationPairs_subset hpartner selectedBad)
    Disjoint (allEliminationPositiveOnly W)
        (allEliminationNegativeOnly W) ∧
      IsUniformDecomposition (allEliminationNegativeOnlyHost W)
        (allEliminationNegativeOnly W) k r ∧
      ∀ g : Finset (Fin n), g.card = r →
        (incidenceCount (allEliminationPositiveOnly W) g : ℤ) -
            (incidenceCount (allEliminationNegativeOnly W) g : ℤ) =
          (incidenceCount
            (selectedPairs.image EliminationPair.positive) g : ℤ) -
            (incidenceCount selectedBad g : ℤ) := by
  let selectedPairs := selectedFurtherEliminationPairs hpartner selectedBad
  let hsub := selectedFurtherEliminationPairs_subset hpartner selectedBad
  let W := V.restrict hsub
  have hselectedRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary selectedPairs ⊆
        forbidden :=
    (eliminationPairSideBoundary_mono hsub).trans huniversalRootForbidden
  have hcommonPairs : ∀ P ∈ selectedPairs, ∀ P' ∈ selectedPairs,
      P ≠ P' → ∀ g ∈ P.negative.powersetCard r,
        g ∈ P'.negative.powersetCard r →
          g ⊆ P.positive ∧ g ⊆ P'.positive := by
    intro P hP P' hP' hne g hg hg'
    exact furtherEliminationPairs_common_in_positive hpartner hcommon
      P (hsub hP) P' (hsub hP') hne g hg hg'
  have hround := allEliminationOnly_round_of_common_in_positive W hr hrk
    hselectedRootForbidden hcommonPairs
  refine ⟨hround.1, hround.2.1, ?_⟩
  intro g hg
  rw [hround.2.2 g hg]
  rw [selectedFurtherPairs_signed_sum hpartner selectedBad hinjective g]
  rw [image_negative_selectedFurtherEliminationPairs hpartner selectedBad
    hselected]

/-- The positive roots selected for the second round are all present after
the first round. -/
theorem image_positive_selectedFurther_subset_firstRoundPositive
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S)) :
    (selectedFurtherEliminationPairs hpartner
        (selectedBadEliminationBlocks S hr hrk hrootForbidden
          theta f hf U)).image EliminationPair.positive ⊆
      firstRoundPositiveBlocks S hr hrk hrootForbidden theta f hf U := by
  intro Q hQ
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
  have hPall := selectedFurtherEliminationPairs_subset hpartner
    (selectedBadEliminationBlocks S hr hrk hrootForbidden theta f hf U) hP
  obtain ⟨A, hAP⟩ := (mem_furtherEliminationPairs_iff hpartner).mp hPall
  have hPselected := (Finset.mem_filter.mp hP).2
  subst P
  exact furtherPositivePartner_mem_firstRoundPositiveBlocks
    S hr hrk hrootForbidden theta f hf U hpositiveForbidden hpartner A
      hPselected

/-- Positive block family after both elimination rounds. -/
def booleanizedPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    Finset (Finset (Fin n)) :=
  let selectedBad := selectedBadEliminationBlocks S hr hrk
    hrootForbidden theta f hf U
  let selectedPairs := selectedFurtherEliminationPairs hpartner selectedBad
  let W := V.restrict
    (selectedFurtherEliminationPairs_subset hpartner selectedBad)
  (firstRoundPositiveBlocks S hr hrk hrootForbidden theta f hf U \
      selectedPairs.image EliminationPair.positive) ∪
    allEliminationPositiveOnly W

/-- Negative block family after both elimination rounds. -/
def booleanizedNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    Finset (Finset (Fin n)) :=
  let selectedBad := selectedBadEliminationBlocks S hr hrk
    hrootForbidden theta f hf U
  let W := V.restrict
    (selectedFurtherEliminationPairs_subset hpartner selectedBad)
  (firstRoundNegativeBlocks S hr hrk hrootForbidden theta f hf U \
      selectedBad) ∪ allEliminationNegativeOnly W

/-- Both elimination rounds together preserve the selected splitting
boundary. -/
theorem booleanizedBlocks_signedIncidence
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hbound : E.SpecialPositiveInterBounded e₀)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (hfurtherRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (furtherEliminationPairs hpartner) ⊆
          furtherForbidden)
    (hprePositiveForbidden :
      (preFurtherPositiveBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden)
    (hprefixForbidden :
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden)
    (g : Finset (Fin n)) (hg : g.card = r) :
    (incidenceCount
        (booleanizedPositiveBlocks S hr hrk hrootForbidden theta f hf U
          hpartner V) g : ℤ) -
      (incidenceCount
        (booleanizedNegativeBlocks S hr hrk hrootForbidden theta f hf U
          hpartner V) g : ℤ) =
      (incidenceCount
        (ExchangeEmbedding.selectedBankPositiveBlocks S theta) g : ℤ) -
      (incidenceCount
        (ExchangeEmbedding.selectedBankNegativeBlocks S theta) g : ℤ) := by
  let selectedBad := selectedBadEliminationBlocks S hr hrk
    hrootForbidden theta f hf U
  let selectedPairs := selectedFurtherEliminationPairs hpartner selectedBad
  let hsub := selectedFurtherEliminationPairs_subset hpartner selectedBad
  let W := V.restrict hsub
  let firstPositive := firstRoundPositiveBlocks S hr hrk hrootForbidden
    theta f hf U
  let firstNegative := firstRoundNegativeBlocks S hr hrk hrootForbidden
    theta f hf U
  have hselected : selectedBad ⊆
      universalBadEliminationBlocks S hr hrk hrootForbidden U := by
    exact selectedBadEliminationBlocks_subset_universal
      S hr hrk hrootForbidden theta f hf U
  have hcommon := universalBadEliminationBlocks_common_in_positivePartner
    S hr hrk hbound hrootForbidden U hpositiveForbidden
      huniversalRootForbidden hpartner
  have hinjective := furtherPositivePartner_injOn_selectedBadEliminationBlocks
    S hr hrk hrootForbidden theta f hf U hpositiveForbidden
      huniversalRootForbidden hpartner
  have hround := (selectedFurtherEliminationRound_of_fixedBank
    hpartner V hr hrk hfurtherRootForbidden hcommon selectedBad
      hselected hinjective).2.2
  have hpositiveRoots : selectedPairs.image EliminationPair.positive ⊆
      firstPositive := by
    exact image_positive_selectedFurther_subset_firstRoundPositive
      S hr hrk hrootForbidden theta f hf U hpositiveForbidden hpartner
  have hnegativeRoots : selectedBad ⊆ firstNegative := by
    exact selectedBadEliminationBlocks_subset_firstRoundNegativeBlocks
      S hr hrk hrootForbidden theta f hf U
  have hfirstPositiveSub : firstPositive ⊆
      preFurtherPositiveBlocks S hr hrk hrootForbidden U := by
    exact firstRoundPositiveBlocks_subset_preFurtherPositiveBlocks
      S hr hrk hrootForbidden theta f hf U
  have hremainingNegativeSub : firstNegative \ selectedBad ⊆
      preFurtherNegativeBlocks S hr hrk hrootForbidden U := by
    exact firstRoundNegativeBlocks_sdiff_selectedBad_subset_preFurtherNegative
      S hr hrk hrootForbidden theta f hf U
  have hpositiveDisjoint : Disjoint
      (firstPositive \ selectedPairs.image EliminationPair.positive)
      (allEliminationPositiveOnly W) := by
    exact (allEliminationPositiveOnly_disjoint_forbiddenFamily W hr hrk
      (preFurtherPositiveBlocks S hr hrk hrootForbidden U)
      hprePositiveForbidden).symm.mono
        (Finset.sdiff_subset.trans hfirstPositiveSub) (fun _ h ↦ h)
  have hnegativeDisjoint : Disjoint (firstNegative \ selectedBad)
      (allEliminationNegativeOnly W) := by
    exact (allEliminationNegativeOnly_disjoint_forbiddenFamily W hr hrk
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U)
      hprefixForbidden).symm.mono hremainingNegativeSub (fun _ h ↦ h)
  have hsecond := signedIncidence_replace firstPositive firstNegative
    (selectedPairs.image EliminationPair.positive) selectedBad
    (allEliminationPositiveOnly W) (allEliminationNegativeOnly W)
    hpositiveRoots hnegativeRoots hpositiveDisjoint hnegativeDisjoint
    hround g hg
  have hfirst := firstRoundBlocks_signedIncidence
    S hr hrk hrootForbidden theta f hf U hpositiveForbidden hfarForbidden
      huniversalRootForbidden g hg
  have hposEq :
      booleanizedPositiveBlocks S hr hrk hrootForbidden theta f hf U
          hpartner V =
        (firstPositive \ selectedPairs.image EliminationPair.positive) ∪
          allEliminationPositiveOnly W := by
    rfl
  have hnegEq :
      booleanizedNegativeBlocks S hr hrk hrootForbidden theta f hf U
          hpartner V =
        (firstNegative \ selectedBad) ∪ allEliminationNegativeOnly W := by
    rfl
  rw [hposEq, hnegEq]
  exact hsecond.trans hfirst

/-- The coefficient-dependent final negative family is a subfamily of the
fixed coefficient-independent negative bank. -/
theorem booleanizedNegativeBlocks_subset_finalNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    booleanizedNegativeBlocks S hr hrk hrootForbidden theta f hf U
        hpartner V ⊆
      finalNegativeBlocks S hr hrk hrootForbidden U hpartner V := by
  let selectedBad := selectedBadEliminationBlocks S hr hrk
    hrootForbidden theta f hf U
  let hsub := selectedFurtherEliminationPairs_subset hpartner selectedBad
  let W := V.restrict hsub
  have hleft :
      firstRoundNegativeBlocks S hr hrk hrootForbidden theta f hf U \
          selectedBad ⊆
        preFurtherNegativeBlocks S hr hrk hrootForbidden U := by
    exact firstRoundNegativeBlocks_sdiff_selectedBad_subset_preFurtherNegative
      S hr hrk hrootForbidden theta f hf U
  have hright : allEliminationNegativeOnly W ⊆
      allEliminationNegativeOnly V := by
    exact allEliminationNegativeOnly_restrict_subset V hsub
  simpa only [booleanizedNegativeBlocks, finalNegativeBlocks,
    selectedBad, W, hsub] using Finset.union_subset_union hleft hright

/-- Fixed coefficient-independent positive bank containing every possible
two-round positive output. -/
def finalPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    Finset (Finset (Fin n)) :=
  preFurtherPositiveBlocks S hr hrk hrootForbidden U ∪
    allEliminationPositiveOnly V

theorem finalPositiveBlocks_uniform
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    {B : Finset (Fin n)}
    (hB : B ∈ finalPositiveBlocks S hr hrk hrootForbidden U hpartner V) :
    B.card = k := by
  rcases Finset.mem_union.mp hB with hB | hB
  · rcases Finset.mem_union.mp hB with hB | hB
    · exact NearPairing.allPositiveSplittingBlocks_uniform S hB
    · exact allEliminationPositiveOnly_uniform U hB
  · exact allEliminationPositiveOnly_uniform V hB

theorem booleanizedPositiveBlocks_subset_finalPositiveBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    (theta : Finset (Fin n) → ℤ)
    (f : ↑(NearPairing.negativeNearOccurrences
        (k := k) (r := r) (m := m) roots theta) ↪
      ↑(NearPairing.positiveNearOccurrences
        (k := k) (r := r) (m := m) roots theta))
    (hf : ∀ O, NearPairing.nearOccurrenceEdge S (f O).1 =
      NearPairing.nearOccurrenceEdge S O.1)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap) :
    booleanizedPositiveBlocks S hr hrk hrootForbidden theta f hf U
        hpartner V ⊆
      finalPositiveBlocks S hr hrk hrootForbidden U hpartner V := by
  let selectedBad := selectedBadEliminationBlocks S hr hrk
    hrootForbidden theta f hf U
  let selectedPairs := selectedFurtherEliminationPairs hpartner selectedBad
  let hsub := selectedFurtherEliminationPairs_subset hpartner selectedBad
  let W := V.restrict hsub
  have hleft : firstRoundPositiveBlocks S hr hrk hrootForbidden theta f hf U \
      selectedPairs.image EliminationPair.positive ⊆
        preFurtherPositiveBlocks S hr hrk hrootForbidden U :=
    Finset.sdiff_subset.trans
      (firstRoundPositiveBlocks_subset_preFurtherPositiveBlocks
        S hr hrk hrootForbidden theta f hf U)
  have hright : allEliminationPositiveOnly W ⊆
      allEliminationPositiveOnly V :=
    allEliminationPositiveOnly_restrict_subset V hsub
  simpa only [booleanizedPositiveBlocks, finalPositiveBlocks,
    selectedBad, selectedPairs, W, hsub] using
      Finset.union_subset_union hleft hright

theorem preFurtherPositiveBlocks_disjoint_preFurtherNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (htradeDisjoint : Disjoint E.positive E.negative)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden) :
    Disjoint (preFurtherPositiveBlocks S hr hrk hrootForbidden U)
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U) := by
  have hsplitFar :=
    NearPairing.allPositiveSplittingBlocks_disjoint_allNegativeFarSplittingBlocks
      S hr hrk hrootForbidden htradeDisjoint
  have hUout : Disjoint (allEliminationPositiveOnly U)
      (allEliminationNegativeOnly U) :=
    allEliminationPositiveOnly_disjoint_allEliminationNegativeOnly
      U hr hrk huniversalRootForbidden
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  rcases Finset.mem_union.mp hBpos with hBsplit | hBUpos <;>
    rcases Finset.mem_union.mp hBneg with hBfar | hBUgood
  · exact Finset.disjoint_left.mp hsplitFar hBsplit hBfar
  · exact Finset.disjoint_left.mp
      (allEliminationNegativeOnly_disjoint_forbiddenFamily U hr hrk
        (NearPairing.allPositiveSplittingBlocks S) hpositiveForbidden).symm
        hBsplit (Finset.mem_sdiff.mp hBUgood).1
  · exact Finset.disjoint_left.mp
      (allEliminationPositiveOnly_disjoint_forbiddenFamily U hr hrk
        (NearPairing.allNegativeFarSplittingBlocks S) hfarForbidden)
        hBUpos hBfar
  · exact Finset.disjoint_left.mp hUout hBUpos
      (Finset.mem_sdiff.mp hBUgood).1

/-- A new elimination bank can be adjoined to two old disjoint block
families when both old boundaries were forbidden to its free part. -/
theorem disjoint_union_allEliminationOnly
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden oldPositive oldNegative : Finset (Finset (Fin n))}
    {C : ℕ}
    (V : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary pairs ⊆
        forbidden)
    (hold : Disjoint oldPositive oldNegative)
    (hpositiveForbidden : oldPositive.biUnion
      (fun B ↦ B.powersetCard r) ⊆ forbidden)
    (hnegativeForbidden : oldNegative.biUnion
      (fun B ↦ B.powersetCard r) ⊆ forbidden) :
    Disjoint (oldPositive ∪ allEliminationPositiveOnly V)
      (oldNegative ∪ allEliminationNegativeOnly V) := by
  have hVout : Disjoint (allEliminationPositiveOnly V)
      (allEliminationNegativeOnly V) :=
    allEliminationPositiveOnly_disjoint_allEliminationNegativeOnly
      V hr hrk hrootForbidden
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  rcases Finset.mem_union.mp hBpos with hBprePos | hBVpos <;>
    rcases Finset.mem_union.mp hBneg with hBpreNeg | hBVneg
  · exact Finset.disjoint_left.mp hold hBprePos hBpreNeg
  · exact Finset.disjoint_left.mp
      (allEliminationNegativeOnly_disjoint_forbiddenFamily V hr hrk
        oldPositive hpositiveForbidden).symm hBprePos hBVneg
  · exact Finset.disjoint_left.mp
      (allEliminationPositiveOnly_disjoint_forbiddenFamily V hr hrk
        oldNegative hnegativeForbidden) hBVpos hBpreNeg
  · exact Finset.disjoint_left.mp hVout hBVpos hBVneg

/-- The two fixed banks used by Booleanization are block-disjoint. -/
theorem finalPositiveBlocks_disjoint_finalNegativeBlocks
    {E : ExchangePattern.RelabeledFullExchange k r}
    {e₀ : Exchange.RootEdge k r}
    {roots splitForbidden : Finset (Finset (Fin n))}
    {m splitCap eliminationCap furtherCap : ℕ}
    (S : RootedFamilyMultiEmbedding.BoundedMultiRootedFamilyEmbeddings
      E.pattern roots splitForbidden (2 * m) splitCap)
    (hr : 0 < r) (hrk : r < k)
    (htradeDisjoint : Disjoint E.positive E.negative)
    (hrootForbidden : ExchangeEmbedding.rootBoundary roots r ⊆ splitForbidden)
    {eliminationForbidden : Finset (Finset (Fin n))}
    (U : BoundedEliminationPairEmbeddings E e₀
      (NearPairing.compatibleNearEliminationPairs S hr hrk hrootForbidden)
      eliminationForbidden eliminationCap)
    (hpositiveForbidden :
      (NearPairing.allPositiveSplittingBlocks S).biUnion
          (fun Q ↦ Q.powersetCard r) ⊆ eliminationForbidden)
    (hfarForbidden :
      (NearPairing.allNegativeFarSplittingBlocks S).biUnion
          (fun B ↦ B.powersetCard r) ⊆ eliminationForbidden)
    (huniversalRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (NearPairing.compatibleNearEliminationPairs S hr hrk
          hrootForbidden) ⊆
            eliminationForbidden)
    (hpartner : HasFurtherPartners n k r
      (universalBadEliminationBlocks S hr hrk hrootForbidden U)
      (NearPairing.allPositiveSplittingBlocks S))
    {furtherForbidden : Finset (Finset (Fin n))}
    (V : BoundedEliminationPairEmbeddings E e₀
      (furtherEliminationPairs hpartner) furtherForbidden furtherCap)
    (hfurtherRootForbidden :
      ExchangeEliminationEmbedding.eliminationPairSideBoundary
        (furtherEliminationPairs hpartner) ⊆
          furtherForbidden)
    (hprePositiveForbidden :
      (preFurtherPositiveBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden)
    (hprefixForbidden :
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U).biUnion
          (fun B ↦ B.powersetCard r) ⊆ furtherForbidden) :
    Disjoint (finalPositiveBlocks S hr hrk hrootForbidden U hpartner V)
      (finalNegativeBlocks S hr hrk hrootForbidden U hpartner V) := by
  have hpre : Disjoint
      (preFurtherPositiveBlocks S hr hrk hrootForbidden U)
      (preFurtherNegativeBlocks S hr hrk hrootForbidden U) := by
    exact preFurtherPositiveBlocks_disjoint_preFurtherNegativeBlocks
      S hr hrk htradeDisjoint hrootForbidden U hpositiveForbidden
        hfarForbidden huniversalRootForbidden
  have h := disjoint_union_allEliminationOnly V hr hrk
    hfurtherRootForbidden hpre hprePositiveForbidden hprefixForbidden
  change Disjoint
    (preFurtherPositiveBlocks S hr hrk hrootForbidden U ∪
      allEliminationPositiveOnly V)
    (preFurtherNegativeBlocks S hr hrk hrootForbidden U ∪
      allEliminationNegativeOnly V)
  exact h

/-- Algebraic replacement lemma for the second elimination round.  Removing
the two prescribed sides and inserting a signed exchange remainder preserves
the entire `r`-boundary.  The hypotheses expose exactly the block-level
disjointness which the three random-greedy placements provide. -/
theorem signedIncidence_furtherElimination
    (positive negative positiveRoots negativeRoots
      outputPositive outputNegative : Finset (Finset (Fin n)))
    (hpositiveRoots : positiveRoots ⊆ positive)
    (hnegativeRoots : negativeRoots ⊆ negative)
    (hpositiveDisjoint : Disjoint (positive \ positiveRoots) outputPositive)
    (hnegativeDisjoint : Disjoint (negative \ negativeRoots) outputNegative)
    (hround : ∀ g : Finset (Fin n), g.card = r →
      (incidenceCount outputPositive g : ℤ) -
          (incidenceCount outputNegative g : ℤ) =
        (incidenceCount positiveRoots g : ℤ) -
          (incidenceCount negativeRoots g : ℤ))
    (g : Finset (Fin n)) (hg : g.card = r) :
    (incidenceCount
        ((positive \ positiveRoots) ∪ outputPositive) g : ℤ) -
        (incidenceCount
          ((negative \ negativeRoots) ∪ outputNegative) g : ℤ) =
      (incidenceCount positive g : ℤ) -
        (incidenceCount negative g : ℤ) := by
  have hposLe : incidenceCount positiveRoots g ≤
      incidenceCount positive g :=
    Finset.card_le_card (Finset.filter_subset_filter _ hpositiveRoots)
  have hnegLe : incidenceCount negativeRoots g ≤
      incidenceCount negative g :=
    Finset.card_le_card (Finset.filter_subset_filter _ hnegativeRoots)
  rw [ExchangeEmbedding.incidenceCount_union_of_disjoint
      hpositiveDisjoint,
    ExchangeEmbedding.incidenceCount_union_of_disjoint hnegativeDisjoint,
    incidenceCount_sdiff hpositiveRoots g,
    incidenceCount_sdiff hnegativeRoots g]
  push_cast [Nat.cast_sub hposLe, Nat.cast_sub hnegLe]
  have hr := hround g hg
  omega

end

end Erdos722.FurtherElimination

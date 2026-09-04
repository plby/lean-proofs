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
import ErdosProblems.Erdos722.ExchangeEmbedding
import ErdosProblems.Erdos722.RequestedFamilyEmbedding
import Mathlib

/-!
# Root requests for two-clique elimination exchanges

The full exchange contains a designated positive root and, for every root
edge, an isolated negative special block.  Their union is the root of the
two-clique elimination pattern.  This file constructs a labelled root
request carrying those two blocks onto any prescribed pair of `k`-sets with
an `r`-vertex intersection.
-/

namespace Erdos722.ExchangeEliminationEmbedding

open Finset
open Erdos722.Transversal
open Erdos722.Exchange
open Erdos722.ExchangePattern
open Erdos722.ExchangeEmbedding
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.RequestedFamilyEmbedding
open Erdos722.RootedFamilyAsymptotic
open Erdos722.LocalDecoderAsymptotic
open Filter

noncomputable section

structure EliminationPair (n k r : ℕ) where
  positive : Finset (Fin n)
  negative : Finset (Fin n)
  positive_card : positive.card = k
  negative_card : negative.card = k
  inter_card : (positive ∩ negative).card = r

def EliminationPair.root (P : EliminationPair n k r) : Finset (Fin n) :=
  P.positive ∪ P.negative

theorem EliminationPair.root_card (P : EliminationPair n k r) :
    P.root.card = 2 * k - r := by
  have hcount := Finset.card_union_add_card_inter P.positive P.negative
  rw [P.positive_card, P.negative_card, P.inter_card] at hcount
  unfold EliminationPair.root
  omega

/-- The family of all prescribed positive and negative sides.  Unlike the
family of pair unions, this is the source-faithful host to which individual
root traces of an admissible elimination extension are charged. -/
def eliminationPairSides
    (pairs : Finset (EliminationPair n k r)) : Finset (Finset (Fin n)) :=
  pairs.image EliminationPair.positive ∪
    pairs.image EliminationPair.negative

/-- The prescribed `r`-edges of the two clique sides of every elimination
request.  Mixed `r`-sets in the union of the two sides are deliberately not
included: trace isolation never needs them in the forbidden host. -/
def eliminationPairSideBoundary
    (pairs : Finset (EliminationPair n k r)) : Finset (Finset (Fin n)) :=
  (eliminationPairSides pairs).biUnion fun Q ↦ Q.powersetCard r

theorem eliminationPairSideBoundary_mono
    {pairs pairs' : Finset (EliminationPair n k r)} (hsub : pairs ⊆ pairs') :
    eliminationPairSideBoundary pairs ⊆ eliminationPairSideBoundary pairs' := by
  intro g hg
  obtain ⟨Q, hQ, hgQ⟩ := Finset.mem_biUnion.mp hg
  apply Finset.mem_biUnion.mpr
  refine ⟨Q, ?_, hgQ⟩
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨P, hsub hP, rfl⟩)
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨P, hsub hP, rfl⟩)

theorem eliminationPairSides_uniform
    (pairs : Finset (EliminationPair n k r))
    {Q : Finset (Fin n)} (hQ : Q ∈ eliminationPairSides pairs) :
    Q.card = k := by
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp hQ
    exact P.positive_card
  · obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp hQ
    exact P.negative_card

def eliminationRootMultiplicity (k r : ℕ) : ℕ :=
  (2 ^ (2 * k - r)) ^ 2

lemma eliminationRootMultiplicity_pos :
    0 < eliminationRootMultiplicity k r := by
  simp [eliminationRootMultiplicity]

/-- The isolation property of the designated special clique: a host edge
lying in the union of the positive root and this special clique already lies
in one of the two cliques. -/
def IsSpecialIsolated (E : RelabeledFullExchange k r)
    (e₀ : RootEdge k r) : Prop :=
  ∀ g ∈ E.pattern.edges,
    g ⊆ E.pattern.root ∪ E.special e₀ →
      g ⊆ E.pattern.root ∨ g ⊆ E.special e₀

theorem RelabeledFullExchange.isSpecialIsolated
    (E : RelabeledFullExchange k r) (e₀ : RootEdge k r) :
    IsSpecialIsolated E e₀ :=
  E.special_isolated e₀

/-- Strong trace isolation says precisely that every non-root edge of the
elimination pattern has its prescribed root part on one of the two
distinguished clique sides. -/
theorem eliminationFreeEdge_rootTrace_subset_side
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    (htrace : E.SpecialTraceIsolated e₀)
    {g : Finset (Fin E.v)}
    (hg : g ∈ (E.eliminationPattern e₀).freeEdges) :
    g ∩ (E.eliminationPattern e₀).root ⊆ E.pattern.root ∨
      g ∩ (E.eliminationPattern e₀).root ⊆ E.special e₀ := by
  have hgedges : g ∈ E.pattern.edges := (Finset.mem_filter.mp hg).1
  simpa [RelabeledFullExchange.eliminationPattern_root] using
    htrace g hgedges

/-- Number of prescribed positive sides containing a fixed ground face,
counting ordered elimination pairs rather than distinct side sets. -/
def positiveSideOccurrenceDegree
    (pairs : Finset (EliminationPair n k r))
    (J : Finset (Fin n)) : ℕ :=
  (pairs.attach.filter fun P ↦ J ⊆ P.1.positive).card

/-- Number of prescribed negative sides containing a fixed ground face,
again retaining repetitions at distinct ordered pairs. -/
def negativeSideOccurrenceDegree
    (pairs : Finset (EliminationPair n k r))
    (J : Finset (Fin n)) : ℕ :=
  (pairs.attach.filter fun P ↦ J ⊆ P.1.negative).card

/-- Trace isolation only needs occurrence-degree control of the two
prescribed side schedules.  This is sharper than bounding a set of sides
and multiplying by its largest fibre, and is essential when a square-root
group deliberately repeats its positive intermediate clique. -/
theorem hasRootPartCountBound_elimination_requests_of_occurrenceDegree
    (E : RelabeledFullExchange k r) (e₀ : RootEdge k r)
    (htrace : E.SpecialTraceIsolated e₀)
    (pairs : Finset (EliminationPair n k r))
    (request : ℕ → RootRequest E.v n (E.eliminationPattern e₀).root)
    (pairAt : Fin pairs.card → EliminationPair n k r)
    (hpairAtMem : ∀ i, pairAt i ∈ pairs)
    (hpairAtInj : Function.Injective pairAt)
    (hrequestPos : ∀ i,
      E.pattern.root.image (request i.1).map = (pairAt i).positive)
    (hrequestNeg : ∀ i,
      (E.special e₀).image (request i.1).map = (pairAt i).negative)
    (cap : ℕ) (hrk : r < k)
    (hpositiveMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      positiveSideOccurrenceDegree pairs J ≤ cap)
    (hnegativeMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      negativeSideOccurrenceDegree pairs J ≤ cap) :
    HasRootPartCountBound (E.eliminationPattern e₀) request pairs.card
      cap := by
  intro g hg I hI
  rcases eliminationFreeEdge_rootTrace_subset_side htrace hg with
      hpositive | hnegative
  · let blockAt : Fin pairs.card → Finset (Fin n) :=
      fun i ↦ (pairAt i).positive
    have hcodim : ∀ J : Finset (Fin n), J.card = r - 1 →
        ((Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
          J ⊆ blockAt i).card ≤ cap := by
      intro J hJ
      let left := (Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
        J ⊆ blockAt i
      let right := pairs.attach.filter fun P ↦ J ⊆ P.1.positive
      have hcard : left.card ≤ right.card := by
        apply Finset.card_le_card_of_injOn
          (fun i ↦ ⟨pairAt i, hpairAtMem i⟩)
        · intro i hi
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp hi).2⟩
        · intro i hi j hj hij
          exact hpairAtInj (congrArg Subtype.val hij)
      exact hcard.trans (by
        simpa [right, positiveSideOccurrenceDegree] using hpositiveMax J hJ)
    have hall := card_indices_containing_le_pow_mul_of_codimOne
      blockAt (fun i ↦ (pairAt i).positive_card) (by omega)
        I hI cap hcodim
    apply (Finset.card_le_card ?_).trans hall
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, hiData.2.trans ?_⟩
    change (g ∩ (E.eliminationPattern e₀).root).image
        (request i.1).map ⊆ (pairAt i).positive
    rw [← hrequestPos i]
    exact Finset.image_mono _ hpositive
  · let blockAt : Fin pairs.card → Finset (Fin n) :=
      fun i ↦ (pairAt i).negative
    have hcodim : ∀ J : Finset (Fin n), J.card = r - 1 →
        ((Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
          J ⊆ blockAt i).card ≤ cap := by
      intro J hJ
      let left := (Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
        J ⊆ blockAt i
      let right := pairs.attach.filter fun P ↦ J ⊆ P.1.negative
      have hcard : left.card ≤ right.card := by
        apply Finset.card_le_card_of_injOn
          (fun i ↦ ⟨pairAt i, hpairAtMem i⟩)
        · intro i hi
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp hi).2⟩
        · intro i hi j hj hij
          exact hpairAtInj (congrArg Subtype.val hij)
      exact hcard.trans (by
        simpa [right, negativeSideOccurrenceDegree] using hnegativeMax J hJ)
    have hall := card_indices_containing_le_pow_mul_of_codimOne
      blockAt (fun i ↦ (pairAt i).negative_card) (by omega)
        I hI cap hcodim
    apply (Finset.card_le_card ?_).trans hall
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, hiData.2.trans ?_⟩
    change (g ∩ (E.eliminationPattern e₀).root).image
        (request i.1).map ⊆ (pairAt i).negative
    rw [← hrequestNeg i]
    exact Finset.image_mono _ hnegative

/-- If every prescribed side occurs only boundedly often and the side
family has bounded codimension-one degree, admissibility gives the sharp
per-pattern-edge root schedule bound. -/
theorem hasRootPartCountBound_elimination_requests
    (E : RelabeledFullExchange k r) (e₀ : RootEdge k r)
    (htrace : E.SpecialTraceIsolated e₀)
    (pairs : Finset (EliminationPair n k r))
    (request : ℕ → RootRequest E.v n (E.eliminationPattern e₀).root)
    (pairAt : Fin pairs.card → EliminationPair n k r)
    (hpairAtMem : ∀ i, pairAt i ∈ pairs)
    (hrequestPos : ∀ i,
      E.pattern.root.image (request i.1).map = (pairAt i).positive)
    (hrequestNeg : ∀ i,
      (E.special e₀).image (request i.1).map = (pairAt i).negative)
    (multiplicity cap : ℕ)
    (hpositiveFiber : ∀ Q : Finset (Fin n),
      ((Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
        (pairAt i).positive = Q).card ≤ multiplicity)
    (hnegativeFiber : ∀ Q : Finset (Fin n),
      ((Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
        (pairAt i).negative = Q).card ≤ multiplicity)
    (hrk : r < k)
    (hsideMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree (eliminationPairSides pairs) J ≤ cap) :
    HasRootPartCountBound (E.eliminationPattern e₀) request pairs.card
      (multiplicity * cap) := by
  intro g hg I hI
  have huniform : ∀ Q ∈ eliminationPairSides pairs, Q.card = k :=
    fun Q hQ ↦ eliminationPairSides_uniform pairs hQ
  have hlower : Reserve.localDegree (eliminationPairSides pairs) I ≤
      n ^ (r - 1 - I.card) * cap :=
    localDegree_le_pow_mul_of_codimOne_of_uniform
      (eliminationPairSides pairs) huniform (by omega) I hI cap hsideMax
  rcases eliminationFreeEdge_rootTrace_subset_side htrace hg with
      hpositive | hnegative
  · let blockAt : Fin pairs.card → Finset (Fin n) :=
      fun i ↦ (pairAt i).positive
    have hblockMem : ∀ i, blockAt i ∈ eliminationPairSides pairs := by
      intro i
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨pairAt i, hpairAtMem i, rfl⟩)
    have hcover : ∀ i,
        rootPartImage (E.eliminationPattern e₀).root (request i.1) g ⊆
          blockAt i := by
      intro i
      change (g ∩ (E.eliminationPattern e₀).root).image
          (request i.1).map ⊆ (pairAt i).positive
      rw [← hrequestPos i]
      exact Finset.image_mono _ hpositive
    have hcount :=
      card_rootPartIndicesContaining_le_localDegree_mul_of_cover
        (E.eliminationPattern e₀) request pairs.card
          (eliminationPairSides pairs) multiplicity blockAt g hblockMem
          hcover (fun Q _hQ ↦ hpositiveFiber Q) I
    calc
      (rootPartIndicesContaining (E.eliminationPattern e₀) request
          pairs.card g I).card ≤
          Reserve.localDegree (eliminationPairSides pairs) I * multiplicity :=
        hcount
      _ ≤ (n ^ (r - 1 - I.card) * cap) * multiplicity :=
        Nat.mul_le_mul_right multiplicity hlower
      _ = n ^ (r - 1 - I.card) * (multiplicity * cap) := by ring
  · let blockAt : Fin pairs.card → Finset (Fin n) :=
      fun i ↦ (pairAt i).negative
    have hblockMem : ∀ i, blockAt i ∈ eliminationPairSides pairs := by
      intro i
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨pairAt i, hpairAtMem i, rfl⟩)
    have hcover : ∀ i,
        rootPartImage (E.eliminationPattern e₀).root (request i.1) g ⊆
          blockAt i := by
      intro i
      change (g ∩ (E.eliminationPattern e₀).root).image
          (request i.1).map ⊆ (pairAt i).negative
      rw [← hrequestNeg i]
      exact Finset.image_mono _ hnegative
    have hcount :=
      card_rootPartIndicesContaining_le_localDegree_mul_of_cover
        (E.eliminationPattern e₀) request pairs.card
          (eliminationPairSides pairs) multiplicity blockAt g hblockMem
          hcover (fun Q _hQ ↦ hnegativeFiber Q) I
    calc
      (rootPartIndicesContaining (E.eliminationPattern e₀) request
          pairs.card g I).card ≤
          Reserve.localDegree (eliminationPairSides pairs) I * multiplicity :=
        hcount
      _ ≤ (n ^ (r - 1 - I.card) * cap) * multiplicity :=
        Nat.mul_le_mul_right multiplicity hlower
      _ = n ^ (r - 1 - I.card) * (multiplicity * cap) := by ring

@[ext] theorem EliminationPair.ext
    {P P' : EliminationPair n k r}
    (hpositive : P.positive = P'.positive)
    (hnegative : P.negative = P'.negative) : P = P' := by
  cases P
  cases P'
  simp_all

/-- Only a fixed number of ordered elimination pairs can have the same
root union.  This makes the labelled request schedule bounded even though
different ordered pairs may share their union. -/
theorem card_eliminationPairs_with_root_le
    (pairs : Finset (EliminationPair n k r)) (Q : Finset (Fin n))
    (hQcard : Q.card = 2 * k - r) :
    (pairs.filter fun P ↦ P.root = Q).card ≤
      eliminationRootMultiplicity k r := by
  classical
  let target := Q.powerset ×ˢ Q.powerset
  let f : EliminationPair n k r →
      Finset (Fin n) × Finset (Fin n) := fun P ↦ (P.positive, P.negative)
  calc
    (pairs.filter fun P ↦ P.root = Q).card ≤ target.card := by
      apply Finset.card_le_card_of_injOn f
      · intro P hP
        have hroot := (Finset.mem_filter.mp hP).2
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_powerset.mpr
          rw [← hroot]
          exact Finset.subset_union_left
        · apply Finset.mem_powerset.mpr
          rw [← hroot]
          exact Finset.subset_union_right
      · intro P hP P' hP' hEq
        exact EliminationPair.ext (congrArg Prod.fst hEq)
          (congrArg Prod.snd hEq)
    _ = eliminationRootMultiplicity k r := by
      simp [target, eliminationRootMultiplicity, hQcard, pow_two]

/-- The pair-preserving finite equivalence gives a root request which maps
the canonical positive and special blocks to the prescribed pair. -/
theorem exists_eliminationRootRequest
    [Nonempty (Fin n)] (E : RelabeledFullExchange k r)
    (hr : 0 < r) (hrk : r < k) (e₀ : RootEdge k r)
    (P : EliminationPair n k r) :
    ∃ request : RootRequest E.v n (E.eliminationPattern e₀).root,
      requestImage (E.eliminationPattern e₀).root request = P.root ∧
      E.pattern.root.image request.map = P.positive ∧
      (E.special e₀).image request.map = P.negative := by
  classical
  let sourceRoot := (E.eliminationPattern e₀).root
  let targetRoot := P.root
  have hsourceCard : sourceRoot.card = 2 * k - r := by
    simpa [sourceRoot] using E.eliminationPattern_root_card e₀
  have htargetCard : targetRoot.card = 2 * k - r := by
    simpa [targetRoot] using P.root_card
  have hinterSource : (E.pattern.root ∩ E.special e₀).card = r := by
    rw [Finset.inter_comm, E.root_eq, E.special_inter_root e₀,
      card_mappedRootEdge, RootEdge.card]
  obtain ⟨σ, hσpos, hσneg⟩ := exists_equiv_subtype_respecting_pair
    (A := sourceRoot) (B := targetRoot)
    (S₁ := E.pattern.root) (S₂ := E.special e₀)
    (T₁ := P.positive) (T₂ := P.negative)
    (by rfl) (by rfl) (hsourceCard.trans htargetCard.symm)
    (E.root_card.trans P.positive_card.symm)
    (hinterSource.trans P.inter_card.symm)
  let fallback : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  let f : Fin E.v → Fin n := fun x ↦
    if hx : x ∈ sourceRoot then (σ ⟨x, hx⟩).1 else fallback
  have hinj : Set.InjOn f (↑sourceRoot : Set (Fin E.v)) := by
    intro x hx y hy hxy
    have hx' : x ∈ sourceRoot := hx
    have hy' : y ∈ sourceRoot := hy
    have hσ : σ ⟨x, hx⟩ = σ ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa [f, hx', hy'] using hxy
    exact congrArg Subtype.val (σ.injective hσ)
  let request : RootRequest E.v n sourceRoot :=
    { map := f
      injOn := hinj }
  have himageRoot : requestImage sourceRoot request = targetRoot := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hval : f x = (σ ⟨x, hx⟩).1 := by simp [f, hx]
      subst y
      change f x ∈ targetRoot
      rw [hval]
      exact (σ ⟨x, hx⟩).2
    · intro hy
      let yt : ↑targetRoot := ⟨y, hy⟩
      obtain ⟨xs, hxs⟩ := σ.surjective yt
      apply Finset.mem_image.mpr
      refine ⟨xs.1, xs.2, ?_⟩
      have hval : f xs.1 = (σ xs).1 := by simp [f, xs.2]
      change f xs.1 = y
      rw [hval]
      exact congrArg Subtype.val hxs
  have himagePos : E.pattern.root.image request.map = P.positive := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxSource : x ∈ sourceRoot := by
        exact Finset.mem_union_left _ hx
      have hval : f x = (σ ⟨x, hxSource⟩).1 := by simp [f, hxSource]
      subst y
      change f x ∈ P.positive
      rw [hval]
      exact (hσpos ⟨x, hxSource⟩).mp hx
    · intro hy
      have hyTarget : y ∈ targetRoot := Finset.mem_union_left _ hy
      let yt : ↑targetRoot := ⟨y, hyTarget⟩
      obtain ⟨xs, hxs⟩ := σ.surjective yt
      have hxPos : xs.1 ∈ E.pattern.root :=
        (hσpos xs).mpr (by simpa [yt, hxs] using hy)
      apply Finset.mem_image.mpr
      refine ⟨xs.1, hxPos, ?_⟩
      have hval : f xs.1 = (σ xs).1 := by simp [f, xs.2]
      change f xs.1 = y
      rw [hval]
      exact congrArg Subtype.val hxs
  have himageNeg : (E.special e₀).image request.map = P.negative := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxSource : x ∈ sourceRoot := Finset.mem_union_right _ hx
      have hval : f x = (σ ⟨x, hxSource⟩).1 := by simp [f, hxSource]
      subst y
      change f x ∈ P.negative
      rw [hval]
      exact (hσneg ⟨x, hxSource⟩).mp hx
    · intro hy
      have hyTarget : y ∈ targetRoot := Finset.mem_union_right _ hy
      let yt : ↑targetRoot := ⟨y, hyTarget⟩
      obtain ⟨xs, hxs⟩ := σ.surjective yt
      have hxNeg : xs.1 ∈ E.special e₀ :=
        (hσneg xs).mpr (by simpa [yt, hxs] using hy)
      apply Finset.mem_image.mpr
      refine ⟨xs.1, hxNeg, ?_⟩
      have hval : f xs.1 = (σ xs).1 := by simp [f, xs.2]
      change f xs.1 = y
      rw [hval]
      exact congrArg Subtype.val hxs
  exact ⟨request, by simpa [sourceRoot, targetRoot, request] using himageRoot,
    by simpa [request] using himagePos, by simpa [request] using himageNeg⟩

lemma mapEdge_eq_requestImage_of_extends_of_subset
    {root S : Finset (Fin v)} (hS : S ⊆ root)
    (request : RootRequest v n root) (φ : Fin v ↪ Fin n)
    (hext : ExtendsRequest root request φ) :
    mapEdge φ S = S.image request.map := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    apply Finset.mem_image.mpr
    exact ⟨x, hx, (hext x (hS hx)).symm.trans hxy⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    apply Finset.mem_map.mpr
    exact ⟨x, hx, (hext x (hS hx)).trans hxy⟩

/-- Any full embedding extending the pair request carries the two
distinguished cliques to the requested positive and negative blocks. -/
theorem extends_eliminationRootRequest_maps_pair
    (E : RelabeledFullExchange k r) (e₀ : RootEdge k r)
    (P : EliminationPair n k r)
    (request : RootRequest E.v n (E.eliminationPattern e₀).root)
    (hrequestPos : E.pattern.root.image request.map = P.positive)
    (hrequestNeg : (E.special e₀).image request.map = P.negative)
    (φ : Fin E.v ↪ Fin n)
    (hext : ExtendsRequest (E.eliminationPattern e₀).root request φ) :
    mapEdge φ E.pattern.root = P.positive ∧
      mappedSpecial E φ e₀ = P.negative := by
  constructor
  · exact (mapEdge_eq_requestImage_of_extends_of_subset
      Finset.subset_union_left request φ hext).trans hrequestPos
  · exact (mapEdge_eq_requestImage_of_extends_of_subset
      Finset.subset_union_right request φ hext).trans hrequestNeg

theorem mappedHost_sdiff_eliminationRoot_eq_freeEdges
    (E : RelabeledFullExchange k r) (e₀ : RootEdge k r)
    (φ : Fin E.v ↪ Fin n) :
    mappedHost E φ \
        (mapEdge φ (E.eliminationPattern e₀).root).powersetCard r =
      imageFreeEdges (E.eliminationPattern e₀) φ := by
  classical
  ext g
  constructor
  · intro hg
    have hgData := Finset.mem_sdiff.mp hg
    obtain ⟨e, he, heg⟩ := mem_mapFamily.mp hgData.1
    subst g
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    intro heroot
    apply hgData.2
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.map_subset_map.mpr heroot, ?_⟩
    simpa [mapEdge] using E.pattern.uniform e he
  · intro hg
    obtain ⟨e, he, heg⟩ := Finset.mem_image.mp hg
    subst g
    have heData := Finset.mem_filter.mp he
    apply Finset.mem_sdiff.mpr
    constructor
    · exact mem_mapFamily.mpr ⟨e, heData.1, rfl⟩
    · intro hrootEdge
      have hsubMap := (Finset.mem_powersetCard.mp hrootEdge).1
      exact heData.2 (Finset.map_subset_map.mp hsubMap)

structure BoundedEliminationPairEmbeddings
    (E : RelabeledFullExchange k r) (e₀ : RootEdge k r)
    (pairs : Finset (EliminationPair n k r))
    (forbidden : Finset (Finset (Fin n))) (C : ℕ) where
  embedding : (P : EliminationPair n k r) → P ∈ pairs → Fin E.v ↪ Fin n
  maps_positive : ∀ P hP,
    mapEdge (embedding P hP) E.pattern.root = P.positive
  maps_negative : ∀ P hP,
    mappedSpecial E (embedding P hP) e₀ = P.negative
  free_disjoint_forbidden : ∀ P hP,
    Disjoint
      (imageFreeEdges (E.eliminationPattern e₀) (embedding P hP)) forbidden
  free_pairwise : ∀ P hP P' hP', P ≠ P' →
    Disjoint
      (imageFreeEdges (E.eliminationPattern e₀) (embedding P hP))
      (imageFreeEdges (E.eliminationPattern e₀) (embedding P' hP'))
  freeUnion : Finset (Finset (Fin n))
  image_subset_freeUnion : ∀ P hP,
    imageFreeEdges (E.eliminationPattern e₀) (embedding P hP) ⊆ freeUnion
  free_uniform : ∀ g ∈ freeUnion, g.card = r
  freeUnion_disjoint_forbidden : Disjoint freeUnion forbidden
  free_degree_le : ∀ J : Finset (Fin n), J.card = r - 1 →
    Reserve.localDegree freeUnion J ≤
      (E.eliminationPattern e₀).freeEdges.card * C

/-- A preallocated elimination bank restricts to any selected subfamily
without changing its free host or quantitative bound. -/
def BoundedEliminationPairEmbeddings.restrict
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs pairs' : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hsub : pairs' ⊆ pairs) :
    BoundedEliminationPairEmbeddings E e₀ pairs' forbidden C where
  embedding P hP := S.embedding P (hsub hP)
  maps_positive P hP := S.maps_positive P (hsub hP)
  maps_negative P hP := S.maps_negative P (hsub hP)
  free_disjoint_forbidden P hP := S.free_disjoint_forbidden P (hsub hP)
  free_pairwise P hP P' hP' hne :=
    S.free_pairwise P (hsub hP) P' (hsub hP') hne
  freeUnion := S.freeUnion
  image_subset_freeUnion P hP := S.image_subset_freeUnion P (hsub hP)
  free_uniform := S.free_uniform
  freeUnion_disjoint_forbidden := S.freeUnion_disjoint_forbidden
  free_degree_le := S.free_degree_le

@[simp] theorem BoundedEliminationPairEmbeddings.restrict_embedding
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs pairs' : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hsub : pairs' ⊆ pairs) (P : EliminationPair n k r) (hP : P ∈ pairs') :
    (S.restrict hsub).embedding P hP = S.embedding P (hsub hP) := rfl

def eliminationPositiveRemainder
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  (mappedNegative E (S.embedding P hP)).erase P.negative

def eliminationNegativeRemainder
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  (mappedPositive E (S.embedding P hP)).erase P.positive

/-- Replacing the two distinguished blocks by the two remainder families
preserves their signed incidence difference exactly. -/
theorem eliminationRemainders_signed_pair
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount (eliminationPositiveRemainder S P hP) g : ℤ) -
        (incidenceCount (eliminationNegativeRemainder S P hP) g : ℤ) =
      (if g ⊆ P.positive then (1 : ℤ) else 0) -
        (if g ⊆ P.negative then (1 : ℤ) else 0) := by
  have hmain := mappedFullExchange_signed_root_sub_special E
    (S.embedding P hP) e₀ hg
  simpa [eliminationPositiveRemainder, eliminationNegativeRemainder,
    S.maps_positive P hP, S.maps_negative P hP] using hmain

theorem eliminationPositiveRemainder_decomp
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    IsUniformDecomposition
      (mappedHost E (S.embedding P hP) \ P.negative.powersetCard r)
      (eliminationPositiveRemainder S P hP) k r := by
  simpa [eliminationPositiveRemainder, S.maps_negative P hP] using
    mappedNegative_erase_special_decomp E (S.embedding P hP) e₀

theorem eliminationNegativeRemainder_decomp
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    IsUniformDecomposition
      (imageFreeEdges E.pattern (S.embedding P hP))
      (eliminationNegativeRemainder S P hP) k r := by
  simpa [eliminationNegativeRemainder, S.maps_positive P hP] using
    mappedPositive_erase_decomp E (S.embedding P hP)

theorem exists_eliminationFreeEdge_of_mem_positiveRemainder
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B : Finset (Fin n)} (hB : B ∈ eliminationPositiveRemainder S P hP) :
    ∃ g ∈ B.powersetCard r,
      g ∈ imageFreeEdges (E.eliminationPattern e₀) (S.embedding P hP) := by
  classical
  let φ := S.embedding P hP
  have hBdata : B ∈ mappedNegative E φ ∧ B ≠ P.negative := by
    have hm := Finset.mem_erase.mp hB
    exact ⟨by simpa [eliminationPositiveRemainder, φ] using hm.2,
      by simpa [eliminationPositiveRemainder, φ] using hm.1⟩
  have hBcard : B.card = k :=
    (mappedNegative_decomp E φ).1 B hBdata.1
  have hinterLt : (B ∩ P.negative).card < r := by
    by_contra hnot
    have hrle : r ≤ (B ∩ P.negative).card := Nat.le_of_not_gt hnot
    obtain ⟨g, hg⟩ := Finset.powersetCard_nonempty.mpr hrle
    have hgB : g ∈ B.powersetCard r := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.mem_powersetCard.mp hg).1.trans Finset.inter_subset_left,
        (Finset.mem_powersetCard.mp hg).2⟩
    have hgNeg : g ∈ P.negative.powersetCard r := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.mem_powersetCard.mp hg).1.trans Finset.inter_subset_right,
        (Finset.mem_powersetCard.mp hg).2⟩
    have hnegMem : P.negative ∈ mappedNegative E φ := by
      simpa [φ, S.maps_negative P hP] using
        mappedSpecial_mem_mappedNegative E φ e₀
    exact hBdata.2
      ((mappedNegative_decomp E φ).blocks_eq_of_common_edge
        hBdata.1 hnegMem hgB hgNeg)
  have hnotRoot : ¬B ⊆ P.root := by
    intro hsub
    have hdiffSub : B \ P.negative ⊆ P.positive \ P.negative := by
      intro x hx
      have hxUnion := hsub (Finset.mem_sdiff.mp hx).1
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_union.mp hxUnion).resolve_right
          (Finset.mem_sdiff.mp hx).2, (Finset.mem_sdiff.mp hx).2⟩
    have hdiffLe := Finset.card_le_card hdiffSub
    have hright : (P.positive \ P.negative).card = k - r := by
      rw [Finset.card_sdiff, P.positive_card, Finset.inter_comm,
        P.inter_card]
    have hleft : (B \ P.negative).card = k - (B ∩ P.negative).card := by
      rw [Finset.card_sdiff, hBcard, Finset.inter_comm]
    rw [hleft, hright] at hdiffLe
    omega
  obtain ⟨g, hgB, hgnot⟩ :=
    exists_powersetCard_not_subset hr (by omega : r ≤ B.card) hnotRoot
  have hgHost : g ∈ mappedHost E φ :=
    (mappedNegative_decomp E φ).2.1 B hBdata.1 hgB
  have hrootMap : mapEdge φ (E.eliminationPattern e₀).root = P.root := by
    simp only [RelabeledFullExchange.eliminationPattern_root, mapEdge,
      Finset.map_union]
    change mapEdge φ E.pattern.root ∪ mappedSpecial E φ e₀ = P.root
    rw [show mapEdge φ E.pattern.root = P.positive by
      simpa [φ] using S.maps_positive P hP]
    rw [show mappedSpecial E φ e₀ = P.negative by
      simpa [φ] using S.maps_negative P hP]
    rfl
  refine ⟨g, hgB, ?_⟩
  rw [← mappedHost_sdiff_eliminationRoot_eq_freeEdges E e₀ φ]
  apply Finset.mem_sdiff.mpr
  exact ⟨hgHost, fun hg ↦ hgnot (by
    rw [hrootMap] at hg
    exact (Finset.mem_powersetCard.mp hg).1)⟩

theorem exists_eliminationFreeEdge_of_mem_negativeRemainder
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B : Finset (Fin n)} (hB : B ∈ eliminationNegativeRemainder S P hP) :
    ∃ g ∈ B.powersetCard r,
      g ∈ imageFreeEdges (E.eliminationPattern e₀) (S.embedding P hP) := by
  classical
  let φ := S.embedding P hP
  have hBdata : B ∈ mappedPositive E φ ∧ B ≠ P.positive := by
    have hm := Finset.mem_erase.mp hB
    exact ⟨by simpa [eliminationNegativeRemainder, φ] using hm.2,
      by simpa [eliminationNegativeRemainder, φ] using hm.1⟩
  have hBcard : B.card = k :=
    (mappedPositive_decomp E φ).1 B hBdata.1
  have hinterLt : (B ∩ P.positive).card < r := by
    by_contra hnot
    have hrle : r ≤ (B ∩ P.positive).card := Nat.le_of_not_gt hnot
    obtain ⟨g, hg⟩ := Finset.powersetCard_nonempty.mpr hrle
    have hgB : g ∈ B.powersetCard r := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.mem_powersetCard.mp hg).1.trans Finset.inter_subset_left,
        (Finset.mem_powersetCard.mp hg).2⟩
    have hgPos : g ∈ P.positive.powersetCard r := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.mem_powersetCard.mp hg).1.trans Finset.inter_subset_right,
        (Finset.mem_powersetCard.mp hg).2⟩
    have hposMem : P.positive ∈ mappedPositive E φ := by
      simpa [φ, S.maps_positive P hP] using
        mappedRoot_mem_mappedPositive E φ
    exact hBdata.2
      ((mappedPositive_decomp E φ).blocks_eq_of_common_edge
        hBdata.1 hposMem hgB hgPos)
  have hnotRoot : ¬B ⊆ P.root := by
    intro hsub
    have hdiffSub : B \ P.positive ⊆ P.negative \ P.positive := by
      intro x hx
      have hxUnion := hsub (Finset.mem_sdiff.mp hx).1
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_union.mp hxUnion).resolve_left
          (Finset.mem_sdiff.mp hx).2, (Finset.mem_sdiff.mp hx).2⟩
    have hdiffLe := Finset.card_le_card hdiffSub
    have hright : (P.negative \ P.positive).card = k - r := by
      rw [Finset.card_sdiff, P.negative_card, P.inter_card]
    have hleft : (B \ P.positive).card = k - (B ∩ P.positive).card := by
      rw [Finset.card_sdiff, hBcard, Finset.inter_comm]
    rw [hleft, hright] at hdiffLe
    omega
  obtain ⟨g, hgB, hgnot⟩ :=
    exists_powersetCard_not_subset hr (by omega : r ≤ B.card) hnotRoot
  have hgHost : g ∈ mappedHost E φ :=
    (mappedPositive_decomp E φ).2.1 B hBdata.1 hgB
  have hrootMap : mapEdge φ (E.eliminationPattern e₀).root = P.root := by
    simp only [RelabeledFullExchange.eliminationPattern_root, mapEdge,
      Finset.map_union]
    change mapEdge φ E.pattern.root ∪ mappedSpecial E φ e₀ = P.root
    rw [show mapEdge φ E.pattern.root = P.positive by
      simpa [φ] using S.maps_positive P hP]
    rw [show mappedSpecial E φ e₀ = P.negative by
      simpa [φ] using S.maps_negative P hP]
    rfl
  refine ⟨g, hgB, ?_⟩
  rw [← mappedHost_sdiff_eliminationRoot_eq_freeEdges E e₀ φ]
  apply Finset.mem_sdiff.mpr
  exact ⟨hgHost, fun hg ↦ hgnot (by
    rw [hrootMap] at hg
    exact (Finset.mem_powersetCard.mp hg).1)⟩

def eliminationRemainderBlocks
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  eliminationPositiveRemainder S P hP ∪
    eliminationNegativeRemainder S P hP

theorem exists_eliminationFreeEdge_of_mem_remainderBlocks
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {B : Finset (Fin n)} (hB : B ∈ eliminationRemainderBlocks S P hP) :
    ∃ g ∈ B.powersetCard r,
      g ∈ imageFreeEdges (E.eliminationPattern e₀) (S.embedding P hP) := by
  rcases Finset.mem_union.mp hB with hB | hB
  · exact exists_eliminationFreeEdge_of_mem_positiveRemainder
      S hr hrk P hP hB
  · exact exists_eliminationFreeEdge_of_mem_negativeRemainder
      S hr hrk P hP hB

theorem BoundedEliminationPairEmbeddings.map_eliminationRoot
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    mapEdge (S.embedding P hP) (E.eliminationPattern e₀).root = P.root := by
  simp only [RelabeledFullExchange.eliminationPattern_root, mapEdge,
    Finset.map_union]
  change mapEdge (S.embedding P hP) E.pattern.root ∪
      mappedSpecial E (S.embedding P hP) e₀ = P.root
  rw [S.maps_positive P hP, S.maps_negative P hP]
  rfl

theorem mem_negativeEdges_or_eliminationFreeEdges
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hisolated : IsSpecialIsolated E e₀)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {g : Finset (Fin n)}
    (hg : g ∈ imageFreeEdges E.pattern (S.embedding P hP)) :
    g ∈ P.negative.powersetCard r ∨
      g ∈ imageFreeEdges (E.eliminationPattern e₀) (S.embedding P hP) := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
  have heData := Finset.mem_filter.mp he
  by_cases heUnion : e ⊆ E.pattern.root ∪ E.special e₀
  · have heSpecial : e ⊆ E.special e₀ :=
      (hisolated e heData.1 heUnion).resolve_left heData.2
    apply Or.inl
    apply Finset.mem_powersetCard.mpr
    constructor
    · rw [← S.maps_negative P hP]
      exact Finset.map_subset_map.mpr heSpecial
    · simpa [mapEdge] using E.pattern.uniform e heData.1
  · apply Or.inr
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨heData.1, heUnion⟩, rfl⟩

theorem mem_eliminationFreeEdges_of_mem_mappedHost_of_not_forbidden
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hisolated : IsSpecialIsolated E e₀)
    (hsideForbidden : eliminationPairSideBoundary pairs ⊆ forbidden)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {g : Finset (Fin n)} (hgcard : g.card = r)
    (hgHost : g ∈ mappedHost E (S.embedding P hP))
    (hgNotForbidden : g ∉ forbidden) :
    g ∈ imageFreeEdges (E.eliminationPattern e₀) (S.embedding P hP) := by
  rw [← mappedHost_sdiff_eliminationRoot_eq_freeEdges E e₀
    (S.embedding P hP)]
  apply Finset.mem_sdiff.mpr
  refine ⟨hgHost, ?_⟩
  intro hgRoot
  apply hgNotForbidden
  apply hsideForbidden
  obtain ⟨e, he, hmap⟩ := mem_mapFamily.mp hgHost
  have heRoot : e ⊆ (E.eliminationPattern e₀).root := by
    have hsub := (Finset.mem_powersetCard.mp hgRoot).1
    have hmapSubset : mapEdge (S.embedding P hP) e ⊆
        mapEdge (S.embedding P hP) (E.eliminationPattern e₀).root := by
      simpa [mapEdge, hmap] using hsub
    exact Finset.map_subset_map.mp hmapSubset
  have heSide : e ⊆ E.pattern.root ∨ e ⊆ E.special e₀ := by
    exact hisolated e he (by
      simpa [RelabeledFullExchange.eliminationPattern_root] using heRoot)
  apply Finset.mem_biUnion.mpr
  rcases heSide with hePos | heNeg
  · refine ⟨P.positive, Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨P, hP, rfl⟩), ?_⟩
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hgcard⟩
    rw [← S.maps_positive P hP, ← hmap]
    exact Finset.map_subset_map.mpr hePos
  · refine ⟨P.negative, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨P, hP, rfl⟩), ?_⟩
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hgcard⟩
    rw [← S.maps_negative P hP, ← hmap]
    exact Finset.map_subset_map.mpr heNeg

/-- Every edge in the host of a pair-rooted elimination embedding is either
prescribed by one of the two sides of the pair or is a free edge charged to
the embedding allocator. -/
theorem mem_eliminationPairSideBoundary_or_freeUnion_of_mem_mappedHost
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hisolated : IsSpecialIsolated E e₀)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {g : Finset (Fin n)} (hgcard : g.card = r)
    (hgHost : g ∈ mappedHost E (S.embedding P hP)) :
    g ∈ eliminationPairSideBoundary pairs ∨ g ∈ S.freeUnion := by
  obtain ⟨e, he, hmap⟩ := mem_mapFamily.mp hgHost
  by_cases heRoot : e ⊆ (E.eliminationPattern e₀).root
  · have heSide : e ⊆ E.pattern.root ∨ e ⊆ E.special e₀ :=
      hisolated e he (by
        simpa [RelabeledFullExchange.eliminationPattern_root] using heRoot)
    apply Or.inl
    apply Finset.mem_biUnion.mpr
    rcases heSide with hePos | heNeg
    · refine ⟨P.positive, Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨P, hP, rfl⟩), ?_⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hgcard⟩
      rw [← S.maps_positive P hP, ← hmap]
      exact Finset.map_subset_map.mpr hePos
    · refine ⟨P.negative, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨P, hP, rfl⟩), ?_⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hgcard⟩
      rw [← S.maps_negative P hP, ← hmap]
      exact Finset.map_subset_map.mpr heNeg
  · apply Or.inr
    apply S.image_subset_freeUnion P hP
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, heRoot⟩, hmap⟩

/-- Remainder block families of distinct pair-rooted exchanges are disjoint.
Every such block contains a free edge; separation of the rooted embeddings
then separates the blocks themselves. -/
theorem eliminationRemainderBlocks_pairwise_disjoint
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hsideForbidden : eliminationPairSideBoundary pairs ⊆ forbidden)
    {P P' : EliminationPair n k r} (hP : P ∈ pairs) (hP' : P' ∈ pairs)
    (hne : P ≠ P') :
    Disjoint (eliminationRemainderBlocks S P hP)
      (eliminationRemainderBlocks S P' hP') := by
  apply Finset.disjoint_left.mpr
  intro B hB hB'
  obtain ⟨g, hgB, hgFree⟩ :=
    exists_eliminationFreeEdge_of_mem_remainderBlocks S hr hrk P hP hB
  have hgcard : g.card = r := (Finset.mem_powersetCard.mp hgB).2
  have hgNotForbidden : g ∉ forbidden := fun hgf ↦
    Finset.disjoint_left.mp (S.free_disjoint_forbidden P hP) hgFree hgf
  have hgHost' : g ∈ mappedHost E (S.embedding P' hP') := by
    rcases Finset.mem_union.mp hB' with hpos | hneg
    · have hm := Finset.mem_erase.mp hpos
      exact (mappedNegative_decomp E (S.embedding P' hP')).2.1 B hm.2 hgB
    · have hm := Finset.mem_erase.mp hneg
      exact (mappedPositive_decomp E (S.embedding P' hP')).2.1 B hm.2 hgB
  have hgFree' := mem_eliminationFreeEdges_of_mem_mappedHost_of_not_forbidden
    S (RelabeledFullExchange.isSpecialIsolated E e₀) hsideForbidden
      P' hP' hgcard hgHost' hgNotForbidden
  exact Finset.disjoint_left.mp (S.free_pairwise P hP P' hP' hne)
    hgFree hgFree'

lemma incidenceCount_sdiff
    {small large : Finset (Finset (Fin n))} (hsub : small ⊆ large)
    (g : Finset (Fin n)) :
    incidenceCount (large \ small) g =
      incidenceCount large g - incidenceCount small g := by
  unfold incidenceCount
  have hf : small.filter (fun B ↦ g ⊆ B) ⊆
      large.filter (fun B ↦ g ⊆ B) :=
    Finset.filter_subset_filter _ hsub
  rw [← Finset.card_sdiff_of_subset hf]
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  aesop

def eliminationPositiveOnly
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  eliminationPositiveRemainder S P hP \
    eliminationNegativeRemainder S P hP

def eliminationNegativeOnly
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  eliminationNegativeRemainder S P hP \
    eliminationPositiveRemainder S P hP

def eliminationCommonRemainder
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  eliminationPositiveRemainder S P hP ∩
    eliminationNegativeRemainder S P hP

def eliminationNegativeOnlyHost
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Finset (Finset (Fin n)) :=
  imageFreeEdges E.pattern (S.embedding P hP) \
    (eliminationCommonRemainder S P hP).biUnion
      (fun B ↦ B.powersetCard r)

theorem eliminationNegativeOnly_decomp
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    IsUniformDecomposition (eliminationNegativeOnlyHost S P hP)
      (eliminationNegativeOnly S P hP) k r := by
  let common := eliminationCommonRemainder S P hP
  let neg := eliminationNegativeRemainder S P hP
  have hdec := (eliminationNegativeRemainder_decomp S P hP).sdiff_blocks
    (fun g hg ↦ imageFreeEdges_uniform E.pattern (S.embedding P hP) hg)
    (show common ⊆ neg by
      exact Finset.inter_subset_right)
  have hblocks : neg \ common = eliminationNegativeOnly S P hP := by
    ext B
    simp [neg, common, eliminationCommonRemainder, eliminationNegativeOnly]
  simpa [eliminationNegativeOnlyHost, common, neg, hblocks] using hdec

theorem eliminationPositiveOnly_disjoint_negativeOnly
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs) :
    Disjoint (eliminationPositiveOnly S P hP)
      (eliminationNegativeOnly S P hP) := by
  exact Finset.disjoint_left.mpr fun B hBpos hBneg ↦
    (Finset.mem_sdiff.mp hBpos).2 (Finset.mem_sdiff.mp hBneg).1

theorem eliminationOnly_signed_pair
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (P : EliminationPair n k r) (hP : P ∈ pairs)
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount (eliminationPositiveOnly S P hP) g : ℤ) -
        (incidenceCount (eliminationNegativeOnly S P hP) g : ℤ) =
      (if g ⊆ P.positive then (1 : ℤ) else 0) -
        (if g ⊆ P.negative then (1 : ℤ) else 0) := by
  let pos := eliminationPositiveRemainder S P hP
  let neg := eliminationNegativeRemainder S P hP
  let common := pos ∩ neg
  have hcommonPos : common ⊆ pos := Finset.inter_subset_left
  have hcommonNeg : common ⊆ neg := Finset.inter_subset_right
  have hposEq : pos \ common = eliminationPositiveOnly S P hP := by
    ext B
    simp [pos, neg, common, eliminationPositiveOnly]
  have hnegEq : neg \ common = eliminationNegativeOnly S P hP := by
    ext B
    simp [pos, neg, common, eliminationNegativeOnly]
  have hposCount := incidenceCount_sdiff hcommonPos g
  have hnegCount := incidenceCount_sdiff hcommonNeg g
  rw [hposEq] at hposCount
  rw [hnegEq] at hnegCount
  have hcommonPosCount : incidenceCount common g ≤ incidenceCount pos g :=
    Finset.card_le_card (Finset.filter_subset_filter _ hcommonPos)
  have hcommonNegCount : incidenceCount common g ≤ incidenceCount neg g :=
    Finset.card_le_card (Finset.filter_subset_filter _ hcommonNeg)
  rw [hposCount, hnegCount]
  push_cast [Nat.cast_sub hcommonPosCount, Nat.cast_sub hcommonNegCount]
  simpa [pos, neg] using eliminationRemainders_signed_pair S P hP hg

def allEliminationPositiveOnly
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C) :
    Finset (Finset (Fin n)) :=
  pairs.attach.biUnion fun P ↦ eliminationPositiveOnly S P.1 P.2

def allEliminationNegativeOnly
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C) :
    Finset (Finset (Fin n)) :=
  pairs.attach.biUnion fun P ↦ eliminationNegativeOnly S P.1 P.2

def allEliminationNegativeOnlyHost
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C) :
    Finset (Finset (Fin n)) :=
  pairs.attach.biUnion fun P ↦ eliminationNegativeOnlyHost S P.1 P.2

theorem allEliminationPositiveOnly_edge_mem_sideBoundary_union_freeUnion
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    {B g : Finset (Fin n)} (hB : B ∈ allEliminationPositiveOnly S)
    (hgB : g ∈ B.powersetCard r) :
    g ∈ eliminationPairSideBoundary pairs ∪ S.freeUnion := by
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  have hgHostSdiff := (eliminationPositiveRemainder_decomp S P.1 P.2).2.1
    B (Finset.mem_sdiff.mp hBP).1 hgB
  rcases mem_eliminationPairSideBoundary_or_freeUnion_of_mem_mappedHost S
      (RelabeledFullExchange.isSpecialIsolated E e₀) P.1 P.2
      (Finset.mem_powersetCard.mp hgB).2
      (Finset.mem_sdiff.mp hgHostSdiff).1 with hgSide | hgFree
  · exact Finset.mem_union_left _ hgSide
  · exact Finset.mem_union_right _ hgFree

/-- Every edge used by the coefficient-independent positive remainder bank
is either prescribed by a pair root or charged by the allocator. -/
theorem allEliminationPositiveOnly_boundary_subset_sideBoundary_union_freeUnion
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C) :
    (allEliminationPositiveOnly S).biUnion (fun B ↦ B.powersetCard r) ⊆
      eliminationPairSideBoundary pairs ∪ S.freeUnion := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  exact allEliminationPositiveOnly_edge_mem_sideBoundary_union_freeUnion
    S hB hgB

theorem allEliminationNegativeOnly_edge_mem_sideBoundary_union_freeUnion
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    {B g : Finset (Fin n)} (hB : B ∈ allEliminationNegativeOnly S)
    (hgB : g ∈ B.powersetCard r) :
    g ∈ eliminationPairSideBoundary pairs ∪ S.freeUnion := by
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  have hgHost := (eliminationNegativeOnly_decomp S P.1 P.2).2.1 B hBP hgB
  rcases mem_negativeEdges_or_eliminationFreeEdges S
      (RelabeledFullExchange.isSpecialIsolated E e₀) P.1 P.2
        (Finset.mem_sdiff.mp hgHost).1 with
    hgRoot | hgFree
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨P.1.negative, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨P.1, P.2, rfl⟩), hgRoot⟩
  · exact Finset.mem_union_right _
      (S.image_subset_freeUnion P.1 P.2 hgFree)

/-- Every edge used by the coefficient-independent negative remainder bank
is either prescribed by a pair root or charged by the allocator. -/
theorem allEliminationNegativeOnly_boundary_subset_sideBoundary_union_freeUnion
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C) :
    (allEliminationNegativeOnly S).biUnion (fun B ↦ B.powersetCard r) ⊆
      eliminationPairSideBoundary pairs ∪ S.freeUnion := by
  intro g hg
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  exact allEliminationNegativeOnly_edge_mem_sideBoundary_union_freeUnion
    S hB hgB

theorem allEliminationPositiveOnly_uniform
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    {B : Finset (Fin n)} (hB : B ∈ allEliminationPositiveOnly S) :
    B.card = k := by
  obtain ⟨P, _hP, hBP⟩ := Finset.mem_biUnion.mp hB
  have hBneg : B ∈ mappedNegative E (S.embedding P.1 P.2) :=
    (Finset.mem_erase.mp (Finset.mem_sdiff.mp hBP).1).2
  exact (mappedNegative_decomp E (S.embedding P.1 P.2)).1 B hBneg

/-- Every positive-only output block is distinct from every block whose
complete `r`-boundary was placed in the forbidden set. -/
theorem allEliminationPositiveOnly_disjoint_forbiddenFamily
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (family : Finset (Finset (Fin n)))
    (hfamily : family.biUnion (fun B ↦ B.powersetCard r) ⊆ forbidden) :
    Disjoint (allEliminationPositiveOnly S) family := by
  apply Finset.disjoint_left.mpr
  intro B hBout hBfamily
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hBout
  have hBrem : B ∈ eliminationRemainderBlocks S P.1 P.2 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mp hBP).1
  obtain ⟨g, hgB, hgFree⟩ :=
    exists_eliminationFreeEdge_of_mem_remainderBlocks
      S hr hrk P.1 P.2 hBrem
  have hgForbidden : g ∈ forbidden := by
    apply hfamily
    exact Finset.mem_biUnion.mpr ⟨B, hBfamily, hgB⟩
  exact Finset.disjoint_left.mp (S.free_disjoint_forbidden P.1 P.2)
    hgFree hgForbidden

/-- Every negative-only output block is distinct from every block whose
complete `r`-boundary was placed in the forbidden set. -/
theorem allEliminationNegativeOnly_disjoint_forbiddenFamily
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (family : Finset (Finset (Fin n)))
    (hfamily : family.biUnion (fun B ↦ B.powersetCard r) ⊆ forbidden) :
    Disjoint (allEliminationNegativeOnly S) family := by
  apply Finset.disjoint_left.mpr
  intro B hBout hBfamily
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hBout
  have hBrem : B ∈ eliminationRemainderBlocks S P.1 P.2 :=
    Finset.mem_union_right _ (Finset.mem_sdiff.mp hBP).1
  obtain ⟨g, hgB, hgFree⟩ :=
    exists_eliminationFreeEdge_of_mem_remainderBlocks
      S hr hrk P.1 P.2 hBrem
  have hgForbidden : g ∈ forbidden := by
    apply hfamily
    exact Finset.mem_biUnion.mpr ⟨B, hBfamily, hgB⟩
  exact Finset.disjoint_left.mp (S.free_disjoint_forbidden P.1 P.2)
    hgFree hgForbidden

/-- Every family selected from a preallocated elimination bank uses only
blocks already present in the corresponding fixed positive bank. -/
theorem allEliminationPositiveOnly_restrict_subset
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs pairs' : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hsub : pairs' ⊆ pairs) :
    allEliminationPositiveOnly (S.restrict hsub) ⊆
      allEliminationPositiveOnly S := by
  intro B hB
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨P.1, hsub P.2⟩, Finset.mem_attach _ _, ?_⟩
  simpa [eliminationPositiveOnly, eliminationPositiveRemainder,
    eliminationNegativeRemainder] using hBP

/-- The analogous monotonicity for the negative output of a restricted
elimination bank. -/
theorem allEliminationNegativeOnly_restrict_subset
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs pairs' : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hsub : pairs' ⊆ pairs) :
    allEliminationNegativeOnly (S.restrict hsub) ⊆
      allEliminationNegativeOnly S := by
  intro B hB
  obtain ⟨P, _hPattach, hBP⟩ := Finset.mem_biUnion.mp hB
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨P.1, hsub P.2⟩, Finset.mem_attach _ _, ?_⟩
  simpa [eliminationPositiveOnly, eliminationPositiveRemainder,
    eliminationNegativeOnly, eliminationNegativeRemainder] using hBP

/-- Every negative host selected from the universal bank is contained in
the universal negative host.  This is the edge-level counterpart of the
preceding block inclusion and is used by the fixed-bank flattening step. -/
theorem allEliminationNegativeOnlyHost_restrict_subset
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs pairs' : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hsub : pairs' ⊆ pairs) :
    allEliminationNegativeOnlyHost (S.restrict hsub) ⊆
      allEliminationNegativeOnlyHost S := by
  intro g hg
  obtain ⟨P, _hPattach, hgP⟩ := Finset.mem_biUnion.mp hg
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨P.1, hsub P.2⟩, Finset.mem_attach _ _, ?_⟩
  simpa [eliminationNegativeOnlyHost, eliminationCommonRemainder,
    eliminationPositiveRemainder, eliminationNegativeRemainder] using hgP

/-- A weaker and source-accurate separation condition for the first
elimination round.  Prescribed negative cliques may share their distinguished
edge, provided every common edge is also inside both prescribed positive
cliques.  Such an edge has already been deleted from each root-erased
negative host. -/
theorem eliminationNegativeOnlyHost_pairwise_disjoint_of_common_in_positive
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hisolated : IsSpecialIsolated E e₀)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hcommon : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      ∀ g ∈ P.negative.powersetCard r,
        g ∈ P'.negative.powersetCard r →
          g ⊆ P.positive ∧ g ⊆ P'.positive)
    {P P' : EliminationPair n k r} (hP : P ∈ pairs) (hP' : P' ∈ pairs)
    (hne : P ≠ P') :
    Disjoint (eliminationNegativeOnlyHost S P hP)
      (eliminationNegativeOnlyHost S P' hP') := by
  apply Finset.disjoint_left.mpr
  intro g hgP hgP'
  have hgBaseP : g ∈ imageFreeEdges E.pattern (S.embedding P hP) :=
    (Finset.mem_sdiff.mp hgP).1
  have hgBaseP' : g ∈ imageFreeEdges E.pattern (S.embedding P' hP') :=
    (Finset.mem_sdiff.mp hgP').1
  have hnegForbidden (Q : EliminationPair n k r) (hQ : Q ∈ pairs)
      {a : Finset (Fin n)} (ha : a ∈ Q.negative.powersetCard r) :
      a ∈ forbidden := by
    apply hrootForbidden
    exact Finset.mem_biUnion.mpr ⟨Q.negative, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨Q, hQ, rfl⟩), ha⟩
  have hnotPositiveRoot (Q : EliminationPair n k r) (hQ : Q ∈ pairs)
      {a : Finset (Fin n)}
      (ha : a ∈ imageFreeEdges E.pattern (S.embedding Q hQ)) :
      a ∉ Q.positive.powersetCard r := by
    have hfree := ha
    rw [← mappedHost_sdiff_root_eq_freeEdges E (S.embedding Q hQ)] at hfree
    intro haPos
    apply (Finset.mem_sdiff.mp hfree).2
    simpa [S.maps_positive Q hQ] using haPos
  rcases mem_negativeEdges_or_eliminationFreeEdges S hisolated P hP hgBaseP
      with hgNeg | hgFree <;>
    rcases mem_negativeEdges_or_eliminationFreeEdges S hisolated P' hP' hgBaseP'
      with hgNeg' | hgFree'
  · have hgPos := (hcommon P hP P' hP' hne g hgNeg hgNeg').1
    exact hnotPositiveRoot P hP hgBaseP
      (Finset.mem_powersetCard.mpr
        ⟨hgPos, (Finset.mem_powersetCard.mp hgNeg).2⟩)
  · exact Finset.disjoint_left.mp (S.free_disjoint_forbidden P' hP')
      hgFree' (hnegForbidden P hP hgNeg)
  · exact Finset.disjoint_left.mp (S.free_disjoint_forbidden P hP)
      hgFree (hnegForbidden P' hP' hgNeg')
  · exact Finset.disjoint_left.mp (S.free_pairwise P hP P' hP' hne)
      hgFree hgFree'

theorem eliminationNegativeOnlyHost_pairwise_disjoint
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hisolated : IsSpecialIsolated E e₀)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hnegativePairwise : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      Disjoint (P.negative.powersetCard r) (P'.negative.powersetCard r))
    {P P' : EliminationPair n k r} (hP : P ∈ pairs) (hP' : P' ∈ pairs)
    (hne : P ≠ P') :
    Disjoint (eliminationNegativeOnlyHost S P hP)
      (eliminationNegativeOnlyHost S P' hP') := by
  apply Finset.disjoint_left.mpr
  intro g hgP hgP'
  have hgBaseP : g ∈ imageFreeEdges E.pattern (S.embedding P hP) :=
    (Finset.mem_sdiff.mp hgP).1
  have hgBaseP' : g ∈ imageFreeEdges E.pattern (S.embedding P' hP') :=
    (Finset.mem_sdiff.mp hgP').1
  have hnegForbidden (Q : EliminationPair n k r) (hQ : Q ∈ pairs)
      {a : Finset (Fin n)} (ha : a ∈ Q.negative.powersetCard r) :
      a ∈ forbidden := by
    apply hrootForbidden
    exact Finset.mem_biUnion.mpr ⟨Q.negative, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨Q, hQ, rfl⟩), ha⟩
  rcases mem_negativeEdges_or_eliminationFreeEdges S hisolated P hP hgBaseP
      with hgNeg | hgFree <;>
    rcases mem_negativeEdges_or_eliminationFreeEdges S hisolated P' hP' hgBaseP'
      with hgNeg' | hgFree'
  · exact Finset.disjoint_left.mp
      (hnegativePairwise P hP P' hP' hne) hgNeg hgNeg'
  · exact Finset.disjoint_left.mp (S.free_disjoint_forbidden P' hP')
      hgFree' (hnegForbidden P hP hgNeg)
  · exact Finset.disjoint_left.mp (S.free_disjoint_forbidden P hP)
      hgFree (hnegForbidden P' hP' hgNeg')
  · exact Finset.disjoint_left.mp (S.free_pairwise P hP P' hP' hne)
      hgFree hgFree'

theorem allEliminationNegativeOnly_decomp
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hrk : r ≤ k)
    (hhostPairwise : ∀ P ∈ pairs.attach, ∀ P' ∈ pairs.attach, P ≠ P' →
      Disjoint (eliminationNegativeOnlyHost S P.1 P.2)
        (eliminationNegativeOnlyHost S P'.1 P'.2)) :
    IsUniformDecomposition (allEliminationNegativeOnlyHost S)
      (allEliminationNegativeOnly S) k r := by
  classical
  let host : ↥pairs → Finset (Finset (Fin n)) := fun P ↦
    eliminationNegativeOnlyHost S P.1 P.2
  let blocks : ↥pairs → Finset (Finset (Fin n)) := fun P ↦
    eliminationNegativeOnly S P.1 P.2
  have hdec : ∀ P ∈ pairs.attach,
      IsUniformDecomposition (host P) (blocks P) k r := by
    intro P hP
    exact eliminationNegativeOnly_decomp S P.1 P.2
  have huniform : ∀ P ∈ pairs.attach, ∀ g ∈ host P, g.card = r := by
    intro P hP g hg
    exact imageFreeEdges_uniform E.pattern (S.embedding P.1 P.2)
      (Finset.mem_sdiff.mp hg).1
  have hpair : ∀ P ∈ pairs.attach, ∀ P' ∈ pairs.attach, P ≠ P' →
      Disjoint (host P) (host P') := hhostPairwise
  simpa [allEliminationNegativeOnlyHost, allEliminationNegativeOnly,
    host, blocks] using
      IsUniformDecomposition.biUnion pairs.attach host blocks
        hdec huniform hpair hrk

theorem allEliminationNegativeOnly_decomp_of_specialIsolated
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hrk : r ≤ k) (hisolated : IsSpecialIsolated E e₀)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hnegativePairwise : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      Disjoint (P.negative.powersetCard r) (P'.negative.powersetCard r)) :
    IsUniformDecomposition (allEliminationNegativeOnlyHost S)
      (allEliminationNegativeOnly S) k r := by
  apply allEliminationNegativeOnly_decomp S hrk
  intro P hP P' hP' hne
  exact eliminationNegativeOnlyHost_pairwise_disjoint S hisolated
    hrootForbidden hnegativePairwise P.2 P'.2
      (fun h ↦ hne (Subtype.ext h))

/-- The constructed full exchange supplies the isolation premise, so the
aggregate negative remainder is unconditionally a decomposition once the
prescribed negative cliques are edge-disjoint. -/
theorem allEliminationNegativeOnly_decomp_checked
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hrk : r ≤ k)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hnegativePairwise : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      Disjoint (P.negative.powersetCard r) (P'.negative.powersetCard r)) :
    IsUniformDecomposition (allEliminationNegativeOnlyHost S)
      (allEliminationNegativeOnly S) k r :=
  allEliminationNegativeOnly_decomp_of_specialIsolated S hrk
    (Erdos722.ExchangeEliminationEmbedding.RelabeledFullExchange.isSpecialIsolated
      E e₀) hrootForbidden hnegativePairwise

/-- Aggregate negative decomposition under the weaker common-edge condition
used by the first near-pair elimination round. -/
theorem allEliminationNegativeOnly_decomp_of_common_in_positive
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hrk : r ≤ k)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hcommon : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      ∀ g ∈ P.negative.powersetCard r,
        g ∈ P'.negative.powersetCard r →
          g ⊆ P.positive ∧ g ⊆ P'.positive) :
    IsUniformDecomposition (allEliminationNegativeOnlyHost S)
      (allEliminationNegativeOnly S) k r := by
  apply allEliminationNegativeOnly_decomp S hrk
  intro P hP P' hP' hne
  exact eliminationNegativeOnlyHost_pairwise_disjoint_of_common_in_positive
    S
    (Erdos722.ExchangeEliminationEmbedding.RelabeledFullExchange.isSpecialIsolated
      E e₀)
    hrootForbidden hcommon P.2 P'.2 (fun h ↦ hne (Subtype.ext h))

theorem allEliminationPositiveOnly_disjoint_allEliminationNegativeOnly
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden) :
    Disjoint (allEliminationPositiveOnly S)
      (allEliminationNegativeOnly S) := by
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  obtain ⟨P, hPattach, hBP⟩ := Finset.mem_biUnion.mp hBpos
  obtain ⟨P', hP'attach, hBP'⟩ := Finset.mem_biUnion.mp hBneg
  by_cases hPP' : P.1 = P'.1
  · have hsub : P = P' := Subtype.ext hPP'
    subst P'
    exact Finset.disjoint_left.mp
      (eliminationPositiveOnly_disjoint_negativeOnly S P.1 P.2)
      hBP (by simpa using hBP')
  · have hdis := eliminationRemainderBlocks_pairwise_disjoint
      S hr hrk hrootForbidden P.2 P'.2 hPP'
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_union_left _ (Finset.mem_sdiff.mp hBP).1)
      (Finset.mem_union_right _ (Finset.mem_sdiff.mp hBP').1)

theorem allEliminationOnly_signed_pairs
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount (allEliminationPositiveOnly S) g : ℤ) -
        (incidenceCount (allEliminationNegativeOnly S) g : ℤ) =
      ∑ P ∈ pairs.attach,
        ((if g ⊆ P.1.positive then (1 : ℤ) else 0) -
          (if g ⊆ P.1.negative then (1 : ℤ) else 0)) := by
  let pos : ↥pairs → Finset (Finset (Fin n)) := fun P ↦
    eliminationPositiveOnly S P.1 P.2
  let neg : ↥pairs → Finset (Finset (Fin n)) := fun P ↦
    eliminationNegativeOnly S P.1 P.2
  have hposPair : (↑pairs.attach : Set ↥pairs).PairwiseDisjoint pos := by
    intro P hP P' hP' hne
    apply Disjoint.mono (Finset.sdiff_subset) (Finset.sdiff_subset)
    apply Disjoint.mono Finset.subset_union_left Finset.subset_union_left
    apply eliminationRemainderBlocks_pairwise_disjoint
      S hr hrk hrootForbidden P.2 P'.2
    intro hEq
    exact hne (Subtype.ext hEq)
  have hnegPair : (↑pairs.attach : Set ↥pairs).PairwiseDisjoint neg := by
    intro P hP P' hP' hne
    apply Disjoint.mono (Finset.sdiff_subset) (Finset.sdiff_subset)
    apply Disjoint.mono Finset.subset_union_right Finset.subset_union_right
    apply eliminationRemainderBlocks_pairwise_disjoint
      S hr hrk hrootForbidden P.2 P'.2
    intro hEq
    exact hne (Subtype.ext hEq)
  have hposFilter : (↑pairs.attach : Set ↥pairs).PairwiseDisjoint fun P ↦
      (pos P).filter fun B ↦ g ⊆ B := by
    intro P hP P' hP' hne
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hposPair hP hP' hne)
  have hnegFilter : (↑pairs.attach : Set ↥pairs).PairwiseDisjoint fun P ↦
      (neg P).filter fun B ↦ g ⊆ B := by
    intro P hP P' hP' hne
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hnegPair hP hP' hne)
  rw [incidenceCount, allEliminationPositiveOnly, Finset.filter_biUnion,
    Finset.card_biUnion hposFilter, incidenceCount,
    allEliminationNegativeOnly, Finset.filter_biUnion,
    Finset.card_biUnion hnegFilter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  simpa [pos, neg, incidenceCount] using eliminationOnly_signed_pair S P.1 P.2 hg

/-- A complete simultaneous cancellation round: the positive and negative
remainders are block-disjoint, the negative remainder is a genuine
decomposition, and their signed boundary is exactly the sum of the
prescribed positive-minus-negative clique pairs. -/
theorem allEliminationOnly_round
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hnegativePairwise : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      Disjoint (P.negative.powersetCard r) (P'.negative.powersetCard r)) :
    Disjoint (allEliminationPositiveOnly S)
        (allEliminationNegativeOnly S) ∧
      IsUniformDecomposition (allEliminationNegativeOnlyHost S)
        (allEliminationNegativeOnly S) k r ∧
      ∀ g : Finset (Fin n), g.card = r →
        (incidenceCount (allEliminationPositiveOnly S) g : ℤ) -
            (incidenceCount (allEliminationNegativeOnly S) g : ℤ) =
          ∑ P ∈ pairs.attach,
            ((if g ⊆ P.1.positive then (1 : ℤ) else 0) -
              (if g ⊆ P.1.negative then (1 : ℤ) else 0)) := by
  refine ⟨allEliminationPositiveOnly_disjoint_allEliminationNegativeOnly
      S hr hrk hrootForbidden,
    allEliminationNegativeOnly_decomp_checked S hrk.le hrootForbidden
      hnegativePairwise, ?_⟩
  intro g hg
  exact allEliminationOnly_signed_pairs S hr hrk hrootForbidden hg

/-- The complete first elimination round when distinct negative roots may
share only edges which are already contained in both corresponding positive
roots. -/
theorem allEliminationOnly_round_of_common_in_positive
    {E : RelabeledFullExchange k r} {e₀ : RootEdge k r}
    {pairs : Finset (EliminationPair n k r)}
    {forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedEliminationPairEmbeddings E e₀ pairs forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : eliminationPairSideBoundary pairs ⊆
      forbidden)
    (hcommon : ∀ P ∈ pairs, ∀ P' ∈ pairs, P ≠ P' →
      ∀ g ∈ P.negative.powersetCard r,
        g ∈ P'.negative.powersetCard r →
          g ⊆ P.positive ∧ g ⊆ P'.positive) :
    Disjoint (allEliminationPositiveOnly S)
        (allEliminationNegativeOnly S) ∧
      IsUniformDecomposition (allEliminationNegativeOnlyHost S)
        (allEliminationNegativeOnly S) k r ∧
      ∀ g : Finset (Fin n), g.card = r →
        (incidenceCount (allEliminationPositiveOnly S) g : ℤ) -
            (incidenceCount (allEliminationNegativeOnly S) g : ℤ) =
          ∑ P ∈ pairs.attach,
            ((if g ⊆ P.1.positive then (1 : ℤ) else 0) -
              (if g ⊆ P.1.negative then (1 : ℤ) else 0)) := by
  refine ⟨allEliminationPositiveOnly_disjoint_allEliminationNegativeOnly
      S hr hrk hrootForbidden,
    allEliminationNegativeOnly_decomp_of_common_in_positive S hrk.le
      hrootForbidden hcommon, ?_⟩
  intro g hg
  exact allEliminationOnly_signed_pairs S hr hrk hrootForbidden hg

/-- All prescribed ordered pairs can eventually be embedded at once.  The
source-faithful hypotheses bound the positive and negative side schedules
separately; strong trace isolation charges every free pattern edge to one
of those schedules. -/
theorem eventually_exists_boundedEliminationPairEmbeddings_twoScale
    {dInput dPath : ℕ}
    (E : RelabeledFullExchange k r) (hr : 0 < r) (hrk : r < k)
    (e₀ : RootEdge k r) (htrace : E.SpecialTraceIsolated e₀)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath) (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (pairs : Finset (EliminationPair n k r))
        (forbidden : Finset (Finset (Fin n))),
      (∀ Q : Finset (Fin n),
        (pairs.filter fun pair ↦ pair.positive = Q).card ≤ M) →
      (∀ Q : Finset (Fin n),
        (pairs.filter fun pair ↦ pair.negative = Q).card ≤ M) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree (eliminationPairSides pairs) J) ^ dInput ≤
          n ^ (dInput - 1)) →
      (∀ g ∈ forbidden, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ dInput ≤
          n ^ (dInput - 1)) →
      Nonempty (BoundedEliminationPairEmbeddings E e₀ pairs forbidden
        (scaledDecoderPathCap M E.v r dPath n)) := by
  let P := E.eliminationPattern e₀
  have hroot : P.root.card < E.v := by
    simpa [P] using E.eliminationPattern_root_card_lt_v hr hrk e₀
  have hrootLarge : r ≤ P.root.card := by
    rw [show P.root.card = 2 * k - r by
      simpa [P] using E.eliminationPattern_root_card e₀]
    omega
  have hrequested :=
    eventually_exists_boundedRequestedFamilyEmbeddings_of_twoScale_rootPartBound
      P hr hroot hrootLarge hdInput hdPath hgap M hM
  filter_upwards [hrequested, eventually_ge_atTop (1 : ℕ)] with
      n hrequested hn
  intro pairs forbidden hpairsPositiveFiber hpairsNegativeFiber
    hpairsDegree hforbiddenUniform hforbiddenDegree
  by_cases hpairs : pairs = ∅
  · subst pairs
    refine ⟨{
      embedding := fun P hP ↦ False.elim (by simpa using hP)
      maps_positive := ?_
      maps_negative := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := ∅
      image_subset_freeUnion := ?_
      free_uniform := ?_
      freeUnion_disjoint_forbidden := ?_
      free_degree_le := ?_ }⟩
    · intro P hP
      simp at hP
    · intro P hP
      simp at hP
    · intro P hP
      simp at hP
    · intro P hP
      simp at hP
    · intro P hP
      simp at hP
    · intro g hg
      simp at hg
    · simp
    · intro J hJ
      simp [Reserve.localDegree]
  · let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨P₀, hP₀⟩ := Finset.nonempty_iff_ne_empty.mpr hpairs
    let pairAtFin (i : Fin pairs.card) : ↥pairs := pairs.equivFin.symm i
    let pairAt (i : ℕ) : EliminationPair n k r :=
      (pairAtFin ⟨i % pairs.card,
        Nat.mod_lt _ (Finset.card_pos.mpr ⟨P₀, hP₀⟩)⟩).1
    have hpairAtMem (i : ℕ) : pairAt i ∈ pairs :=
      (pairAtFin ⟨i % pairs.card,
        Nat.mod_lt _ (Finset.card_pos.mpr ⟨P₀, hP₀⟩)⟩).2
    have hpairAtFin (i : Fin pairs.card) :
        pairAt i.1 = (pairs.equivFin.symm i).1 := by
      have himod : i.1 % pairs.card = i.1 := Nat.mod_eq_of_lt i.2
      simp [pairAt, pairAtFin, himod]
    have hrequestExists (i : ℕ) :
        ∃ request : RootRequest E.v n P.root,
          requestImage P.root request = (pairAt i).root ∧
          E.pattern.root.image request.map = (pairAt i).positive ∧
          (E.special e₀).image request.map = (pairAt i).negative := by
      simpa [P] using exists_eliminationRootRequest E hr hrk e₀ (pairAt i)
    let request : ℕ → RootRequest E.v n P.root := fun i ↦
      Classical.choose (hrequestExists i)
    have hrequest (i : ℕ) :
        requestImage P.root (request i) = (pairAt i).root ∧
          E.pattern.root.image (request i).map = (pairAt i).positive ∧
          (E.special e₀).image (request i).map = (pairAt i).negative :=
      Classical.choose_spec (hrequestExists i)
    have hpositiveFiber (Q : Finset (Fin n)) :
        ((Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
          (pairAt i.1).positive = Q).card ≤ M := by
      let left := (Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
        (pairAt i.1).positive = Q
      let right := pairs.filter fun pair ↦ pair.positive = Q
      have hcard : left.card ≤ right.card := by
        apply Finset.card_le_card_of_injOn (fun i ↦ pairAt i.1)
        · intro i hi
          exact Finset.mem_filter.mpr
            ⟨hpairAtMem i.1, (Finset.mem_filter.mp hi).2⟩
        · intro i hi j hj hij
          have heq : pairs.equivFin.symm i = pairs.equivFin.symm j := by
            apply Subtype.ext
            simpa [hpairAtFin] using hij
          exact pairs.equivFin.symm.injective heq
      exact hcard.trans (by
        simpa [left, right] using hpairsPositiveFiber Q)
    have hnegativeFiber (Q : Finset (Fin n)) :
        ((Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
          (pairAt i.1).negative = Q).card ≤ M := by
      let left := (Finset.univ : Finset (Fin pairs.card)).filter fun i ↦
        (pairAt i.1).negative = Q
      let right := pairs.filter fun pair ↦ pair.negative = Q
      have hcard : left.card ≤ right.card := by
        apply Finset.card_le_card_of_injOn (fun i ↦ pairAt i.1)
        · intro i hi
          exact Finset.mem_filter.mpr
            ⟨hpairAtMem i.1, (Finset.mem_filter.mp hi).2⟩
        · intro i hi j hj hij
          have heq : pairs.equivFin.symm i = pairs.equivFin.symm j := by
            apply Subtype.ext
            simpa [hpairAtFin] using hij
          exact pairs.equivFin.symm.injective heq
      exact hcard.trans (by
        simpa [left, right] using hpairsNegativeFiber Q)
    have hsideMax : ∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (eliminationPairSides pairs) J ≤
          decoderInputCap dInput n := by
      intro J hJ
      exact le_decoderInputCap_of_pow_le dInput n _ hdInput
        (hpairsDegree J hJ)
    have hcount : HasRootPartCountBound P request pairs.card
        (M * decoderInputCap dInput n) := by
      simpa [P] using hasRootPartCountBound_elimination_requests
        E e₀ htrace pairs request (fun i ↦ pairAt i.1)
          (fun i ↦ hpairAtMem i.1)
          (fun i ↦ (hrequest i.1).2.1)
          (fun i ↦ (hrequest i.1).2.2)
          M (decoderInputCap dInput n) hpositiveFiber hnegativeFiber hrk
            hsideMax
    obtain ⟨S⟩ := hrequested request forbidden pairs.card hcount
      hforbiddenUniform hforbiddenDegree
    let index (pair : EliminationPair n k r) (hpair : pair ∈ pairs) :
        Fin pairs.card := pairs.equivFin ⟨pair, hpair⟩
    have hpairIndex (pair : EliminationPair n k r) (hpair : pair ∈ pairs) :
        pairAt (index pair hpair).1 = pair := by
      rw [hpairAtFin]
      simp [index]
    let embedding (pair : EliminationPair n k r) (hpair : pair ∈ pairs) :=
      S.embedding (index pair hpair)
    have hmaps (pair : EliminationPair n k r) (hpair : pair ∈ pairs) :
        mapEdge (embedding pair hpair) E.pattern.root = pair.positive ∧
          mappedSpecial E (embedding pair hpair) e₀ = pair.negative := by
      have hspec := hrequest (index pair hpair).1
      have hmain := extends_eliminationRootRequest_maps_pair E e₀ pair
        (request (index pair hpair).1)
        (by simpa [hpairIndex pair hpair] using hspec.2.1)
        (by simpa [hpairIndex pair hpair] using hspec.2.2)
        (embedding pair hpair)
        (by simpa [P, embedding] using
          S.extends_request (index pair hpair))
      exact hmain
    refine ⟨{
      embedding := embedding
      maps_positive := fun pair hpair ↦ (hmaps pair hpair).1
      maps_negative := fun pair hpair ↦ (hmaps pair hpair).2
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := S.freeUnion
      image_subset_freeUnion := ?_
      free_uniform := S.free_uniform
      freeUnion_disjoint_forbidden := S.freeUnion_disjoint_forbidden
      free_degree_le := S.free_degree_le }⟩
    · intro pair hpair
      exact S.free_disjoint_forbidden (index pair hpair)
    · intro pair hpair pair' hpair' hne
      apply S.free_pairwise (index pair hpair) (index pair' hpair')
      intro hindex
      apply hne
      have hsub : (⟨pair, hpair⟩ : ↥pairs) = ⟨pair', hpair'⟩ :=
        pairs.equivFin.injective hindex
      exact congrArg Subtype.val hsub
    · intro pair hpair
      exact S.image_subset_freeUnion (index pair hpair)

/-- Equal-denominator compatibility wrapper for existing applications. -/
theorem eventually_exists_boundedEliminationPairEmbeddings
    (E : RelabeledFullExchange k r) (hr : 0 < r) (hrk : r < k)
    (e₀ : RootEdge k r) (htrace : E.SpecialTraceIsolated e₀)
    (hd : 0 < d) (M : ℕ) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (pairs : Finset (EliminationPair n k r))
        (forbidden : Finset (Finset (Fin n))),
      (∀ Q : Finset (Fin n),
        (pairs.filter fun pair ↦ pair.positive = Q).card ≤ M) →
      (∀ Q : Finset (Fin n),
        (pairs.filter fun pair ↦ pair.negative = Q).card ≤ M) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree (eliminationPairSides pairs) J) ^ d ≤
          n ^ (d - 1)) →
      (∀ g ∈ forbidden, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedEliminationPairEmbeddings E e₀ pairs forbidden
        (scaledDecoderPathCap M E.v r d n)) := by
  simpa using
    (eventually_exists_boundedEliminationPairEmbeddings_twoScale
      E hr hrk e₀ htrace hd hd (by omega) M hM)

end

end Erdos722.ExchangeEliminationEmbedding

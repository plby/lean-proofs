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
import ErdosProblems.Erdos722.RandomGreedy
import ErdosProblems.Erdos722.Reserve
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Rooted hypergraph embeddings for random-greedy extension

This file supplies the finite objects used in Lemma 5.5 of the short proof:
a fixed rooted pattern, root requests, images of its non-root edges, and the
history-dependent legal embedding set.  The final theorem reduces successful
simultaneous placement to explicit finite numerator/denominator counts.
-/

namespace Erdos722.RootedEmbedding

open Finset
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.AdaptiveChernoff
open Erdos722.RandomGreedy

noncomputable section

/-- A finite `r`-uniform pattern with a distinguished root vertex set. -/
structure RootedPattern (v r : ℕ) where
  edges : Finset (Finset (Fin v))
  root : Finset (Fin v)
  uniform : ∀ e ∈ edges, e.card = r

/-- Pattern edges not contained entirely inside the root. -/
def RootedPattern.freeEdges (P : RootedPattern v r) :
    Finset (Finset (Fin v)) :=
  P.edges.filter fun e ↦ ¬e ⊆ P.root

/-- A prescribed injection of the root vertices into the ground set. -/
structure RootRequest (v n : ℕ) (root : Finset (Fin v)) where
  map : Fin v → Fin n
  injOn : Set.InjOn map (↑root : Set (Fin v))

/-- A full embedding respects the prescribed map on all root vertices. -/
def ExtendsRequest (root : Finset (Fin v))
    (request : RootRequest v n root) (φ : Fin v ↪ Fin n) : Prop :=
  ∀ x ∈ root, φ x = request.map x

/-- A root injection whose image lies in a `v`-set extends to a full
embedding onto that set.  This finite extension lemma is used to turn each
unlabelled reserve candidate into a distinct labelled rooted candidate. -/
theorem exists_embedding_extending_request_with_range
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (Q : Finset (Fin n)) (hQcard : Q.card = v)
    (himage : root.image request.map ⊆ Q) :
    ∃ φ : Fin v ↪ Fin n,
      ExtendsRequest root request φ ∧
        (Finset.univ : Finset (Fin v)).map φ = Q := by
  classical
  have hcard : Fintype.card (Fin v) = Q.card := by simp [hQcard]
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hcard himage
    request.injOn
  let φ : Fin v ↪ Fin n :=
    g.toEmbedding.trans (Function.Embedding.subtype fun x : Fin n ↦ x ∈ Q)
  refine ⟨φ, ?_, ?_⟩
  · intro x hx
    simpa [φ] using (hg x hx)
  · ext y
    constructor
    · intro hy
      obtain ⟨x, _hx, hxy⟩ := Finset.mem_map.mp hy
      rw [← hxy]
      exact (g x).property
    · intro hy
      obtain ⟨x, hx⟩ := g.surjective ⟨y, hy⟩
      apply Finset.mem_map.mpr
      refine ⟨x, Finset.mem_univ x, ?_⟩
      exact congrArg Subtype.val hx

/-- Image of one pattern edge. -/
def mapEdge (φ : Fin v ↪ Fin n) (e : Finset (Fin v)) : Finset (Fin n) :=
  e.map φ

@[simp] theorem card_mapEdge (φ : Fin v ↪ Fin n) (e : Finset (Fin v)) :
    (mapEdge φ e).card = e.card := by
  simp [mapEdge]

/-- Images of all non-root edges of the pattern. -/
def imageFreeEdges (P : RootedPattern v r) (φ : Fin v ↪ Fin n) :
    Finset (Finset (Fin n)) :=
  P.freeEdges.image (mapEdge φ)

theorem imageFreeEdges_uniform (P : RootedPattern v r)
    (φ : Fin v ↪ Fin n) {g : Finset (Fin n)}
    (hg : g ∈ imageFreeEdges P φ) : g.card = r := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
  exact (card_mapEdge φ e).trans (P.uniform e (Finset.mem_filter.mp he).1)

/-- All target edges already spent by a history of embeddings. -/
def usedEdges (P : RootedPattern v r) (history : List (Fin v ↪ Fin n)) :
    Finset (Finset (Fin n)) :=
  history.toFinset.biUnion (imageFreeEdges P)

theorem usedEdges_uniform (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) {g : Finset (Fin n)}
    (hg : g ∈ usedEdges P history) : g.card = r := by
  obtain ⟨φ, _hφ, hgφ⟩ := Finset.mem_biUnion.mp hg
  exact imageFreeEdges_uniform P φ hgφ

theorem card_imageFreeEdges_le (P : RootedPattern v r)
    (φ : Fin v ↪ Fin n) :
    (imageFreeEdges P φ).card ≤ P.freeEdges.card := by
  exact Finset.card_image_le

/-- The history union has the elementary global size bound used before the
sharper induced-load estimate is applied. -/
theorem card_usedEdges_le (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) :
    (usedEdges P history).card ≤ history.length * P.freeEdges.card := by
  calc
    (usedEdges P history).card ≤
        ∑ φ ∈ history.toFinset, (imageFreeEdges P φ).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _φ ∈ history.toFinset, P.freeEdges.card := by
      apply Finset.sum_le_sum
      intro φ hφ
      exact card_imageFreeEdges_le P φ
    _ = history.toFinset.card * P.freeEdges.card := by simp
    _ ≤ history.length * P.freeEdges.card := by
      exact Nat.mul_le_mul_right _ (List.toFinset_card_le history)

/-- The legal full embeddings for the next scheduled root request. -/
def legalEmbeddings (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) : Finset (Fin v ↪ Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin v ↪ Fin n)).filter fun φ ↦
    ExtendsRequest P.root (request history.length) φ ∧
      Disjoint (imageFreeEdges P φ) forbidden ∧
      Disjoint (imageFreeEdges P φ) (usedEdges P history)

/-- The free vertices of an edge, whose images are the induced loads tracked
in the rooted extension lemma. -/
def freePart (P : RootedPattern v r) (e : Finset (Fin v)) :
    Finset (Fin v) :=
  e \ P.root

/-- A load target is a pattern edge together with a proposed image of its
free part.  Irrelevant pairs simply have zero hit probability. -/
abbrev LoadTarget (v n : ℕ) :=
  Finset (Fin v) × Finset (Fin n)

/-- Indicator that an embedding maps the specified free part to the target
set. -/
def loadHit (P : RootedPattern v r) (target : LoadTarget v n)
    (_history : List (Fin v ↪ Fin n)) (φ : Fin v ↪ Fin n) : Bool :=
  decide (target.1 ∈ P.freeEdges ∧
    mapEdge φ (freePart P target.1) = target.2)

lemma loadHit_eq_true_iff (P : RootedPattern v r)
    (target : LoadTarget v n) (history : List (Fin v ↪ Fin n))
    (φ : Fin v ↪ Fin n) :
    loadHit P target history φ = true ↔
      target.1 ∈ P.freeEdges ∧
        mapEdge φ (freePart P target.1) = target.2 := by
  simp [loadHit]

/-! ## Partial induced loads -/

/-- A partial load target records an edge of the pattern, a selected family
of its free vertices, and their proposed image.  Tracking every nonempty
selection (rather than only the whole free part) is what controls the final
codimension-one degree of the used host. -/
structure PartialLoadTarget (v n : ℕ) where
  edge : Finset (Fin v)
  vertices : Finset (Fin v)
  image : Finset (Fin n)
  deriving DecidableEq, Fintype

/-- The finite subtype of targets which can actually be hit. -/
def IsRelevantPartialLoad (P : RootedPattern v r)
    (target : PartialLoadTarget v n) : Prop :=
  target.edge ∈ P.freeEdges ∧ target.vertices.Nonempty ∧
    target.vertices ⊆ freePart P target.edge ∧
    target.image.card = target.vertices.card

abbrev RelevantPartialLoadTarget (P : RootedPattern v r) (n : ℕ) :=
  {target : PartialLoadTarget v n // IsRelevantPartialLoad P target}

noncomputable instance relevantPartialLoadTargetFintype
    (P : RootedPattern v r) (n : ℕ) :
    Fintype (RelevantPartialLoadTarget P n) :=
  Fintype.ofFinite _

/-! The source-faithful induced-load counter couples a pattern edge to the
entire ground `(r-1)`-face.  This coupling is essential when summing the
conditional probabilities over a bounded root-request schedule. -/

structure FaceLoadTarget (v n : ℕ) where
  edge : Finset (Fin v)
  face : Finset (Fin n)
  deriving DecidableEq, Fintype

def IsRelevantFaceLoad (P : RootedPattern v r)
    (target : FaceLoadTarget v n) : Prop :=
  target.edge ∈ P.freeEdges ∧ target.face.card = r - 1

abbrev RelevantFaceLoadTarget (P : RootedPattern v r) (n : ℕ) :=
  {target : FaceLoadTarget v n // IsRelevantFaceLoad P target}

noncomputable instance relevantFaceLoadTargetFintype
    (P : RootedPattern v r) (n : ℕ) :
    Fintype (RelevantFaceLoadTarget P n) :=
  Fintype.ofFinite _

def faceLoadHit (P : RootedPattern v r)
    (target : RelevantFaceLoadTarget P n)
    (_history : List (Fin v ↪ Fin n)) (φ : Fin v ↪ Fin n) : Bool :=
  decide (target.1.face ⊆ mapEdge φ target.1.edge)

lemma faceLoadHit_eq_true_iff
    (P : RootedPattern v r) (target : RelevantFaceLoadTarget P n)
    (history : List (Fin v ↪ Fin n)) (φ : Fin v ↪ Fin n) :
    faceLoadHit P target history φ = true ↔
      target.1.face ⊆ mapEdge φ target.1.edge := by
  simp [faceLoadHit]

/-- Indicator for one relevant partial induced load. -/
def partialLoadHit (P : RootedPattern v r)
    (target : RelevantPartialLoadTarget P n)
    (_history : List (Fin v ↪ Fin n)) (φ : Fin v ↪ Fin n) : Bool :=
  decide (mapEdge φ target.1.vertices = target.1.image)

lemma partialLoadHit_eq_true_iff
    (P : RootedPattern v r) (target : RelevantPartialLoadTarget P n)
    (history : List (Fin v ↪ Fin n)) (φ : Fin v ↪ Fin n) :
    partialLoadHit P target history φ = true ↔
      mapEdge φ target.1.vertices = target.1.image := by
  simp [partialLoadHit]

/-- Free pattern vertices whose images lie in one prescribed ground face. -/
def selectedFreeVertices (P : RootedPattern v r)
    (φ : Fin v ↪ Fin n) (e : Finset (Fin v))
    (J : Finset (Fin n)) : Finset (Fin v) :=
  (freePart P e).filter fun x ↦ φ x ∈ J

lemma selectedFreeVertices_subset (P : RootedPattern v r)
    (φ : Fin v ↪ Fin n) (e : Finset (Fin v))
    (J : Finset (Fin n)) :
    selectedFreeVertices P φ e J ⊆ freePart P e := by
  exact Finset.filter_subset _ _

lemma mapEdge_selectedFreeVertices_subset
    (P : RootedPattern v r) (φ : Fin v ↪ Fin n)
    (e : Finset (Fin v)) (J : Finset (Fin n)) :
    mapEdge φ (selectedFreeVertices P φ e J) ⊆ J := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
  exact (Finset.mem_filter.mp hx).2

/-- Relevant partial targets whose proposed image is supported on `J`. -/
noncomputable def partialTargetsInside (P : RootedPattern v r)
    (n : ℕ) (J : Finset (Fin n)) :
    Finset (RelevantPartialLoadTarget P n) := by
  classical
  exact Finset.univ.filter fun target ↦ target.1.image ⊆ J

lemma mem_partialTargetsInside
    {target : RelevantPartialLoadTarget P n} :
    target ∈ partialTargetsInside P n J ↔ target.1.image ⊆ J := by
  classical
  simp [partialTargetsInside]

/-- History/edge witnesses whose used image contains `J`. -/
def usedWitnessPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset ((Fin v ↪ Fin n) × Finset (Fin v)) :=
  (history.toFinset ×ˢ P.freeEdges).filter fun z ↦
    J ⊆ mapEdge z.1 z.2

/-- Witnesses for which at least one free vertex maps into `J`. -/
def nonemptyFreeWitnessPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset ((Fin v ↪ Fin n) × Finset (Fin v)) :=
  (usedWitnessPairs P history J).filter fun z ↦
    (selectedFreeVertices P z.1 z.2 J).Nonempty

/-- The complementary exceptional witnesses, whose free vertices all map
to the unique point of the used edge outside `J`. -/
def emptyFreeWitnessPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset ((Fin v ↪ Fin n) × Finset (Fin v)) :=
  (usedWitnessPairs P history J).filter fun z ↦
    ¬(selectedFreeVertices P z.1 z.2 J).Nonempty

/-- Pairs represented by one fixed partial-load target. -/
def partialTargetPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n))
    (target : RelevantPartialLoadTarget P n) :
    Finset ((Fin v ↪ Fin n) × Finset (Fin v)) :=
  (history.toFinset.filter fun φ ↦
    mapEdge φ target.1.vertices = target.1.image).image fun φ ↦
      (φ, target.1.edge)

/-- Every used edge through `J` has at least one history/edge witness. -/
theorem localDegree_usedEdges_le_witnessPairs
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    Reserve.localDegree (usedEdges P history) J ≤
      (usedWitnessPairs P history J).card := by
  let f : ((Fin v ↪ Fin n) × Finset (Fin v)) → Finset (Fin n) :=
    fun z ↦ mapEdge z.1 z.2
  have hsubset : ((usedEdges P history).filter fun g ↦ J ⊆ g) ⊆
      (usedWitnessPairs P history J).image f := by
    intro g hg
    have hm := Finset.mem_filter.mp hg
    obtain ⟨φ, hφ, hgφ⟩ := Finset.mem_biUnion.mp hm.1
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hgφ
    apply Finset.mem_image.mpr
    refine ⟨(φ, e), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hφ, he⟩, ?_⟩, ?_⟩
    · simpa [heq] using hm.2
    · simpa [f] using heq
  calc
    Reserve.localDegree (usedEdges P history) J ≤
        ((usedWitnessPairs P history J).image f).card :=
      Finset.card_le_card hsubset
    _ ≤ (usedWitnessPairs P history J).card := Finset.card_image_le

theorem card_usedWitnessPairs_le_empty_add_nonempty
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    (usedWitnessPairs P history J).card ≤
      (emptyFreeWitnessPairs P history J).card +
        (nonemptyFreeWitnessPairs P history J).card := by
  have hsubset : usedWitnessPairs P history J ⊆
      emptyFreeWitnessPairs P history J ∪
        nonemptyFreeWitnessPairs P history J := by
    intro z hz
    by_cases hnonempty :
        (selectedFreeVertices P z.1 z.2 J).Nonempty
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, hnonempty⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hz, hnonempty⟩)
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

/-- Membership in the legal set records all three requirements. -/
lemma mem_legalEmbeddings {φ : Fin v ↪ Fin n} :
    φ ∈ legalEmbeddings P request forbidden history ↔
      ExtendsRequest P.root (request history.length) φ ∧
        Disjoint (imageFreeEdges P φ) forbidden ∧
        Disjoint (imageFreeEdges P φ) (usedEdges P history) := by
  classical
  simp [legalEmbeddings]

lemma pathHits_partialLoadHit_eq_countP
    (P : RootedPattern v r) (target : RelevantPartialLoadTarget P n) :
    ∀ (initial history : List (Fin v ↪ Fin n)),
      pathHits (partialLoadHit P target) initial history =
        history.countP fun φ ↦
          mapEdge φ target.1.vertices = target.1.image := by
  intro initial history
  induction history generalizing initial with
  | nil => simp [pathHits]
  | cons φ rest ih =>
      by_cases h : mapEdge φ target.1.vertices = target.1.image
      · simp [pathHits, partialLoadHit, hitBit, h, ih, Nat.add_comm]
      · simp [pathHits, partialLoadHit, hitBit, h, ih]

lemma card_history_filter_partialLoad_le_pathHits
    (P : RootedPattern v r) (target : RelevantPartialLoadTarget P n)
    (initial history : List (Fin v ↪ Fin n)) :
    (history.toFinset.filter fun φ ↦
      mapEdge φ target.1.vertices = target.1.image).card ≤
        pathHits (partialLoadHit P target) initial history := by
  let q : (Fin v ↪ Fin n) → Bool := fun φ ↦
    decide (mapEdge φ target.1.vertices = target.1.image)
  have hfilter :
      (history.toFinset.filter fun φ ↦
        mapEdge φ target.1.vertices = target.1.image) =
        (history.filter q).toFinset := by
    ext φ
    simp [q]
  rw [hfilter, pathHits_partialLoadHit_eq_countP]
  calc
    (history.filter q).toFinset.card ≤ (history.filter q).length :=
      List.toFinset_card_le _
    _ = history.countP q := history.countP_eq_length_filter.symm
    _ = history.countP (fun φ ↦
        decide (mapEdge φ target.1.vertices = target.1.image)) := rfl

/-- A used pattern edge through `J` with a nonempty selected free part is
recorded by the corresponding relevant partial-load target supported on
`J`. -/
theorem nonemptyFreeWitnessPairs_subset_partialTargetPairs
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    nonemptyFreeWitnessPairs P history J ⊆
      (partialTargetsInside P n J).biUnion
        (partialTargetPairs P history) := by
  intro z hz
  rcases z with ⟨φ, e⟩
  have hzNonempty := Finset.mem_filter.mp hz
  have hzUsed := Finset.mem_filter.mp hzNonempty.1
  have hzProduct := Finset.mem_product.mp hzUsed.1
  let S : Finset (Fin v) := selectedFreeVertices P φ e J
  have hSNonempty : S.Nonempty := by
    simpa [S] using hzNonempty.2
  let raw : PartialLoadTarget v n :=
    { edge := e
      vertices := S
      image := mapEdge φ S }
  have hraw : IsRelevantPartialLoad P raw := by
    refine ⟨hzProduct.2, hSNonempty, ?_, ?_⟩
    · simpa [raw, S] using selectedFreeVertices_subset P φ e J
    · simp [raw]
  let target : RelevantPartialLoadTarget P n := ⟨raw, hraw⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨target, ?_, ?_⟩
  · apply mem_partialTargetsInside.mpr
    simpa [target, raw, S] using
      mapEdge_selectedFreeVertices_subset P φ e J
  · apply Finset.mem_image.mpr
    refine ⟨φ, Finset.mem_filter.mpr ⟨hzProduct.1, ?_⟩, ?_⟩
    · simp [target, raw]
    · simp [target, raw]

/-- The total number of nonexceptional witnesses through `J` is bounded by
the sum of the partial-load counters supported on `J`. -/
theorem card_nonemptyFreeWitnessPairs_le_sum_pathHits
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    (nonemptyFreeWitnessPairs P history J).card ≤
      ∑ target ∈ partialTargetsInside P n J,
        pathHits (partialLoadHit P target) initial history := by
  calc
    (nonemptyFreeWitnessPairs P history J).card ≤
        ((partialTargetsInside P n J).biUnion
          (partialTargetPairs P history)).card :=
      Finset.card_le_card
        (nonemptyFreeWitnessPairs_subset_partialTargetPairs P history J)
    _ ≤ ∑ target ∈ partialTargetsInside P n J,
        (partialTargetPairs P history target).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ target ∈ partialTargetsInside P n J,
        pathHits (partialLoadHit P target) initial history := by
      apply Finset.sum_le_sum
      intro target htarget
      exact Finset.card_image_le.trans
        (card_history_filter_partialLoad_le_pathHits
          P target initial history)

/-- If every relevant partial load stays below its cap, their contribution
to the used-edge degree through `J` is bounded by the sum of those caps. -/
theorem card_nonemptyFreeWitnessPairs_le_sum_caps
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n))
    (cap : RelevantPartialLoadTarget P n → ℕ)
    (hcaps : ∀ target,
      pathHits (partialLoadHit P target) initial history < cap target) :
    (nonemptyFreeWitnessPairs P history J).card ≤
      ∑ target ∈ partialTargetsInside P n J, cap target := by
  calc
    (nonemptyFreeWitnessPairs P history J).card ≤
        ∑ target ∈ partialTargetsInside P n J,
          pathHits (partialLoadHit P target) initial history :=
      card_nonemptyFreeWitnessPairs_le_sum_pathHits P initial history J
    _ ≤ ∑ target ∈ partialTargetsInside P n J, cap target := by
      apply Finset.sum_le_sum
      intro target htarget
      exact Nat.le_of_lt (hcaps target)

/-- Exact bridge from stopping-time partial-load caps to the local degree of
the used host.  The only remaining term consists of witnesses whose free
part avoids `J`; in the rooted application it is bounded by the request
schedule. -/
theorem localDegree_usedEdges_le_empty_add_sum_caps
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n))
    (cap : RelevantPartialLoadTarget P n → ℕ)
    (hcaps : ∀ target,
      pathHits (partialLoadHit P target) initial history < cap target) :
    Reserve.localDegree (usedEdges P history) J ≤
      (emptyFreeWitnessPairs P history J).card +
        ∑ target ∈ partialTargetsInside P n J, cap target := by
  calc
    Reserve.localDegree (usedEdges P history) J ≤
        (usedWitnessPairs P history J).card :=
      localDegree_usedEdges_le_witnessPairs P history J
    _ ≤ (emptyFreeWitnessPairs P history J).card +
        (nonemptyFreeWitnessPairs P history J).card :=
      card_usedWitnessPairs_le_empty_add_nonempty P history J
    _ ≤ (emptyFreeWitnessPairs P history J).card +
        ∑ target ∈ partialTargetsInside P n J, cap target :=
      Nat.add_le_add_left
        (card_nonemptyFreeWitnessPairs_le_sum_caps
          P initial history J cap hcaps) _

/-- For a fixed face `J`, relevant targets supported on `J` are encoded by
a free pattern edge, a subset of the pattern vertices, and a subset of
`J`.  In particular their number is independent of the ambient ground-set
size apart from `J.card`. -/
theorem card_partialTargetsInside_le
    (P : RootedPattern v r) (J : Finset (Fin n)) :
    (partialTargetsInside P n J).card ≤
      P.freeEdges.card * 2 ^ v * 2 ^ J.card := by
  let codes :
      Finset ((Finset (Fin v) × Finset (Fin v)) × Finset (Fin n)) :=
    (P.freeEdges ×ˢ (Finset.univ : Finset (Fin v)).powerset) ×ˢ J.powerset
  let code : RelevantPartialLoadTarget P n →
      ((Finset (Fin v) × Finset (Fin v)) × Finset (Fin n)) :=
    fun target ↦
      ((target.1.edge, target.1.vertices), target.1.image)
  have hmaps : ∀ target ∈ partialTargetsInside P n J,
      code target ∈ codes := by
    intro target htarget
    have hrel := target.2
    exact Finset.mem_product.mpr ⟨
      Finset.mem_product.mpr ⟨hrel.1, Finset.mem_powerset.mpr
        (Finset.subset_univ target.1.vertices)⟩,
      Finset.mem_powerset.mpr (mem_partialTargetsInside.mp htarget)⟩
  have hinj : Set.InjOn code
      (↑(partialTargetsInside P n J) :
        Set (RelevantPartialLoadTarget P n)) := by
    intro a ha b hb hab
    rcases a with ⟨⟨ae, av, ai⟩, harelevant⟩
    rcases b with ⟨⟨be, bv, bi⟩, hbrelevant⟩
    simp only [code] at hab
    cases hab
    rfl
  have hcard := Finset.card_le_card_of_injOn code hmaps hinj
  simpa [codes, Nat.mul_assoc] using hcard

/-- Uniform partial-load caps give a closed codimension-one degree bound;
the number of counters through `J` is the fixed-pattern constant from the
preceding theorem. -/
theorem localDegree_usedEdges_le_empty_add_uniformCap
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) (C : ℕ)
    (hcaps : ∀ target : RelevantPartialLoadTarget P n,
      pathHits (partialLoadHit P target) initial history < C) :
    Reserve.localDegree (usedEdges P history) J ≤
      (emptyFreeWitnessPairs P history J).card +
        (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C := by
  calc
    Reserve.localDegree (usedEdges P history) J ≤
        (emptyFreeWitnessPairs P history J).card +
          ∑ _target ∈ partialTargetsInside P n J, C :=
      localDegree_usedEdges_le_empty_add_sum_caps P initial history J
        (fun _ ↦ C) hcaps
    _ = (emptyFreeWitnessPairs P history J).card +
        (partialTargetsInside P n J).card * C := by simp
    _ ≤ (emptyFreeWitnessPairs P history J).card +
        (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right C (card_partialTargetsInside_le P J)) _

/-! ## Multiplicity-sensitive indexed witnesses -/

/-- History positions and pattern edges whose image contains `J`.  Indexing
by list positions, rather than by `history.toFinset`, is the right interface
for a scheduled list of root requests. -/
def indexedUsedWitnessPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset (Fin history.length × Finset (Fin v)) :=
  ((Finset.univ : Finset (Fin history.length)) ×ˢ P.freeEdges).filter
    fun z ↦ J ⊆ mapEdge (history.get z.1) z.2

def indexedNonemptyFreeWitnessPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset (Fin history.length × Finset (Fin v)) :=
  (indexedUsedWitnessPairs P history J).filter fun z ↦
    (selectedFreeVertices P (history.get z.1) z.2 J).Nonempty

def indexedEmptyFreeWitnessPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset (Fin history.length × Finset (Fin v)) :=
  (indexedUsedWitnessPairs P history J).filter fun z ↦
    ¬(selectedFreeVertices P (history.get z.1) z.2 J).Nonempty

/-- The indexed witnesses still cover every edge of the used host, even if
the history list contains repetitions. -/
theorem localDegree_usedEdges_le_indexedWitnessPairs
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    Reserve.localDegree (usedEdges P history) J ≤
      (indexedUsedWitnessPairs P history J).card := by
  let f : (Fin history.length × Finset (Fin v)) → Finset (Fin n) :=
    fun z ↦ mapEdge (history.get z.1) z.2
  have hsubset : ((usedEdges P history).filter fun g ↦ J ⊆ g) ⊆
      (indexedUsedWitnessPairs P history J).image f := by
    intro g hg
    have hm := Finset.mem_filter.mp hg
    obtain ⟨φ, hφ, hgφ⟩ := Finset.mem_biUnion.mp hm.1
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hgφ
    have hφList : φ ∈ history := by simpa using hφ
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hφList
    apply Finset.mem_image.mpr
    refine ⟨(i, e), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i, he⟩, ?_⟩, ?_⟩
    · rw [hi, heq]
      exact hm.2
    · change mapEdge (history.get i) e = g
      rw [hi]
      exact heq
  calc
    Reserve.localDegree (usedEdges P history) J ≤
        ((indexedUsedWitnessPairs P history J).image f).card :=
      Finset.card_le_card hsubset
    _ ≤ (indexedUsedWitnessPairs P history J).card := Finset.card_image_le

theorem card_indexedUsedWitnessPairs_le_empty_add_nonempty
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    (indexedUsedWitnessPairs P history J).card ≤
      (indexedEmptyFreeWitnessPairs P history J).card +
        (indexedNonemptyFreeWitnessPairs P history J).card := by
  have hsubset : indexedUsedWitnessPairs P history J ⊆
      indexedEmptyFreeWitnessPairs P history J ∪
        indexedNonemptyFreeWitnessPairs P history J := by
    intro z hz
    by_cases hnonempty :
        (selectedFreeVertices P (history.get z.1) z.2 J).Nonempty
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, hnonempty⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hz, hnonempty⟩)
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

/-- History indices represented by one partial-load target. -/
def indexedPartialTargetIndices (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n))
    (target : RelevantPartialLoadTarget P n) :
    Finset (Fin history.length) :=
  (Finset.univ : Finset (Fin history.length)).filter fun i ↦
    mapEdge (history.get i) target.1.vertices = target.1.image

lemma card_indexedPartialTargetIndices_eq_pathHits
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (target : RelevantPartialLoadTarget P n) :
    (indexedPartialTargetIndices P history target).card =
      pathHits (partialLoadHit P target) initial history := by
  rw [pathHits_partialLoadHit_eq_countP]
  change ((Finset.univ : Finset (Fin history.length)).filter fun i ↦
      mapEdge (history.get i) target.1.vertices = target.1.image).card = _
  induction history with
  | nil => simp
  | cons φ rest ih =>
      change ((Finset.univ : Finset (Fin (rest.length + 1))).filter
        (fun i ↦ mapEdge ((φ :: rest).get i) target.1.vertices =
          target.1.image)).card = _
      rw [Fin.univ_succ, Finset.filter_cons, apply_ite Finset.card,
        Finset.card_cons]
      rw [Finset.filter_map, Finset.card_map]
      simp only [List.get_cons_zero, List.countP_cons]
      change (if mapEdge φ target.1.vertices = target.1.image then
          ((Finset.univ : Finset (Fin rest.length)).filter fun i ↦
            mapEdge (rest.get i) target.1.vertices = target.1.image).card + 1
        else
          ((Finset.univ : Finset (Fin rest.length)).filter fun i ↦
            mapEdge (rest.get i) target.1.vertices = target.1.image).card) = _
      rw [ih]
      by_cases hmap : mapEdge φ target.1.vertices = target.1.image <;>
        simp [hmap, Nat.add_comm]

def indexedPartialTargetPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n))
    (target : RelevantPartialLoadTarget P n) :
    Finset (Fin history.length × Finset (Fin v)) :=
  (indexedPartialTargetIndices P history target).image fun i ↦
    (i, target.1.edge)

theorem indexedNonemptyFreeWitnessPairs_subset_partialTargetPairs
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    indexedNonemptyFreeWitnessPairs P history J ⊆
      (partialTargetsInside P n J).biUnion
        (indexedPartialTargetPairs P history) := by
  intro z hz
  rcases z with ⟨i, e⟩
  have hzNonempty := Finset.mem_filter.mp hz
  have hzUsed := Finset.mem_filter.mp hzNonempty.1
  have hzProduct := Finset.mem_product.mp hzUsed.1
  let φ : Fin v ↪ Fin n := history.get i
  let S : Finset (Fin v) := selectedFreeVertices P φ e J
  have hSNonempty : S.Nonempty := by
    simpa [S, φ] using hzNonempty.2
  let raw : PartialLoadTarget v n :=
    { edge := e
      vertices := S
      image := mapEdge φ S }
  have hraw : IsRelevantPartialLoad P raw := by
    refine ⟨hzProduct.2, hSNonempty, ?_, ?_⟩
    · simpa [raw, S] using selectedFreeVertices_subset P φ e J
    · simp [raw]
  let target : RelevantPartialLoadTarget P n := ⟨raw, hraw⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨target, ?_, ?_⟩
  · apply mem_partialTargetsInside.mpr
    simpa [target, raw, S] using
      mapEdge_selectedFreeVertices_subset P φ e J
  · apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, ?_⟩
    · simp [target, raw, φ]
    · simp [target, raw]

theorem card_indexedNonemptyFreeWitnessPairs_le_sum_pathHits
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    (indexedNonemptyFreeWitnessPairs P history J).card ≤
      ∑ target ∈ partialTargetsInside P n J,
        pathHits (partialLoadHit P target) initial history := by
  calc
    (indexedNonemptyFreeWitnessPairs P history J).card ≤
        ((partialTargetsInside P n J).biUnion
          (indexedPartialTargetPairs P history)).card :=
      Finset.card_le_card
        (indexedNonemptyFreeWitnessPairs_subset_partialTargetPairs
          P history J)
    _ ≤ ∑ target ∈ partialTargetsInside P n J,
        (indexedPartialTargetPairs P history target).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ target ∈ partialTargetsInside P n J,
        pathHits (partialLoadHit P target) initial history := by
      apply Finset.sum_le_sum
      intro target htarget
      exact Finset.card_image_le.trans_eq
        (card_indexedPartialTargetIndices_eq_pathHits
          P initial history target)

theorem localDegree_usedEdges_le_indexedEmpty_add_uniformCap
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) (C : ℕ)
    (hcaps : ∀ target : RelevantPartialLoadTarget P n,
      pathHits (partialLoadHit P target) initial history < C) :
    Reserve.localDegree (usedEdges P history) J ≤
      (indexedEmptyFreeWitnessPairs P history J).card +
        (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C := by
  calc
    Reserve.localDegree (usedEdges P history) J ≤
        (indexedUsedWitnessPairs P history J).card :=
      localDegree_usedEdges_le_indexedWitnessPairs P history J
    _ ≤ (indexedEmptyFreeWitnessPairs P history J).card +
        (indexedNonemptyFreeWitnessPairs P history J).card :=
      card_indexedUsedWitnessPairs_le_empty_add_nonempty P history J
    _ ≤ (indexedEmptyFreeWitnessPairs P history J).card +
        ∑ target ∈ partialTargetsInside P n J,
          pathHits (partialLoadHit P target) initial history := by
      exact Nat.add_le_add_left
        (card_indexedNonemptyFreeWitnessPairs_le_sum_pathHits
          P initial history J) _
    _ ≤ (indexedEmptyFreeWitnessPairs P history J).card +
        ∑ _target ∈ partialTargetsInside P n J, C := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro target htarget
      exact Nat.le_of_lt (hcaps target)
    _ = (indexedEmptyFreeWitnessPairs P history J).card +
        (partialTargetsInside P n J).card * C := by simp
    _ ≤ (indexedEmptyFreeWitnessPairs P history J).card +
        (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right C (card_partialTargetsInside_le P J)) _

/-! ## Full-face load counters -/

def indexedFaceTargetIndices (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n))
    (target : RelevantFaceLoadTarget P n) :
    Finset (Fin history.length) :=
  (Finset.univ : Finset (Fin history.length)).filter fun i ↦
    target.1.face ⊆ mapEdge (history.get i) target.1.edge

lemma pathHits_faceLoadHit_eq_countP
    (P : RootedPattern v r) (target : RelevantFaceLoadTarget P n) :
    ∀ (initial history : List (Fin v ↪ Fin n)),
      pathHits (faceLoadHit P target) initial history =
        history.countP fun φ ↦
          target.1.face ⊆ mapEdge φ target.1.edge := by
  intro initial history
  induction history generalizing initial with
  | nil => simp [pathHits]
  | cons φ rest ih =>
      by_cases h : target.1.face ⊆ mapEdge φ target.1.edge
      · simp [pathHits, faceLoadHit, hitBit, h, ih, Nat.add_comm]
      · simp [pathHits, faceLoadHit, hitBit, h, ih]

lemma card_indexedFaceTargetIndices_eq_pathHits
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (target : RelevantFaceLoadTarget P n) :
    (indexedFaceTargetIndices P history target).card =
      pathHits (faceLoadHit P target) initial history := by
  rw [pathHits_faceLoadHit_eq_countP]
  change ((Finset.univ : Finset (Fin history.length)).filter fun i ↦
      target.1.face ⊆ mapEdge (history.get i) target.1.edge).card = _
  induction history with
  | nil => simp
  | cons φ rest ih =>
      change ((Finset.univ : Finset (Fin (rest.length + 1))).filter
        (fun i ↦ target.1.face ⊆
          mapEdge ((φ :: rest).get i) target.1.edge)).card = _
      rw [Fin.univ_succ, Finset.filter_cons, apply_ite Finset.card,
        Finset.card_cons, Finset.filter_map, Finset.card_map]
      simp only [List.get_cons_zero, List.countP_cons]
      change (if target.1.face ⊆ mapEdge φ target.1.edge then
          ((Finset.univ : Finset (Fin rest.length)).filter fun i ↦
            target.1.face ⊆ mapEdge (rest.get i) target.1.edge).card + 1
        else
          ((Finset.univ : Finset (Fin rest.length)).filter fun i ↦
            target.1.face ⊆ mapEdge (rest.get i) target.1.edge).card) = _
      rw [ih]
      by_cases hmap : target.1.face ⊆ mapEdge φ target.1.edge <;>
        simp [hmap, Nat.add_comm]

def indexedFaceTargetPairs (P : RootedPattern v r)
    (history : List (Fin v ↪ Fin n))
    (target : RelevantFaceLoadTarget P n) :
    Finset (Fin history.length × Finset (Fin v)) :=
  (indexedFaceTargetIndices P history target).image fun i ↦
    (i, target.1.edge)

theorem indexedUsedWitnessPairs_subset_faceTargetPairs
    (P : RootedPattern v r) (history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    indexedUsedWitnessPairs P history J ⊆
      (P.freeEdges.attach.biUnion fun e ↦
        indexedFaceTargetPairs P history
          ⟨{ edge := e.1, face := J }, ⟨e.2, hJ⟩⟩) := by
  intro z hz
  rcases z with ⟨i, e⟩
  have hzData := Finset.mem_filter.mp hz
  have hzProduct := Finset.mem_product.mp hzData.1
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨e, hzProduct.2⟩, Finset.mem_attach _ _, Finset.mem_image.mpr ?_⟩
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, rfl⟩
  exact hzData.2

/-- Uniform caps for the full-face counters directly bound every
codimension-one degree of the used host. -/
theorem localDegree_usedEdges_le_faceLoadCaps
    (P : RootedPattern v r) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) (hJ : J.card = r - 1) (C : ℕ)
    (hcaps : ∀ target : RelevantFaceLoadTarget P n,
      pathHits (faceLoadHit P target) initial history < C) :
    Reserve.localDegree (usedEdges P history) J ≤ P.freeEdges.card * C := by
  calc
    Reserve.localDegree (usedEdges P history) J ≤
        (indexedUsedWitnessPairs P history J).card :=
      localDegree_usedEdges_le_indexedWitnessPairs P history J
    _ ≤ (P.freeEdges.attach.biUnion fun e ↦
        indexedFaceTargetPairs P history
          ⟨{ edge := e.1, face := J }, ⟨e.2, hJ⟩⟩).card :=
      Finset.card_le_card
        (indexedUsedWitnessPairs_subset_faceTargetPairs P history J hJ)
    _ ≤ ∑ e ∈ P.freeEdges.attach,
        (indexedFaceTargetPairs P history
          ⟨{ edge := e.1, face := J }, ⟨e.2, hJ⟩⟩).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ P.freeEdges.attach, C := by
      apply Finset.sum_le_sum
      intro e he
      let target : RelevantFaceLoadTarget P n :=
        ⟨{ edge := e.1, face := J }, ⟨e.2, hJ⟩⟩
      have hlt : (indexedFaceTargetPairs P history target).card < C := calc
        (indexedFaceTargetPairs P history target).card ≤
            (indexedFaceTargetIndices P history target).card :=
          Finset.card_image_le
        _ = pathHits (faceLoadHit P target) initial history :=
          card_indexedFaceTargetIndices_eq_pathHits P initial history target
        _ < C := hcaps target
      simpa [target] using Nat.le_of_lt hlt
    _ = P.freeEdges.card * C := by simp

/-! ## The one-step embedding numerator count -/

/-- Full embeddings satisfying one root condition and one prescribed
free-part image. -/
noncomputable def constrainedEmbeddings
    (root S : Finset (Fin v)) (request : RootRequest v n root)
    (g : Finset (Fin n)) : Finset (Fin v ↪ Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin v ↪ Fin n)).filter fun φ ↦
    ExtendsRequest root request φ ∧ mapEdge φ S = g

lemma mem_constrainedEmbeddings {φ : Fin v ↪ Fin n} :
    φ ∈ constrainedEmbeddings root S request g ↔
      ExtendsRequest root request φ ∧ mapEdge φ S = g := by
  classical
  simp [constrainedEmbeddings]

/-! ## The unrestricted rooted-extension denominator -/

/-- Images already prescribed by a root request. -/
def requestImage (root : Finset (Fin v))
    (request : RootRequest v n root) : Finset (Fin n) :=
  root.image request.map

lemma mapEdge_root_eq_requestImage_of_extends
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (φ : Fin v ↪ Fin n) (hext : ExtendsRequest root request φ) :
    mapEdge φ root = requestImage root request := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    apply Finset.mem_image.mpr
    exact ⟨x, hx, (hext x hx).symm.trans hxy⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    apply Finset.mem_map.mpr
    exact ⟨x, hx, (hext x hx).trans hxy⟩

/-- Vertices of the pattern outside the root. -/
def outsideRoot (root : Finset (Fin v)) : Finset (Fin v) :=
  (Finset.univ : Finset (Fin v)) \ root

/-- Ground vertices which are not prescribed images of root vertices. -/
def outsideRequestImage (root : Finset (Fin v))
    (request : RootRequest v n root) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ requestImage root request

lemma card_requestImage (root : Finset (Fin v))
    (request : RootRequest v n root) :
    (requestImage root request).card = root.card := by
  exact Finset.card_image_of_injOn request.injOn

@[simp] lemma card_outsideRoot (root : Finset (Fin v)) :
    (outsideRoot root).card = v - root.card := by
  rw [outsideRoot, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin]

lemma card_outsideRequestImage (root : Finset (Fin v))
    (request : RootRequest v n root) :
    (outsideRequestImage root request).card = n - root.card := by
  rw [outsideRequestImage,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, card_requestImage]

/-- Extend an injection of the non-root vertices into the unused ground
vertices by the prescribed root map. -/
def extendOutsideRoot (root : Finset (Fin v))
    (request : RootRequest v n root)
    (ψ : (↑(outsideRoot root) : Type) ↪
      (↑(outsideRequestImage root request) : Type)) : Fin v ↪ Fin n where
  toFun x := if hx : x ∈ root then request.map x
    else ψ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩
  inj' := by
    intro x y hxy
    by_cases hx : x ∈ root
    · by_cases hy : y ∈ root
      · exact request.injOn hx hy (by simpa [hx, hy] using hxy)
      · have hyOutside : y ∈ outsideRoot root :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩
        have hψOutside :
            (ψ ⟨y, hyOutside⟩).1 ∈ outsideRequestImage root request :=
          (ψ ⟨y, hyOutside⟩).2
        have hrequestMem : request.map x ∈ requestImage root request := by
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have heq : request.map x = (ψ ⟨y, hyOutside⟩).1 := by
          simpa [hx, hy] using hxy
        have hbad : (ψ ⟨y, hyOutside⟩).1 ∈
            requestImage root request := by
          rw [← heq]
          exact hrequestMem
        exact ((Finset.mem_sdiff.mp hψOutside).2 hbad).elim
    · by_cases hy : y ∈ root
      · have hxOutside : x ∈ outsideRoot root :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
        have hψOutside :
            (ψ ⟨x, hxOutside⟩).1 ∈ outsideRequestImage root request :=
          (ψ ⟨x, hxOutside⟩).2
        have hrequestMem : request.map y ∈ requestImage root request := by
          exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
        have heq : (ψ ⟨x, hxOutside⟩).1 = request.map y := by
          simpa [hx, hy] using hxy
        have hbad : (ψ ⟨x, hxOutside⟩).1 ∈
            requestImage root request := by
          rw [heq]
          exact hrequestMem
        exact ((Finset.mem_sdiff.mp hψOutside).2 hbad).elim
      · have hψ :
            ψ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩ =
              ψ ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩ := by
          simpa [hx, hy] using hxy
        exact congrArg Subtype.val (ψ.injective hψ)

lemma extendOutsideRoot_extendsRequest
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (ψ : (↑(outsideRoot root) : Type) ↪
      (↑(outsideRequestImage root request) : Type)) :
    ExtendsRequest root request (extendOutsideRoot root request ψ) := by
  intro x hx
  change (if h : x ∈ root then request.map x else _) = request.map x
  rw [dif_pos hx]

lemma extendOutsideRoot_injective
    (root : Finset (Fin v)) (request : RootRequest v n root) :
    Function.Injective (extendOutsideRoot root request) := by
  intro ψ χ h
  apply Function.Embedding.ext
  intro x
  have hx : x.1 ∉ root := (Finset.mem_sdiff.mp x.2).2
  have hfun := congrFun (congrArg Function.Embedding.toFun h) x.1
  change (if hx' : x.1 ∈ root then request.map x.1 else (ψ x).1) =
    (if hx' : x.1 ∈ root then request.map x.1 else (χ x).1) at hfun
  rw [dif_neg hx, dif_neg hx] at hfun
  exact Subtype.ext hfun

/-- All full embeddings which respect one prescribed root request. -/
noncomputable def rootedEmbeddings (root : Finset (Fin v))
    (request : RootRequest v n root) : Finset (Fin v ↪ Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin v ↪ Fin n)).filter
    (ExtendsRequest root request)

lemma mem_rootedEmbeddings {φ : Fin v ↪ Fin n} :
    φ ∈ rootedEmbeddings root request ↔ ExtendsRequest root request φ := by
  classical
  simp [rootedEmbeddings]

/-- There are at least the expected falling-factorial number of unrestricted
rooted extensions.  Equality also holds, but this direction is the one used
after subtracting embeddings meeting forbidden edges. -/
theorem descFactorial_le_card_rootedEmbeddings
    (root : Finset (Fin v)) (request : RootRequest v n root) :
    (n - root.card).descFactorial (v - root.card) ≤
      (rootedEmbeddings root request).card := by
  let f :
      ((↑(outsideRoot root) : Type) ↪
        (↑(outsideRequestImage root request) : Type)) →
          (↑(rootedEmbeddings root request) : Type) := fun ψ ↦
    ⟨extendOutsideRoot root request ψ, by
      exact mem_rootedEmbeddings.mpr
        (extendOutsideRoot_extendsRequest root request ψ)⟩
  have hf : Function.Injective f := by
    intro ψ χ h
    apply extendOutsideRoot_injective root request
    exact congrArg Subtype.val h
  calc
    (n - root.card).descFactorial (v - root.card) =
        Fintype.card
          ((↑(outsideRoot root) : Type) ↪
            (↑(outsideRequestImage root request) : Type)) := by
      simp [Fintype.card_embedding_eq,
        card_outsideRoot, card_outsideRequestImage]
    _ ≤ Fintype.card (↑(rootedEmbeddings root request) : Type) :=
      Fintype.card_le_of_injective f hf
    _ = (rootedEmbeddings root request).card :=
      Fintype.card_coe (rootedEmbeddings root request)

/-- Root-respecting embeddings which use at least one edge of `host`. -/
noncomputable def embeddingsMeeting (P : RootedPattern v r)
    (request : RootRequest v n P.root)
    (host : Finset (Finset (Fin n))) : Finset (Fin v ↪ Fin n) := by
  classical
  exact (rootedEmbeddings P.root request).filter fun φ ↦
    ¬Disjoint (imageFreeEdges P φ) host

lemma mem_embeddingsMeeting {φ : Fin v ↪ Fin n} :
    φ ∈ embeddingsMeeting P request host ↔
      ExtendsRequest P.root request φ ∧
        ¬Disjoint (imageFreeEdges P φ) host := by
  classical
  rw [embeddingsMeeting, Finset.mem_filter]
  exact and_congr mem_rootedEmbeddings Iff.rfl

/-- The unrestricted rooted family is covered by the legal family and the
two families which meet the fixed or history-dependent forbidden hosts. -/
theorem rootedEmbeddings_subset_legal_union_meeting
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) :
    rootedEmbeddings P.root (request history.length) ⊆
      legalEmbeddings P request forbidden history ∪
        (embeddingsMeeting P (request history.length) forbidden ∪
          embeddingsMeeting P (request history.length) (usedEdges P history)) := by
  intro φ hφ
  have hroot := mem_rootedEmbeddings.mp hφ
  by_cases hforbidden : Disjoint (imageFreeEdges P φ) forbidden
  · by_cases hused : Disjoint (imageFreeEdges P φ) (usedEdges P history)
    · exact Finset.mem_union_left _ (mem_legalEmbeddings.mpr
        ⟨hroot, hforbidden, hused⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (mem_embeddingsMeeting.mpr ⟨hroot, hused⟩))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (mem_embeddingsMeeting.mpr ⟨hroot, hforbidden⟩))

/-- Baseline rooted count minus the two explicitly bad families is a lower
bound for the legal set.  Subsequent lemmas estimate those bad families from
local host degrees. -/
theorem descFactorial_sub_meeting_le_card_legalEmbeddings
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) :
    (n - P.root.card).descFactorial (v - P.root.card) -
          (embeddingsMeeting P (request history.length) forbidden).card -
          (embeddingsMeeting P (request history.length)
            (usedEdges P history)).card ≤
      (legalEmbeddings P request forbidden history).card := by
  have hbase := descFactorial_le_card_rootedEmbeddings P.root
    (request history.length)
  have hcover := Finset.card_le_card
    (rootedEmbeddings_subset_legal_union_meeting P request forbidden history)
  have hunion :
      (legalEmbeddings P request forbidden history ∪
        (embeddingsMeeting P (request history.length) forbidden ∪
          embeddingsMeeting P (request history.length)
            (usedEdges P history))).card ≤
        (legalEmbeddings P request forbidden history).card +
          (embeddingsMeeting P (request history.length) forbidden).card +
          (embeddingsMeeting P (request history.length)
            (usedEdges P history)).card := by
    calc
      _ ≤ (legalEmbeddings P request forbidden history).card +
          (embeddingsMeeting P (request history.length) forbidden ∪
            embeddingsMeeting P (request history.length)
              (usedEdges P history)).card := Finset.card_union_le _ _
      _ ≤ (legalEmbeddings P request forbidden history).card +
          ((embeddingsMeeting P (request history.length) forbidden).card +
            (embeddingsMeeting P (request history.length)
              (usedEdges P history)).card) :=
        Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = _ := by omega
  omega

/-! ## Counting embeddings which meet a host -/

/-- Rooted embeddings which map one specified pattern edge to one specified
ground edge. -/
noncomputable def edgeConstrainedEmbeddings
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (e : Finset (Fin v)) (g : Finset (Fin n)) :
    Finset (Fin v ↪ Fin n) := by
  classical
  exact (rootedEmbeddings root request).filter fun φ ↦ mapEdge φ e = g

lemma mem_edgeConstrainedEmbeddings {φ : Fin v ↪ Fin n} :
    φ ∈ edgeConstrainedEmbeddings root request e g ↔
      ExtendsRequest root request φ ∧ mapEdge φ e = g := by
  classical
  rw [edgeConstrainedEmbeddings, Finset.mem_filter]
  exact and_congr mem_rootedEmbeddings Iff.rfl

/-- The image of the root part of a pattern edge is already fixed by a root
request. -/
def rootPartImage (root : Finset (Fin v))
    (request : RootRequest v n root) (e : Finset (Fin v)) :
    Finset (Fin n) :=
  (e ∩ root).image request.map

/-- Scheduled request/edge pairs whose prescribed root image contains
`J`.  This is the deterministic root-load quantity in the rooted extension
lemma. -/
def scheduledRootWitnessPairs (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (J : Finset (Fin n)) :
    Finset (Fin depth × Finset (Fin v)) :=
  ((Finset.univ : Finset (Fin depth)) ×ˢ P.freeEdges).filter fun z ↦
    J ⊆ rootPartImage P.root (request z.1) z.2

/-- Uniform root-load bound for every initial segment of a scheduled
request family. -/
def IsRootScheduleBoundedUpTo (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth D : ℕ) : Prop :=
  ∀ d ≤ depth, ∀ J : Finset (Fin n), J.card = r - 1 →
    (scheduledRootWitnessPairs P request d J).card ≤ D

/-- The part of a target face not already prescribed by the current root
request. -/
def faceMissing (P : RootedPattern v r)
    (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) : Finset (Fin n) :=
  target.1.face \ rootPartImage P.root request target.1.edge

/-- Pattern free vertices which map into the missing part of a face. -/
def facePreimageVertices (P : RootedPattern v r)
    (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) (φ : Fin v ↪ Fin n) :
    Finset (Fin v) :=
  (freePart P target.1.edge).filter fun x ↦
    φ x ∈ faceMissing P request target

/-- Crude but exponent-sharp numerator for one full-face hit. -/
def faceLoadNumeratorAt (P : RootedPattern v r) (n : ℕ)
    (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) : ℕ :=
  let s := (faceMissing P request target).card
  if s ≤ (freePart P target.1.edge).card then
    2 ^ v * (s ^ s * n ^ (v - (P.root.card + s)))
  else 0

lemma rootPartImage_subset_of_mem_edgeConstrained
    (hφ : φ ∈ edgeConstrainedEmbeddings root request e g) :
    rootPartImage root request e ⊆ g := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hxEdge : x ∈ e := (Finset.mem_inter.mp hx).1
  have hxRoot : x ∈ root := (Finset.mem_inter.mp hx).2
  have hrequest := (mem_edgeConstrainedEmbeddings.mp hφ).1 x hxRoot
  have hmap : φ x ∈ mapEdge φ e := by
    exact Finset.mem_map.mpr ⟨x, hxEdge, rfl⟩
  rw [(mem_edgeConstrainedEmbeddings.mp hφ).2] at hmap
  simpa [hrequest] using hmap

lemma mapEdge_freePart_subset_of_mem_edgeConstrained
    (hφ : φ ∈ edgeConstrainedEmbeddings root request e g) :
    mapEdge φ (e \ root) ⊆ g := by
  have hsub : e \ root ⊆ e := Finset.sdiff_subset
  have hmapped : mapEdge φ (e \ root) ⊆ mapEdge φ e := by
    exact Finset.map_subset_map.mpr hsub
  simpa [(mem_edgeConstrainedEmbeddings.mp hφ).2] using hmapped

/-- For one pattern edge and one target edge, enumerate the possible
unordered images of the free vertices. -/
theorem edgeConstrainedEmbeddings_subset_biUnion
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (e : Finset (Fin v)) (g : Finset (Fin n)) :
    edgeConstrainedEmbeddings root request e g ⊆
      g.powerset.biUnion fun h ↦
        constrainedEmbeddings root (e \ root) request h := by
  intro φ hφ
  let h := mapEdge φ (e \ root)
  have hh : h ∈ g.powerset := by
    exact Finset.mem_powerset.mpr
      (mapEdge_freePart_subset_of_mem_edgeConstrained hφ)
  apply Finset.mem_biUnion.mpr
  refine ⟨h, hh, mem_constrainedEmbeddings.mpr ?_⟩
  exact ⟨(mem_edgeConstrainedEmbeddings.mp hφ).1, rfl⟩

/-- Fixing the root values and the unordered image of `s` further vertices
leaves at most `|g|^s n^(v-|root|-s)` possibilities.  The paper sharpens
the fixed factor `s^s` to `s!`; the present bound has the same exponent and
is sufficient for every asymptotic application. -/
theorem card_embeddings_extending_mapEdge_le
    (root S : Finset (Fin v)) (hdisjoint : Disjoint root S)
    (request : RootRequest v n root) (g : Finset (Fin n)) :
    (constrainedEmbeddings root S request g).card ≤
        g.card ^ S.card * n ^ (v - (root.card + S.card)) := by
  classical
  let T : Finset (Fin v) :=
    (Finset.univ : Finset (Fin v)) \ (root ∪ S)
  let selected := constrainedEmbeddings root S request g
  let code (φ : ↑selected) : (↑S → ↑g) × (↑T → Fin n) :=
    (fun x ↦ ⟨φ.1 x.1, by
      have hm : φ.1 x.1 ∈ mapEdge φ.1 S := by
        exact Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩
      exact (mem_constrainedEmbeddings.mp φ.2).2 ▸ hm⟩,
      fun x ↦ φ.1 x.1)
  have hcode : Function.Injective code := by
    intro φ ψ h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    by_cases hxroot : x ∈ root
    · have hφ := (mem_constrainedEmbeddings.mp φ.2).1 x hxroot
      have hψ := (mem_constrainedEmbeddings.mp ψ.2).1 x hxroot
      exact hφ.trans hψ.symm
    · by_cases hxS : x ∈ S
      · have hfun := congrFun (congrArg Prod.fst h) ⟨x, hxS⟩
        exact congrArg Subtype.val hfun
      · have hxT : x ∈ T := by
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ x, by simp [hxroot, hxS]⟩
        have hfun := congrFun (congrArg Prod.snd h) ⟨x, hxT⟩
        exact hfun
  have hcardCode : selected.card ≤
      Fintype.card ((↑S → ↑g) × (↑T → Fin n)) := by
    calc
      selected.card = Fintype.card ↑selected := (Fintype.card_coe selected).symm
      _ ≤ Fintype.card ((↑S → ↑g) × (↑T → Fin n)) :=
        Fintype.card_le_of_injective code hcode
  have hTcard : T.card = v - (root.card + S.card) := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjoint]
  simpa [selected, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe, hTcard] using hcardCode

/-! ## Touching a fixed ground face outside the root -/

/-- An embedding touches `J` outside its prescribed root when some pattern
vertex not in the root is sent into `J`.  This is the coarse event which
dominates every new mixed near-pair in the splitting construction. -/
def OutsideRootTouches (root : Finset (Fin v))
    (J : Finset (Fin n)) (phi : Fin v ↪ Fin n) : Prop :=
  ∃ x ∈ outsideRoot root, phi x ∈ J

/-- Boolean form of `OutsideRootTouches`, suitable for the generic
history-dependent counter theorem. -/
def outsideRootTouchHit (root : Finset (Fin v))
    (J : Finset (Fin n)) (_history : List (Fin v ↪ Fin n))
    (phi : Fin v ↪ Fin n) : Bool := by
  classical
  exact decide (OutsideRootTouches root J phi)

lemma outsideRootTouchHit_eq_true_iff
    (root : Finset (Fin v)) (J : Finset (Fin n))
    (history : List (Fin v ↪ Fin n)) (phi : Fin v ↪ Fin n) :
    outsideRootTouchHit root J history phi = true ↔
      OutsideRootTouches root J phi := by
  classical
  simp [outsideRootTouchHit]

/-- Positions in a history whose embedding touches `J` outside the root. -/
def indexedOutsideRootTouchIndices (root : Finset (Fin v))
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    Finset (Fin history.length) :=
  (Finset.univ : Finset (Fin history.length)).filter fun i ↦
    outsideRootTouchHit root J [] (history.get i)

lemma pathHits_outsideRootTouchHit_eq_countP
    (root : Finset (Fin v)) (J : Finset (Fin n)) :
    ∀ (initial history : List (Fin v ↪ Fin n)),
      pathHits (outsideRootTouchHit root J) initial history =
        history.countP fun phi ↦ outsideRootTouchHit root J [] phi := by
  intro initial history
  induction history generalizing initial with
  | nil => simp [pathHits]
  | cons phi rest ih =>
      by_cases h : OutsideRootTouches root J phi
      · have htrue : outsideRootTouchHit root J [] phi = true :=
          (outsideRootTouchHit_eq_true_iff root J [] phi).mpr h
        have hhistory : outsideRootTouchHit root J initial phi = true :=
          (outsideRootTouchHit_eq_true_iff root J initial phi).mpr h
        simp [pathHits, hitBit, htrue, hhistory, ih, Nat.add_comm]
      · have hfalse : outsideRootTouchHit root J [] phi = false := by
          cases hvalue : outsideRootTouchHit root J [] phi with
          | false => rfl
          | true =>
              exact False.elim (h
                ((outsideRootTouchHit_eq_true_iff root J [] phi).mp hvalue))
        have hhistory : outsideRootTouchHit root J initial phi = false := by
          cases hvalue : outsideRootTouchHit root J initial phi with
          | false => rfl
          | true =>
              exact False.elim (h
                ((outsideRootTouchHit_eq_true_iff root J initial phi).mp hvalue))
        simp [pathHits, hitBit, hfalse, hhistory, ih]

lemma card_indexedOutsideRootTouchIndices_eq_pathHits
    (root : Finset (Fin v)) (initial history : List (Fin v ↪ Fin n))
    (J : Finset (Fin n)) :
    (indexedOutsideRootTouchIndices root history J).card =
      pathHits (outsideRootTouchHit root J) initial history := by
  rw [pathHits_outsideRootTouchHit_eq_countP]
  change ((Finset.univ : Finset (Fin history.length)).filter fun i ↦
      outsideRootTouchHit root J [] (history.get i)).card = _
  induction history with
  | nil => simp
  | cons phi rest ih =>
      change ((Finset.univ : Finset (Fin (rest.length + 1))).filter
        (fun i ↦ outsideRootTouchHit root J []
          ((phi :: rest).get i))).card = _
      rw [Fin.univ_succ, Finset.filter_cons, apply_ite Finset.card,
        Finset.card_cons, Finset.filter_map, Finset.card_map]
      simp only [List.get_cons_zero, List.countP_cons]
      change (if outsideRootTouchHit root J [] phi then
          ((Finset.univ : Finset (Fin rest.length)).filter fun i ↦
            outsideRootTouchHit root J [] (rest.get i)).card + 1
        else
          ((Finset.univ : Finset (Fin rest.length)).filter fun i ↦
            outsideRootTouchHit root J [] (rest.get i)).card) = _
      rw [ih]
      cases outsideRootTouchHit root J [] phi <;> simp [Nat.add_comm]

/-- Root-respecting embeddings which touch `J` outside the root are covered
by the singleton constraints `phi x = y`, with `x` outside the root and
`y ∈ J`. -/
theorem rootedOutsideTouch_subset_biUnion
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (J : Finset (Fin n)) :
    (rootedEmbeddings root request).filter (fun phi ↦
        outsideRootTouchHit root J [] phi) ⊆
      (outsideRoot root).biUnion fun x ↦
        J.biUnion fun y ↦ constrainedEmbeddings root {x} request {y} := by
  classical
  intro phi hphi
  have hdata := Finset.mem_filter.mp hphi
  have htouch : OutsideRootTouches root J phi :=
    (outsideRootTouchHit_eq_true_iff root J [] phi).mp (by
      simpa using hdata.2)
  obtain ⟨x, hxOutside, hxJ⟩ := htouch
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hxOutside, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨phi x, hxJ, mem_constrainedEmbeddings.mpr ⟨?_, ?_⟩⟩
  · exact mem_rootedEmbeddings.mp hdata.1
  · simp [mapEdge]

/-- Fixing one non-root vertex to lie in a prescribed face costs one power
of the ground-set size.  The factor `(v - |root|) * |J|` only enumerates
the possible pattern and ground witnesses. -/
theorem card_rootedEmbeddings_outsideRootTouches_le
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (J : Finset (Fin n)) :
    ((rootedEmbeddings root request).filter (fun phi ↦
        outsideRootTouchHit root J [] phi)).card ≤
      (v - root.card) * J.card * n ^ (v - (root.card + 1)) := by
  classical
  let term := n ^ (v - (root.card + 1))
  calc
    ((rootedEmbeddings root request).filter (fun phi ↦
        outsideRootTouchHit root J [] phi)).card ≤
        ((outsideRoot root).biUnion fun x ↦
          J.biUnion fun y ↦
            constrainedEmbeddings root {x} request {y}).card :=
      Finset.card_le_card
        (rootedOutsideTouch_subset_biUnion root request J)
    _ ≤ ∑ x ∈ outsideRoot root,
          (J.biUnion fun y ↦
            constrainedEmbeddings root {x} request {y}).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ x ∈ outsideRoot root, ∑ y ∈ J,
          (constrainedEmbeddings root {x} request {y}).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ outsideRoot root, ∑ _y ∈ J, term := by
      apply Finset.sum_le_sum
      intro x hxOutside
      apply Finset.sum_le_sum
      intro y _hy
      have hxNotRoot : x ∉ root :=
        (Finset.mem_sdiff.mp hxOutside).2
      have hdisjoint : Disjoint root ({x} : Finset (Fin v)) := by
        apply Finset.disjoint_left.mpr
        intro z hzRoot hzSingleton
        have hzx : z = x := by simpa using hzSingleton
        exact hxNotRoot (hzx ▸ hzRoot)
      simpa [term] using
        (card_embeddings_extending_mapEdge_le root {x} hdisjoint
          request ({y} : Finset (Fin n)))
    _ = (v - root.card) * J.card * term := by
      simp [card_outsideRoot, Nat.mul_assoc]
    _ = (v - root.card) * J.card *
        n ^ (v - (root.card + 1)) := rfl

/-- The same one-power saving for the legal subset used at one random-greedy
step. -/
theorem card_legalEmbeddings_outsideRootTouchHit_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) :
    ((legalEmbeddings P request forbidden history).filter fun phi ↦
        outsideRootTouchHit P.root J history phi).card ≤
      (v - P.root.card) * J.card *
        n ^ (v - (P.root.card + 1)) := by
  classical
  calc
    ((legalEmbeddings P request forbidden history).filter fun phi ↦
        outsideRootTouchHit P.root J history phi).card ≤
        ((rootedEmbeddings P.root (request history.length)).filter fun phi ↦
          outsideRootTouchHit P.root J [] phi).card := by
      apply Finset.card_le_card
      intro phi hphi
      have hdata := Finset.mem_filter.mp hphi
      apply Finset.mem_filter.mpr
      refine ⟨mem_rootedEmbeddings.mpr
        (mem_legalEmbeddings.mp hdata.1).1, ?_⟩
      have htouch :=
        (outsideRootTouchHit_eq_true_iff P.root J history phi).mp
          (by simpa using hdata.2)
      exact (outsideRootTouchHit_eq_true_iff P.root J [] phi).mpr htouch
    _ ≤ _ := card_rootedEmbeddings_outsideRootTouches_le
      P.root (request history.length) J

lemma mapEdge_facePreimageVertices
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) (φ : Fin v ↪ Fin n)
    (hext : ExtendsRequest P.root request φ)
    (hhit : target.1.face ⊆ mapEdge φ target.1.edge) :
    mapEdge φ (facePreimageVertices P request target φ) =
      faceMissing P request target := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro y hy
    have hyData := Finset.mem_sdiff.mp hy
    have hyEdge := hhit hyData.1
    obtain ⟨x, hxEdge, hxy⟩ := Finset.mem_map.mp hyEdge
    have hxNotRoot : x ∉ P.root := by
      intro hxRoot
      have hyRootImage : y ∈
          rootPartImage P.root request target.1.edge := by
        apply Finset.mem_image.mpr
        refine ⟨x, Finset.mem_inter.mpr ⟨hxEdge, hxRoot⟩, ?_⟩
        exact (hext x hxRoot).symm.trans hxy
      exact hyData.2 hyRootImage
    apply Finset.mem_map.mpr
    refine ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hxEdge, hxNotRoot⟩, ?_⟩, hxy⟩
    rw [hxy]
    exact hy

lemma facePreimageVertices_mem_powersetCard
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) (φ : Fin v ↪ Fin n)
    (hext : ExtendsRequest P.root request φ)
    (hhit : target.1.face ⊆ mapEdge φ target.1.edge) :
    facePreimageVertices P request target φ ∈
      (freePart P target.1.edge).powersetCard
        (faceMissing P request target).card := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  rw [← card_mapEdge φ (facePreimageVertices P request target φ),
    mapEdge_facePreimageVertices P request target φ hext hhit]

noncomputable def faceConstrainedEmbeddings
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) : Finset (Fin v ↪ Fin n) :=
  ((freePart P target.1.edge).powersetCard
    (faceMissing P request target).card).biUnion fun S ↦
      constrainedEmbeddings P.root S request
        (faceMissing P request target)

theorem legalFaceHit_subset_faceConstrainedEmbeddings
    (P : RootedPattern v r)
    (requestSchedule : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (target : RelevantFaceLoadTarget P n)
    (history : List (Fin v ↪ Fin n)) :
    (legalEmbeddings P requestSchedule forbidden history).filter
        (fun φ ↦ faceLoadHit P target history φ) ⊆
      faceConstrainedEmbeddings P (requestSchedule history.length) target := by
  intro φ hφ
  have hdata := Finset.mem_filter.mp hφ
  have hlegal := mem_legalEmbeddings.mp hdata.1
  have hhit := (faceLoadHit_eq_true_iff P target history φ).mp (by
    simpa using hdata.2)
  let S := facePreimageVertices P (requestSchedule history.length) target φ
  apply Finset.mem_biUnion.mpr
  refine ⟨S, facePreimageVertices_mem_powersetCard P
    (requestSchedule history.length) target φ hlegal.1 hhit, ?_⟩
  exact mem_constrainedEmbeddings.mpr
    ⟨hlegal.1, mapEdge_facePreimageVertices P
      (requestSchedule history.length) target φ hlegal.1 hhit⟩

theorem card_faceConstrainedEmbeddings_le
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) :
    (faceConstrainedEmbeddings P request target).card ≤
      faceLoadNumeratorAt P n request target := by
  let s := (faceMissing P request target).card
  let family := (freePart P target.1.edge).powersetCard s
  let term := s ^ s * n ^ (v - (P.root.card + s))
  by_cases hs : s ≤ (freePart P target.1.edge).card
  swap
  · have hslt : (freePart P target.1.edge).card < s := by omega
    have hfamilyEmpty : family = ∅ := by
      simp [family, hslt]
    have hfaceEmpty : faceConstrainedEmbeddings P request target = ∅ := by
      rw [faceConstrainedEmbeddings]
      change family.biUnion (fun S ↦
        constrainedEmbeddings P.root S request
          (faceMissing P request target)) = ∅
      rw [hfamilyEmpty]
      simp
    rw [hfaceEmpty]
    simp [faceLoadNumeratorAt, s, hs]
  have hfamily : family ⊆ (Finset.univ : Finset (Fin v)).powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.subset_univ S)
  have hfamilyCard : family.card ≤ 2 ^ v := by
    calc
      family.card ≤ (Finset.univ : Finset (Fin v)).powerset.card :=
        Finset.card_le_card hfamily
      _ = 2 ^ v := by simp
  calc
    (faceConstrainedEmbeddings P request target).card ≤
        ∑ S ∈ family,
          (constrainedEmbeddings P.root S request
            (faceMissing P request target)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ family, term := by
      apply Finset.sum_le_sum
      intro S hS
      have hSdata := Finset.mem_powersetCard.mp hS
      have hdisjoint : Disjoint P.root S := by
        apply Finset.disjoint_left.mpr
        intro x hxRoot hxS
        exact (Finset.mem_sdiff.mp (hSdata.1 hxS)).2 hxRoot
      simpa [term, s, hSdata.2] using
        (card_embeddings_extending_mapEdge_le P.root S hdisjoint request
          (faceMissing P request target))
    _ = family.card * term := by simp
    _ ≤ 2 ^ v * term := Nat.mul_le_mul_right term hfamilyCard
    _ = faceLoadNumeratorAt P n request target := by
      simp [faceLoadNumeratorAt, term, s, hs]

theorem card_legalEmbeddings_faceLoadHit_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (target : RelevantFaceLoadTarget P n)
    (history : List (Fin v ↪ Fin n)) :
    ((legalEmbeddings P request forbidden history).filter
      fun φ ↦ faceLoadHit P target history φ).card ≤
        faceLoadNumeratorAt P n (request history.length) target := by
  calc
    ((legalEmbeddings P request forbidden history).filter
        fun φ ↦ faceLoadHit P target history φ).card ≤
        (faceConstrainedEmbeddings P (request history.length) target).card :=
      Finset.card_le_card
        (legalFaceHit_subset_faceConstrainedEmbeddings
          P request forbidden target history)
    _ ≤ _ := card_faceConstrainedEmbeddings_le
      P (request history.length) target

/-- One edge-image constraint costs one power of `n` for each free vertex.
The factor `2^|g|` only enumerates its possible unordered free-part image. -/
theorem card_edgeConstrainedEmbeddings_le
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (e : Finset (Fin v)) (g : Finset (Fin n)) :
    (edgeConstrainedEmbeddings root request e g).card ≤
      2 ^ g.card *
        (g.card ^ (e \ root).card *
          n ^ (v - (root.card + (e \ root).card))) := by
  have hdisjoint : Disjoint root (e \ root) := by
    exact Finset.disjoint_sdiff
  calc
    (edgeConstrainedEmbeddings root request e g).card ≤
        (g.powerset.biUnion fun h ↦
          constrainedEmbeddings root (e \ root) request h).card :=
      Finset.card_le_card
        (edgeConstrainedEmbeddings_subset_biUnion root request e g)
    _ ≤ ∑ h ∈ g.powerset,
        (constrainedEmbeddings root (e \ root) request h).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _h ∈ g.powerset,
        (g.card ^ (e \ root).card *
          n ^ (v - (root.card + (e \ root).card))) := by
      apply Finset.sum_le_sum
      intro h hh
      have hhsub : h ⊆ g := Finset.mem_powerset.mp hh
      exact (card_embeddings_extending_mapEdge_le root (e \ root)
        hdisjoint request h).trans
          (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_left (Finset.card_le_card hhsub) _))
    _ = 2 ^ g.card *
        (g.card ^ (e \ root).card *
          n ^ (v - (root.card + (e \ root).card))) := by
      simp

/-- Host edges compatible with the values prescribed on the root part of
one pattern edge. -/
def compatibleHostEdges (root : Finset (Fin v))
    (request : RootRequest v n root) (e : Finset (Fin v))
    (host : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  host.filter fun g ↦ rootPartImage root request e ⊆ g

/-- Every rooted embedding meeting `host` has a witness pattern edge and a
compatible target edge. -/
theorem embeddingsMeeting_subset_biUnion_edgeConstrained
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (host : Finset (Finset (Fin n))) :
    embeddingsMeeting P request host ⊆
      P.freeEdges.biUnion fun e ↦
        (compatibleHostEdges P.root request e host).biUnion fun g ↦
          edgeConstrainedEmbeddings P.root request e g := by
  intro φ hφ
  have hmeet := (mem_embeddingsMeeting.mp hφ).2
  obtain ⟨g, hgImage, hgHost⟩ := Finset.not_disjoint_iff.mp hmeet
  obtain ⟨e, heFree, heMap⟩ := Finset.mem_image.mp hgImage
  apply Finset.mem_biUnion.mpr
  refine ⟨e, heFree, Finset.mem_biUnion.mpr ?_⟩
  have hconstrained :
      φ ∈ edgeConstrainedEmbeddings P.root request e g := by
    exact mem_edgeConstrainedEmbeddings.mpr
      ⟨(mem_embeddingsMeeting.mp hφ).1, heMap⟩
  refine ⟨g, Finset.mem_filter.mpr
    ⟨hgHost, rootPartImage_subset_of_mem_edgeConstrained hconstrained⟩,
      hconstrained⟩

/-- A union-bound estimate for all bad rooted embeddings in terms of the
local host degrees at the fixed root-part images. -/
theorem card_embeddingsMeeting_le_sum_local
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (host : Finset (Finset (Fin n)))
    (huniform : ∀ g ∈ host, g.card = r) :
    (embeddingsMeeting P request host).card ≤
      ∑ e ∈ P.freeEdges,
        (compatibleHostEdges P.root request e host).card *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) := by
  calc
    (embeddingsMeeting P request host).card ≤
        (P.freeEdges.biUnion fun e ↦
          (compatibleHostEdges P.root request e host).biUnion fun g ↦
            edgeConstrainedEmbeddings P.root request e g).card :=
      Finset.card_le_card
        (embeddingsMeeting_subset_biUnion_edgeConstrained P request host)
    _ ≤ ∑ e ∈ P.freeEdges,
        ((compatibleHostEdges P.root request e host).biUnion fun g ↦
          edgeConstrainedEmbeddings P.root request e g).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ e ∈ P.freeEdges,
        ∑ g ∈ compatibleHostEdges P.root request e host,
          (edgeConstrainedEmbeddings P.root request e g).card := by
      apply Finset.sum_le_sum
      intro e he
      exact Finset.card_biUnion_le
    _ ≤ ∑ e ∈ P.freeEdges,
        ∑ _g ∈ compatibleHostEdges P.root request e host,
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro g hg
      have hgHost : g ∈ host := (Finset.mem_filter.mp hg).1
      simpa [huniform g hgHost] using
        (card_edgeConstrainedEmbeddings_le P.root request e g)
    _ = ∑ e ∈ P.freeEdges,
        (compatibleHostEdges P.root request e host).card *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) := by
      apply Finset.sum_congr rfl
      intro e he
      simp

lemma card_compatibleHostEdges
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (e : Finset (Fin v)) (host : Finset (Finset (Fin n))) :
    (compatibleHostEdges root request e host).card =
      Reserve.localDegree host (rootPartImage root request e) := by
  rfl

lemma card_rootPartImage
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (e : Finset (Fin v)) :
    (rootPartImage root request e).card = (e ∩ root).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  exact request.injOn (Finset.mem_inter.mp hx).2
    (Finset.mem_inter.mp hy).2 hxy

/-- Possible collections of new vertices which enlarge `I` to an
`(r-1)`-face. -/
def lowerFaceExtensions (n r : ℕ) (I : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)) \ I).powersetCard (r - 1 - I.card)

lemma card_lowerFaceExtensions_le_pow
    (I : Finset (Fin n)) :
    (lowerFaceExtensions n r I).card ≤ n ^ (r - 1 - I.card) := by
  calc
    (lowerFaceExtensions n r I).card =
        Nat.choose ((Finset.univ : Finset (Fin n)) \ I).card
          (r - 1 - I.card) := by
      simp [lowerFaceExtensions]
    _ ≤ ((Finset.univ : Finset (Fin n)) \ I).card ^
        (r - 1 - I.card) := Nat.choose_le_pow _ _
    _ ≤ n ^ (r - 1 - I.card) := by
      apply Nat.pow_le_pow_left
      exact (Finset.card_le_card (Finset.sdiff_subset)).trans_eq (by simp)

lemma exists_lowerFaceExtension
    (A I : Finset (Fin n))
    (huniform : A.card = r) (hIA : I ⊆ A) (hI : I.card < r) :
    ∃ T ∈ lowerFaceExtensions n r I,
      I ∪ T ⊆ A ∧ (I ∪ T).card = r - 1 := by
  have hdiff : (A \ I).card = r - I.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIA, huniform]
  have hsize : r - 1 - I.card ≤ (A \ I).card := by
    rw [hdiff]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hsize
  have hTI : Disjoint I T := by
    exact Finset.disjoint_of_subset_right hTsub Finset.disjoint_sdiff
  have hTuniv : T ⊆ (Finset.univ : Finset (Fin n)) \ I := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
      fun hxI ↦ Finset.disjoint_left.mp hTI hxI hx⟩
  refine ⟨T, Finset.mem_powersetCard.mpr ⟨hTuniv, hTcard⟩, ?_, ?_⟩
  · exact Finset.union_subset hIA (hTsub.trans Finset.sdiff_subset)
  · rw [Finset.card_union_of_disjoint hTI, hTcard]
    omega

/-- A bound on all `(r-1)`-face degrees propagates to every smaller face,
with one factor of `n` per missing vertex. -/
theorem localDegree_le_pow_mul_of_codimOne
    (host : Finset (Finset (Fin n)))
    (huniform : ∀ A ∈ host, A.card = r)
    (I : Finset (Fin n)) (hI : I.card < r)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D) :
    Reserve.localDegree host I ≤ n ^ (r - 1 - I.card) * D := by
  let extensions := lowerFaceExtensions n r I
  let fiber (T : Finset (Fin n)) :=
    host.filter fun A ↦ I ∪ T ⊆ A
  have hsubset : (host.filter fun A ↦ I ⊆ A) ⊆
      extensions.biUnion fiber := by
    intro A hA
    have hm := Finset.mem_filter.mp hA
    obtain ⟨T, hT, hsub, hcard⟩ :=
      exists_lowerFaceExtension A I (huniform A hm.1) hm.2 hI
    exact Finset.mem_biUnion.mpr
      ⟨T, hT, Finset.mem_filter.mpr ⟨hm.1, hsub⟩⟩
  have hfiber : ∀ T ∈ extensions, (fiber T).card ≤ D := by
    intro T hT
    have hTdata := Finset.mem_powersetCard.mp hT
    have hdisjoint : Disjoint I T := by
      exact Finset.disjoint_of_subset_right hTdata.1 Finset.disjoint_sdiff
    have hcard : (I ∪ T).card = r - 1 := by
      rw [Finset.card_union_of_disjoint hdisjoint, hTdata.2]
      omega
    exact hmax (I ∪ T) hcard
  calc
    Reserve.localDegree host I ≤ (extensions.biUnion fiber).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ T ∈ extensions, (fiber T).card := Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ extensions, D := by
      apply Finset.sum_le_sum
      exact hfiber
    _ = extensions.card * D := by simp
    _ ≤ n ^ (r - 1 - I.card) * D :=
      Nat.mul_le_mul_right D (card_lowerFaceExtensions_le_pow I)

/-- Substituting the codimension-one host-degree cap into the bad-embedding
union bound. -/
theorem card_embeddingsMeeting_le_of_codimOne
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (host : Finset (Finset (Fin n)))
    (huniform : ∀ g ∈ host, g.card = r)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D) :
    (embeddingsMeeting P request host).card ≤
      ∑ e ∈ P.freeEdges,
        (n ^ (r - 1 - (e ∩ P.root).card) * D) *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) := by
  calc
    (embeddingsMeeting P request host).card ≤
      ∑ e ∈ P.freeEdges,
        (compatibleHostEdges P.root request e host).card *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) :=
      card_embeddingsMeeting_le_sum_local P request host huniform
    _ ≤ ∑ e ∈ P.freeEdges,
        (n ^ (r - 1 - (e ∩ P.root).card) * D) *
          (2 ^ r *
            (r ^ (e \ P.root).card *
              n ^ (v - (P.root.card + (e \ P.root).card)))) := by
      apply Finset.sum_le_sum
      intro e he
      apply Nat.mul_le_mul_right
      rw [card_compatibleHostEdges]
      have heData := Finset.mem_filter.mp he
      have hrootCard :
          (rootPartImage P.root request e).card = (e ∩ P.root).card :=
        card_rootPartImage P.root request e
      have hnotSub : ¬e ⊆ P.root := heData.2
      have hinterLt : (e ∩ P.root).card < e.card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        exact ⟨Finset.inter_subset_left, by
          intro hEq
          apply hnotSub
          intro x hx
          have : x ∈ e ∩ P.root := hEq.symm ▸ hx
          exact (Finset.mem_inter.mp this).2⟩
      have hIlt : (rootPartImage P.root request e).card < r := by
        rw [hrootCard]
        simpa [P.uniform e heData.1] using hinterLt
      exact (localDegree_le_pow_mul_of_codimOne host huniform
        (rootPartImage P.root request e) hIlt D hmax).trans_eq (by
          rw [hrootCard])

/-- The explicit loss term contributed by an `r`-uniform host of maximum
`(r-1)`-degree `D`. -/
def codimOneMeetingBound (P : RootedPattern v r) (n D : ℕ) : ℕ :=
  ∑ e ∈ P.freeEdges,
    (n ^ (r - 1 - (e ∩ P.root).card) * D) *
      (2 ^ r *
        (r ^ (e \ P.root).card *
          n ^ (v - (P.root.card + (e \ P.root).card))))

/-- Concrete legal-extension denominator after subtracting the losses from
the fixed forbidden host and the already used host. -/
theorem codimOneMeetingBound_sub_le_card_legalEmbeddings
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n))
    (Dfixed Dused : ℕ)
    (hfixedUniform : ∀ g ∈ forbidden, g.card = r)
    (husedUniform : ∀ g ∈ usedEdges P history, g.card = r)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (husedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree (usedEdges P history) J ≤ Dused) :
    (n - P.root.card).descFactorial (v - P.root.card) -
        codimOneMeetingBound P n Dfixed -
        codimOneMeetingBound P n Dused ≤
      (legalEmbeddings P request forbidden history).card := by
  have hlower := descFactorial_sub_meeting_le_card_legalEmbeddings
    P request forbidden history
  have hfixed := card_embeddingsMeeting_le_of_codimOne P
    (request history.length) forbidden hfixedUniform Dfixed hfixedMax
  have hused := card_embeddingsMeeting_le_of_codimOne P
    (request history.length) (usedEdges P history) husedUniform Dused husedMax
  change (embeddingsMeeting P (request history.length) forbidden).card ≤
      codimOneMeetingBound P n Dfixed at hfixed
  change (embeddingsMeeting P (request history.length)
      (usedEdges P history)).card ≤ codimOneMeetingBound P n Dused at hused
  omega

/-- The legal embeddings producing one load form a subset of the fixed-root
embedding family counted above. -/
theorem card_legalEmbeddings_loadHit_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (target : LoadTarget v n) (history : List (Fin v ↪ Fin n)) :
    ((legalEmbeddings P request forbidden history).filter
      fun φ ↦ loadHit P target history φ).card ≤
      target.2.card ^ (freePart P target.1).card *
        n ^ (v - (P.root.card + (freePart P target.1).card)) := by
  classical
  by_cases hedge : target.1 ∈ P.freeEdges
  · have hdisjoint : Disjoint P.root (freePart P target.1) := by
      apply Finset.disjoint_left.mpr
      intro x hxroot hx
      exact (Finset.mem_sdiff.mp hx).2 hxroot
    calc
      ((legalEmbeddings P request forbidden history).filter
          fun φ ↦ loadHit P target history φ).card ≤
          (constrainedEmbeddings P.root (freePart P target.1)
            (request history.length) target.2).card := by
        apply Finset.card_le_card
        intro φ hφ
        have hm := Finset.mem_filter.mp hφ
        have hlegal := mem_legalEmbeddings.mp hm.1
        have hhit := (loadHit_eq_true_iff P target history φ).mp (by
          simpa using hm.2)
        exact mem_constrainedEmbeddings.mpr ⟨hlegal.1, hhit.2⟩
      _ ≤ _ := card_embeddings_extending_mapEdge_le P.root
        (freePart P target.1) hdisjoint (request history.length) target.2
  · have hempty :
        (legalEmbeddings P request forbidden history).filter
          (fun φ ↦ loadHit P target history φ) = ∅ := by
      ext φ
      simp [loadHit, hedge]
    rw [hempty]
    simp

/-- Numerator bound for an arbitrary nonempty selection of free vertices. -/
theorem card_legalEmbeddings_partialLoadHit_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (target : RelevantPartialLoadTarget P n)
    (history : List (Fin v ↪ Fin n)) :
    ((legalEmbeddings P request forbidden history).filter
      fun φ ↦ partialLoadHit P target history φ).card ≤
      target.1.image.card ^ target.1.vertices.card *
        n ^ (v - (P.root.card + target.1.vertices.card)) := by
  have hvertices := target.2.2.2.1
  have hdisjoint : Disjoint P.root target.1.vertices := by
    apply Finset.disjoint_left.mpr
    intro x hxroot hxvertices
    have hxFree : x ∈ freePart P target.1.edge := hvertices hxvertices
    exact (Finset.mem_sdiff.mp hxFree).2 hxroot
  calc
    ((legalEmbeddings P request forbidden history).filter
        fun φ ↦ partialLoadHit P target history φ).card ≤
        (constrainedEmbeddings P.root target.1.vertices
          (request history.length) target.1.image).card := by
      apply Finset.card_le_card
      intro φ hφ
      have hm := Finset.mem_filter.mp hφ
      have hlegal := mem_legalEmbeddings.mp hm.1
      have hhit := (partialLoadHit_eq_true_iff P target history φ).mp (by
        simpa using hm.2)
      exact mem_constrainedEmbeddings.mpr ⟨hlegal.1, hhit⟩
    _ ≤ _ := card_embeddings_extending_mapEdge_le P.root
      target.1.vertices hdisjoint (request history.length) target.1.image

/-- A legal random-greedy path is a sequence of root-respecting embeddings
whose new edge families avoid the forbidden graph and every earlier family. -/
def IsLegalEmbeddingPath (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n))) :
    List (Fin v ↪ Fin n) → List (Fin v ↪ Fin n) → Prop :=
  FollowsLegal (legalEmbeddings P request forbidden)

/-- Along a legal path starting from the empty history, every indexed
exceptional witness is already visible in the prescribed root schedule. -/
theorem indexedEmptyFreeWitnessPairs_subset_scheduled
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (path : List (Fin v ↪ Fin n)) (J : Finset (Fin n))
    (hlegal : IsLegalEmbeddingPath P request forbidden [] path) :
    indexedEmptyFreeWitnessPairs P path J ⊆
      scheduledRootWitnessPairs P request path.length J := by
  intro z hz
  rcases z with ⟨i, e⟩
  have hzEmpty := Finset.mem_filter.mp hz
  have hzUsed := Finset.mem_filter.mp hzEmpty.1
  have hzProduct := Finset.mem_product.mp hzUsed.1
  have hstep := FollowsLegal.get_mem
    (legalEmbeddings P request forbidden) hlegal i
  have hextPrefix := (mem_legalEmbeddings.mp hstep).1
  have hext : ExtendsRequest P.root (request i.1) (path.get i) := by
    simpa using hextPrefix
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i, hzProduct.2⟩, ?_⟩
  intro y hy
  have hyMap : y ∈ mapEdge (path.get i) e := hzUsed.2 hy
  obtain ⟨x, hxEdge, rfl⟩ := Finset.mem_map.mp hyMap
  have hxRoot : x ∈ P.root := by
    by_contra hxNotRoot
    have hxFree : x ∈ freePart P e :=
      Finset.mem_sdiff.mpr ⟨hxEdge, hxNotRoot⟩
    have hxSelected :
        x ∈ selectedFreeVertices P (path.get i) e J :=
      Finset.mem_filter.mpr ⟨hxFree, hy⟩
    exact hzEmpty.2 ⟨x, hxSelected⟩
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_inter.mpr ⟨hxEdge, hxRoot⟩,
      (hext x hxRoot).symm⟩

theorem card_indexedEmptyFreeWitnessPairs_le_scheduled
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (path : List (Fin v ↪ Fin n)) (J : Finset (Fin n))
    (hlegal : IsLegalEmbeddingPath P request forbidden [] path) :
    (indexedEmptyFreeWitnessPairs P path J).card ≤
      (scheduledRootWitnessPairs P request path.length J).card :=
  Finset.card_le_card
    (indexedEmptyFreeWitnessPairs_subset_scheduled
      P request forbidden path J hlegal)

/-- Complete deterministic load conclusion of the rooted extension lemma:
root-schedule load plus the bounded family of partial induced loads controls
the used host's local degree. -/
theorem localDegree_usedEdges_le_scheduled_add_uniformCap
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (path : List (Fin v ↪ Fin n)) (J : Finset (Fin n)) (C : ℕ)
    (hlegal : IsLegalEmbeddingPath P request forbidden [] path)
    (hcaps : ∀ target : RelevantPartialLoadTarget P n,
      pathHits (partialLoadHit P target) [] path < C) :
    Reserve.localDegree (usedEdges P path) J ≤
      (scheduledRootWitnessPairs P request path.length J).card +
        (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C := by
  calc
    Reserve.localDegree (usedEdges P path) J ≤
        (indexedEmptyFreeWitnessPairs P path J).card +
          (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C :=
      localDegree_usedEdges_le_indexedEmpty_add_uniformCap
        P [] path J C hcaps
    _ ≤ (scheduledRootWitnessPairs P request path.length J).card +
          (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C :=
      Nat.add_le_add_right
        (card_indexedEmptyFreeWitnessPairs_le_scheduled
          P request forbidden path J hlegal) _

theorem localDegree_usedEdges_le_of_rootSchedule_and_uniformCap
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (depth D C : ℕ)
    (hroot : IsRootScheduleBoundedUpTo P request depth D)
    (path : List (Fin v ↪ Fin n)) (hlen : path.length ≤ depth)
    (hlegal : IsLegalEmbeddingPath P request forbidden [] path)
    (hcaps : ∀ target : RelevantPartialLoadTarget P n,
      pathHits (partialLoadHit P target) [] path < C)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    Reserve.localDegree (usedEdges P path) J ≤
      D + (P.freeEdges.card * 2 ^ v * 2 ^ (r - 1)) * C := by
  calc
    Reserve.localDegree (usedEdges P path) J ≤
        (scheduledRootWitnessPairs P request path.length J).card +
          (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C :=
      localDegree_usedEdges_le_scheduled_add_uniformCap
        P request forbidden path J C hlegal hcaps
    _ ≤ D + (P.freeEdges.card * 2 ^ v * 2 ^ J.card) * C :=
      Nat.add_le_add_right (hroot path.length hlen J hJ) _
    _ = D + (P.freeEdges.card * 2 ^ v * 2 ^ (r - 1)) * C := by
      rw [hJ]

/-- Specialized random-greedy extension theorem.  Its hypotheses are the
exact finite estimates proved in the counting layer: nonempty legal sets and
a numerator bound for every induced load. -/
theorem exists_legalEmbeddingPath_of_count_bounds
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (hnonempty : ∀ history,
      (legalEmbeddings P request forbidden history).Nonempty)
    (p : LoadTarget v n → ℕ → ℝ)
    (hp : ∀ target i, 0 ≤ p target i)
    (hcount : ∀ target history,
      (((legalEmbeddings P request forbidden history).filter
        fun φ ↦ loadHit P target history φ).card : ℝ) ≤
          p target history.length *
            (legalEmbeddings P request forbidden history).card)
    {t : ℝ} (ht : 0 ≤ t)
    {history : List (Fin v ↪ Fin n)} {depth : ℕ}
    {cap : LoadTarget v n → ℕ}
    (hsmall : (∑ target : LoadTarget v n,
      Real.exp (-t * cap target) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (p target) history.length depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden history path ∧
      ∀ target : LoadTarget v n,
        pathHits (loadHit P target) history path < cap target := by
  apply exists_legal_path_with_load_caps
    (legalEmbeddings P request forbidden) hnonempty
    (loadHit P) p hp ht
  · intro target hist
    rw [sum_uniformStep_mul_hitBit
      (legalEmbeddings P request forbidden) hist (hnonempty hist)]
    have hcardPos : (0 : ℝ) <
        (legalEmbeddings P request forbidden hist).card := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty hist)
    exact (div_le_iff₀ hcardPos).2 (hcount target hist)
  · exact hsmall

/-- Stopping-time version of the rooted extension theorem.  The denominator
and numerator estimates are needed only while `good` holds. -/
theorem exists_legalEmbeddingPath_until_bad_of_count_bounds
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (good : List (Fin v ↪ Fin n) → Prop) [DecidablePred good]
    (hnonempty : ∀ history, good history →
      (legalEmbeddings P request forbidden history).Nonempty)
    (p : LoadTarget v n → ℕ → ℝ)
    (hp : ∀ target i, 0 ≤ p target i)
    (hcount : ∀ target history, good history →
      (((legalEmbeddings P request forbidden history).filter
        fun φ ↦ loadHit P target history φ).card : ℝ) ≤
          p target history.length *
            (legalEmbeddings P request forbidden history).card)
    {t : ℝ} (ht : 0 ≤ t)
    {history : List (Fin v ↪ Fin n)} {depth : ℕ}
    {cap : LoadTarget v n → ℕ}
    (hgood : ∀ pref : List (Fin v ↪ Fin n), pref.length ≤ depth →
      (∀ target : LoadTarget v n,
        pathHits (loadHit P target) history pref < cap target) →
      IsLegalEmbeddingPath P request forbidden history pref →
      good (history ++ pref))
    (hsmall : (∑ target : LoadTarget v n,
      Real.exp (-t * cap target) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (p target) history.length depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden history path ∧
      ∀ target : LoadTarget v n,
        pathHits (loadHit P target) history path < cap target := by
  apply exists_legal_path_with_load_caps_until_bad
    (legalEmbeddings P request forbidden) good (loadHit P) p hp ht
    hnonempty
  · intro target hist hgoodHist
    rw [sum_uniformStep_mul_hitBit
      (legalEmbeddings P request forbidden) hist (hnonempty hist hgoodHist)]
    have hcardPos : (0 : ℝ) <
        (legalEmbeddings P request forbidden hist).card := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty hist hgoodHist)
    exact (div_le_iff₀ hcardPos).2 (hcount target hist hgoodHist)
  · exact hgood
  · exact hsmall

/-- Partial-load stopping-time theorem used by the actual rooted extension
lemma.  The target type is polynomial-sized for a fixed pattern. -/
theorem exists_legalEmbeddingPath_until_bad_of_partialCount_bounds
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (good : List (Fin v ↪ Fin n) → Prop) [DecidablePred good]
    (hnonempty : ∀ history, good history →
      (legalEmbeddings P request forbidden history).Nonempty)
    (p : RelevantPartialLoadTarget P n → ℕ → ℝ)
    (hp : ∀ target i, 0 ≤ p target i)
    (hcount : ∀ target history, good history →
      (((legalEmbeddings P request forbidden history).filter
        fun φ ↦ partialLoadHit P target history φ).card : ℝ) ≤
          p target history.length *
            (legalEmbeddings P request forbidden history).card)
    {t : ℝ} (ht : 0 ≤ t)
    {history : List (Fin v ↪ Fin n)} {depth : ℕ}
    {cap : RelevantPartialLoadTarget P n → ℕ}
    (hgood : ∀ pref : List (Fin v ↪ Fin n), pref.length ≤ depth →
      (∀ target : RelevantPartialLoadTarget P n,
        pathHits (partialLoadHit P target) history pref < cap target) →
      IsLegalEmbeddingPath P request forbidden history pref →
      good (history ++ pref))
    (hsmall : (∑ target : RelevantPartialLoadTarget P n,
      Real.exp (-t * cap target) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (p target) history.length depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden history path ∧
      ∀ target : RelevantPartialLoadTarget P n,
        pathHits (partialLoadHit P target) history path < cap target := by
  apply exists_legal_path_with_load_caps_until_bad
    (legalEmbeddings P request forbidden) good (partialLoadHit P) p hp ht
    hnonempty
  · intro target hist hgoodHist
    rw [sum_uniformStep_mul_hitBit
      (legalEmbeddings P request forbidden) hist (hnonempty hist hgoodHist)]
    have hcardPos : (0 : ℝ) <
        (legalEmbeddings P request forbidden hist).card := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty hist hgoodHist)
    exact (div_le_iff₀ hcardPos).2 (hcount target hist hgoodHist)
  · exact hgood
  · exact hsmall

/-! ## Closed finite rooted-extension theorem -/

def partialLoadNumerator (P : RootedPattern v r) (n : ℕ)
    (target : RelevantPartialLoadTarget P n) : ℕ :=
  target.1.image.card ^ target.1.vertices.card *
    n ^ (v - (P.root.card + target.1.vertices.card))

def rootedUsedDegreeCap (P : RootedPattern v r)
    (Droot C : ℕ) : ℕ :=
  Droot + (P.freeEdges.card * 2 ^ v * 2 ^ (r - 1)) * C

def rootedLegalLowerBound (P : RootedPattern v r)
    (n Dfixed Droot C : ℕ) : ℕ :=
  (n - P.root.card).descFactorial (v - P.root.card) -
    codimOneMeetingBound P n Dfixed -
    codimOneMeetingBound P n (rootedUsedDegreeCap P Droot C)

/-- Fully assembled finite rooted-extension lemma.  Its remaining numerical
hypothesis is exactly the explicit exponential union bound; all history-
dependent legality and denominator estimates are discharged here. -/
theorem exists_legalEmbeddingPath_of_rootSchedule
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (depth Dfixed Droot C : ℕ)
    (hfixedUniform : ∀ g ∈ forbidden, g.card = r)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hroot : IsRootScheduleBoundedUpTo P request depth Droot)
    (hLpos : 0 < rootedLegalLowerBound P n Dfixed Droot C)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall :
      (∑ target : RelevantPartialLoadTarget P n,
        Real.exp (-t * C) *
          Real.exp ((Real.exp t - 1) *
            adaptiveBudget
              (fun _ ↦ (partialLoadNumerator P n target : ℝ) /
                rootedLegalLowerBound P n Dfixed Droot C)
              0 depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden [] path ∧
      ∀ target : RelevantPartialLoadTarget P n,
        pathHits (partialLoadHit P target) [] path < C := by
  classical
  let Dused := rootedUsedDegreeCap P Droot C
  let L := rootedLegalLowerBound P n Dfixed Droot C
  let good : List (Fin v ↪ Fin n) → Prop := fun history ↦
    history.length ≤ depth ∧
      ∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (usedEdges P history) J ≤ Dused
  letI : DecidablePred good := Classical.decPred _
  have hnonempty : ∀ history, good history →
      (legalEmbeddings P request forbidden history).Nonempty := by
    intro history hgood
    apply Finset.card_pos.mp
    apply hLpos.trans_le
    change L ≤ (legalEmbeddings P request forbidden history).card
    apply codimOneMeetingBound_sub_le_card_legalEmbeddings
      P request forbidden history Dfixed Dused hfixedUniform
      (fun g hg ↦ usedEdges_uniform P history hg) hfixedMax
    exact hgood.2
  let probability : RelevantPartialLoadTarget P n → ℕ → ℝ :=
    fun target _ ↦ (partialLoadNumerator P n target : ℝ) / L
  have hp : ∀ target i, 0 ≤ probability target i := by
    intro target i
    positivity
  have hcount : ∀ target history, good history →
      (((legalEmbeddings P request forbidden history).filter
        fun φ ↦ partialLoadHit P target history φ).card : ℝ) ≤
          probability target history.length *
            (legalEmbeddings P request forbidden history).card := by
    intro target history hgood
    have hupperNat := card_legalEmbeddings_partialLoadHit_le
      P request forbidden target history
    have hupperReal :
        (((legalEmbeddings P request forbidden history).filter
          fun φ ↦ partialLoadHit P target history φ).card : ℝ) ≤
            partialLoadNumerator P n target := by
      exact_mod_cast hupperNat
    have hlowerNat : L ≤
        (legalEmbeddings P request forbidden history).card := by
      apply codimOneMeetingBound_sub_le_card_legalEmbeddings
        P request forbidden history Dfixed Dused hfixedUniform
        (fun g hg ↦ usedEdges_uniform P history hg) hfixedMax
      exact hgood.2
    have hlowerReal : (L : ℝ) ≤
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast hlowerNat
    have hLReal : (0 : ℝ) < L := by exact_mod_cast hLpos
    calc
      (((legalEmbeddings P request forbidden history).filter
          fun φ ↦ partialLoadHit P target history φ).card : ℝ) ≤
          partialLoadNumerator P n target := hupperReal
      _ = probability target history.length * L := by
        dsimp [probability]
        field_simp
      _ ≤ probability target history.length *
          (legalEmbeddings P request forbidden history).card := by
        exact mul_le_mul_of_nonneg_left hlowerReal (hp target history.length)
  apply exists_legalEmbeddingPath_until_bad_of_partialCount_bounds
    P request forbidden good hnonempty probability hp hcount ht
  · intro pref hlen hcaps hlegal
    change good ([] ++ pref)
    constructor
    · simpa using hlen
    · intro J hJ
      simpa [Dused, rootedUsedDegreeCap] using
        (localDegree_usedEdges_le_of_rootSchedule_and_uniformCap
          P request forbidden depth Droot C hroot pref hlen
          (by simpa using hlegal) hcaps J hJ)
  · simpa [probability, L] using hsmall

def rootedFaceLegalLowerBound (P : RootedPattern v r)
    (n Dfixed C : ℕ) : ℕ :=
  (n - P.root.card).descFactorial (v - P.root.card) -
    codimOneMeetingBound P n Dfixed -
    codimOneMeetingBound P n (P.freeEdges.card * C)

/-- Source-faithful finite rooted-extension theorem using full
`(r-1)`-face loads.  The adaptive budget now retains the dependence on the
scheduled root request at each step. -/
theorem exists_legalEmbeddingPath_of_faceLoads
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (depth Dfixed C : ℕ)
    (hfixedUniform : ∀ g ∈ forbidden, g.card = r)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hLpos : 0 < rootedFaceLegalLowerBound P n Dfixed C)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall :
      (∑ target : RelevantFaceLoadTarget P n,
        Real.exp (-t * C) *
          Real.exp ((Real.exp t - 1) *
            adaptiveBudget
              (fun i ↦
                (faceLoadNumeratorAt P n (request i) target : ℝ) /
                  rootedFaceLegalLowerBound P n Dfixed C)
              0 depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden [] path ∧
      ∀ target : RelevantFaceLoadTarget P n,
        pathHits (faceLoadHit P target) [] path < C := by
  classical
  let Dused := P.freeEdges.card * C
  let L := rootedFaceLegalLowerBound P n Dfixed C
  let good : List (Fin v ↪ Fin n) → Prop := fun history ↦
    history.length ≤ depth ∧
      ∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (usedEdges P history) J ≤ Dused
  letI : DecidablePred good := Classical.decPred _
  have hnonempty : ∀ history, good history →
      (legalEmbeddings P request forbidden history).Nonempty := by
    intro history hgood
    apply Finset.card_pos.mp
    apply hLpos.trans_le
    change L ≤ (legalEmbeddings P request forbidden history).card
    apply codimOneMeetingBound_sub_le_card_legalEmbeddings
      P request forbidden history Dfixed Dused hfixedUniform
      (fun g hg ↦ usedEdges_uniform P history hg) hfixedMax
    exact hgood.2
  let probability : RelevantFaceLoadTarget P n → ℕ → ℝ :=
    fun target i ↦ (faceLoadNumeratorAt P n (request i) target : ℝ) / L
  have hp : ∀ target i, 0 ≤ probability target i := by
    intro target i
    positivity
  have hcount : ∀ target history, good history →
      (((legalEmbeddings P request forbidden history).filter
        fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
          probability target history.length *
            (legalEmbeddings P request forbidden history).card := by
    intro target history hgood
    have hupperNat := card_legalEmbeddings_faceLoadHit_le
      P request forbidden target history
    have hupperReal :
        (((legalEmbeddings P request forbidden history).filter
          fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
            faceLoadNumeratorAt P n (request history.length) target := by
      exact_mod_cast hupperNat
    have hlowerNat : L ≤
        (legalEmbeddings P request forbidden history).card := by
      apply codimOneMeetingBound_sub_le_card_legalEmbeddings
        P request forbidden history Dfixed Dused hfixedUniform
        (fun g hg ↦ usedEdges_uniform P history hg) hfixedMax
      exact hgood.2
    have hlowerReal : (L : ℝ) ≤
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast hlowerNat
    have hLReal : (0 : ℝ) < L := by exact_mod_cast hLpos
    calc
      (((legalEmbeddings P request forbidden history).filter
          fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
          faceLoadNumeratorAt P n (request history.length) target := hupperReal
      _ = probability target history.length * L := by
        dsimp [probability]
        field_simp
      _ ≤ probability target history.length *
          (legalEmbeddings P request forbidden history).card := by
        exact mul_le_mul_of_nonneg_left hlowerReal (hp target history.length)
  apply exists_legal_path_with_load_caps_until_bad
    (legalEmbeddings P request forbidden) good (faceLoadHit P)
    probability hp ht hnonempty
  · intro target history hgoodHistory
    rw [sum_uniformStep_mul_hitBit
      (legalEmbeddings P request forbidden) history
        (hnonempty history hgoodHistory)]
    have hcardPos : (0 : ℝ) <
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty history hgoodHistory)
    exact (div_le_iff₀ hcardPos).2 (hcount target history hgoodHistory)
  · intro pref hlen hcaps hlegal
    constructor
    · simpa using hlen
    · intro J hJ
      simpa [Dused] using
        (localDegree_usedEdges_le_faceLoadCaps P [] pref J hJ C hcaps)
  · simpa [probability, L] using hsmall

/-- The full-face path theorem with an additional finite family of
history-dependent counters.  The extra observables do not participate in
legality; they are concentrated on the same random-greedy path. -/
theorem exists_legalEmbeddingPath_of_faceLoads_and_extra
    {β : Type*} [Fintype β]
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (depth Dfixed C : ℕ)
    (hfixedUniform : ∀ g ∈ forbidden, g.card = r)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hLpos : 0 < rootedFaceLegalLowerBound P n Dfixed C)
    (extraHit : β → List (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Bool)
    (extraProbability : β → ℕ → ℝ)
    (hextraProbability : ∀ b i, 0 ≤ extraProbability b i)
    (extraCap : β → ℕ)
    (hextraMean : ∀ b history,
      history.length ≤ depth →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (usedEdges P history) J ≤
          P.freeEdges.card * C) →
      (∑ φ : Fin v ↪ Fin n,
        uniformStep (legalEmbeddings P request forbidden) history φ *
          hitBit (extraHit b) history φ) ≤
        extraProbability b history.length)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall :
      (∑ target : Sum (RelevantFaceLoadTarget P n) β,
        Real.exp (-t *
          (match target with
          | Sum.inl _ => C
          | Sum.inr b => extraCap b)) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget
            (match target with
            | Sum.inl face => fun i ↦
                (faceLoadNumeratorAt P n (request i) face : ℝ) /
                  rootedFaceLegalLowerBound P n Dfixed C
            | Sum.inr b => extraProbability b)
            0 depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden [] path ∧
      (∀ target : RelevantFaceLoadTarget P n,
        pathHits (faceLoadHit P target) [] path < C) ∧
      ∀ b : β, pathHits (extraHit b) [] path < extraCap b := by
  classical
  let Dused := P.freeEdges.card * C
  let L := rootedFaceLegalLowerBound P n Dfixed C
  let good : List (Fin v ↪ Fin n) → Prop := fun history ↦
    history.length ≤ depth ∧
      ∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (usedEdges P history) J ≤ Dused
  letI : DecidablePred good := Classical.decPred _
  let hit : Sum (RelevantFaceLoadTarget P n) β →
      List (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Bool
    | Sum.inl target => faceLoadHit P target
    | Sum.inr b => extraHit b
  let probability : Sum (RelevantFaceLoadTarget P n) β → ℕ → ℝ
    | Sum.inl target => fun i ↦
        (faceLoadNumeratorAt P n (request i) target : ℝ) / L
    | Sum.inr b => extraProbability b
  let cap : Sum (RelevantFaceLoadTarget P n) β → ℕ
    | Sum.inl _ => C
    | Sum.inr b => extraCap b
  have hnonempty : ∀ history, good history →
      (legalEmbeddings P request forbidden history).Nonempty := by
    intro history hgood
    apply Finset.card_pos.mp
    apply hLpos.trans_le
    change L ≤ (legalEmbeddings P request forbidden history).card
    apply codimOneMeetingBound_sub_le_card_legalEmbeddings
      P request forbidden history Dfixed Dused hfixedUniform
      (fun g hg ↦ usedEdges_uniform P history hg) hfixedMax
    exact hgood.2
  have hp : ∀ target i, 0 ≤ probability target i := by
    intro target i
    rcases target with target | b
    · dsimp [probability]
      positivity
    · exact hextraProbability b i
  have hfaceMean (target : RelevantFaceLoadTarget P n) (history)
      (hgood : good history) :
      (∑ φ : Fin v ↪ Fin n,
        uniformStep (legalEmbeddings P request forbidden) history φ *
          hitBit (faceLoadHit P target) history φ) ≤
        probability (Sum.inl target) history.length := by
    rw [sum_uniformStep_mul_hitBit
      (legalEmbeddings P request forbidden) history
        (hnonempty history hgood)]
    have hupperNat := card_legalEmbeddings_faceLoadHit_le
      P request forbidden target history
    have hupperReal :
        (((legalEmbeddings P request forbidden history).filter
          fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
            faceLoadNumeratorAt P n (request history.length) target := by
      exact_mod_cast hupperNat
    have hlowerNat : L ≤
        (legalEmbeddings P request forbidden history).card := by
      apply codimOneMeetingBound_sub_le_card_legalEmbeddings
        P request forbidden history Dfixed Dused hfixedUniform
        (fun g hg ↦ usedEdges_uniform P history hg) hfixedMax
      exact hgood.2
    have hlowerReal : (L : ℝ) ≤
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast hlowerNat
    have hLReal : (0 : ℝ) < L := by exact_mod_cast hLpos
    have hcardPos : (0 : ℝ) <
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty history hgood)
    apply (div_le_iff₀ hcardPos).2
    calc
      (((legalEmbeddings P request forbidden history).filter
          fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
          faceLoadNumeratorAt P n (request history.length) target := hupperReal
      _ = probability (Sum.inl target) history.length * L := by
        dsimp [probability]
        field_simp [ne_of_gt hLReal]
      _ ≤ probability (Sum.inl target) history.length *
          (legalEmbeddings P request forbidden history).card := by
        exact mul_le_mul_of_nonneg_left hlowerReal
          (hp (Sum.inl target) history.length)
  obtain ⟨path, hlen, hlegal, hcaps⟩ :=
    exists_legal_path_with_load_caps_until_bad
      (legalEmbeddings P request forbidden) good hit probability hp ht
      hnonempty (history := []) (depth := depth) (cap := cap) (by
        intro target history hgood
        rcases target with target | b
        · exact hfaceMean target history hgood
        · exact hextraMean b history hgood.1 (by
            simpa [Dused] using hgood.2)) (by
        intro pref hpref hloads hfollow
        constructor
        · simpa using hpref
        · intro J hJ
          simpa [Dused] using
            (localDegree_usedEdges_le_faceLoadCaps P [] pref J hJ C
              (fun target ↦ hloads (Sum.inl target)))) (by
        simpa [probability, cap, L] using hsmall)
  refine ⟨path, hlen, hlegal, ?_, ?_⟩
  · intro target
    exact hcaps (Sum.inl target)
  · intro b
    exact hcaps (Sum.inr b)

/-- Denominator/numerator form matching the actual embedding count: at
least `L` legal embeddings and at most `U target` embeddings producing one
specified induced load. -/
theorem exists_legalEmbeddingPath_of_card_bounds
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (L : ℕ) (hL : 0 < L)
    (U : LoadTarget v n → ℕ)
    (hlower : ∀ history,
      L ≤ (legalEmbeddings P request forbidden history).card)
    (hupper : ∀ target history,
      ((legalEmbeddings P request forbidden history).filter
        fun φ ↦ loadHit P target history φ).card ≤ U target)
    {t : ℝ} (ht : 0 ≤ t)
    {history : List (Fin v ↪ Fin n)} {depth : ℕ}
    {cap : LoadTarget v n → ℕ}
    (hsmall : (∑ target : LoadTarget v n,
      Real.exp (-t * cap target) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (fun _ ↦ (U target : ℝ) / L)
            history.length depth)) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden history path ∧
      ∀ target : LoadTarget v n,
        pathHits (loadHit P target) history path < cap target := by
  have hnonempty : ∀ hist,
      (legalEmbeddings P request forbidden hist).Nonempty := by
    intro hist
    exact Finset.card_pos.mp (hL.trans_le (hlower hist))
  apply exists_legalEmbeddingPath_of_count_bounds P request forbidden
    hnonempty (fun target _ ↦ (U target : ℝ) / L)
  · intro target i
    positivity
  · intro target hist
    have hupperReal :
        (((legalEmbeddings P request forbidden hist).filter
          fun φ ↦ loadHit P target hist φ).card : ℝ) ≤ U target := by
      exact_mod_cast hupper target hist
    have hlowerReal : (L : ℝ) ≤
        (legalEmbeddings P request forbidden hist).card := by
      exact_mod_cast hlower hist
    have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
    calc
      (((legalEmbeddings P request forbidden hist).filter
          fun φ ↦ loadHit P target hist φ).card : ℝ) ≤ U target := hupperReal
      _ = ((U target : ℝ) / L) * L := by field_simp
      _ ≤ ((U target : ℝ) / L) *
          (legalEmbeddings P request forbidden hist).card := by
        exact mul_le_mul_of_nonneg_left hlowerReal (by positivity)
  · exact ht
  · exact hsmall

/-- Every step of a legal path avoids the fixed forbidden edge family. -/
theorem IsLegalEmbeddingPath.head_disjoint_forbidden
    {φ : Fin v ↪ Fin n} {rest : List (Fin v ↪ Fin n)}
    (h : IsLegalEmbeddingPath P request forbidden history (φ :: rest)) :
    Disjoint (imageFreeEdges P φ) forbidden := by
  exact (mem_legalEmbeddings.mp h.1).2.1

/-- Every step of a legal path avoids all images used in its preceding
history. -/
theorem IsLegalEmbeddingPath.head_disjoint_used
    {φ : Fin v ↪ Fin n} {rest : List (Fin v ↪ Fin n)}
    (h : IsLegalEmbeddingPath P request forbidden history (φ :: rest)) :
    Disjoint (imageFreeEdges P φ) (usedEdges P history) := by
  exact (mem_legalEmbeddings.mp h.1).2.2

/-- Every indexed step of a legal path avoids the fixed forbidden host. -/
theorem IsLegalEmbeddingPath.get_disjoint_forbidden
    {path : List (Fin v ↪ Fin n)}
    (h : IsLegalEmbeddingPath P request forbidden [] path)
    (i : Fin path.length) :
    Disjoint (imageFreeEdges P (path.get i)) forbidden := by
  have hi := FollowsLegal.get_mem
    (legalEmbeddings P request forbidden) h i
  exact (mem_legalEmbeddings.mp (by simpa using hi)).2.1

/-- The union of all free edges used by a legal path avoids the fixed
forbidden host.  This packages the pointwise avoidance invariant in the
form needed when the whole path becomes the forbidden host for a later
allocation. -/
theorem IsLegalEmbeddingPath.usedEdges_disjoint_forbidden
    {path : List (Fin v ↪ Fin n)}
    (h : IsLegalEmbeddingPath P request forbidden [] path) :
    Disjoint (usedEdges P path) forbidden := by
  rw [Finset.disjoint_left]
  intro g hgUsed hgForbidden
  obtain ⟨φ, hφ, hgφ⟩ := Finset.mem_biUnion.mp hgUsed
  have hφList : φ ∈ path := by simpa using hφ
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hφList
  exact Finset.disjoint_left.mp (h.get_disjoint_forbidden i)
    (by simpa only [← hi] using hgφ) hgForbidden

/-- Distinct steps of a legal rooted path use pairwise disjoint free-edge
families. -/
theorem IsLegalEmbeddingPath.pairwise_disjoint
    {path : List (Fin v ↪ Fin n)}
    (hpath : IsLegalEmbeddingPath P request forbidden [] path)
    (i j : Fin path.length) (hij : i ≠ j) :
    Disjoint (imageFreeEdges P (path.get i))
      (imageFreeEdges P (path.get j)) := by
  classical
  wlog hijlt : i.1 < j.1 generalizing i j
  · have hji : j.1 < i.1 := by omega
    exact disjoint_comm.mp (this j i (Ne.symm hij) hji)
  have hjmem := FollowsLegal.get_mem
    (legalEmbeddings P request forbidden) hpath j
  have hjdis := (mem_legalEmbeddings.mp (by simpa using hjmem)).2.2
  have hiTake : path.get i ∈ path.take j.1 := by
    have hilength : i.1 < (path.take j.1).length := by
      simp only [List.length_take]
      omega
    have hm := List.getElem_mem (l := path.take j.1) hilength
    rw [List.getElem_take] at hm
    simpa [List.get_eq_getElem] using hm
  have hsub : imageFreeEdges P (path.get i) ⊆
      usedEdges P (path.take j.1) := by
    intro g hg
    apply Finset.mem_biUnion.mpr
    exact ⟨path.get i, by simpa using hiTake, hg⟩
  exact Disjoint.mono hsub Finset.Subset.rfl (disjoint_comm.mp hjdis)

end

end Erdos722.RootedEmbedding

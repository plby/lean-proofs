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
import ErdosProblems.Erdos722.RootedEmbedding
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Root-request schedule bounds

This file converts lower-face degree bounds for the list of root images into
the deterministic conditional-probability budget used by the full-face
rooted extension theorem.
-/

namespace Erdos722.RootSchedule

open Finset
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.AdaptiveChernoff

noncomputable section

/-- The first `depth` requests enumerate distinct root images in `host`. -/
def IsRootImageSchedule (root : Finset (Fin v))
    (request : ℕ → RootRequest v n root) (depth : ℕ)
    (host : Finset (Finset (Fin n))) : Prop :=
  (∀ i : Fin depth, requestImage root (request i.1) ∈ host) ∧
    Function.Injective
      (fun i : Fin depth ↦ requestImage root (request i.1))

/-- A schedule in which each root image may occur a bounded number of
times.  This is the exact interface needed to place a fixed number of
coefficient-splitting gadgets at every input clique. -/
def IsRootImageScheduleMultiplicity (root : Finset (Fin v))
    (request : ℕ → RootRequest v n root) (depth : ℕ)
    (host : Finset (Finset (Fin n))) (multiplicity : ℕ) : Prop :=
  (∀ i : Fin depth, requestImage root (request i.1) ∈ host) ∧
    ∀ Q ∈ host,
      ((Finset.univ : Finset (Fin depth)).filter fun i ↦
        requestImage root (request i.1) = Q).card ≤ multiplicity

/-- Request indices at which a fixed ground set lies in the prescribed
image of one pattern edge's root part. -/
def rootPartIndicesContaining (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (e : Finset (Fin v)) (I : Finset (Fin n)) :
    Finset (Fin depth) :=
  (Finset.univ : Finset (Fin depth)).filter fun i ↦
    I ⊆ rootPartImage P.root (request i.1) e

lemma rootPartImage_subset_requestImage
    (root : Finset (Fin v)) (request : RootRequest v n root)
    (e : Finset (Fin v)) :
    rootPartImage root request e ⊆ requestImage root request := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr
    ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩

/-- Distinct scheduled root images inject the root-part occurrence indices
into the corresponding host-degree fibre. -/
theorem card_rootPartIndicesContaining_le_localDegree
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (e : Finset (Fin v)) (I : Finset (Fin n)) :
    (rootPartIndicesContaining P request depth e I).card ≤
      Reserve.localDegree host I := by
  let f : Fin depth → Finset (Fin n) := fun i ↦
    requestImage P.root (request i.1)
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    have hiData := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hschedule.1 i, ?_⟩
    exact hiData.2.trans
      (rootPartImage_subset_requestImage P.root (request i.1) e)
  · exact hschedule.2.injOn

theorem card_rootPartIndicesContaining_le_localDegree_mul
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n))) (multiplicity : ℕ)
    (hschedule : IsRootImageScheduleMultiplicity P.root request depth
      host multiplicity)
    (e : Finset (Fin v)) (I : Finset (Fin n)) :
    (rootPartIndicesContaining P request depth e I).card ≤
      Reserve.localDegree host I * multiplicity := by
  classical
  let left := rootPartIndicesContaining P request depth e I
  let right := host.filter fun Q ↦ I ⊆ Q
  let rel : Fin depth → Finset (Fin n) → Prop := fun i Q ↦
    requestImage P.root (request i.1) = Q
  have hcount := card_mul_le_card_mul_of_relation left right rel 1 multiplicity
    (by
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      let Q := requestImage P.root (request i.1)
      have hQright : Q ∈ right := by
        apply Finset.mem_filter.mpr
        exact ⟨hschedule.1 i, hiData.2.trans
          (rootPartImage_subset_requestImage P.root (request i.1) e)⟩
      have hmem : Q ∈ right.filter (rel i) := by
        exact Finset.mem_filter.mpr ⟨hQright, rfl⟩
      exact Finset.card_pos.mpr ⟨Q, hmem⟩)
    (by
      intro Q hQ
      have hQhost : Q ∈ host := (Finset.mem_filter.mp hQ).1
      have hsub : (left.filter fun i ↦ rel i Q) ⊆
          (Finset.univ : Finset (Fin depth)).filter fun i ↦
            requestImage P.root (request i.1) = Q := by
        intro i hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      exact (Finset.card_le_card hsub).trans (hschedule.2 Q hQhost))
  simpa [left, right, Reserve.localDegree] using hcount

/-- A root-part schedule may be charged to any family of covering blocks,
not only to the full root images.  This is the form used by admissible
two-clique elimination extensions: each fixed pattern edge chooses one of
the two prescribed cliques containing its root trace. -/
theorem card_rootPartIndicesContaining_le_localDegree_mul_of_cover
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n))) (multiplicity : ℕ)
    (blockAt : Fin depth → Finset (Fin n))
    (e : Finset (Fin v))
    (hblockMem : ∀ i, blockAt i ∈ host)
    (hcover : ∀ i, rootPartImage P.root (request i.1) e ⊆ blockAt i)
    (hfiber : ∀ Q ∈ host,
      ((Finset.univ : Finset (Fin depth)).filter fun i ↦
        blockAt i = Q).card ≤ multiplicity)
    (I : Finset (Fin n)) :
    (rootPartIndicesContaining P request depth e I).card ≤
      Reserve.localDegree host I * multiplicity := by
  classical
  let left := rootPartIndicesContaining P request depth e I
  let right := host.filter fun Q ↦ I ⊆ Q
  let rel : Fin depth → Finset (Fin n) → Prop := fun i Q ↦ blockAt i = Q
  have hcount := card_mul_le_card_mul_of_relation left right rel 1 multiplicity
    (by
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      have hQright : blockAt i ∈ right := by
        apply Finset.mem_filter.mpr
        exact ⟨hblockMem i, hiData.2.trans (hcover i)⟩
      exact Finset.card_pos.mpr
        ⟨blockAt i, Finset.mem_filter.mpr ⟨hQright, rfl⟩⟩)
    (by
      intro Q hQ
      have hQhost : Q ∈ host := (Finset.mem_filter.mp hQ).1
      have hsub : (left.filter fun i ↦ rel i Q) ⊆
          (Finset.univ : Finset (Fin depth)).filter fun i ↦ blockAt i = Q := by
        intro i hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      exact (Finset.card_le_card hsub).trans (hfiber Q hQhost))
  simpa [left, right, Reserve.localDegree] using hcount

/-- A codimension-`(r-1)` degree bound controls lower degrees in an
arbitrary uniform host whose edges have at least `r-1` vertices.  Unlike
the reserve specialization, the scheduled objects may be whole rooted
blocks rather than `r`-edges. -/
theorem localDegree_le_pow_mul_of_codimOne_of_uniform
    (host : Finset (Finset (Fin n)))
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (I : Finset (Fin n)) (hI : I.card < r) (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D) :
    Reserve.localDegree host I ≤ n ^ (r - 1 - I.card) * D := by
  classical
  let left := host.filter fun g ↦ I ⊆ g
  let right :=
    (Typicality.uniformEdges n (r - 1)).filter fun J ↦ I ⊆ J
  have hcount := card_mul_le_card_mul_of_relation left right
    (fun g J : Finset (Fin n) ↦ J ⊆ g) 1 D (by
      intro g hg
      have hgData := Finset.mem_filter.mp hg
      obtain ⟨J, hIJ, hJg, hJcard⟩ :=
        Finset.exists_subsuperset_card_eq hgData.2
          (by omega : I.card ≤ r - 1)
          (by rw [huniform g hgData.1]; exact hrs)
      have hJright : J ∈ right := by
        apply Finset.mem_filter.mpr
        exact ⟨Typicality.mem_uniformEdges.mpr hJcard, hIJ⟩
      exact Finset.card_pos.mpr
        ⟨J, Finset.mem_filter.mpr ⟨hJright, hJg⟩⟩) (by
      intro J hJ
      have hJcard : J.card = r - 1 :=
        Typicality.mem_uniformEdges.mp (Finset.mem_filter.mp hJ).1
      have hsub : (left.filter fun g ↦ J ⊆ g) ⊆
          host.filter fun g ↦ J ⊆ g := by
        intro g hg
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1,
            (Finset.mem_filter.mp hg).2⟩
      exact (Finset.card_le_card hsub).trans (hmax J hJcard))
  have hright : right.card ≤ n ^ (r - 1 - I.card) := by
    rw [show right =
        ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).filter
          (I ⊆ ·) by rfl,
      Finset.card_filter_powersetCard_subset I Finset.univ (r - 1)
        (Finset.subset_univ I) (by omega)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (Nat.choose_le_pow (n - I.card) (r - 1 - I.card)).trans
      (Nat.pow_le_pow_left (Nat.sub_le n I.card) _)
  calc
    Reserve.localDegree host I = left.card := by
      rfl
    _ ≤ right.card * D := by simpa using hcount
    _ ≤ n ^ (r - 1 - I.card) * D := Nat.mul_le_mul_right D hright

/-- Codimension-one control for a finite *indexed* family of uniform
blocks.  Unlike `localDegree_le_pow_mul_of_codimOne_of_uniform`, repetitions
of the same block at different indices are retained.  This is the natural
quantity for elimination schedules, where one prescribed side may occur in
several ordered pairs. -/
theorem card_indices_containing_le_pow_mul_of_codimOne
    (blockAt : Fin depth → Finset (Fin n))
    (huniform : ∀ i, (blockAt i).card = s) (hrs : r - 1 ≤ s)
    (I : Finset (Fin n)) (hI : I.card < r) (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      ((Finset.univ : Finset (Fin depth)).filter fun i ↦
        J ⊆ blockAt i).card ≤ D) :
    ((Finset.univ : Finset (Fin depth)).filter fun i ↦
        I ⊆ blockAt i).card ≤
      n ^ (r - 1 - I.card) * D := by
  classical
  let left := (Finset.univ : Finset (Fin depth)).filter fun i ↦
    I ⊆ blockAt i
  let right :=
    (Typicality.uniformEdges n (r - 1)).filter fun J ↦ I ⊆ J
  let rel : Fin depth → Finset (Fin n) → Prop := fun i J ↦ J ⊆ blockAt i
  have hcount := card_mul_le_card_mul_of_relation left right rel 1 D (by
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      obtain ⟨J, hIJ, hJblock, hJcard⟩ :=
        Finset.exists_subsuperset_card_eq hiData.2
          (by omega : I.card ≤ r - 1)
          (by rw [huniform i]; exact hrs)
      have hJright : J ∈ right := by
        exact Finset.mem_filter.mpr
          ⟨Typicality.mem_uniformEdges.mpr hJcard, hIJ⟩
      exact Finset.card_pos.mpr
        ⟨J, Finset.mem_filter.mpr ⟨hJright, hJblock⟩⟩) (by
      intro J hJ
      have hJcard : J.card = r - 1 :=
        Typicality.mem_uniformEdges.mp (Finset.mem_filter.mp hJ).1
      have hsub : (left.filter fun i ↦ J ⊆ blockAt i) ⊆
          (Finset.univ : Finset (Fin depth)).filter fun i ↦
            J ⊆ blockAt i := by
        intro i hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      exact (Finset.card_le_card hsub).trans (hmax J hJcard))
  have hright : right.card ≤ n ^ (r - 1 - I.card) := by
    rw [show right =
        ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).filter
          (I ⊆ ·) by rfl,
      Finset.card_filter_powersetCard_subset I Finset.univ (r - 1)
        (Finset.subset_univ I) (by omega)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (Nat.choose_le_pow (n - I.card) (r - 1 - I.card)).trans
      (Nat.pow_le_pow_left (Nat.sub_le n I.card) _)
  calc
    ((Finset.univ : Finset (Fin depth)).filter fun i ↦
        I ⊆ blockAt i).card = left.card := by rfl
    _ ≤ right.card * D := by simpa using hcount
    _ ≤ n ^ (r - 1 - I.card) * D := Nat.mul_le_mul_right D hright

theorem card_rootPartIndicesContaining_le_pow_mul_of_uniform
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (e : Finset (Fin v)) (I : Finset (Fin n)) (hI : I.card < r) :
    (rootPartIndicesContaining P request depth e I).card ≤
      n ^ (r - 1 - I.card) * D := by
  exact (card_rootPartIndicesContaining_le_localDegree
    P request depth host hschedule e I).trans
      (localDegree_le_pow_mul_of_codimOne_of_uniform
        host huniform hrs I hI D hmax)

theorem card_rootPartIndicesContaining_le_pow_mul_of_uniform_mul
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n))) (multiplicity : ℕ)
    (hschedule : IsRootImageScheduleMultiplicity P.root request depth
      host multiplicity)
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (e : Finset (Fin v)) (I : Finset (Fin n)) (hI : I.card < r) :
    (rootPartIndicesContaining P request depth e I).card ≤
      n ^ (r - 1 - I.card) * (multiplicity * D) := by
  calc
    (rootPartIndicesContaining P request depth e I).card ≤
        Reserve.localDegree host I * multiplicity :=
      card_rootPartIndicesContaining_le_localDegree_mul
        P request depth host multiplicity hschedule e I
    _ ≤ (n ^ (r - 1 - I.card) * D) * multiplicity :=
      Nat.mul_le_mul_right multiplicity
        (localDegree_le_pow_mul_of_codimOne_of_uniform
          host huniform hrs I hI D hmax)
    _ = n ^ (r - 1 - I.card) * (multiplicity * D) := by ring

/-- A codimension-one host-degree bound propagates to every root-part
occurrence count with the sharp power of `n`. -/
theorem card_rootPartIndicesContaining_le_pow_mul
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (huniform : ∀ g ∈ host, g.card = r)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (e : Finset (Fin v)) (I : Finset (Fin n)) (hI : I.card < r) :
    (rootPartIndicesContaining P request depth e I).card ≤
      n ^ (r - 1 - I.card) * D := by
  exact (card_rootPartIndicesContaining_le_localDegree
    P request depth host hschedule e I).trans
      (localDegree_le_pow_mul_of_codimOne host huniform I hI D hmax)

/-- Indices where the missing part of a target face can fit into the free
part of its pattern edge.  At all other indices the face-hit numerator is
exactly zero. -/
def activeFaceIndices (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) : Finset (Fin depth) :=
  (Finset.univ : Finset (Fin depth)).filter fun i ↦
    (faceMissing P (request i.1) target).card ≤
      (freePart P target.1.edge).card

/-- Possible intersections of the target face with a scheduled root part
which leave no more vertices than the pattern edge's free part. -/
def admissibleFaceIntersections (P : RootedPattern v r)
    (target : RelevantFaceLoadTarget P n) : Finset (Finset (Fin n)) :=
  target.1.face.powerset.filter fun I ↦
    target.1.face.card - I.card ≤ (freePart P target.1.edge).card

/-- The enlarged schedule space used to sum the face-hit numerators. -/
def admissibleSchedulePairs (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) :
    Finset (Finset (Fin n) × Fin depth) :=
  (admissibleFaceIntersections P target ×ˢ
    (Finset.univ : Finset (Fin depth))).filter fun z ↦
      z.1 ⊆ rootPartImage P.root (request z.2.1) target.1.edge

/-- Each active request is encoded by its actual intersection of the target
face with the prescribed root-part image. -/
def chosenSchedulePairs (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) :
    Finset (Finset (Fin n) × Fin depth) :=
  (activeFaceIndices P request depth target).image fun i ↦
    (target.1.face ∩
      rootPartImage P.root (request i.1) target.1.edge, i)

def scheduleIntersectionWeight (P : RootedPattern v r) (n : ℕ)
    (target : RelevantFaceLoadTarget P n)
    (I : Finset (Fin n)) : ℕ :=
  (2 ^ v * r ^ r) *
    n ^ (v - P.root.card - (target.1.face.card - I.card))

def schedulePairWeight (P : RootedPattern v r) (n : ℕ)
    (target : RelevantFaceLoadTarget P n)
    (z : Finset (Fin n) × Fin depth) : ℕ :=
  scheduleIntersectionWeight P n target z.1

lemma card_faceMissing_eq
    (P : RootedPattern v r) (request : RootRequest v n P.root)
    (target : RelevantFaceLoadTarget P n) :
    (faceMissing P request target).card =
      target.1.face.card -
        (target.1.face ∩
          rootPartImage P.root request target.1.edge).card := by
  rw [faceMissing, Finset.card_sdiff]
  rw [Finset.inter_comm]

theorem chosenSchedulePairs_subset_admissibleSchedulePairs
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) :
    chosenSchedulePairs P request depth target ⊆
      admissibleSchedulePairs P request depth target := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  have hiActive := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ i⟩,
    Finset.inter_subset_right⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_left, ?_⟩
  simpa [card_faceMissing_eq] using hiActive.2

lemma faceLoadNumeratorAt_le_schedulePairWeight
    (P : RootedPattern v r) (request : ℕ → RootRequest v n P.root)
    (depth : ℕ) (target : RelevantFaceLoadTarget P n)
    (hr : 0 < r) (i : Fin depth)
    (hi : i ∈ activeFaceIndices P request depth target) :
    faceLoadNumeratorAt P n (request i.1) target ≤
      schedulePairWeight P n target
        (target.1.face ∩
          rootPartImage P.root (request i.1) target.1.edge, i) := by
  let s := (faceMissing P (request i.1) target).card
  have hiData := Finset.mem_filter.mp hi
  have hsFree : s ≤ (freePart P target.1.edge).card := by
    simpa [s] using hiData.2
  have hsFace : s ≤ target.1.face.card := by
    exact Finset.card_le_card Finset.sdiff_subset
  have hfaceCard : target.1.face.card = r - 1 := target.2.2
  have hsr : s ≤ r := by omega
  have hsPow : s ^ s ≤ r ^ r := by
    calc
      s ^ s ≤ r ^ s := Nat.pow_le_pow_left hsr s
      _ ≤ r ^ r := Nat.pow_le_pow_right hr hsr
  have hexponent :
      v - (P.root.card + s) =
        v - P.root.card -
          (target.1.face.card -
            (target.1.face ∩
              rootPartImage P.root (request i.1) target.1.edge).card) := by
    rw [← card_faceMissing_eq P (request i.1) target]
    omega
  unfold faceLoadNumeratorAt
  dsimp only
  rw [if_pos hsFree, hexponent]
  unfold schedulePairWeight scheduleIntersectionWeight
  change 2 ^ v * (s ^ s * _) ≤ (2 ^ v * r ^ r) * _
  calc
    2 ^ v * (s ^ s *
        n ^ (v - P.root.card -
          (target.1.face.card -
            (target.1.face ∩
              rootPartImage P.root (request i.1) target.1.edge).card))) =
        (2 ^ v * s ^ s) *
          n ^ (v - P.root.card -
            (target.1.face.card -
              (target.1.face ∩
                rootPartImage P.root (request i.1) target.1.edge).card)) := by
      ring
    _ ≤ (2 ^ v * r ^ r) *
          n ^ (v - P.root.card -
            (target.1.face.card -
              (target.1.face ∩
                rootPartImage P.root (request i.1) target.1.edge).card)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsPow)

lemma sum_faceLoadNumerator_eq_sum_active
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) :
    (∑ i : Fin depth, faceLoadNumeratorAt P n (request i.1) target) =
      ∑ i ∈ activeFaceIndices P request depth target,
        faceLoadNumeratorAt P n (request i.1) target := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hiUniv hiNotActive
  have hnot : ¬(faceMissing P (request i.1) target).card ≤
      (freePart P target.1.edge).card := by
    simpa [activeFaceIndices] using hiNotActive
  unfold faceLoadNumeratorAt
  dsimp only
  rw [if_neg hnot]

theorem sum_activeFaceNumerators_le_sum_chosenWeights
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) (hr : 0 < r) :
    (∑ i ∈ activeFaceIndices P request depth target,
        faceLoadNumeratorAt P n (request i.1) target) ≤
      ∑ z ∈ chosenSchedulePairs P request depth target,
        schedulePairWeight P n target z := by
  calc
    (∑ i ∈ activeFaceIndices P request depth target,
        faceLoadNumeratorAt P n (request i.1) target) ≤
        ∑ i ∈ activeFaceIndices P request depth target,
          schedulePairWeight P n target
            (target.1.face ∩
              rootPartImage P.root (request i.1) target.1.edge, i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact faceLoadNumeratorAt_le_schedulePairWeight
        P request depth target hr i hi
    _ = ∑ z ∈ chosenSchedulePairs P request depth target,
          schedulePairWeight P n target z := by
      symm
      rw [chosenSchedulePairs, Finset.sum_image]
      intro i hi j hj hij
      exact congrArg Prod.snd hij

theorem sum_chosenWeights_le_sum_admissibleWeights
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) :
    (∑ z ∈ chosenSchedulePairs P request depth target,
        schedulePairWeight P n target z) ≤
      ∑ z ∈ admissibleSchedulePairs P request depth target,
        schedulePairWeight P n target z := by
  exact Finset.sum_le_sum_of_subset
    (chosenSchedulePairs_subset_admissibleSchedulePairs
      P request depth target)

theorem sum_admissibleScheduleWeights_eq
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (target : RelevantFaceLoadTarget P n) :
    (∑ z ∈ admissibleSchedulePairs P request depth target,
        schedulePairWeight P n target z) =
      ∑ I ∈ admissibleFaceIntersections P target,
        (rootPartIndicesContaining P request depth target.1.edge I).card *
          scheduleIntersectionWeight P n target I := by
  rw [admissibleSchedulePairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.sum_filter]
  change (∑ _i ∈ rootPartIndicesContaining P request depth
      target.1.edge I, scheduleIntersectionWeight P n target I) = _
  simp

def faceScheduleNumeratorBound (P : RootedPattern v r)
    (n D : ℕ) : ℕ :=
  2 ^ (r - 1) * (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D

def HasRootPartCountBound (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth D : ℕ) : Prop :=
  ∀ (e : Finset (Fin v)), e ∈ P.freeEdges →
    ∀ (I : Finset (Fin n)), I.card < r →
    (rootPartIndicesContaining P request depth e I).card ≤
      n ^ (r - 1 - I.card) * D

lemma rootPartCount_mul_intersectionWeight_le_of_bound
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth D : ℕ)
    (hcountBound : HasRootPartCountBound P request depth D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n)
    (I : Finset (Fin n))
    (hI : I ∈ admissibleFaceIntersections P target) :
    (rootPartIndicesContaining P request depth target.1.edge I).card *
        scheduleIntersectionWeight P n target I ≤
      (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D := by
  have hIData := Finset.mem_filter.mp hI
  have hIsub : I ⊆ target.1.face := Finset.mem_powerset.mp hIData.1
  have hfaceCard : target.1.face.card = r - 1 := target.2.2
  have hIcard : I.card < r := by
    have := Finset.card_le_card hIsub
    omega
  let s := target.1.face.card - I.card
  let m := v - P.root.card
  have hfreeM : (freePart P target.1.edge).card ≤ m := by
    calc
      (freePart P target.1.edge).card ≤
          ((Finset.univ : Finset (Fin v)) \ P.root).card := by
        apply Finset.card_le_card
        intro x hx
        have hxData := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxData.2⟩
      _ = m := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]
  have hsM : s ≤ m := hIData.2.trans hfreeM
  have hcount := hcountBound target.1.edge target.2.1 I hIcard
  have hpow : n ^ s * n ^ (m - s) = n ^ m := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (rootPartIndicesContaining P request depth target.1.edge I).card *
        scheduleIntersectionWeight P n target I ≤
        (n ^ (r - 1 - I.card) * D) *
          scheduleIntersectionWeight P n target I :=
      Nat.mul_le_mul_right _ hcount
    _ = (n ^ s * D) * ((2 ^ v * r ^ r) * n ^ (m - s)) := by
      simp only [scheduleIntersectionWeight, s, m, hfaceCard]
    _ = (2 ^ v * r ^ r) * n ^ m * D := by
      rw [show (n ^ s * D) * ((2 ^ v * r ^ r) * n ^ (m - s)) =
          (2 ^ v * r ^ r) * (n ^ s * n ^ (m - s)) * D by ring,
        hpow]
    _ = (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D := by
      rfl

lemma rootPartCount_mul_intersectionWeight_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n)
    (I : Finset (Fin n))
    (hI : I ∈ admissibleFaceIntersections P target) :
    (rootPartIndicesContaining P request depth target.1.edge I).card *
        scheduleIntersectionWeight P n target I ≤
      (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D := by
  have hIData := Finset.mem_filter.mp hI
  have hIsub : I ⊆ target.1.face := Finset.mem_powerset.mp hIData.1
  have hfaceCard : target.1.face.card = r - 1 := target.2.2
  have hIcard : I.card < r := by
    have := Finset.card_le_card hIsub
    omega
  let s := target.1.face.card - I.card
  let m := v - P.root.card
  have hfreeM : (freePart P target.1.edge).card ≤ m := by
    calc
      (freePart P target.1.edge).card ≤
          ((Finset.univ : Finset (Fin v)) \ P.root).card := by
        apply Finset.card_le_card
        intro x hx
        have hxData := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxData.2⟩
      _ = m := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]
  have hsM : s ≤ m := hIData.2.trans hfreeM
  have hcount := card_rootPartIndicesContaining_le_pow_mul_of_uniform
    P request depth host hschedule huniform hrs D hmax
      target.1.edge I hIcard
  have hpow : n ^ s * n ^ (m - s) = n ^ m := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (rootPartIndicesContaining P request depth target.1.edge I).card *
        scheduleIntersectionWeight P n target I ≤
        (n ^ (r - 1 - I.card) * D) *
          scheduleIntersectionWeight P n target I :=
      Nat.mul_le_mul_right _ hcount
    _ = (n ^ s * D) * ((2 ^ v * r ^ r) * n ^ (m - s)) := by
      simp only [scheduleIntersectionWeight, s, m, hfaceCard]
    _ = (2 ^ v * r ^ r) * n ^ m * D := by
      rw [show (n ^ s * D) * ((2 ^ v * r ^ r) * n ^ (m - s)) =
          (2 ^ v * r ^ r) * (n ^ s * n ^ (m - s)) * D by ring,
        hpow]
    _ = (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D := by
      rfl

theorem sum_admissibleScheduleWeights_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n) :
    (∑ z ∈ admissibleSchedulePairs P request depth target,
        schedulePairWeight P n target z) ≤
      faceScheduleNumeratorBound P n D := by
  let base := (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D
  have hcard : (admissibleFaceIntersections P target).card ≤ 2 ^ (r - 1) := by
    calc
      (admissibleFaceIntersections P target).card ≤
          target.1.face.powerset.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ target.1.face.card := by simp
      _ = 2 ^ (r - 1) := by rw [target.2.2]
  rw [sum_admissibleScheduleWeights_eq]
  calc
    (∑ I ∈ admissibleFaceIntersections P target,
        (rootPartIndicesContaining P request depth target.1.edge I).card *
          scheduleIntersectionWeight P n target I) ≤
        ∑ _I ∈ admissibleFaceIntersections P target, base := by
      apply Finset.sum_le_sum
      intro I hI
      exact rootPartCount_mul_intersectionWeight_le P request depth host
        hschedule huniform hrs D hmax hr target I hI
    _ = (admissibleFaceIntersections P target).card * base := by simp
    _ ≤ 2 ^ (r - 1) * base := Nat.mul_le_mul_right base hcard
    _ = faceScheduleNumeratorBound P n D := by
      simp [faceScheduleNumeratorBound, base, Nat.mul_assoc]

theorem sum_admissibleScheduleWeights_le_of_bound
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth D : ℕ)
    (hcountBound : HasRootPartCountBound P request depth D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n) :
    (∑ z ∈ admissibleSchedulePairs P request depth target,
        schedulePairWeight P n target z) ≤
      faceScheduleNumeratorBound P n D := by
  let base := (2 ^ v * r ^ r) * n ^ (v - P.root.card) * D
  have hcard : (admissibleFaceIntersections P target).card ≤ 2 ^ (r - 1) := by
    calc
      (admissibleFaceIntersections P target).card ≤
          target.1.face.powerset.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ target.1.face.card := by simp
      _ = 2 ^ (r - 1) := by rw [target.2.2]
  rw [sum_admissibleScheduleWeights_eq]
  calc
    (∑ I ∈ admissibleFaceIntersections P target,
        (rootPartIndicesContaining P request depth target.1.edge I).card *
          scheduleIntersectionWeight P n target I) ≤
        ∑ _I ∈ admissibleFaceIntersections P target, base := by
      apply Finset.sum_le_sum
      intro I hI
      exact rootPartCount_mul_intersectionWeight_le_of_bound
        P request depth D hcountBound hr target I hI
    _ = (admissibleFaceIntersections P target).card * base := by simp
    _ ≤ 2 ^ (r - 1) * base := Nat.mul_le_mul_right base hcard
    _ = faceScheduleNumeratorBound P n D := by
      simp [faceScheduleNumeratorBound, base, Nat.mul_assoc]

/-- The complete numerator budget: after summing over all scheduled root
requests, every fixed full-face target costs only the codimension-one root
degree `D` times the unrestricted rooted embedding scale. -/
theorem sum_faceLoadNumeratorAt_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (D : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n) :
    (∑ i : Fin depth,
        faceLoadNumeratorAt P n (request i.1) target) ≤
      faceScheduleNumeratorBound P n D := by
  rw [sum_faceLoadNumerator_eq_sum_active]
  exact (sum_activeFaceNumerators_le_sum_chosenWeights
    P request depth target hr).trans
      ((sum_chosenWeights_le_sum_admissibleWeights
        P request depth target).trans
          (sum_admissibleScheduleWeights_le P request depth host
            hschedule huniform hrs D hmax hr target))

theorem sum_faceLoadNumeratorAt_le_of_bound
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth D : ℕ)
    (hcountBound : HasRootPartCountBound P request depth D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n) :
    (∑ i : Fin depth,
        faceLoadNumeratorAt P n (request i.1) target) ≤
      faceScheduleNumeratorBound P n D := by
  rw [sum_faceLoadNumerator_eq_sum_active]
  exact (sum_activeFaceNumerators_le_sum_chosenWeights
    P request depth target hr).trans
      ((sum_chosenWeights_le_sum_admissibleWeights
        P request depth target).trans
          (sum_admissibleScheduleWeights_le_of_bound
            P request depth D hcountBound hr target))

lemma adaptiveBudget_shift (p : ℕ → ℝ) (start depth : ℕ) :
    adaptiveBudget p start depth =
      adaptiveBudget (fun i ↦ p (start + i)) 0 depth := by
  induction depth generalizing p start with
  | zero => simp [adaptiveBudget]
  | succ depth ih =>
      simp only [adaptiveBudget]
      rw [ih (p := p) (start := start + 1),
        ih (p := fun i ↦ p (start + i)) (start := 1)]
      congr 1
      apply congrArg (fun q : ℕ → ℝ ↦ adaptiveBudget q 0 depth)
      funext i
      congr 1
      omega

lemma adaptiveBudget_zero_eq_sum_fin :
    ∀ (depth : ℕ) (p : ℕ → ℝ),
      adaptiveBudget p 0 depth = ∑ i : Fin depth, p i.1
  | 0, p => by simp [adaptiveBudget]
  | depth + 1, p => by
      rw [adaptiveBudget, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      rw [adaptiveBudget_shift p 1 depth,
        adaptiveBudget_zero_eq_sum_fin depth (fun i ↦ p (1 + i))]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega

theorem adaptiveFaceBudget_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth : ℕ)
    (host : Finset (Finset (Fin n)))
    (hschedule : IsRootImageSchedule P.root request depth host)
    (huniform : ∀ g ∈ host, g.card = s) (hrs : r - 1 ≤ s)
    (D L : ℕ)
    (hmax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree host J ≤ D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n) :
    adaptiveBudget
        (fun i ↦ (faceLoadNumeratorAt P n (request i) target : ℝ) / L)
        0 depth ≤
      (faceScheduleNumeratorBound P n D : ℝ) / L := by
  rw [adaptiveBudget_zero_eq_sum_fin]
  have hsumNat := sum_faceLoadNumeratorAt_le P request depth host
    hschedule huniform hrs D hmax hr target
  have hsumReal :
      (∑ i : Fin depth,
        (faceLoadNumeratorAt P n (request i.1) target : ℝ)) ≤
          faceScheduleNumeratorBound P n D := by
    exact_mod_cast hsumNat
  calc
    (∑ i : Fin depth,
        (faceLoadNumeratorAt P n (request i.1) target : ℝ) / L) =
        (∑ i : Fin depth,
          (faceLoadNumeratorAt P n (request i.1) target : ℝ)) / L := by
      rw [Finset.sum_div]
    _ ≤ (faceScheduleNumeratorBound P n D : ℝ) / L :=
      div_le_div_of_nonneg_right hsumReal (Nat.cast_nonneg L)

/-- There are only polynomially many source-faithful face counters: one
counter for a free pattern edge and one ground `(r-1)`-face. -/
theorem card_relevantFaceLoadTarget_le (P : RootedPattern v r) (n : ℕ) :
    Fintype.card (RelevantFaceLoadTarget P n) ≤
      P.freeEdges.card * Nat.choose n (r - 1) := by
  classical
  let f : RelevantFaceLoadTarget P n →
      (↑P.freeEdges × ↑(Typicality.uniformEdges n (r - 1))) :=
    fun target ↦
      (⟨target.1.edge, target.2.1⟩,
        ⟨target.1.face, Typicality.mem_uniformEdges.mpr target.2.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨ae, af⟩, ha⟩ ⟨⟨be, bf⟩, hb⟩ hab
    simp only [f] at hab
    injection hab with hedge hface
    have he : ae = be := congrArg Subtype.val hedge
    have hfa : af = bf := congrArg Subtype.val hface
    subst be
    subst bf
    rfl
  calc
    Fintype.card (RelevantFaceLoadTarget P n) ≤
        Fintype.card (↑P.freeEdges ×
          ↑(Typicality.uniformEdges n (r - 1))) :=
      Fintype.card_le_of_injective f hf
    _ = P.freeEdges.card * Nat.choose n (r - 1) := by
      simp [Fintype.card_prod, Typicality.uniformEdges,
        Finset.card_powersetCard]

/-- A reusable finite exponential-union-bound calculation.  It packages
the last analytic line of the rooted extension lemma without any limiting
notation. -/
theorem sum_exp_faceBudget_lt_one
    {β : Type*} [Fintype β]
    (budget : β → ℝ) (B L C : ℕ)
    (hbudget : ∀ x, budget x ≤ (B : ℝ) / L)
    (hquant : (Real.exp 1 - 1) * ((B : ℝ) / L) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card β : ℝ) * Real.exp (-(C : ℝ) / 2) < 1) :
    (∑ x : β,
        Real.exp (-(1 : ℝ) * C) *
          Real.exp ((Real.exp 1 - 1) * budget x)) < 1 := by
  have hcoef : 0 ≤ Real.exp 1 - 1 := by
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  calc
    (∑ x : β,
        Real.exp (-(1 : ℝ) * C) *
          Real.exp ((Real.exp 1 - 1) * budget x)) ≤
        ∑ _x : β, Real.exp (-(C : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← Real.exp_add]
      apply Real.exp_monotone
      have hxq : (Real.exp 1 - 1) * budget x ≤ (C : ℝ) / 2 :=
        (mul_le_mul_of_nonneg_left (hbudget x) hcoef).trans hquant
      norm_num only [one_mul, neg_mul]
      linarith
    _ = (Fintype.card β : ℝ) * Real.exp (-(C : ℝ) / 2) := by simp
    _ < 1 := hcard

/-- Closed finite specialization of the full-face rooted extension theorem.
The schedule degree bound supplies every adaptive numerator budget, while
the two displayed real inequalities are the remaining scalar estimates. -/
theorem exists_legalEmbeddingPath_of_faceSchedule
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (rootHost forbidden : Finset (Finset (Fin n)))
    (depth Droot Dfixed C : ℕ)
    (hschedule : IsRootImageSchedule P.root request depth rootHost)
    (hrootUniform : ∀ g ∈ rootHost, g.card = s)
    (hrs : r - 1 ≤ s)
    (hrootMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree rootHost J ≤ Droot)
    (hfixedUniform : ∀ g ∈ forbidden, g.card = r)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hr : 0 < r)
    (hLpos : 0 < rootedFaceLegalLowerBound P n Dfixed C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound P n Droot : ℝ) /
          rootedFaceLegalLowerBound P n Dfixed C) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden [] path ∧
      ∀ target : RelevantFaceLoadTarget P n,
        pathHits (faceLoadHit P target) [] path < C := by
  apply exists_legalEmbeddingPath_of_faceLoads P request forbidden depth
    Dfixed C hfixedUniform hfixedMax hLpos (t := 1) (by norm_num)
  apply sum_exp_faceBudget_lt_one
    (budget := fun target ↦
      adaptiveBudget
        (fun i ↦
          (faceLoadNumeratorAt P n (request i) target : ℝ) /
            rootedFaceLegalLowerBound P n Dfixed C)
        0 depth)
    (B := faceScheduleNumeratorBound P n Droot)
    (L := rootedFaceLegalLowerBound P n Dfixed C) (C := C)
  · intro target
    exact adaptiveFaceBudget_le P request depth rootHost hschedule
      hrootUniform hrs Droot (rootedFaceLegalLowerBound P n Dfixed C)
      hrootMax hr target
  · exact hquant
  · exact hcard

theorem adaptiveFaceBudget_le_of_bound
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root) (depth D L : ℕ)
    (hcountBound : HasRootPartCountBound P request depth D)
    (hr : 0 < r) (target : RelevantFaceLoadTarget P n) :
    adaptiveBudget
        (fun i ↦ (faceLoadNumeratorAt P n (request i) target : ℝ) / L)
        0 depth ≤
      (faceScheduleNumeratorBound P n D : ℝ) / L := by
  rw [adaptiveBudget_zero_eq_sum_fin]
  have hsumNat := sum_faceLoadNumeratorAt_le_of_bound
    P request depth D hcountBound hr target
  have hsumReal :
      (∑ i : Fin depth,
        (faceLoadNumeratorAt P n (request i.1) target : ℝ)) ≤
          faceScheduleNumeratorBound P n D := by
    exact_mod_cast hsumNat
  calc
    (∑ i : Fin depth,
        (faceLoadNumeratorAt P n (request i.1) target : ℝ) / L) =
        (∑ i : Fin depth,
          (faceLoadNumeratorAt P n (request i.1) target : ℝ)) / L := by
      rw [Finset.sum_div]
    _ ≤ (faceScheduleNumeratorBound P n D : ℝ) / L :=
      div_le_div_of_nonneg_right hsumReal (Nat.cast_nonneg L)

/-- Finite rooted-path theorem driven directly by a root-part occurrence
bound.  Unlike `exists_legalEmbeddingPath_of_faceSchedule`, it permits
bounded repetition of the same root image. -/
theorem exists_legalEmbeddingPath_of_rootPartBound
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
    (depth Droot Dfixed C : ℕ)
    (hcountBound : HasRootPartCountBound P request depth Droot)
    (hfixedUniform : ∀ g ∈ forbidden, g.card = r)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hr : 0 < r)
    (hLpos : 0 < rootedFaceLegalLowerBound P n Dfixed C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound P n Droot : ℝ) /
          rootedFaceLegalLowerBound P n Dfixed C) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsLegalEmbeddingPath P request forbidden [] path ∧
      ∀ target : RelevantFaceLoadTarget P n,
        pathHits (faceLoadHit P target) [] path < C := by
  apply exists_legalEmbeddingPath_of_faceLoads P request forbidden depth
    Dfixed C hfixedUniform hfixedMax hLpos (t := 1) (by norm_num)
  apply sum_exp_faceBudget_lt_one
    (budget := fun target ↦
      adaptiveBudget
        (fun i ↦
          (faceLoadNumeratorAt P n (request i) target : ℝ) /
            rootedFaceLegalLowerBound P n Dfixed C)
        0 depth)
    (B := faceScheduleNumeratorBound P n Droot)
    (L := rootedFaceLegalLowerBound P n Dfixed C) (C := C)
  · intro target
    exact adaptiveFaceBudget_le_of_bound P request depth Droot
      (rootedFaceLegalLowerBound P n Dfixed C) hcountBound hr target
  · exact hquant
  · exact hcard

end

end Erdos722.RootSchedule

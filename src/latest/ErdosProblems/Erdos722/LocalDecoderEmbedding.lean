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
import ErdosProblems.Erdos722.CoverClique
import ErdosProblems.Erdos722.RootSchedule
import Mathlib

/-!
# Separated placements for the local decoders

The local integer decoder rooted at an `r`-edge uses all `k`-sets in a
`(k+r)`-vertex set.  This file specializes the checked rooted random-greedy
extension theorem to place one such complete rooted hypergraph at every
edge of a prescribed sparse family.  Its free `r`-edges avoid a fixed host
and are pairwise disjoint between distinct roots.
-/

namespace Erdos722.LocalDecoderEmbedding

open Finset
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverClique
open Erdos722.RandomGreedy

noncomputable section

/-- A labelled rooted-clique embedding for every edge of `roots`, with all
free edge images separated from `forbidden` and from one another. -/
structure SeparatedCliqueExtensions (n v r : ℕ)
    (roots forbidden : Finset (Finset (Fin n))) where
  embedding : (e : Finset (Fin n)) → e ∈ roots → Fin v ↪ Fin n
  root_image : ∀ e he,
    mapEdge (embedding e he) (coverRoot v r) = e
  free_eq : ∀ e he,
    imageFreeEdges (coverPattern v r) (embedding e he) =
      cliqueEdges
        ((Finset.univ : Finset (Fin v)).map (embedding e he)) r \ {e}
  free_disjoint_forbidden : ∀ e he,
    Disjoint (imageFreeEdges (coverPattern v r) (embedding e he)) forbidden
  free_pairwise : ∀ e he e' he', e ≠ e' →
    Disjoint (imageFreeEdges (coverPattern v r) (embedding e he))
      (imageFreeEdges (coverPattern v r) (embedding e' he'))

/-- Union of the free edge images in a root-indexed separated placement. -/
def separatedFreeEdges
    {n v r : ℕ} {roots forbidden : Finset (Finset (Fin n))}
    (S : SeparatedCliqueExtensions n v r roots forbidden) :
    Finset (Finset (Fin n)) :=
  roots.biUnion fun e ↦
    if he : e ∈ roots then
      imageFreeEdges (coverPattern v r) (S.embedding e he)
    else ∅

/-- A separated placement retaining the codimension-one degree conclusion
of the rooted concentration theorem. -/
structure BoundedSeparatedCliqueExtensions (n v r C : ℕ)
    (roots forbidden : Finset (Finset (Fin n)))
    extends SeparatedCliqueExtensions n v r roots forbidden where
  free_degree_le : ∀ J : Finset (Fin n), J.card = r - 1 →
    Reserve.localDegree (separatedFreeEdges toSeparatedCliqueExtensions) J ≤
      (coverPattern v r).freeEdges.card * C

/-- Extract the root-indexed placement from a legal path whose requests list
the roots in their canonical finset order. -/
def separatedCliqueExtensionsOfPath
    {n v r : ℕ} (hrv : r ≤ v)
    (roots forbidden : Finset (Finset (Fin n)))
    (e₀ : Finset (Fin n))
    (request : ℕ → RootRequest v n (coverRoot v r))
    (path : List (Fin v ↪ Fin n))
    (hrequest : ∀ i,
      requestImage (coverRoot v r) (request i) = scheduledEdge roots e₀ i)
    (hlen : path.length = roots.card)
    (hpath : IsLegalEmbeddingPath
      (coverPattern v r) request forbidden [] path) :
    SeparatedCliqueExtensions n v r roots forbidden := by
  classical
  let index (e : Finset (Fin n)) (he : e ∈ roots) : Fin roots.card :=
    roots.equivFin ⟨e, he⟩
  let pathIndex (e : Finset (Fin n)) (he : e ∈ roots) : Fin path.length :=
    ⟨(index e he).1, by rw [hlen]; exact (index e he).2⟩
  let embedding (e : Finset (Fin n)) (he : e ∈ roots) : Fin v ↪ Fin n :=
    path.get (pathIndex e he)
  have hscheduled (e : Finset (Fin n)) (he : e ∈ roots) :
      scheduledEdge roots e₀ (pathIndex e he).1 = e := by
    have hfin := scheduledEdge_fin roots e₀ (index e he)
    have hinv : roots.equivFin.symm (index e he) = ⟨e, he⟩ := by
      simp [index]
    simpa [pathIndex, hinv] using hfin
  have hstep (e : Finset (Fin n)) (he : e ∈ roots) :
      embedding e he ∈ legalEmbeddings (coverPattern v r) request forbidden
        (path.take (pathIndex e he).1) := by
    have hm := FollowsLegal.get_mem
      (legalEmbeddings (coverPattern v r) request forbidden)
      hpath (pathIndex e he)
    simpa [embedding] using hm
  have hext (e : Finset (Fin n)) (he : e ∈ roots) :
      ExtendsRequest (coverRoot v r)
        (request (pathIndex e he).1) (embedding e he) := by
    have hx := (mem_legalEmbeddings.mp (hstep e he)).1
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (pathIndex e he).2)] using hx
  refine
    { embedding := embedding
      root_image := ?_
      free_eq := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_ }
  · intro e he
    exact (mapEdge_root_eq_requestImage_of_extends
      (coverRoot v r) (request (pathIndex e he).1)
      (embedding e he) (hext e he)).trans
        ((hrequest _).trans (hscheduled e he))
  · intro e he
    exact imageFreeEdges_coverPattern_eq_spill hrv
      (request (pathIndex e he).1) e
      ((Finset.univ : Finset (Fin v)).map (embedding e he))
      (embedding e he) (hext e he)
      ((hrequest _).trans (hscheduled e he)) rfl
  · intro e he
    exact hpath.get_disjoint_forbidden (pathIndex e he)
  · intro e he e' he' hee'
    have hindexNe : pathIndex e he ≠ pathIndex e' he' := by
      intro hidx
      apply hee'
      have hval : (index e he).1 = (index e' he').1 :=
        congrArg (fun z : Fin path.length ↦ z.1) hidx
      have hfin : index e he = index e' he' := Fin.ext hval
      have hsub : (⟨e, he⟩ : ↑roots) = ⟨e', he'⟩ :=
        roots.equivFin.injective hfin
      exact congrArg Subtype.val hsub
    exact hpath.pairwise_disjoint (pathIndex e he) (pathIndex e' he') hindexNe

lemma separatedFreeEdgesOfPath_subset_usedEdges
    {n v r : ℕ} (hrv : r ≤ v)
    (roots forbidden : Finset (Finset (Fin n)))
    (e₀ : Finset (Fin n))
    (request : ℕ → RootRequest v n (coverRoot v r))
    (path : List (Fin v ↪ Fin n))
    (hrequest : ∀ i,
      requestImage (coverRoot v r) (request i) = scheduledEdge roots e₀ i)
    (hlen : path.length = roots.card)
    (hpath : IsLegalEmbeddingPath
      (coverPattern v r) request forbidden [] path) :
    separatedFreeEdges
        (separatedCliqueExtensionsOfPath hrv roots forbidden e₀
          request path hrequest hlen hpath) ⊆
      usedEdges (coverPattern v r) path := by
  classical
  intro g hg
  obtain ⟨e, he, hg⟩ := Finset.mem_biUnion.mp hg
  simp only [separatedFreeEdges, he, dite_true] at hg
  apply Finset.mem_biUnion.mpr
  refine ⟨(separatedCliqueExtensionsOfPath hrv roots forbidden e₀
    request path hrequest hlen hpath).embedding e he, ?_, hg⟩
  simp [separatedCliqueExtensionsOfPath]

/-- Finite rooted-extension theorem specialized to simultaneous local
decoder placements.  Only the two scalar concentration estimates and the
standard codimension-one degree bounds remain as inputs. -/
theorem exists_separatedCliqueExtensions_of_finite_bounds
    {n v r Droot Dfixed C : ℕ}
    [Nonempty (Fin v ↪ Fin n)]
    (hr : 0 < r) (hrv : r < v)
    (roots forbidden : Finset (Finset (Fin n)))
    (hrootUniform : ∀ e ∈ roots, e.card = r)
    (hforbiddenUniform : ∀ e ∈ forbidden, e.card = r)
    (e₀ : Finset (Fin n)) (he₀ : e₀ ∈ roots)
    (hrootMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree roots J ≤ Droot)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hLpos : 0 < rootedFaceLegalLowerBound
      (coverPattern v r) n Dfixed C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound (coverPattern v r) n Droot : ℝ) /
          rootedFaceLegalLowerBound (coverPattern v r) n Dfixed C) ≤
        (C : ℝ) / 2)
    (hcard :
      (Fintype.card (RelevantFaceLoadTarget (coverPattern v r) n) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    Nonempty (BoundedSeparatedCliqueExtensions n v r C roots forbidden) := by
  classical
  let ambientEmbedding : Fin v ↪ Fin n :=
    Classical.choice (inferInstance : Nonempty (Fin v ↪ Fin n))
  letI : Nonempty (Fin n) :=
    ⟨ambientEmbedding ⟨0, by omega⟩⟩
  have hedgeCard (i : ℕ) :
      (coverRoot v r).card = (scheduledEdge roots e₀ i).card := by
    rw [card_coverRoot hrv.le,
      hrootUniform (scheduledEdge roots e₀ i)
        (scheduledEdge_mem roots he₀ i)]
  have hrequestExists (i : ℕ) :
      ∃ request : RootRequest v n (coverRoot v r),
        requestImage (coverRoot v r) request = scheduledEdge roots e₀ i :=
    exists_rootRequest_with_image (coverRoot v r)
      (scheduledEdge roots e₀ i) (hedgeCard i)
  let request : ℕ → RootRequest v n (coverRoot v r) :=
    fun i ↦ Classical.choose (hrequestExists i)
  have hrequest (i : ℕ) :
      requestImage (coverRoot v r) (request i) = scheduledEdge roots e₀ i :=
    Classical.choose_spec (hrequestExists i)
  have hschedule : IsRootImageSchedule (coverRoot v r) request
      roots.card roots := by
    constructor
    · intro i
      rw [hrequest]
      exact scheduledEdge_mem roots he₀ i.1
    · intro i j hij
      apply scheduledEdge_injective_fin roots e₀
      simpa [hrequest] using hij
  obtain ⟨path, hlen, hpath, hcaps⟩ :=
    exists_legalEmbeddingPath_of_faceSchedule
      (coverPattern v r) request roots forbidden roots.card
      Droot Dfixed C hschedule hrootUniform
      (by omega : r - 1 ≤ r) hrootMax
      hforbiddenUniform hfixedMax hr hLpos hquant hcard
  let S := separatedCliqueExtensionsOfPath hrv.le roots forbidden e₀
    request path hrequest hlen hpath
  refine ⟨{
    toSeparatedCliqueExtensions := S
    free_degree_le := ?_ }⟩
  intro J hJ
  have hsub : separatedFreeEdges S ⊆
      usedEdges (coverPattern v r) path := by
    exact separatedFreeEdgesOfPath_subset_usedEdges hrv.le roots forbidden e₀
      request path hrequest hlen hpath
  calc
    Reserve.localDegree (separatedFreeEdges S) J ≤
        Reserve.localDegree (usedEdges (coverPattern v r) path) J := by
      exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    _ ≤ (coverPattern v r).freeEdges.card * C :=
      localDegree_usedEdges_le_faceLoadCaps
        (coverPattern v r) [] path J hJ C hcaps

end

end Erdos722.LocalDecoderEmbedding

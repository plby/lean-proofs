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
import ErdosProblems.Erdos722.RootSchedule
import ErdosProblems.Erdos722.CoverClique
import Mathlib

/-!
# Bounded embeddings rooted at a family of larger vertex sets

The cover and local-decoder applications root a pattern at one `r`-edge.
Exchange gadgets instead fix an entire `k`-clique.  The root-schedule
estimate is now cardinality-generic, so the same random-greedy path gives
separated embeddings indexed by any uniform family of root images.
-/

namespace Erdos722.RootedFamilyEmbedding

open Finset
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverClique
open Erdos722.RandomGreedy

noncomputable section

structure BoundedRootedFamilyEmbeddings
    {v r n : ℕ} (P : RootedPattern v r)
    (roots forbidden : Finset (Finset (Fin n))) (C : ℕ) where
  embedding : (Q : Finset (Fin n)) → Q ∈ roots → Fin v ↪ Fin n
  root_image : ∀ Q hQ,
    mapEdge (embedding Q hQ) P.root = Q
  free_disjoint_forbidden : ∀ Q hQ,
    Disjoint (imageFreeEdges P (embedding Q hQ)) forbidden
  free_pairwise : ∀ Q hQ Q' hQ', Q ≠ Q' →
    Disjoint (imageFreeEdges P (embedding Q hQ))
      (imageFreeEdges P (embedding Q' hQ'))
  freeUnion : Finset (Finset (Fin n))
  image_subset_freeUnion : ∀ Q hQ,
    imageFreeEdges P (embedding Q hQ) ⊆ freeUnion
  free_degree_le : ∀ J : Finset (Fin n), J.card = r - 1 →
    Reserve.localDegree freeUnion J ≤ P.freeEdges.card * C

theorem exists_boundedRootedFamilyEmbeddings_of_finite_bounds
    {v r n Droot Dfixed C : ℕ}
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (roots forbidden : Finset (Finset (Fin n)))
    (hrootUniform : ∀ Q ∈ roots, Q.card = P.root.card)
    (hrootNonempty : P.root.Nonempty)
    (hrootLarge : r - 1 ≤ P.root.card)
    (hforbiddenUniform : ∀ e ∈ forbidden, e.card = r)
    (Q₀ : Finset (Fin n)) (hQ₀ : Q₀ ∈ roots)
    (hrootMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree roots J ≤ Droot)
    (hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ Dfixed)
    (hr : 0 < r)
    (hLpos : 0 < rootedFaceLegalLowerBound P n Dfixed C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound P n Droot : ℝ) /
          rootedFaceLegalLowerBound P n Dfixed C) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    Nonempty (BoundedRootedFamilyEmbeddings P roots forbidden C) := by
  classical
  let ambientEmbedding : Fin v ↪ Fin n :=
    Classical.choice (inferInstance : Nonempty (Fin v ↪ Fin n))
  let : Nonempty (Fin n) :=
    ⟨ambientEmbedding ⟨0, by
      have hv : 0 < v := by
        have hrootCard := Finset.card_le_univ P.root
        have : 0 < P.root.card := Finset.card_pos.mpr hrootNonempty
        simpa using this.trans_le hrootCard
      exact hv⟩⟩
  have hrequestExists (i : ℕ) :
      ∃ request : RootRequest v n P.root,
        requestImage P.root request = scheduledEdge roots Q₀ i :=
    exists_rootRequest_with_image P.root (scheduledEdge roots Q₀ i) (by
      rw [hrootUniform (scheduledEdge roots Q₀ i)
        (scheduledEdge_mem roots hQ₀ i)])
  let request : ℕ → RootRequest v n P.root :=
    fun i ↦ Classical.choose (hrequestExists i)
  have hrequest (i : ℕ) :
      requestImage P.root (request i) = scheduledEdge roots Q₀ i :=
    Classical.choose_spec (hrequestExists i)
  have hschedule : IsRootImageSchedule P.root request roots.card roots := by
    constructor
    · intro i
      rw [hrequest]
      exact scheduledEdge_mem roots hQ₀ i.1
    · intro i j hij
      apply scheduledEdge_injective_fin roots Q₀
      simpa [hrequest] using hij
  obtain ⟨path, hlen, hpath, hcaps⟩ :=
    exists_legalEmbeddingPath_of_faceSchedule P request roots forbidden
      roots.card Droot Dfixed C hschedule hrootUniform hrootLarge hrootMax
      hforbiddenUniform hfixedMax hr hLpos hquant hcard
  let index (Q : Finset (Fin n)) (hQ : Q ∈ roots) : Fin roots.card :=
    roots.equivFin ⟨Q, hQ⟩
  let pathIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots) : Fin path.length :=
    ⟨(index Q hQ).1, by rw [hlen]; exact (index Q hQ).2⟩
  let embedding (Q : Finset (Fin n)) (hQ : Q ∈ roots) : Fin v ↪ Fin n :=
    path.get (pathIndex Q hQ)
  have hscheduled (Q : Finset (Fin n)) (hQ : Q ∈ roots) :
      scheduledEdge roots Q₀ (pathIndex Q hQ).1 = Q := by
    have hfin := scheduledEdge_fin roots Q₀ (index Q hQ)
    have hinv : roots.equivFin.symm (index Q hQ) = ⟨Q, hQ⟩ := by
      simp [index]
    simpa [pathIndex, hinv] using hfin
  have hstep (Q : Finset (Fin n)) (hQ : Q ∈ roots) :
      embedding Q hQ ∈ legalEmbeddings P request forbidden
        (path.take (pathIndex Q hQ).1) := by
    have hm := FollowsLegal.get_mem
      (legalEmbeddings P request forbidden) hpath (pathIndex Q hQ)
    simpa [embedding] using hm
  have hext (Q : Finset (Fin n)) (hQ : Q ∈ roots) :
      ExtendsRequest P.root (request (pathIndex Q hQ).1) (embedding Q hQ) := by
    have hx := (mem_legalEmbeddings.mp (hstep Q hQ)).1
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (pathIndex Q hQ).2)] using hx
  refine ⟨{
    embedding := embedding
    root_image := ?_
    free_disjoint_forbidden := ?_
    free_pairwise := ?_
    freeUnion := usedEdges P path
    image_subset_freeUnion := ?_
    free_degree_le := ?_ }⟩
  · intro Q hQ
    exact (mapEdge_root_eq_requestImage_of_extends P.root
      (request (pathIndex Q hQ).1) (embedding Q hQ) (hext Q hQ)).trans
        ((hrequest _).trans (hscheduled Q hQ))
  · intro Q hQ
    exact hpath.get_disjoint_forbidden (pathIndex Q hQ)
  · intro Q hQ Q' hQ' hQQ'
    have hindexNe : pathIndex Q hQ ≠ pathIndex Q' hQ' := by
      intro hidx
      apply hQQ'
      have hval : (index Q hQ).1 = (index Q' hQ').1 :=
        congrArg (fun z : Fin path.length ↦ z.1) hidx
      have hfin : index Q hQ = index Q' hQ' := Fin.ext hval
      have hsub : (⟨Q, hQ⟩ : ↑roots) = ⟨Q', hQ'⟩ :=
        roots.equivFin.injective hfin
      exact congrArg Subtype.val hsub
    exact hpath.pairwise_disjoint (pathIndex Q hQ) (pathIndex Q' hQ') hindexNe
  · intro Q hQ g hg
    apply Finset.mem_biUnion.mpr
    refine ⟨embedding Q hQ, ?_, hg⟩
    simp [embedding]
  · intro J hJ
    exact localDegree_usedEdges_le_faceLoadCaps P [] path J hJ C hcaps

end

end Erdos722.RootedFamilyEmbedding

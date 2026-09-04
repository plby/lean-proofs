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
import ErdosProblems.Erdos722.RootedFamilyAsymptotic
import Mathlib

/-!
# Rooted embeddings retaining prescribed root maps

Some applications prescribe more than the image of the root as an
unlabelled set.  In the two-clique elimination move, for example, the map
must carry each of two overlapping distinguished cliques to a specified
member of an ordered pair.  This file packages the output of the generic
random-greedy path while retaining the full `ExtendsRequest` conclusion at
every scheduled index.
-/

namespace Erdos722.RequestedFamilyEmbedding

open Finset
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.RandomGreedy
open Erdos722.RootedFamilyAsymptotic
open Erdos722.LocalDecoderAsymptotic
open Filter

noncomputable section

structure BoundedRequestedFamilyEmbeddings
    {v r n : ℕ} (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n))) (depth C : ℕ) where
  embedding : Fin depth → Fin v ↪ Fin n
  extends_request : ∀ i,
    ExtendsRequest P.root (request i.1) (embedding i)
  free_disjoint_forbidden : ∀ i,
    Disjoint (imageFreeEdges P (embedding i)) forbidden
  free_pairwise : ∀ i j, i ≠ j →
    Disjoint (imageFreeEdges P (embedding i))
      (imageFreeEdges P (embedding j))
  freeUnion : Finset (Finset (Fin n))
  image_subset_freeUnion : ∀ i,
    imageFreeEdges P (embedding i) ⊆ freeUnion
  free_uniform : ∀ g ∈ freeUnion, g.card = r
  freeUnion_disjoint_forbidden : Disjoint freeUnion forbidden
  free_degree_le : ∀ J : Finset (Fin n), J.card = r - 1 →
    Reserve.localDegree freeUnion J ≤ P.freeEdges.card * C

/-- The finite root-part estimate supplies a family of embeddings which
extends the actual chosen requests, rather than remembering only their root
images. -/
theorem exists_boundedRequestedFamilyEmbeddings_of_finite_bounds
    {v r n depth Droot Dfixed C : ℕ}
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (forbidden : Finset (Finset (Fin n)))
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
    Nonempty (BoundedRequestedFamilyEmbeddings
      P request forbidden depth C) := by
  obtain ⟨path, hlen, hpath, hcaps⟩ :=
    exists_legalEmbeddingPath_of_rootPartBound P request forbidden
      depth Droot Dfixed C hcountBound hfixedUniform hfixedMax hr
      hLpos hquant hcard
  let pathIndex (i : Fin depth) : Fin path.length :=
    ⟨i.1, by rw [hlen]; exact i.2⟩
  let embedding (i : Fin depth) : Fin v ↪ Fin n :=
    path.get (pathIndex i)
  have hstep (i : Fin depth) :
      embedding i ∈ legalEmbeddings P request forbidden
        (path.take (pathIndex i).1) := by
    have hm := FollowsLegal.get_mem
      (legalEmbeddings P request forbidden) hpath (pathIndex i)
    simpa [embedding] using hm
  refine ⟨{
    embedding := embedding
    extends_request := ?_
    free_disjoint_forbidden := ?_
    free_pairwise := ?_
    freeUnion := usedEdges P path
    image_subset_freeUnion := ?_
    free_uniform := fun g hg ↦ usedEdges_uniform P path hg
    freeUnion_disjoint_forbidden := hpath.usedEdges_disjoint_forbidden
    free_degree_le := ?_ }⟩
  · intro i
    have hext := (mem_legalEmbeddings.mp (hstep i)).1
    simpa [pathIndex, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (pathIndex i).2)] using hext
  · intro i
    exact hpath.get_disjoint_forbidden (pathIndex i)
  · intro i j hij
    have hindex : pathIndex i ≠ pathIndex j := by
      intro heq
      apply hij
      apply Fin.ext
      exact congrArg (fun z : Fin path.length ↦ z.1) heq
    exact hpath.pairwise_disjoint (pathIndex i) (pathIndex j) hindex
  · intro i g hg
    apply Finset.mem_biUnion.mpr
    refine ⟨embedding i, ?_, hg⟩
    simp [embedding]
  · intro J hJ
    exact localDegree_usedEdges_le_faceLoadCaps P [] path J hJ C hcaps

/-- Source-faithful asymptotic interface for a labelled request sequence:
the caller may prove the sharp occurrence bound separately for each
non-root pattern edge, without first bounding the degree of the unions of
all prescribed roots. -/
theorem eventually_exists_boundedRequestedFamilyEmbeddings_of_rootPartBound
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hd : 0 < d) (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (request : ℕ → RootRequest v n P.root)
        (forbidden : Finset (Finset (Fin n))) (depth : ℕ),
      HasRootPartCountBound P request depth
        (scale * decoderInputCap d n) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedRequestedFamilyEmbeddings P request forbidden depth
        (scaledDecoderPathCap scale v r d n)) := by
  have hlegal := eventually_rooted_scaled_legalLowerBound
    P hr hroot hd scale hscale
  have hquant := eventually_rooted_scaled_quantitative_bound
    P hr hroot hrootLarge hd scale hscale
  have hcard := eventually_rooted_scaled_exponential_union_bound
    P hr hd scale hscale
  filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
      n hlegal hquant hcard hvn
  intro request forbidden depth hcount hforbiddenUniform hforbiddenDegree
  let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
  have hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ decoderInputCap d n := by
    intro J hJ
    exact le_decoderInputCap_of_pow_le d n _ hd
      (hforbiddenDegree J hJ)
  exact exists_boundedRequestedFamilyEmbeddings_of_finite_bounds
    P request forbidden hcount hforbiddenUniform hfixedMax hr
      hlegal.1 hquant hcard

/-- Graded-exponent version of the labelled request interface.  The root
schedule and fixed forbidden host are controlled with `dInput`, whereas the
free output is allowed the independent `dPath` cap. -/
theorem eventually_exists_boundedRequestedFamilyEmbeddings_of_twoScale_rootPartBound
    {dInput dPath : ℕ}
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath)
    (scale : ℕ) (hscale : 0 < scale) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (request : ℕ → RootRequest v n P.root)
        (forbidden : Finset (Finset (Fin n))) (depth : ℕ),
      HasRootPartCountBound P request depth
        (scale * decoderInputCap dInput n) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ dInput ≤ n ^ (dInput - 1)) →
      Nonempty (BoundedRequestedFamilyEmbeddings P request forbidden depth
        (scaledDecoderPathCap scale v r dPath n)) := by
  have hlegal := eventually_rooted_twoScale_scaled_legalLowerBound
    P hr hroot hdInput hdPath scale hscale
  have hquant := eventually_rooted_twoScale_scaled_quantitative_bound
    P hr hroot hrootLarge hdInput hdPath hgap scale hscale
  have hcard := eventually_rooted_scaled_exponential_union_bound
    P hr hdPath scale hscale
  filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
      n hlegal hquant hcard hvn
  intro request forbidden depth hcount hforbiddenUniform hforbiddenDegree
  let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
  have hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ decoderInputCap dInput n := by
    intro J hJ
    exact le_decoderInputCap_of_pow_le dInput n _ hdInput
      (hforbiddenDegree J hJ)
  exact exists_boundedRequestedFamilyEmbeddings_of_finite_bounds
    P request forbidden hcount hforbiddenUniform hfixedMax hr
      hlegal.1 hquant hcard

/-- Eventual placement of any labelled request schedule whose unlabelled
root images come from a power-bounded uniform family and occur with bounded
multiplicity. -/
theorem eventually_exists_boundedRequestedFamilyEmbeddings_of_power_bound
    (P : RootedPattern v r) (hr : 0 < r)
    (hroot : P.root.card < v) (hrootLarge : r ≤ P.root.card)
    (hd : 0 < d) (multiplicity : ℕ) (hmultiplicity : 0 < multiplicity) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (request : ℕ → RootRequest v n P.root)
        (forbidden roots : Finset (Finset (Fin n))) (depth : ℕ),
      IsRootImageScheduleMultiplicity P.root request depth roots multiplicity →
      (∀ Q ∈ roots, Q.card = P.root.card) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedRequestedFamilyEmbeddings P request forbidden depth
        (scaledDecoderPathCap multiplicity v r d n)) := by
  have hlegal := eventually_rooted_scaled_legalLowerBound
    P hr hroot hd multiplicity hmultiplicity
  have hquant := eventually_rooted_scaled_quantitative_bound
    P hr hroot hrootLarge hd multiplicity hmultiplicity
  have hcard := eventually_rooted_scaled_exponential_union_bound
    P hr hd multiplicity hmultiplicity
  filter_upwards [hlegal, hquant, hcard, eventually_ge_atTop v] with
      n hlegal hquant hcard hvn
  intro request forbidden roots depth hschedule hrootsUniform
    hforbiddenUniform hrootDegree hforbiddenDegree
  let : Nonempty (Fin v ↪ Fin n) := ⟨Fin.castLEEmb hvn⟩
  have hrootMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree roots J ≤ decoderInputCap d n := by
    intro J hJ
    exact le_decoderInputCap_of_pow_le d n _ hd (hrootDegree J hJ)
  have hfixedMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree forbidden J ≤ decoderInputCap d n := by
    intro J hJ
    exact le_decoderInputCap_of_pow_le d n _ hd
      (hforbiddenDegree J hJ)
  have hcount : HasRootPartCountBound P request depth
      (multiplicity * decoderInputCap d n) := by
    intro e he I hI
    exact card_rootPartIndicesContaining_le_pow_mul_of_uniform_mul
      P request depth roots multiplicity hschedule hrootsUniform
        (by omega) (decoderInputCap d n) hrootMax e I hI
  exact exists_boundedRequestedFamilyEmbeddings_of_finite_bounds
    P request forbidden hcount hforbiddenUniform hfixedMax hr
      hlegal.1 hquant hcard

end

end Erdos722.RequestedFamilyEmbedding

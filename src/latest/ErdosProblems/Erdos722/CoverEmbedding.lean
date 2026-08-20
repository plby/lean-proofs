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
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Rooted embeddings constrained to a sparse reserve

The cover stage cannot regard the complement of the reserve as a sparse
forbidden host.  Instead its baseline family consists of rooted embeddings
whose free edges all lie in the reserve.  This file proves the corresponding
finite random-greedy theorem: an explicit lower bound on that baseline,
together with the already established codimension-one overlap and scheduled
face estimates, yields edge-disjoint reserve extensions.
-/

namespace Erdos722.CoverEmbedding

open Finset
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.AdaptiveChernoff
open Erdos722.RandomGreedy

noncomputable section

/-- Rooted embeddings all of whose non-root pattern edges lie in the
reserve. -/
def reserveEmbeddings (P : RootedPattern v r)
    (request : RootRequest v n P.root)
    (reserve : Finset (Finset (Fin n))) : Finset (Fin v ↪ Fin n) :=
  (rootedEmbeddings P.root request).filter fun φ ↦
    imageFreeEdges P φ ⊆ reserve

lemma mem_reserveEmbeddings {φ : Fin v ↪ Fin n} :
    φ ∈ reserveEmbeddings P request reserve ↔
      ExtendsRequest P.root request φ ∧ imageFreeEdges P φ ⊆ reserve := by
  simp [reserveEmbeddings, mem_rootedEmbeddings]

/-- At a history, exclude reserve embeddings which reuse a previously spent
free edge. -/
def reserveLegalEmbeddings (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (reserve : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) : Finset (Fin v ↪ Fin n) :=
  (reserveEmbeddings P (request history.length) reserve).filter fun φ ↦
    Disjoint (imageFreeEdges P φ) (usedEdges P history)

lemma mem_reserveLegalEmbeddings {φ : Fin v ↪ Fin n} :
    φ ∈ reserveLegalEmbeddings P request reserve history ↔
      ExtendsRequest P.root (request history.length) φ ∧
        imageFreeEdges P φ ⊆ reserve ∧
        Disjoint (imageFreeEdges P φ) (usedEdges P history) := by
  simp only [reserveLegalEmbeddings, Finset.mem_filter,
    mem_reserveEmbeddings]
  tauto

/-- The reserve-compatible family is covered by the legal family and the
family meeting the already used host. -/
lemma reserveEmbeddings_subset_legal_union_meeting
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (reserve : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) :
    reserveEmbeddings P (request history.length) reserve ⊆
      reserveLegalEmbeddings P request reserve history ∪
        embeddingsMeeting P (request history.length) (usedEdges P history) := by
  intro φ hφ
  by_cases hdis : Disjoint (imageFreeEdges P φ) (usedEdges P history)
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hφ, hdis⟩)
  · exact Finset.mem_union_right _ (mem_embeddingsMeeting.mpr
      ⟨(mem_reserveEmbeddings.mp hφ).1, hdis⟩)

/-- Baseline reserve count minus the overlap loss lower-bounds the legal
family. -/
lemma card_reserveEmbeddings_sub_meeting_le_legal
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (reserve : Finset (Finset (Fin n)))
    (history : List (Fin v ↪ Fin n)) :
    (reserveEmbeddings P (request history.length) reserve).card -
        (embeddingsMeeting P (request history.length)
          (usedEdges P history)).card ≤
      (reserveLegalEmbeddings P request reserve history).card := by
  have hcover := Finset.card_le_card
    (reserveEmbeddings_subset_legal_union_meeting P request reserve history)
  have hunion := Finset.card_union_le
    (reserveLegalEmbeddings P request reserve history)
    (embeddingsMeeting P (request history.length) (usedEdges P history))
  omega

/-- The full-face numerator estimate applies unchanged to the smaller
reserve-legal family. -/
lemma card_reserveLegalEmbeddings_faceLoadHit_le
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (reserve : Finset (Finset (Fin n)))
    (target : RelevantFaceLoadTarget P n)
    (history : List (Fin v ↪ Fin n)) :
    ((reserveLegalEmbeddings P request reserve history).filter
      fun φ ↦ faceLoadHit P target history φ).card ≤
        faceLoadNumeratorAt P n (request history.length) target := by
  apply (Finset.card_le_card ?_).trans
    (card_faceConstrainedEmbeddings_le P
      (request history.length) target)
  intro φ hφ
  have hdata := Finset.mem_filter.mp hφ
  have hlegal := mem_reserveLegalEmbeddings.mp hdata.1
  have hhit := (faceLoadHit_eq_true_iff P target history φ).mp (by
    simpa using hdata.2)
  let S := facePreimageVertices P (request history.length) target φ
  apply Finset.mem_biUnion.mpr
  refine ⟨S, facePreimageVertices_mem_powersetCard P
    (request history.length) target φ hlegal.1 hhit, ?_⟩
  exact mem_constrainedEmbeddings.mpr
    ⟨hlegal.1, mapEdge_facePreimageVertices P
      (request history.length) target φ hlegal.1 hhit⟩

/-- For a clique pattern, every unlabelled reserve candidate gives a
distinct reserve-compatible rooted embedding. -/
theorem card_reserveCandidates_le_reserveEmbeddings
    (P : RootedPattern v r)
    (hallEdges : P.edges = Typicality.uniformEdges v r)
    (hrootCard : P.root.card = r)
    (request : RootRequest v n P.root)
    (e : Finset (Fin n))
    (hrequest : requestImage P.root request = e)
    (reserve : Finset (Finset (Fin n))) :
    (reserveCandidates n v r reserve e).card ≤
      (reserveEmbeddings P request reserve).card := by
  classical
  let candidates := reserveCandidates n v r reserve e
  have hchoose : ∀ B : ↑candidates,
      ∃ φ : Fin v ↪ Fin n,
        ExtendsRequest P.root request φ ∧
          (Finset.univ : Finset (Fin v)).map φ = B.1 := by
    intro B
    have hB := Finset.mem_filter.mp B.2
    have hBcard : B.1.card = v := Typicality.mem_uniformEdges.mp hB.1
    apply exists_embedding_extending_request_with_range
      P.root request B.1 hBcard
    change requestImage P.root request ⊆ B.1
    rw [hrequest]
    exact hB.2.1
  let chosen (B : ↑candidates) : Fin v ↪ Fin n :=
    Classical.choose (hchoose B)
  have hchosen (B : ↑candidates) :
      ExtendsRequest P.root request (chosen B) ∧
        (Finset.univ : Finset (Fin v)).map (chosen B) = B.1 :=
    Classical.choose_spec (hchoose B)
  have hchosenReserve (B : ↑candidates) :
      chosen B ∈ reserveEmbeddings P request reserve := by
    apply mem_reserveEmbeddings.mpr
    refine ⟨(hchosen B).1, ?_⟩
    intro g hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
    have haData := Finset.mem_filter.mp ha
    have hB := Finset.mem_filter.mp B.2
    have hsub : mapEdge (chosen B) a ⊆ B.1 := by
      rw [← (hchosen B).2]
      exact Finset.map_subset_map.mpr (Finset.subset_univ a)
    have hcard : (mapEdge (chosen B) a).card = r := by
      rw [card_mapEdge, P.uniform a haData.1]
    have hclique : mapEdge (chosen B) a ∈ Reserve.cliqueEdges B.1 r := by
      exact Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩
    have hrootMap : mapEdge (chosen B) P.root = e :=
      (mapEdge_root_eq_requestImage_of_extends P.root request
        (chosen B) (hchosen B).1).trans hrequest
    have hne : mapEdge (chosen B) a ≠ e := by
      intro heq
      have hmaps : a.map (chosen B) = P.root.map (chosen B) :=
        heq.trans hrootMap.symm
      have haroot : a = P.root := Finset.map_injective (chosen B) hmaps
      exact haData.2 (haroot ▸ Finset.Subset.rfl)
    exact hB.2.2 (Finset.mem_sdiff.mpr
      ⟨hclique, by simpa using hne⟩)
  let f : ↑candidates → ↑(reserveEmbeddings P request reserve) :=
    fun B ↦ ⟨chosen B, hchosenReserve B⟩
  have hf : Function.Injective f := by
    intro B C hBC
    apply Subtype.ext
    have hemb : chosen B = chosen C := congrArg Subtype.val hBC
    have hrange := (hchosen B).2.symm.trans
      (congrArg (fun φ : Fin v ↪ Fin n ↦
        (Finset.univ : Finset (Fin v)).map φ) hemb)
    exact hrange.trans (hchosen C).2
  simpa [candidates, Fintype.card_coe] using
    (Fintype.card_le_of_injective f hf)

/-- Legal lower bound for reserve-constrained placement. -/
def reserveLegalLowerBound (P : RootedPattern v r)
    (n A C : ℕ) : ℕ :=
  A - codimOneMeetingBound P n (P.freeEdges.card * C)

/-- A path in the reserve-constrained process. -/
def IsReserveEmbeddingPath (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (reserve : Finset (Finset (Fin n)))
    (history path : List (Fin v ↪ Fin n)) : Prop :=
  FollowsLegal (reserveLegalEmbeddings P request reserve) history path

/-- Distinct steps of a reserve-legal path spend disjoint free-edge
families. -/
theorem IsReserveEmbeddingPath.pairwise_disjoint
    {path : List (Fin v ↪ Fin n)}
    (hpath : IsReserveEmbeddingPath P request reserve [] path)
    (i j : Fin path.length) (hij : i ≠ j) :
    Disjoint (imageFreeEdges P (path.get i))
      (imageFreeEdges P (path.get j)) := by
  classical
  wlog hijlt : i.1 < j.1 generalizing i j
  · have hji : j.1 < i.1 := by omega
    exact disjoint_comm.mp
      (this j i (Ne.symm hij) hji)
  have hjmem := FollowsLegal.get_mem
    (reserveLegalEmbeddings P request reserve) hpath j
  have hjdis := (mem_reserveLegalEmbeddings.mp (by
    simpa using hjmem)).2.2
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
  apply Finset.disjoint_left.mpr
  intro g hgi hgj
  exact Finset.disjoint_left.mp hjdis hgj (hsub hgi)

/-- Closed finite sparse-reserve extension theorem.  `A` is a uniform lower
bound for the initial reserve-compatible family. -/
theorem exists_reserveEmbeddingPath_of_faceSchedule
    [Nonempty (Fin v ↪ Fin n)]
    (P : RootedPattern v r)
    (request : ℕ → RootRequest v n P.root)
    (rootHost reserve : Finset (Finset (Fin n)))
    (depth Droot A C : ℕ)
    (hschedule : IsRootImageSchedule P.root request depth rootHost)
    (hrootUniform : ∀ g ∈ rootHost, g.card = r)
    (hrootMax : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree rootHost J ≤ Droot)
    (hreserveUniform : ∀ g ∈ reserve, g.card = r)
    (hbaseline : ∀ i : ℕ,
      A ≤ (reserveEmbeddings P (request i) reserve).card)
    (hr : 0 < r)
    (hLpos : 0 < reserveLegalLowerBound P n A C)
    (hquant : (Real.exp 1 - 1) *
        ((faceScheduleNumeratorBound P n Droot : ℝ) /
          reserveLegalLowerBound P n A C) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    ∃ path : List (Fin v ↪ Fin n), path.length = depth ∧
      IsReserveEmbeddingPath P request reserve [] path ∧
      ∀ target : RelevantFaceLoadTarget P n,
        pathHits (faceLoadHit P target) [] path < C := by
  classical
  let Dused := P.freeEdges.card * C
  let L := reserveLegalLowerBound P n A C
  let good : List (Fin v ↪ Fin n) → Prop := fun history ↦
    history.length ≤ depth ∧
      ∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (usedEdges P history) J ≤ Dused
  letI : DecidablePred good := Classical.decPred _
  have hnonempty : ∀ history, good history →
      (reserveLegalEmbeddings P request reserve history).Nonempty := by
    intro history hgood
    have hmeet :
        (embeddingsMeeting P (request history.length)
          (usedEdges P history)).card ≤ codimOneMeetingBound P n Dused :=
      (card_embeddingsMeeting_le_of_codimOne P
        (request history.length) (usedEdges P history)
        (fun g hg ↦ usedEdges_uniform P history hg) Dused hgood.2).trans
          (by rfl)
    have hlegal : L ≤
        (reserveLegalEmbeddings P request reserve history).card := by
      dsimp [L, reserveLegalLowerBound]
      calc
        A - codimOneMeetingBound P n Dused ≤
            (reserveEmbeddings P (request history.length) reserve).card -
              (embeddingsMeeting P (request history.length)
                (usedEdges P history)).card := by
          exact (Nat.sub_le_sub_right (hbaseline history.length)
            (codimOneMeetingBound P n Dused)).trans
              (Nat.sub_le_sub_left hmeet
                (reserveEmbeddings P (request history.length) reserve).card)
        _ ≤ _ := card_reserveEmbeddings_sub_meeting_le_legal
          P request reserve history
    apply Finset.card_pos.mp
    exact hLpos.trans_le hlegal
  let probability : RelevantFaceLoadTarget P n → ℕ → ℝ :=
    fun target i ↦
      (faceLoadNumeratorAt P n (request i) target : ℝ) / L
  have hp : ∀ target i, 0 ≤ probability target i := by
    intro target i
    positivity
  have hcount : ∀ target history, good history →
      (((reserveLegalEmbeddings P request reserve history).filter
        fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
          probability target history.length *
            (reserveLegalEmbeddings P request reserve history).card := by
    intro target history hgood
    have hupperNat := card_reserveLegalEmbeddings_faceLoadHit_le
      P request reserve target history
    have hupperReal :
        (((reserveLegalEmbeddings P request reserve history).filter
          fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
            faceLoadNumeratorAt P n (request history.length) target := by
      exact_mod_cast hupperNat
    have hmeet :
        (embeddingsMeeting P (request history.length)
          (usedEdges P history)).card ≤ codimOneMeetingBound P n Dused :=
      (card_embeddingsMeeting_le_of_codimOne P
        (request history.length) (usedEdges P history)
        (fun g hg ↦ usedEdges_uniform P history hg) Dused hgood.2).trans
          (by rfl)
    have hlowerNat : L ≤
        (reserveLegalEmbeddings P request reserve history).card := by
      dsimp [L, reserveLegalLowerBound]
      exact ((Nat.sub_le_sub_right (hbaseline history.length)
        (codimOneMeetingBound P n Dused)).trans
          (Nat.sub_le_sub_left hmeet
            (reserveEmbeddings P (request history.length) reserve).card)).trans
        (card_reserveEmbeddings_sub_meeting_le_legal
          P request reserve history)
    have hlowerReal : (L : ℝ) ≤
        (reserveLegalEmbeddings P request reserve history).card := by
      exact_mod_cast hlowerNat
    calc
      (((reserveLegalEmbeddings P request reserve history).filter
          fun φ ↦ faceLoadHit P target history φ).card : ℝ) ≤
          faceLoadNumeratorAt P n (request history.length) target := hupperReal
      _ = probability target history.length * L := by
        dsimp [probability]
        have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hLpos)
        field_simp
      _ ≤ probability target history.length *
          (reserveLegalEmbeddings P request reserve history).card :=
        mul_le_mul_of_nonneg_left hlowerReal (hp target history.length)
  have hsmall :
      (∑ target : RelevantFaceLoadTarget P n,
        Real.exp (-(1 : ℝ) * C) *
          Real.exp ((Real.exp 1 - 1) *
            adaptiveBudget
              (fun i ↦
                (faceLoadNumeratorAt P n (request i) target : ℝ) / L)
              0 depth)) < 1 := by
    apply sum_exp_faceBudget_lt_one
      (budget := fun target ↦
        adaptiveBudget
          (fun i ↦
            (faceLoadNumeratorAt P n (request i) target : ℝ) / L)
          0 depth)
      (B := faceScheduleNumeratorBound P n Droot) (L := L) (C := C)
    · intro target
      exact adaptiveFaceBudget_le P request depth rootHost hschedule
        hrootUniform (Nat.sub_le r 1) Droot L hrootMax hr target
    · exact hquant
    · exact hcard
  apply exists_legal_path_with_load_caps_until_bad
    (reserveLegalEmbeddings P request reserve) good (faceLoadHit P)
    probability hp (t := 1) (by norm_num) hnonempty
  · intro target history hgoodHistory
    rw [sum_uniformStep_mul_hitBit
      (reserveLegalEmbeddings P request reserve) history
        (hnonempty history hgoodHistory)]
    have hcardPos : (0 : ℝ) <
        (reserveLegalEmbeddings P request reserve history).card := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty history hgoodHistory)
    exact (div_le_iff₀ hcardPos).2 (hcount target history hgoodHistory)
  · intro pref hlen hcaps hlegal
    constructor
    · simpa using hlen
    · intro J hJ
      simpa [Dused] using
        (localDegree_usedEdges_le_faceLoadCaps P [] pref J hJ C hcaps)
  · simpa [probability, L] using hsmall

end

end Erdos722.CoverEmbedding

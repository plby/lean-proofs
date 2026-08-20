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
import ErdosProblems.Erdos722.RootedFamilyEmbedding
import Mathlib

/-!
# Bounded repeated embeddings at every root

A bounded coefficient requires several independent gadget copies at the
same prescribed root.  This module schedules `multiplicity` copies of a
fixed pattern at every root, retaining exact root images, mutual separation,
forbidden-edge avoidance, and the final face-load bound.
-/

namespace Erdos722.RootedFamilyMultiEmbedding

open Finset
open Erdos722.Reserve
open Erdos722.RootedEmbedding
open Erdos722.RootSchedule
open Erdos722.CoverClique
open Erdos722.RandomGreedy
open Erdos722.AdaptiveChernoff

noncomputable section

structure BoundedMultiRootedFamilyEmbeddings
    {v r n : ℕ} (P : RootedPattern v r)
    (roots forbidden : Finset (Finset (Fin n)))
    (multiplicity C : ℕ) where
  embedding : (Q : Finset (Fin n)) → Q ∈ roots → Fin multiplicity →
    Fin v ↪ Fin n
  root_image : ∀ Q hQ t, mapEdge (embedding Q hQ t) P.root = Q
  free_disjoint_forbidden : ∀ Q hQ t,
    Disjoint (imageFreeEdges P (embedding Q hQ t)) forbidden
  free_pairwise : ∀ Q hQ (t : Fin multiplicity) Q' hQ'
      (t' : Fin multiplicity),
    (Q, (t : ℕ)) ≠ (Q', (t' : ℕ)) →
    Disjoint (imageFreeEdges P (embedding Q hQ t))
      (imageFreeEdges P (embedding Q' hQ' t'))
  freeUnion : Finset (Finset (Fin n))
  image_subset_freeUnion : ∀ Q hQ t,
    imageFreeEdges P (embedding Q hQ t) ⊆ freeUnion
  free_uniform : ∀ g ∈ freeUnion, g.card = r
  freeUnion_disjoint_forbidden : Disjoint freeUnion forbidden
  free_degree_le : ∀ J : Finset (Fin n), J.card = r - 1 →
    Reserve.localDegree freeUnion J ≤ P.freeEdges.card * C

/-- A bounded multi-rooted family together with the actual random-greedy
history and a finite family of additional counter bounds.  Retaining the
history is essential when a later construction has to count correlations
between two members of the family rather than only individual free-edge
loads. -/
structure TrackedBoundedMultiRootedFamilyEmbeddings
    {v r n : ℕ} (P : RootedPattern v r)
    (roots forbidden : Finset (Finset (Fin n)))
    (multiplicity C : ℕ) (beta : Type*)
    (extraHit : beta → List (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Bool)
    (extraCap : beta → ℕ)
    extends BoundedMultiRootedFamilyEmbeddings
      P roots forbidden multiplicity C where
  path : List (Fin v ↪ Fin n)
  path_length : path.length = roots.card * multiplicity
  position : (Q : Finset (Fin n)) → Q ∈ roots → Fin multiplicity →
    Fin path.length
  position_value : ∀ Q hQ t,
    (position Q hQ t).1 =
      (finProdFinEquiv (roots.equivFin ⟨Q, hQ⟩, t)).1
  position_injective : ∀ Q hQ t Q' hQ' t',
    position Q hQ t = position Q' hQ' t' →
      (Q, (t : ℕ)) = (Q', (t' : ℕ))
  embedding_at_position : ∀ Q hQ t,
    embedding Q hQ t = path.get (position Q hQ t)
  extra_lt : ∀ b : beta, pathHits (extraHit b) [] path < extraCap b

theorem exists_boundedMultiRootedFamilyEmbeddings_of_finite_bounds
    {v r n multiplicity Droot Dfixed C : ℕ}
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
        ((faceScheduleNumeratorBound P n (multiplicity * Droot) : ℝ) /
          rootedFaceLegalLowerBound P n Dfixed C) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card (RelevantFaceLoadTarget P n) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    Nonempty (BoundedMultiRootedFamilyEmbeddings
      P roots forbidden multiplicity C) := by
  classical
  let ambientEmbedding : Fin v ↪ Fin n :=
    Classical.choice (inferInstance : Nonempty (Fin v ↪ Fin n))
  letI : Nonempty (Fin n) :=
    ⟨ambientEmbedding ⟨0, by
      have hrootCard := Finset.card_le_univ P.root
      have : 0 < P.root.card := Finset.card_pos.mpr hrootNonempty
      simpa using this.trans_le hrootCard⟩⟩
  let depth := roots.card * multiplicity
  let decode : Fin depth → Fin roots.card × Fin multiplicity :=
    fun i ↦ finProdFinEquiv.symm i
  by_cases hm : multiplicity = 0
  · subst multiplicity
    refine ⟨{
      embedding := fun Q hQ t ↦ Fin.elim0 t
      root_image := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := ∅
      image_subset_freeUnion := ?_
      free_uniform := ?_
      freeUnion_disjoint_forbidden := ?_
      free_degree_le := ?_ }⟩
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro Q hQ t
      exact Fin.elim0 t
    · intro g hg
      simp at hg
    · simp
    · intro J hJ
      simp [Reserve.localDegree]
  · have hmpos : 0 < multiplicity := Nat.pos_of_ne_zero hm
    have hdepth : 0 < depth := by
      exact Nat.mul_pos (Finset.card_pos.mpr ⟨Q₀, hQ₀⟩) hmpos
    have hrequestExists (i : ℕ) :
        ∃ request : RootRequest v n P.root,
          requestImage P.root request =
            scheduledEdge roots Q₀
              (decode ⟨i % depth, Nat.mod_lt _ hdepth⟩).1.1 := by
      apply exists_rootRequest_with_image
      rw [hrootUniform (scheduledEdge roots Q₀ _)
        (scheduledEdge_mem roots hQ₀ _)]
    let request : ℕ → RootRequest v n P.root := fun i ↦
      Classical.choose (hrequestExists i)
    have hrequest (i : ℕ) :
        requestImage P.root (request i) =
          scheduledEdge roots Q₀
            (decode ⟨i % depth, Nat.mod_lt _ hdepth⟩).1.1 :=
      Classical.choose_spec (hrequestExists i)
    have hrequestFin (i : Fin depth) :
        requestImage P.root (request i.1) =
          scheduledEdge roots Q₀ (decode i).1.1 := by
      have himod : i.1 % depth = i.1 := Nat.mod_eq_of_lt i.2
      simpa [himod] using hrequest i.1
    have hschedule : IsRootImageScheduleMultiplicity P.root request depth
        roots multiplicity := by
      constructor
      · intro i
        rw [hrequestFin]
        exact scheduledEdge_mem roots hQ₀ _
      · intro Q hQ
        let fiber := (Finset.univ : Finset (Fin depth)).filter fun i ↦
          requestImage P.root (request i.1) = Q
        let layer : Fin depth → Fin multiplicity := fun i ↦ (decode i).2
        change fiber.card ≤ multiplicity
        calc
          fiber.card ≤ (Finset.univ : Finset (Fin multiplicity)).card := by
            apply Finset.card_le_card_of_injOn layer
            · intro i hi
              exact Finset.mem_univ _
            · intro i hi j hj hlayer
              have hiQ := (Finset.mem_filter.mp hi).2
              have hjQ := (Finset.mem_filter.mp hj).2
              rw [hrequestFin] at hiQ hjQ
              have hrootIndex : (decode i).1 = (decode j).1 := by
                exact scheduledEdge_injective_fin roots Q₀
                  (hiQ.trans hjQ.symm)
              have hdecode : decode i = decode j := by
                apply Prod.ext hrootIndex hlayer
              exact (Equiv.injective finProdFinEquiv.symm) hdecode
          _ = multiplicity := by simp
    have hcountBound : HasRootPartCountBound P request depth
        (multiplicity * Droot) := by
      intro e he I hI
      exact card_rootPartIndicesContaining_le_pow_mul_of_uniform_mul
        P request depth roots multiplicity hschedule hrootUniform hrootLarge
        Droot hrootMax e I hI
    obtain ⟨path, hlen, hpath, hcaps⟩ :=
      exists_legalEmbeddingPath_of_rootPartBound P request forbidden
        depth (multiplicity * Droot) Dfixed C hcountBound
        hforbiddenUniform hfixedMax hr hLpos hquant hcard
    let rootIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots) : Fin roots.card :=
      roots.equivFin ⟨Q, hQ⟩
    let scheduleIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots)
        (t : Fin multiplicity) : Fin depth :=
      finProdFinEquiv (rootIndex Q hQ, t)
    let pathIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots)
        (t : Fin multiplicity) : Fin path.length :=
      ⟨(scheduleIndex Q hQ t).1, by
        rw [hlen]
        exact (scheduleIndex Q hQ t).2⟩
    let embedding (Q : Finset (Fin n)) (hQ : Q ∈ roots)
        (t : Fin multiplicity) : Fin v ↪ Fin n :=
      path.get (pathIndex Q hQ t)
    have hscheduled (Q : Finset (Fin n)) (hQ : Q ∈ roots)
        (t : Fin multiplicity) :
        scheduledEdge roots Q₀ (decode (scheduleIndex Q hQ t)).1.1 = Q := by
      have hfin := scheduledEdge_fin roots Q₀ (rootIndex Q hQ)
      have hinv : roots.equivFin.symm (rootIndex Q hQ) = ⟨Q, hQ⟩ := by
        simp [rootIndex]
      have hdecode : decode (scheduleIndex Q hQ t) = (rootIndex Q hQ, t) := by
        exact finProdFinEquiv.symm_apply_apply _
      rw [hdecode]
      simpa [hinv] using hfin
    have hstep (Q : Finset (Fin n)) (hQ : Q ∈ roots)
        (t : Fin multiplicity) :
        embedding Q hQ t ∈ legalEmbeddings P request forbidden
          (path.take (pathIndex Q hQ t).1) := by
      have hmem := FollowsLegal.get_mem
        (legalEmbeddings P request forbidden) hpath (pathIndex Q hQ t)
      simpa [embedding] using hmem
    have hext (Q : Finset (Fin n)) (hQ : Q ∈ roots)
        (t : Fin multiplicity) :
        ExtendsRequest P.root (request (pathIndex Q hQ t).1)
          (embedding Q hQ t) := by
      have hx := (mem_legalEmbeddings.mp (hstep Q hQ t)).1
      simpa [List.length_take,
        Nat.min_eq_left (Nat.le_of_lt (pathIndex Q hQ t).2)] using hx
    refine ⟨{
      embedding := embedding
      root_image := ?_
      free_disjoint_forbidden := ?_
      free_pairwise := ?_
      freeUnion := usedEdges P path
      image_subset_freeUnion := ?_
      free_uniform := fun g hg ↦ usedEdges_uniform P path hg
      freeUnion_disjoint_forbidden := hpath.usedEdges_disjoint_forbidden
      free_degree_le := ?_ }⟩
    · intro Q hQ t
      have hreq := hrequestFin (scheduleIndex Q hQ t)
      exact (mapEdge_root_eq_requestImage_of_extends P.root
        (request (pathIndex Q hQ t).1) (embedding Q hQ t)
        (hext Q hQ t)).trans (by
          rw [show (pathIndex Q hQ t).1 = (scheduleIndex Q hQ t).1 by rfl]
          exact hreq.trans (hscheduled Q hQ t))
    · intro Q hQ t
      exact hpath.get_disjoint_forbidden (pathIndex Q hQ t)
    · intro Q hQ t Q' hQ' t' hne
      have hindexNe : pathIndex Q hQ t ≠ pathIndex Q' hQ' t' := by
        intro hidx
        have hval : scheduleIndex Q hQ t = scheduleIndex Q' hQ' t' := by
          apply Fin.ext
          exact congrArg (fun z : Fin path.length ↦ z.1) hidx
        have hpair : (rootIndex Q hQ, t) = (rootIndex Q' hQ', t') :=
          finProdFinEquiv.injective hval
        have hrootEq : Q = Q' := by
          have hri : rootIndex Q hQ = rootIndex Q' hQ' := congrArg Prod.fst hpair
          have hsub : (⟨Q, hQ⟩ : ↑roots) = ⟨Q', hQ'⟩ :=
            roots.equivFin.injective hri
          exact congrArg Subtype.val hsub
        have htEq : (t : ℕ) = (t' : ℕ) :=
          congrArg (fun z : Fin roots.card × Fin multiplicity ↦ (z.2 : ℕ)) hpair
        exact hne (by simp [hrootEq, htEq])
      exact hpath.pairwise_disjoint
        (pathIndex Q hQ t) (pathIndex Q' hQ' t') hindexNe
    · intro Q hQ t g hg
      apply Finset.mem_biUnion.mpr
      refine ⟨embedding Q hQ t, ?_, hg⟩
      simp [embedding]
    · intro J hJ
      exact localDegree_usedEdges_le_faceLoadCaps P [] path J hJ C hcaps

/-- The repeated rooted-family construction with a finite family of extra
Boolean counters.  The extra one-step estimate is supplied as a cardinality
bound uniform over every root-request schedule; the theorem divides it by
the same legal-embedding lower bound used for the ordinary face counters. -/
theorem exists_trackedBoundedMultiRootedFamilyEmbeddings_of_finite_bounds
    {v r n multiplicity Droot Dfixed C : ℕ}
    {beta : Type*} [Fintype beta]
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
    (hr : 0 < r) (hmultiplicity : 0 < multiplicity)
    (hLpos : 0 < rootedFaceLegalLowerBound P n Dfixed C)
    (extraHit : beta → List (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Bool)
    (extraNumerator : beta → ℕ)
    (hextraCard : ∀ (b : beta)
      (request : ℕ → RootRequest v n P.root) history,
      ((legalEmbeddings P request forbidden history).filter fun phi ↦
        extraHit b history phi).card ≤ extraNumerator b)
    (B : ℕ)
    (hfaceBudget : faceScheduleNumeratorBound P n
      (multiplicity * Droot) ≤ B)
    (hextraBudget : ∀ b, roots.card * multiplicity * extraNumerator b ≤ B)
    (hquant : (Real.exp 1 - 1) *
      ((B : ℝ) / rootedFaceLegalLowerBound P n Dfixed C) ≤ (C : ℝ) / 2)
    (hcard : (Fintype.card
      (Sum (RelevantFaceLoadTarget P n) beta) : ℝ) *
        Real.exp (-(C : ℝ) / 2) < 1) :
    Nonempty (TrackedBoundedMultiRootedFamilyEmbeddings
      P roots forbidden multiplicity C beta extraHit (fun _ ↦ C)) := by
  classical
  let ambientEmbedding : Fin v ↪ Fin n :=
    Classical.choice (inferInstance : Nonempty (Fin v ↪ Fin n))
  letI : Nonempty (Fin n) :=
    ⟨ambientEmbedding ⟨0, by
      have hrootCard := Finset.card_le_univ P.root
      have : 0 < P.root.card := Finset.card_pos.mpr hrootNonempty
      simpa using this.trans_le hrootCard⟩⟩
  let depth := roots.card * multiplicity
  have hdepth : 0 < depth :=
    Nat.mul_pos (Finset.card_pos.mpr ⟨Q₀, hQ₀⟩) hmultiplicity
  let decode : Fin depth → Fin roots.card × Fin multiplicity :=
    fun i ↦ finProdFinEquiv.symm i
  have hrequestExists (i : ℕ) :
      ∃ request : RootRequest v n P.root,
        requestImage P.root request =
          scheduledEdge roots Q₀
            (decode ⟨i % depth, Nat.mod_lt _ hdepth⟩).1.1 := by
    apply exists_rootRequest_with_image
    rw [hrootUniform (scheduledEdge roots Q₀ _)
      (scheduledEdge_mem roots hQ₀ _)]
  let request : ℕ → RootRequest v n P.root := fun i ↦
    Classical.choose (hrequestExists i)
  have hrequest (i : ℕ) :
      requestImage P.root (request i) =
        scheduledEdge roots Q₀
          (decode ⟨i % depth, Nat.mod_lt _ hdepth⟩).1.1 :=
    Classical.choose_spec (hrequestExists i)
  have hrequestFin (i : Fin depth) :
      requestImage P.root (request i.1) =
        scheduledEdge roots Q₀ (decode i).1.1 := by
    have himod : i.1 % depth = i.1 := Nat.mod_eq_of_lt i.2
    simpa [himod] using hrequest i.1
  have hschedule : IsRootImageScheduleMultiplicity P.root request depth
      roots multiplicity := by
    constructor
    · intro i
      rw [hrequestFin]
      exact scheduledEdge_mem roots hQ₀ _
    · intro Q hQ
      let fiber := (Finset.univ : Finset (Fin depth)).filter fun i ↦
        requestImage P.root (request i.1) = Q
      let layer : Fin depth → Fin multiplicity := fun i ↦ (decode i).2
      change fiber.card ≤ multiplicity
      calc
        fiber.card ≤ (Finset.univ : Finset (Fin multiplicity)).card := by
          apply Finset.card_le_card_of_injOn layer
          · intro i hi
            exact Finset.mem_univ _
          · intro i hi j hj hlayer
            have hiQ := (Finset.mem_filter.mp hi).2
            have hjQ := (Finset.mem_filter.mp hj).2
            rw [hrequestFin] at hiQ hjQ
            have hrootIndex : (decode i).1 = (decode j).1 :=
              scheduledEdge_injective_fin roots Q₀ (hiQ.trans hjQ.symm)
            have hdecode : decode i = decode j :=
              Prod.ext hrootIndex hlayer
            exact (Equiv.injective finProdFinEquiv.symm) hdecode
        _ = multiplicity := by simp
  have hcountBound : HasRootPartCountBound P request depth
      (multiplicity * Droot) := by
    intro e he I hI
    exact card_rootPartIndicesContaining_le_pow_mul_of_uniform_mul
      P request depth roots multiplicity hschedule hrootUniform hrootLarge
      Droot hrootMax e I hI
  let L := rootedFaceLegalLowerBound P n Dfixed C
  let extraProbability : beta → ℕ → ℝ := fun b _ ↦
    (extraNumerator b : ℝ) / L
  have hextraProbability : ∀ b i, 0 ≤ extraProbability b i := by
    intro b i
    dsimp [extraProbability]
    positivity
  have hextraMean : ∀ b history,
      history.length ≤ depth →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree (usedEdges P history) J ≤
          P.freeEdges.card * C) →
      (∑ phi : Fin v ↪ Fin n,
        uniformStep (legalEmbeddings P request forbidden) history phi *
          hitBit (extraHit b) history phi) ≤
        extraProbability b history.length := by
    intro b history _hlen hused
    have hlowerNat : L ≤
        (legalEmbeddings P request forbidden history).card := by
      apply codimOneMeetingBound_sub_le_card_legalEmbeddings
        P request forbidden history Dfixed (P.freeEdges.card * C)
        hforbiddenUniform (fun g hg ↦ usedEdges_uniform P history hg)
        hfixedMax
      exact hused
    have hnonempty :
        (legalEmbeddings P request forbidden history).Nonempty := by
      apply Finset.card_pos.mp
      exact hLpos.trans_le hlowerNat
    rw [sum_uniformStep_mul_hitBit
      (legalEmbeddings P request forbidden) history hnonempty]
    have hupperNat := hextraCard b request history
    have hupperReal :
        (((legalEmbeddings P request forbidden history).filter fun phi ↦
          extraHit b history phi).card : ℝ) ≤ extraNumerator b := by
      exact_mod_cast hupperNat
    have hlowerReal : (L : ℝ) ≤
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast hlowerNat
    have hcardPos : (0 : ℝ) <
        (legalEmbeddings P request forbidden history).card := by
      exact_mod_cast Finset.card_pos.mpr hnonempty
    apply (div_le_iff₀ hcardPos).2
    calc
      (((legalEmbeddings P request forbidden history).filter fun phi ↦
          extraHit b history phi).card : ℝ) ≤ extraNumerator b := hupperReal
      _ = extraProbability b history.length * L := by
        dsimp [extraProbability]
        have hLReal : (0 : ℝ) < L := by exact_mod_cast hLpos
        field_simp [ne_of_gt hLReal]
      _ ≤ extraProbability b history.length *
          (legalEmbeddings P request forbidden history).card :=
        mul_le_mul_of_nonneg_left hlowerReal
          (hextraProbability b history.length)
  have hsmall' :
      (∑ target : Sum (RelevantFaceLoadTarget P n) beta,
        Real.exp (-(1 : ℝ) *
          (match target with
          | Sum.inl _ => C
          | Sum.inr _ => C)) *
        Real.exp ((Real.exp 1 - 1) *
          adaptiveBudget
            (match target with
            | Sum.inl face => fun i ↦
                (faceLoadNumeratorAt P n (request i) face : ℝ) / L
            | Sum.inr b => extraProbability b)
            0 depth)) < 1 := by
    have hcommon :
        (∑ target : Sum (RelevantFaceLoadTarget P n) beta,
          Real.exp (-(1 : ℝ) * C) *
            Real.exp ((Real.exp 1 - 1) *
              adaptiveBudget
                (match target with
                | Sum.inl face => fun i ↦
                    (faceLoadNumeratorAt P n (request i) face : ℝ) / L
                | Sum.inr b => extraProbability b)
                0 depth)) < 1 := by
      norm_num only [Nat.cast_one]
      apply sum_exp_faceBudget_lt_one
        (β := Sum (RelevantFaceLoadTarget P n) beta)
        (budget := fun target ↦ adaptiveBudget
          (match target with
          | Sum.inl face => fun i ↦
              (faceLoadNumeratorAt P n (request i) face : ℝ) / L
          | Sum.inr b => extraProbability b) 0 depth)
        (B := B) (L := L) (C := C)
      · intro target
        rcases target with face | b
        · have hface := adaptiveFaceBudget_le_of_bound
            P request depth (multiplicity * Droot) L hcountBound hr face
          exact hface.trans (div_le_div_of_nonneg_right
            (by exact_mod_cast hfaceBudget) (Nat.cast_nonneg L))
        · rw [adaptiveBudget_const]
          have hbudgetReal :
              ((roots.card * multiplicity * extraNumerator b : ℕ) : ℝ) ≤ B := by
            exact_mod_cast hextraBudget b
          calc
            (depth : ℝ) * extraProbability b 0 =
                ((roots.card * multiplicity * extraNumerator b : ℕ) : ℝ) /
                  L := by
              simp [depth, extraProbability]
              ring
            _ ≤ (B : ℝ) / L :=
              div_le_div_of_nonneg_right hbudgetReal (Nat.cast_nonneg L)
      · simpa [L] using hquant
      · exact hcard
    convert hcommon using 1
    apply Finset.sum_congr rfl
    intro target htarget
    rcases target with face | b <;> rfl
  obtain ⟨path, hlen, hpath, hcaps, hextra⟩ :=
    exists_legalEmbeddingPath_of_faceLoads_and_extra
      (t := 1)
      P request forbidden depth Dfixed C hforbiddenUniform hfixedMax
      hLpos extraHit extraProbability hextraProbability (fun _ ↦ C)
      hextraMean (by norm_num) (by simpa [L] using hsmall')
  let rootIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots) : Fin roots.card :=
    roots.equivFin ⟨Q, hQ⟩
  let scheduleIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots)
      (u : Fin multiplicity) : Fin depth :=
    finProdFinEquiv (rootIndex Q hQ, u)
  let pathIndex (Q : Finset (Fin n)) (hQ : Q ∈ roots)
      (u : Fin multiplicity) : Fin path.length :=
    ⟨(scheduleIndex Q hQ u).1, by
      rw [hlen]
      exact (scheduleIndex Q hQ u).2⟩
  let embedding (Q : Finset (Fin n)) (hQ : Q ∈ roots)
      (u : Fin multiplicity) : Fin v ↪ Fin n :=
    path.get (pathIndex Q hQ u)
  have hscheduled (Q : Finset (Fin n)) (hQ : Q ∈ roots)
      (u : Fin multiplicity) :
      scheduledEdge roots Q₀ (decode (scheduleIndex Q hQ u)).1.1 = Q := by
    have hfin := scheduledEdge_fin roots Q₀ (rootIndex Q hQ)
    have hinv : roots.equivFin.symm (rootIndex Q hQ) = ⟨Q, hQ⟩ := by
      simp [rootIndex]
    have hdecode : decode (scheduleIndex Q hQ u) = (rootIndex Q hQ, u) :=
      finProdFinEquiv.symm_apply_apply _
    rw [hdecode]
    simpa [hinv] using hfin
  have hstep (Q : Finset (Fin n)) (hQ : Q ∈ roots)
      (u : Fin multiplicity) :
      embedding Q hQ u ∈ legalEmbeddings P request forbidden
        (path.take (pathIndex Q hQ u).1) := by
    have hmem := FollowsLegal.get_mem
      (legalEmbeddings P request forbidden) hpath (pathIndex Q hQ u)
    simpa [embedding] using hmem
  have hext (Q : Finset (Fin n)) (hQ : Q ∈ roots)
      (u : Fin multiplicity) :
      ExtendsRequest P.root (request (pathIndex Q hQ u).1)
        (embedding Q hQ u) := by
    have hx := (mem_legalEmbeddings.mp (hstep Q hQ u)).1
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (pathIndex Q hQ u).2)] using hx
  have hpositionInjective : ∀ Q hQ u Q' hQ' u',
      pathIndex Q hQ u = pathIndex Q' hQ' u' →
        (Q, (u : ℕ)) = (Q', (u' : ℕ)) := by
    intro Q hQ u Q' hQ' u' hidx
    have hval : scheduleIndex Q hQ u = scheduleIndex Q' hQ' u' := by
      apply Fin.ext
      exact congrArg (fun z : Fin path.length ↦ z.1) hidx
    have hpair : (rootIndex Q hQ, u) = (rootIndex Q' hQ', u') :=
      finProdFinEquiv.injective hval
    have hrootEq : Q = Q' := by
      have hri : rootIndex Q hQ = rootIndex Q' hQ' := congrArg Prod.fst hpair
      have hsub : (⟨Q, hQ⟩ : ↑roots) = ⟨Q', hQ'⟩ :=
        roots.equivFin.injective hri
      exact congrArg Subtype.val hsub
    have huEq : (u : ℕ) = (u' : ℕ) :=
      congrArg (fun z : Fin roots.card × Fin multiplicity ↦ (z.2 : ℕ)) hpair
    simp [hrootEq, huEq]
  refine ⟨{
    embedding := embedding
    root_image := ?_
    free_disjoint_forbidden := ?_
    free_pairwise := ?_
    freeUnion := usedEdges P path
    image_subset_freeUnion := ?_
    free_uniform := fun g hg ↦ usedEdges_uniform P path hg
    freeUnion_disjoint_forbidden := hpath.usedEdges_disjoint_forbidden
    free_degree_le := ?_
    path := path
    path_length := hlen
    position := pathIndex
    position_value := ?_
    position_injective := hpositionInjective
    embedding_at_position := ?_
    extra_lt := hextra }⟩
  · intro Q hQ u
    have hreq := hrequestFin (scheduleIndex Q hQ u)
    exact (mapEdge_root_eq_requestImage_of_extends P.root
      (request (pathIndex Q hQ u).1) (embedding Q hQ u)
      (hext Q hQ u)).trans (by
        rw [show (pathIndex Q hQ u).1 = (scheduleIndex Q hQ u).1 by rfl]
        exact hreq.trans (hscheduled Q hQ u))
  · intro Q hQ u
    exact hpath.get_disjoint_forbidden (pathIndex Q hQ u)
  · intro Q hQ u Q' hQ' u' hne
    apply hpath.pairwise_disjoint
      (pathIndex Q hQ u) (pathIndex Q' hQ' u')
    intro hidx
    exact hne (hpositionInjective Q hQ u Q' hQ' u' hidx)
  · intro Q hQ u g hg
    apply Finset.mem_biUnion.mpr
    refine ⟨embedding Q hQ u, ?_, hg⟩
    simp [embedding]
  · intro J hJ
    exact localDegree_usedEdges_le_faceLoadCaps P [] path J hJ C hcaps
  · intro Q hQ u
    rfl
  · intro Q hQ u
    rfl

end

end Erdos722.RootedFamilyMultiEmbedding

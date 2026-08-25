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
import ErdosProblems.Erdos76.PippengerSpencerLocality
import ErdosProblems.Erdos76.FiniteProductBoundedDifferences

/-!
# The fixed-length inner matching generator

One colour in the Pippenger--Spencer nibble is not a single altered
Bernoulli sample.  It is a fixed finite sequence of alteration rounds.  At
each round we discard sampled edges which conflict with the matching already
built, isolate the remaining sampled edges, and add those isolated edges.

This file gives the completely finite algorithm and its explicit product
probability space.  Quantitative marginal estimates and locality estimates
can therefore be proved without any measure-theoretic or asymptotic oracle.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- From the new sample retain only edges which are new and disjoint from
every edge already in the partial matching. -/
def liveSample (H : FiniteHypergraph V E) (M S : Finset E) : Finset E :=
  S.filter fun e ↦ e ∉ M ∧ ∀ f ∈ M, Disjoint (H.support e) (H.support f)

lemma liveSample_subset_sample (H : FiniteHypergraph V E) (M S : Finset E) :
    H.liveSample M S ⊆ S := by
  exact filter_subset _ _

lemma liveSample_disjoint_old
    (H : FiniteHypergraph V E) {M S : Finset E} {e : E}
    (he : e ∈ H.liveSample M S) {f : E} (hf : f ∈ M) :
    Disjoint (H.support e) (H.support f) := by
  exact (mem_filter.mp he).2.2 f hf

/-- One inner alteration step. -/
def innerStep (H : FiniteHypergraph V E) (M S : Finset E) : Finset E :=
  M ∪ H.isolatedSample (H.liveSample M S)

lemma subset_innerStep (H : FiniteHypergraph V E) (M S : Finset E) :
    M ⊆ H.innerStep M S := by
  exact subset_union_left

/-- A single step preserves the matching invariant. -/
lemma innerStep_isMatching (H : FiniteHypergraph V E)
    {M : Finset E} (hM : H.IsMatching M) (S : Finset E) :
    H.IsMatching (H.innerStep M S) := by
  intro e he f hf hef
  rcases mem_union.mp he with heM | heNew
  · rcases mem_union.mp hf with hfM | hfNew
    · exact hM heM hfM hef
    · have hfLive : f ∈ H.liveSample M S :=
        H.isolatedSample_subset _ hfNew
      exact (H.liveSample_disjoint_old hfLive heM).symm
  · rcases mem_union.mp hf with hfM | hfNew
    · have heLive : e ∈ H.liveSample M S :=
        H.isolatedSample_subset _ heNew
      exact H.liveSample_disjoint_old heLive hfM
    · exact H.isolatedSample_isMatching (H.liveSample M S) heNew hfNew hef

/-- Membership of one edge after one inner step only uses the old matching
inside its radius-two conflict ball and the new sample inside radius one. -/
lemma innerStep_mem_iff_of_local_agreement
    (H : FiniteHypergraph V E) {M N S T : Finset E} {e : E}
    (hstate : ∀ f ∈ H.conflictBall 2 e, f ∈ M ↔ f ∈ N)
    (hsample : ∀ f ∈ H.conflictBall 1 e, f ∈ S ↔ f ∈ T) :
    e ∈ H.innerStep M S ↔ e ∈ H.innerStep N T := by
  have hself1 : e ∈ H.conflictBall 1 e := H.mem_conflictBall_self 1 e
  have hself2 : e ∈ H.conflictBall 2 e := H.mem_conflictBall_self 2 e
  have hlive : ∀ f ∈ H.conflictBall 1 e,
      f ∈ H.liveSample M S ↔ f ∈ H.liveSample N T := by
    intro f hf
    have hf2 : f ∈ H.conflictBall 2 e :=
      H.conflictBall_mono_radius 1 e hf
    constructor
    · intro hfm
      obtain ⟨hfS, hfM, hall⟩ := mem_filter.mp hfm
      apply mem_filter.mpr
      refine ⟨(hsample f hf).mp hfS, ?_, ?_⟩
      · exact fun hfN ↦ hfM ((hstate f hf2).mpr hfN)
      · intro g hgN
        by_cases hd : Disjoint (H.support f) (H.support g)
        · exact hd
        · have hfg : g ∈ H.conflictBall 1 f := by
            rw [conflictBall_succ, mem_conflictExpand]
            refine ⟨f, by simp, ?_⟩
            rw [H.mem_closedConflictNeighborhood]
            by_cases hgf : g = f
            · exact Or.inl hgf
            · exact Or.inr ⟨fun hfg ↦ hgf hfg.symm, hd⟩
          have hg2 : g ∈ H.conflictBall 2 e := by
            simpa using H.conflictBall_comp hf 1 hfg
          exact hall g ((hstate g hg2).mpr hgN)
    · intro hfn
      obtain ⟨hfT, hfN, hall⟩ := mem_filter.mp hfn
      apply mem_filter.mpr
      refine ⟨(hsample f hf).mpr hfT, ?_, ?_⟩
      · exact fun hfM ↦ hfN ((hstate f hf2).mp hfM)
      · intro g hgM
        by_cases hd : Disjoint (H.support f) (H.support g)
        · exact hd
        · have hfg : g ∈ H.conflictBall 1 f := by
            rw [conflictBall_succ, mem_conflictExpand]
            refine ⟨f, by simp, ?_⟩
            rw [H.mem_closedConflictNeighborhood]
            by_cases hgf : g = f
            · exact Or.inl hgf
            · exact Or.inr ⟨fun hfg ↦ hgf hfg.symm, hd⟩
          have hg2 : g ∈ H.conflictBall 2 e := by
            simpa using H.conflictBall_comp hf 1 hfg
          exact hall g ((hstate g hg2).mp hgM)
  have hisolated :
      e ∈ H.isolatedSample (H.liveSample M S) ↔
        e ∈ H.isolatedSample (H.liveSample N T) := by
    constructor
    · intro heM
      apply mem_filter.mpr
      refine ⟨(hlive e hself1).mp (mem_filter.mp heM).1, ?_⟩
      intro f hfN hef
      by_cases hd : Disjoint (H.support e) (H.support f)
      · exact hd
      · have hf1 : f ∈ H.conflictBall 1 e := by
          rw [conflictBall_succ, mem_conflictExpand]
          refine ⟨e, by simp, ?_⟩
          rw [H.mem_closedConflictNeighborhood]
          exact Or.inr ⟨hef, hd⟩
        exact (mem_filter.mp heM).2 f ((hlive f hf1).mpr hfN) hef
    · intro heN
      apply mem_filter.mpr
      refine ⟨(hlive e hself1).mpr (mem_filter.mp heN).1, ?_⟩
      intro f hfM hef
      by_cases hd : Disjoint (H.support e) (H.support f)
      · exact hd
      · have hf1 : f ∈ H.conflictBall 1 e := by
          rw [conflictBall_succ, mem_conflictExpand]
          refine ⟨e, by simp, ?_⟩
          rw [H.mem_closedConflictNeighborhood]
          exact Or.inr ⟨hef, hd⟩
        exact (mem_filter.mp heN).2 f ((hlive f hf1).mp hfM) hef
  simp only [innerStep, mem_union]
  exact or_congr (hstate e hself2) hisolated

/-- Run the inner alteration process through a finite list of samples. -/
def innerMatchingList (H : FiniteHypergraph V E) (samples : List (Finset E)) : Finset E :=
  samples.foldl H.innerStep ∅

/-- State after `r` rounds of a fixed-length input.  For `r > L` it remains
constant; the intended uses have `r ≤ L`. -/
def innerState (H : FiniteHypergraph V E) {L : ℕ}
    (X : Fin L → Finset E) : ℕ → Finset E
  | 0 => ∅
  | r + 1 => if hr : r < L then
      H.innerStep (H.innerState X r) (X ⟨r, hr⟩)
    else H.innerState X r

/-- The fixed-length generated matching. -/
def innerMatching (H : FiniteHypergraph V E) {L : ℕ}
    (X : Fin L → Finset E) : Finset E :=
  H.innerState X L

lemma innerMatchingList_isMatching (H : FiniteHypergraph V E)
    (samples : List (Finset E)) : H.IsMatching (H.innerMatchingList samples) := by
  have haux : ∀ (samples : List (Finset E)) (M : Finset E), H.IsMatching M →
      H.IsMatching (samples.foldl H.innerStep M) := by
    intro samples
    induction samples with
    | nil =>
        intro M hM
        simpa using hM
    | cons S samples ih =>
        intro M hM
        simp only [List.foldl_cons]
        exact ih (H.innerStep M S) (H.innerStep_isMatching hM S)
  exact haux samples ∅ H.empty_isMatching

lemma innerMatching_isMatching (H : FiniteHypergraph V E) {L : ℕ}
    (X : Fin L → Finset E) : H.IsMatching (H.innerMatching X) := by
  have hstate : ∀ r, H.IsMatching (H.innerState X r) := by
    intro r
    induction r with
    | zero => exact H.empty_isMatching
    | succ r ih =>
        rw [innerState]
        split
        · exact H.innerStep_isMatching ih _
        · exact ih
  exact hstate L

/-- Conflict balls are monotone in their radius. -/
lemma conflictBall_mono_of_le (H : FiniteHypergraph V E) {r s : ℕ}
    (hrs : r ≤ s) (e : E) : H.conflictBall r e ⊆ H.conflictBall s e := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrs
  intro f hf
  exact H.conflictBall_comp hf t (H.mem_conflictBall_self t f)

/-- After `r` inner rounds, membership of `e` only uses input samples in
the radius-`2r+1` conflict ball around `e`. -/
lemma innerState_mem_iff_of_sample_agreement
    (H : FiniteHypergraph V E) {L r : ℕ}
    {X Y : Fin L → Finset E} {e : E} (hr : r ≤ L)
    (hXY : ∀ i : Fin L, ∀ f ∈ H.conflictBall (2 * r + 1) e,
      f ∈ X i ↔ f ∈ Y i) :
    e ∈ H.innerState X r ↔ e ∈ H.innerState Y r := by
  induction r generalizing e with
  | zero => simp [innerState]
  | succ r ih =>
      have hrL : r < L := by omega
      rw [innerState, innerState, dif_pos hrL, dif_pos hrL]
      apply H.innerStep_mem_iff_of_local_agreement
      · intro f hf
        apply ih (by omega)
        intro i g hg
        apply hXY i g
        have hge : g ∈ H.conflictBall (2 + (2 * r + 1)) e :=
          H.conflictBall_comp hf (2 * r + 1) hg
        have harith : 2 + (2 * r + 1) = 2 * (r + 1) + 1 := by omega
        rw [← harith]
        exact hge
      · intro f hf
        apply hXY ⟨r, hrL⟩ f
        exact H.conflictBall_mono_of_le (by omega) e hf

lemma innerMatchingList_mono_initial (H : FiniteHypergraph V E)
    (samples : List (Finset E)) (M : Finset E) :
    M ⊆ samples.foldl H.innerStep M := by
  induction samples generalizing M with
  | nil => simp
  | cons S samples ih =>
      exact (H.subset_innerStep M S).trans (ih (H.innerStep M S))

/-- Explicit product mass that a fixed edge belongs to the generated
matching. -/
def innerAcceptanceMass (H : FiniteHypergraph V E) (L : ℕ)
    (p : E → ℝ) (e : E) : ℝ :=
  ∑ X : Fin L → Finset E,
    FiniteProduct.productMass (FiniteNibble.bernoulliMass univ p) X *
      if e ∈ H.innerMatching X then 1 else 0

/-- Coordinates in the radius-`2L+1` conflict ball which may influence the
membership of `e` in the fixed-length inner matching. -/
def innerEdgeInfluenceSupport (H : FiniteHypergraph V E) (L : ℕ) (e : E) :
    Finset (Fin L × E) :=
  (univ : Finset (Fin L)).product (H.conflictBall (2 * L + 1) e)

@[simp] lemma mem_innerEdgeInfluenceSupport
    (H : FiniteHypergraph V E) (L : ℕ) (e : E) (z : Fin L × E) :
    z ∈ H.innerEdgeInfluenceSupport L e ↔
      z.2 ∈ H.conflictBall (2 * L + 1) e := by
  simp [innerEdgeInfluenceSupport]

lemma innerEdgeInfluenceSupport_card_le
    {H : FiniteHypergraph V E} {k D L : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) :
    (H.innerEdgeInfluenceSupport L e).card ≤
      L * (k * D + 1) ^ (2 * L + 1) := by
  unfold innerEdgeInfluenceSupport
  change (((univ : Finset (Fin L)) ×ˢ
    H.conflictBall (2 * L + 1) e).card ≤ _)
  rw [card_product, card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_left L
    (H.conflictBall_card_le hunif hdeg (2 * L + 1) e)

/-- The event that the fixed-length inner generator accepts `e`, expressed
on flattened Bernoulli coordinates. -/
def innerAcceptedEvent (H : FiniteHypergraph V E) (L : ℕ) (e : E)
    (Z : Finset (Fin L × E)) : Prop :=
  e ∈ H.innerMatching (fun i ↦ batchAt Z i)

end FiniteHypergraph

end

end Erdos76

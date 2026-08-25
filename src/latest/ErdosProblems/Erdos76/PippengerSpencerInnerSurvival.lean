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
import ErdosProblems.Erdos76.PippengerSpencerInnerMarginal

/-!
# Survival identities for the fixed-length inner generator

The sharp marginal calculation is a survival calculation.  This file
records the exact deterministic bridge: an edge is live precisely when it
has not already been accepted and every vertex in its support is uncovered.
Consequently, sharpness requires a joint uncovered-vertex estimate; a union
bound over the `k` vertices is not sufficient.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Exact deterministic characterization of a live edge. -/
lemma innerLive_iff_not_mem_and_uncovered
    (H : FiniteHypergraph V E) (M : Finset E) (e : E) :
    H.InnerLive M e ↔
      e ∉ M ∧ ∀ v ∈ H.support e, H.UncoveredBy M v := by
  constructor
  · intro hlive
    have hfilter := mem_filter.mp hlive
    refine ⟨hfilter.2.1, ?_⟩
    intro v hve f hfM hvf
    exact (Finset.disjoint_left.mp (hfilter.2.2 f hfM)) hve hvf
  · rintro ⟨heM, hall⟩
    rw [InnerLive, liveSample, mem_filter]
    refine ⟨mem_univ e, heM, ?_⟩
    intro f hfM
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact hall v hve f hfM hvf

@[simp] lemma innerLive_empty (H : FiniteHypergraph V E) (e : E) :
    H.InnerLive ∅ e := by
  simp [InnerLive, liveSample]

/-- When the edge support is nonempty, the separate `e ∉ M` condition is
already forced by all its vertices being uncovered. -/
lemma innerLive_iff_uncovered_of_support_nonempty
    (H : FiniteHypergraph V E) (M : Finset E) (e : E)
    (hne : (H.support e).Nonempty) :
    H.InnerLive M e ↔ ∀ v ∈ H.support e, H.UncoveredBy M v := by
  rw [H.innerLive_iff_not_mem_and_uncovered]
  constructor
  · exact fun h ↦ h.2
  · intro hall
    refine ⟨?_, hall⟩
    intro heM
    obtain ⟨v, hve⟩ := hne
    exact hall v hve e heM hve

/-- Positive uniformity guarantees the nonempty-support version of the
survival identity for every indexed edge. -/
lemma innerLive_iff_uncovered_of_uniform
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (e : E) :
    H.InnerLive M e ↔ ∀ v ∈ H.support e, H.UncoveredBy M v := by
  apply H.innerLive_iff_uncovered_of_support_nonempty
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have := hunif e
  rw [hempty, card_empty] at this
  omega

/-- Explicit product mass that `e` is live after `r` independent inner
rounds, starting from the partial matching `M`.  This is the summand hidden
inside `innerLiveTimeKernel`. -/
def innerLiveMass (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (e : E) : ℝ :=
  ∑ X : Fin r → Finset E,
    FiniteProduct.productMass w X *
      if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e then 1 else 0

@[simp] lemma innerLiveMass_zero
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (M : Finset E) (e : E) :
    H.innerLiveMass w 0 M e = if H.InnerLive M e then 1 else 0 := by
  simp [innerLiveMass, FiniteProduct.productMass]

@[simp] lemma innerLiveMass_zero_empty
    (H : FiniteHypergraph V E) (w : Finset E → ℝ) (e : E) :
    H.innerLiveMass w 0 ∅ e = 1 := by
  simp

/-- Under positive uniformity, the explicit survival mass is exactly the
mass of the joint event that all vertices of `e` remain uncovered. -/
lemma innerLiveMass_eq_sum_all_uncovered_of_uniform
    {H : FiniteHypergraph V E} {k r : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (w : Finset E → ℝ)
    (M : Finset E) (e : E) :
    H.innerLiveMass w r M e =
      ∑ X : Fin r → Finset E,
        FiniteProduct.productMass w X *
          if ∀ v ∈ H.support e,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0 := by
  unfold innerLiveMass
  apply sum_congr rfl
  intro X _
  by_cases h : ∀ v ∈ H.support e,
      H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
  · have hlive : H.InnerLive ((List.ofFn X).foldl H.innerStep M) e :=
      (H.innerLive_iff_uncovered_of_uniform hk hunif _ _).2 h
    rw [if_pos hlive, if_pos h]
  · have hnot : ¬H.InnerLive ((List.ofFn X).foldl H.innerStep M) e :=
      fun hlive ↦ h
        ((H.innerLive_iff_uncovered_of_uniform hk hunif _ _).1 hlive)
    rw [if_neg hnot, if_neg h]

/-- Splitting off the first sample gives the one-step recursion for the
explicit survival mass. -/
lemma innerLiveMass_succ
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (e : E) :
    H.innerLiveMass w (r + 1) M e =
      ∑ S : Finset E, w S * H.innerLiveMass w r (H.innerStep M S) e := by
  unfold innerLiveMass
  calc
    (∑ X : Fin (r + 1) → Finset E,
        FiniteProduct.productMass w X *
          if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e then 1 else 0) =
        ∑ z : Finset E × (Fin r → Finset E),
          FiniteProduct.productMass w
              ((Fin.consEquiv (fun _ : Fin (r + 1) ↦ Finset E)) z) *
            if H.InnerLive
                ((List.ofFn
                  ((Fin.consEquiv (fun _ : Fin (r + 1) ↦ Finset E)) z)).foldl
                    H.innerStep M) e then 1 else 0 :=
      (Fin.consEquiv (fun _ : Fin (r + 1) ↦ Finset E)).sum_comp
        (fun X ↦ FiniteProduct.productMass w X *
          if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e then 1 else 0) |>.symm
    _ = ∑ S : Finset E, w S *
          ∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X *
              if H.InnerLive
                  ((List.ofFn X).foldl H.innerStep (H.innerStep M S)) e
                then 1 else 0 := by
      simp only [Fintype.sum_prod_type, Fin.consEquiv_apply,
        FiniteProduct.productMass, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, List.ofFn_succ, List.foldl_cons, mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro X _
      ring

/-- The recursive expected live time is exactly the sum, over all starting
rounds, of the corresponding finite-product survival masses. -/
theorem innerLiveTimeKernel_eq_sum_innerLiveMass
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (L : ℕ) (M : Finset E) (e : E) :
    H.innerLiveTimeKernel w L M e =
      ∑ r ∈ range L, H.innerLiveMass w r M e := by
  induction L generalizing M with
  | zero => simp [innerLiveTimeKernel]
  | succ L ih =>
      rw [innerLiveTimeKernel, sum_range_succ', innerLiveMass_zero]
      simp_rw [ih, innerLiveMass_succ]
      simp_rw [Finset.mul_sum]
      rw [sum_comm]
      ring

/-- Pointwise survival estimates for the first `L` rounds can be summed and
inserted directly into the marginal recursion.  This is the quantitative
interface used by the near-regular calculation: it remains only to supply
the lower bounds `survival r` from degree and codegree information. -/
theorem mul_sum_le_innerAcceptanceMass_of_innerLiveMass_ge
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ f, 0 ≤ p f) (hp₁ : ∀ f, p f ≤ 1)
    {q : ℝ} (hq₀ : 0 ≤ q) {e : E}
    (hq : q ≤ FiniteNibble.trialAcceptanceMass H p e)
    (L : ℕ) (survival : ℕ → ℝ)
    (hsurvival : ∀ r < L, survival r ≤
      H.innerLiveMass (FiniteNibble.bernoulliMass univ p) r ∅ e) :
    q * (∑ r ∈ range L, survival r) ≤ H.innerAcceptanceMass L p e := by
  calc
    q * (∑ r ∈ range L, survival r) ≤
        q * (∑ r ∈ range L,
          H.innerLiveMass (FiniteNibble.bernoulliMass univ p) r ∅ e) := by
      gcongr with r hr
      exact hsurvival r (mem_range.mp hr)
    _ = q * H.innerLiveTimeKernel
          (FiniteNibble.bernoulliMass univ p) L ∅ e := by
      rw [H.innerLiveTimeKernel_eq_sum_innerLiveMass]
    _ ≤ H.innerAcceptanceMass L p e :=
      H.mul_innerLiveTimeKernel_empty_le_innerAcceptanceMass hp₀ hp₁ hq L

/-- Constant-probability specialization of the preceding survival-sum
interface.  The coefficient is the elementary one-round alteration lower
bound; the hard near-regular input is isolated in `hsurvival`. -/
theorem sub_mul_sum_le_innerAcceptanceMass_const_of_innerLiveMass_ge
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ p - ((k * D : ℕ) : ℝ) * p ^ 2)
    (L : ℕ) (survival : ℕ → ℝ) {e : E}
    (hsurvival : ∀ r < L, survival r ≤
      H.innerLiveMass
        (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ e) :
    (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
        (∑ r ∈ range L, survival r) ≤
      H.innerAcceptanceMass L (fun _ ↦ p) e := by
  exact H.mul_sum_le_innerAcceptanceMass_of_innerLiveMass_ge
    (fun _ ↦ hp₀) (fun _ ↦ hp₁) hq₀
    (FiniteNibble.trialAcceptanceMass_const_ge hunif hdeg hp₀ hp₁ e)
    L survival hsurvival

/-! ### Upper marginal recursion -/

/-- If an edge was not already present, membership after one inner step
forces that edge to have been sampled in the new Bernoulli coordinate. -/
lemma mem_sample_of_mem_innerStep_of_not_mem
    (H : FiniteHypergraph V E) {M S : Finset E} {e : E}
    (heM : e ∉ M) (he : e ∈ H.innerStep M S) : e ∈ S := by
  rcases mem_union.mp he with heOld | heNew
  · exact (heM heOld).elim
  · exact H.liveSample_subset_sample M S
      (H.isolatedSample_subset (H.liveSample M S) heNew)

/-- If an edge is newly accepted by one step, it was live before the step. -/
lemma innerLive_of_mem_innerStep_of_not_mem
    (H : FiniteHypergraph V E) {M S : Finset E} {e : E}
    (heM : e ∉ M) (he : e ∈ H.innerStep M S) : H.InnerLive M e := by
  rcases mem_union.mp he with heOld | heNew
  · exact (heM heOld).elim
  · exact (H.mem_liveSample_iff M S e).1
      (H.isolatedSample_subset (H.liveSample M S) heNew) |>.2

/-- First Bernoulli moment in indicator form over the full finite sample
space. -/
lemma sum_bernoulliMass_mul_indicator_mem
    (p : E → ℝ) (e : E) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ S then 1 else 0) = p e := by
  calc
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ S then 1 else 0) =
        ∑ S ∈ (univ : Finset E).powerset with e ∈ S,
          FiniteNibble.bernoulliMass univ p S := by
      simp only [powerset_univ, sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases heS : e ∈ S <;> simp [heS]
    _ = p e := FiniteNibble.sum_bernoulliMass_filter_mem (mem_univ e)

/-- In one step, conditional acceptance is at most the probability of
sampling the distinguished edge. -/
lemma sum_innerStep_indicator_le_mem_add_prob_mul_live
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ f, 0 ≤ p f) (hp₁ : ∀ f, p f ≤ 1)
    (M : Finset E) (e : E) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ H.innerStep M S then 1 else 0) ≤
      (if e ∈ M then 1 else 0) +
        p e * (if H.InnerLive M e then 1 else 0) := by
  by_cases heM : e ∈ M
  · have hnotlive := H.not_innerLive_of_mem heM
    simp only [heM, hnotlive, if_true, if_false, mul_zero, add_zero]
    calc
      (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
          if e ∈ H.innerStep M S then 1 else 0) ≤
          ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S := by
        apply sum_le_sum
        intro S _
        have hmass : 0 ≤ FiniteNibble.bernoulliMass univ p S :=
          FiniteNibble.bernoulliMass_nonneg (subset_univ S)
            (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
        split <;> simp [hmass]
      _ = 1 := by
        simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) p
  · by_cases hlive : H.InnerLive M e
    · simp only [heM, hlive, if_false, if_true, mul_one, zero_add]
      calc
        (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
            if e ∈ H.innerStep M S then 1 else 0) ≤
            ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
              if e ∈ S then 1 else 0 := by
          apply sum_le_sum
          intro S _
          have hmass : 0 ≤ FiniteNibble.bernoulliMass univ p S :=
            FiniteNibble.bernoulliMass_nonneg (subset_univ S)
              (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
          by_cases hstep : e ∈ H.innerStep M S
          · have heS := H.mem_sample_of_mem_innerStep_of_not_mem heM hstep
            simp [hstep, heS]
          · by_cases heS : e ∈ S <;> simp [hstep, heS, hmass]
        _ = p e := sum_bernoulliMass_mul_indicator_mem p e
    · simp only [heM, hlive, if_false, mul_zero, add_zero]
      apply sum_nonpos
      intro S _
      have hstep : e ∉ H.innerStep M S := fun he ↦
        hlive (H.innerLive_of_mem_innerStep_of_not_mem heM he)
      simp [hstep]

/-- Upper counterpart of the live-time marginal recursion. -/
theorem innerAcceptanceKernel_le_indicator_add_mul_innerLiveTimeKernel
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ f, 0 ≤ p f) (hp₁ : ∀ f, p f ≤ 1)
    (n : ℕ) (M : Finset E) (e : E) :
    H.innerAcceptanceKernel (FiniteNibble.bernoulliMass univ p) n M e ≤
      (if e ∈ M then 1 else 0) + p e *
        H.innerLiveTimeKernel (FiniteNibble.bernoulliMass univ p) n M e := by
  induction n generalizing M with
  | zero => simp [innerAcceptanceKernel, innerLiveTimeKernel]
  | succ n ih =>
      let w : Finset E → ℝ := FiniteNibble.bernoulliMass univ p
      have hw₀ (S : Finset E) : 0 ≤ w S :=
        FiniteNibble.bernoulliMass_nonneg (subset_univ S)
          (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
      simp only [innerAcceptanceKernel, innerLiveTimeKernel]
      calc
        (∑ S, w S * H.innerAcceptanceKernel w n (H.innerStep M S) e) ≤
            ∑ S, w S * ((if e ∈ H.innerStep M S then 1 else 0) +
              p e * H.innerLiveTimeKernel w n (H.innerStep M S) e) := by
          apply sum_le_sum
          intro S _
          exact mul_le_mul_of_nonneg_left (ih (H.innerStep M S)) (hw₀ S)
        _ = (∑ S, w S * (if e ∈ H.innerStep M S then 1 else 0)) +
              p e * ∑ S, w S *
                H.innerLiveTimeKernel w n (H.innerStep M S) e := by
          simp_rw [mul_add]
          rw [sum_add_distrib]
          apply congrArg₂ (.+.) rfl
          rw [mul_sum]
          apply sum_congr rfl
          intro S _
          ring
        _ ≤ ((if e ∈ M then 1 else 0) +
              p e * (if H.InnerLive M e then 1 else 0)) +
              p e * ∑ S, w S *
                H.innerLiveTimeKernel w n (H.innerStep M S) e := by
          gcongr
          exact H.sum_innerStep_indicator_le_mem_add_prob_mul_live hp₀ hp₁ M e
        _ = (if e ∈ M then 1 else 0) + p e *
              ((if H.InnerLive M e then 1 else 0) +
                ∑ S, w S *
                  H.innerLiveTimeKernel w n (H.innerStep M S) e) := by ring

/-- Public upper marginal bound by the sampling probability times accumulated
expected live time. -/
theorem innerAcceptanceMass_le_mul_innerLiveTimeKernel_empty
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ f, 0 ≤ p f) (hp₁ : ∀ f, p f ≤ 1)
    (L : ℕ) (e : E) :
    H.innerAcceptanceMass L p e ≤ p e *
      H.innerLiveTimeKernel (FiniteNibble.bernoulliMass univ p) L ∅ e := by
  rw [← H.innerAcceptanceKernel_empty_eq_innerAcceptanceMass L p e]
  simpa using
    H.innerAcceptanceKernel_le_indicator_add_mul_innerLiveTimeKernel hp₀ hp₁ L ∅ e

/-- Explicit survival-sum form of the public upper marginal bound. -/
theorem innerAcceptanceMass_le_mul_sum_innerLiveMass
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ f, 0 ≤ p f) (hp₁ : ∀ f, p f ≤ 1)
    (L : ℕ) (e : E) :
    H.innerAcceptanceMass L p e ≤
      p e * (∑ r ∈ range L,
        H.innerLiveMass (FiniteNibble.bernoulliMass univ p) r ∅ e) := by
  rw [← H.innerLiveTimeKernel_eq_sum_innerLiveMass]
  exact H.innerAcceptanceMass_le_mul_innerLiveTimeKernel_empty hp₀ hp₁ L e

/-- A supplied round-by-round upper survival profile gives a public upper
marginal bound.  Together with
`mul_sum_le_innerAcceptanceMass_of_innerLiveMass_ge`, this is the symmetric
interface for the two-sided sharp inner theorem. -/
theorem innerAcceptanceMass_le_mul_sum_of_innerLiveMass_le
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ f, 0 ≤ p f) (hp₁ : ∀ f, p f ≤ 1)
    (L : ℕ) (e : E) (survival : ℕ → ℝ)
    (hsurvival : ∀ r < L,
      H.innerLiveMass (FiniteNibble.bernoulliMass univ p) r ∅ e ≤ survival r) :
    H.innerAcceptanceMass L p e ≤
      p e * (∑ r ∈ range L, survival r) := by
  calc
    H.innerAcceptanceMass L p e ≤ p e *
        (∑ r ∈ range L,
          H.innerLiveMass (FiniteNibble.bernoulliMass univ p) r ∅ e) :=
      H.innerAcceptanceMass_le_mul_sum_innerLiveMass hp₀ hp₁ L e
    _ ≤ p e * (∑ r ∈ range L, survival r) := by
      apply mul_le_mul_of_nonneg_left _ (hp₀ e)
      apply sum_le_sum
      intro r hr
      exact hsurvival r (mem_range.mp hr)

/-! ### Exact one-round conditional drift -/

/-- The currently live edges which would conflict with `e`. -/
def innerLiveConflictNeighbors (H : FiniteHypergraph V E)
    (M : Finset E) (e : E) : Finset E :=
  univ.filter fun f ↦ f ≠ e ∧ H.InnerLive M f ∧
    ¬Disjoint (H.support e) (H.support f)

@[simp] lemma mem_innerLiveConflictNeighbors
    (H : FiniteHypergraph V E) (M : Finset E) (e f : E) :
    f ∈ H.innerLiveConflictNeighbors M e ↔
      f ≠ e ∧ H.InnerLive M f ∧
        ¬Disjoint (H.support e) (H.support f) := by
  simp [innerLiveConflictNeighbors]

lemma self_not_mem_innerLiveConflictNeighbors
    (H : FiniteHypergraph V E) (M : Finset E) (e : E) :
    e ∉ H.innerLiveConflictNeighbors M e := by
  simp

lemma eventDependsOn_mem_singleton (e : E) :
    FiniteNibble.EventDependsOn {e} (fun S : Finset E ↦ e ∈ S) := by
  intro S T hST
  unfold FiniteNibble.AgreesOn at hST
  have hmem := congrArg (fun U : Finset E ↦ e ∈ U) hST
  simpa using hmem

lemma eventDependsOn_disjoint_right (B : Finset E) :
    FiniteNibble.EventDependsOn B (fun S : Finset E ↦ Disjoint S B) := by
  intro S T hST
  unfold FiniteNibble.AgreesOn at hST
  change Disjoint S B ↔ Disjoint T B
  rw [Finset.disjoint_iff_inter_eq_empty,
    Finset.disjoint_iff_inter_eq_empty, hST]

/-- Bernoulli mass of the event that none of the coordinates in `B` is
selected. -/
lemma eventMass_disjoint_right (p : E → ℝ) (B : Finset E) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ FiniteNibble.bernoulliMass univ p S)
        (fun S ↦ Disjoint S B) =
      ∏ f ∈ B, (1 - p f) := by
  rw [FiniteNibble.eventMass_eq_restrictedEventMass
    (eventDependsOn_disjoint_right B)]
  unfold FiniteNibble.restrictedEventMass
  rw [Fintype.sum_eq_single ⟨∅, empty_subset B⟩]
  · simp [FiniteNibble.bernoulliMass]
  · intro S hSne
    have hSnonempty : S.1.Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro hSempty
      apply hSne
      apply Subtype.ext
      exact hSempty
    have hnot : ¬Disjoint S.1 B := by
      obtain ⟨f, hfS⟩ := hSnonempty
      exact fun hdis ↦ (Finset.disjoint_left.mp hdis) hfS (S.2 hfS)
    simp [hnot]

/-- Bernoulli cylinder formula: require `e` to be selected and every
coordinate of a disjoint forbidden set to be absent. -/
lemma eventMass_mem_and_disjoint
    (p : E → ℝ) (e : E) (B : Finset E) (heB : e ∉ B) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ FiniteNibble.bernoulliMass univ p S)
        (fun S ↦ e ∈ S ∧ Disjoint S B) =
      p e * ∏ f ∈ B, (1 - p f) := by
  rw [FiniteNibble.eventMass_and_of_disjoint
    (disjoint_singleton_left.mpr heB)
    (eventDependsOn_mem_singleton e)
    (eventDependsOn_disjoint_right B)]
  rw [eventMass_disjoint_right]
  congr 1
  unfold FiniteLocalLemma.eventMass
  trans ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
      if e ∈ S then 1 else 0
  · apply sum_congr rfl
    intro S _
    by_cases heS : e ∈ S <;> simp [heS]
  · exact sum_bernoulliMass_mul_indicator_mem p e

/-- Deterministic cylinder characterization of new acceptance in one inner
step. -/
lemma mem_isolatedSample_liveSample_iff
    (H : FiniteHypergraph V E) (M S : Finset E) (e : E) :
    e ∈ H.isolatedSample (H.liveSample M S) ↔
      H.InnerLive M e ∧ e ∈ S ∧
        Disjoint S (H.innerLiveConflictNeighbors M e) := by
  constructor
  · intro he
    have heIso := mem_filter.mp he
    have heLive : e ∈ H.liveSample M S := H.isolatedSample_subset _ he
    have heParts := (H.mem_liveSample_iff M S e).1 heLive
    refine ⟨heParts.2, heParts.1, ?_⟩
    rw [Finset.disjoint_left]
    intro f hfS hfN
    have hfLive : f ∈ H.liveSample M S :=
      (H.mem_liveSample_iff M S f).2 ⟨hfS, (H.mem_innerLiveConflictNeighbors M e f).1 hfN |>.2.1⟩
    exact (H.mem_innerLiveConflictNeighbors M e f).1 hfN |>.2.2
      (heIso.2 f hfLive ((H.mem_innerLiveConflictNeighbors M e f).1 hfN |>.1).symm)
  · rintro ⟨hlive, heS, hdis⟩
    rw [isolatedSample, mem_filter]
    refine ⟨(H.mem_liveSample_iff M S e).2 ⟨heS, hlive⟩, ?_⟩
    intro f hfLive hef
    by_contra hsupport
    have hfN : f ∈ H.innerLiveConflictNeighbors M e := by
      rw [H.mem_innerLiveConflictNeighbors M e f]
      exact ⟨hef.symm, (H.mem_liveSample_iff M S f).1 hfLive |>.2, hsupport⟩
    exact (Finset.disjoint_left.mp hdis)
      ((H.mem_liveSample_iff M S f).1 hfLive |>.1) hfN

/-- Conditional mass that `e` is newly accepted in one round. -/
def innerNewAcceptanceMass (H : FiniteHypergraph V E)
    (M : Finset E) (p : E → ℝ) (e : E) : ℝ :=
  ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
    if e ∈ H.isolatedSample (H.liveSample M S) then 1 else 0

/-- Exact one-round acceptance probability: sample `e`, and sample none of
its currently live conflicting neighbours. -/
theorem innerNewAcceptanceMass_eq
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ) (e : E) :
    H.innerNewAcceptanceMass M p e =
      if H.InnerLive M e then
        p e * ∏ f ∈ H.innerLiveConflictNeighbors M e, (1 - p f)
      else 0 := by
  unfold innerNewAcceptanceMass
  by_cases hlive : H.InnerLive M e
  · rw [if_pos hlive]
    calc
      (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
          if e ∈ H.isolatedSample (H.liveSample M S) then 1 else 0) =
          FiniteLocalLemma.eventMass
            (fun S : Finset E ↦ FiniteNibble.bernoulliMass univ p S)
            (fun S ↦ e ∈ S ∧
              Disjoint S (H.innerLiveConflictNeighbors M e)) := by
        unfold FiniteLocalLemma.eventMass
        apply sum_congr rfl
        intro S _
        by_cases hEvent : e ∈ S ∧
            Disjoint S (H.innerLiveConflictNeighbors M e)
        · have hIso : e ∈ H.isolatedSample (H.liveSample M S) :=
            (H.mem_isolatedSample_liveSample_iff M S e).2
              ⟨hlive, hEvent⟩
          simp [hEvent, hIso]
        · have hIso : e ∉ H.isolatedSample (H.liveSample M S) :=
            fun he ↦ hEvent
              ((H.mem_isolatedSample_liveSample_iff M S e).1 he |>.2)
          simp [hEvent, hIso]
      _ = p e * ∏ f ∈ H.innerLiveConflictNeighbors M e, (1 - p f) :=
        eventMass_mem_and_disjoint p e _
          (H.self_not_mem_innerLiveConflictNeighbors M e)
  · rw [if_neg hlive]
    apply sum_eq_zero
    intro S _
    have hnot : e ∉ H.isolatedSample (H.liveSample M S) := fun he ↦
      hlive ((H.mem_isolatedSample_liveSample_iff M S e).1 he).1
    simp [hnot]

/-! ### Exact simultaneous one-round acceptance -/

/-- Requiring all coordinates in `A` to be selected depends only on `A`. -/
lemma eventDependsOn_subset_left (A : Finset E) :
    FiniteNibble.EventDependsOn A (fun S : Finset E ↦ A ⊆ S) := by
  intro S T hST
  unfold FiniteNibble.AgreesOn at hST
  constructor
  · intro hAS e heA
    have heInter : e ∈ S ∩ A := mem_inter.mpr ⟨hAS heA, heA⟩
    rw [hST] at heInter
    exact (mem_inter.mp heInter).1
  · intro hAT e heA
    have heInter : e ∈ T ∩ A := mem_inter.mpr ⟨hAT heA, heA⟩
    rw [← hST] at heInter
    exact (mem_inter.mp heInter).1

/-- Bernoulli mass of requiring every coordinate in `A` to be selected. -/
lemma eventMass_subset_left (p : E → ℝ) (A : Finset E) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ FiniteNibble.bernoulliMass univ p S)
        (fun S ↦ A ⊆ S) =
      ∏ e ∈ A, p e := by
  rw [FiniteNibble.eventMass_eq_restrictedEventMass
    (eventDependsOn_subset_left A)]
  unfold FiniteNibble.restrictedEventMass
  rw [Fintype.sum_eq_single ⟨A, Subset.rfl⟩]
  · simp [FiniteNibble.bernoulliMass]
  · intro S hSA
    have hnot : ¬A ⊆ S.1 := by
      intro hAS
      apply hSA
      apply Subtype.ext
      exact Subset.antisymm S.2 hAS
    simp [hnot]

/-- Bernoulli cylinder formula for a required family `A` and a disjoint
forbidden family `B`. -/
lemma eventMass_subset_and_disjoint
    (p : E → ℝ) (A B : Finset E) (hAB : Disjoint A B) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ FiniteNibble.bernoulliMass univ p S)
        (fun S ↦ A ⊆ S ∧ Disjoint S B) =
      (∏ e ∈ A, p e) * ∏ f ∈ B, (1 - p f) := by
  rw [FiniteNibble.eventMass_and_of_disjoint hAB
    (eventDependsOn_subset_left A)
    (eventDependsOn_disjoint_right B)]
  rw [eventMass_subset_left, eventMass_disjoint_right]

/-- Union of all currently live conflict neighbourhoods of the edges in
`F`.  Simultaneous isolated acceptance of `F` is the cylinder requiring
`F` and forbidding this union. -/
def innerLiveConflictUnion (H : FiniteHypergraph V E)
    (M F : Finset E) : Finset E :=
  F.biUnion fun e ↦ H.innerLiveConflictNeighbors M e

lemma mem_innerLiveConflictUnion
    (H : FiniteHypergraph V E) (M F : Finset E) (g : E) :
    g ∈ H.innerLiveConflictUnion M F ↔
      ∃ e ∈ F, g ∈ H.innerLiveConflictNeighbors M e := by
  simp [innerLiveConflictUnion]

/-- A matching family is disjoint from the union of its live conflict
neighbourhoods. -/
lemma disjoint_innerLiveConflictUnion_of_isMatching
    (H : FiniteHypergraph V E) (M F : Finset E)
    (hF : H.IsMatching F) :
    Disjoint F (H.innerLiveConflictUnion M F) := by
  rw [disjoint_left]
  intro f hfF hfUnion
  obtain ⟨e, heF, hfe⟩ :=
    (H.mem_innerLiveConflictUnion M F f).1 hfUnion
  have hinfo := (H.mem_innerLiveConflictNeighbors M e f).1 hfe
  exact hinfo.2.2 (hF heF hfF hinfo.1.symm)

/-- Deterministic cylinder characterization of simultaneous new isolated
acceptance. -/
lemma subset_isolatedSample_liveSample_iff
    (H : FiniteHypergraph V E) (M S F : Finset E) :
    F ⊆ H.isolatedSample (H.liveSample M S) ↔
      (∀ e ∈ F, H.InnerLive M e) ∧ F ⊆ S ∧
        Disjoint S (H.innerLiveConflictUnion M F) := by
  constructor
  · intro hF
    refine ⟨?_, ?_, ?_⟩
    · intro e heF
      exact ((H.mem_isolatedSample_liveSample_iff M S e).1 (hF heF)).1
    · intro e heF
      exact ((H.mem_isolatedSample_liveSample_iff M S e).1 (hF heF)).2.1
    · rw [disjoint_left]
      intro g hgS hgUnion
      obtain ⟨e, heF, hge⟩ :=
        (H.mem_innerLiveConflictUnion M F g).1 hgUnion
      have hdis :=
        ((H.mem_isolatedSample_liveSample_iff M S e).1 (hF heF)).2.2
      exact (disjoint_left.mp hdis) hgS hge
  · rintro ⟨hlive, hFS, hdis⟩ e heF
    apply (H.mem_isolatedSample_liveSample_iff M S e).2
    refine ⟨hlive e heF, hFS heF, ?_⟩
    exact hdis.mono_left Subset.rfl |>.mono_right
      (subset_biUnion_of_mem (fun f ↦ H.innerLiveConflictNeighbors M f) heF)

/-- Bernoulli mass that every edge in `F` is newly accepted in one inner
round. -/
def innerNewAcceptanceFamilyMass (H : FiniteHypergraph V E)
    (M : Finset E) (p : E → ℝ) (F : Finset E) : ℝ :=
  ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
    if F ⊆ H.isolatedSample (H.liveSample M S) then 1 else 0

/-- Exact product formula for simultaneous isolated acceptance of a matching
family. -/
theorem innerNewAcceptanceFamilyMass_eq
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ) (F : Finset E)
    (hF : H.IsMatching F) :
    H.innerNewAcceptanceFamilyMass M p F =
      if ∀ e ∈ F, H.InnerLive M e then
        (∏ e ∈ F, p e) *
          ∏ g ∈ H.innerLiveConflictUnion M F, (1 - p g)
      else 0 := by
  unfold innerNewAcceptanceFamilyMass
  by_cases hlive : ∀ e ∈ F, H.InnerLive M e
  · rw [if_pos hlive]
    calc
      (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
          if F ⊆ H.isolatedSample (H.liveSample M S) then 1 else 0) =
          FiniteLocalLemma.eventMass
            (fun S : Finset E ↦ FiniteNibble.bernoulliMass univ p S)
            (fun S ↦ F ⊆ S ∧
              Disjoint S (H.innerLiveConflictUnion M F)) := by
        unfold FiniteLocalLemma.eventMass
        apply sum_congr rfl
        intro S _
        have hiff := H.subset_isolatedSample_liveSample_iff M S F
        by_cases hEvent : F ⊆ S ∧
            Disjoint S (H.innerLiveConflictUnion M F)
        · have hIso : F ⊆ H.isolatedSample (H.liveSample M S) :=
            hiff.2 ⟨hlive, hEvent⟩
          simp [hEvent, hIso]
        · have hIso : ¬F ⊆ H.isolatedSample (H.liveSample M S) :=
            fun h ↦ hEvent (hiff.1 h |>.2)
          simp [hEvent, hIso]
      _ = (∏ e ∈ F, p e) *
          ∏ g ∈ H.innerLiveConflictUnion M F, (1 - p g) :=
        eventMass_subset_and_disjoint p F _
          (H.disjoint_innerLiveConflictUnion_of_isMatching M F hF)
  · rw [if_neg hlive]
    apply sum_eq_zero
    intro S _
    have hnot : ¬F ⊆ H.isolatedSample (H.liveSample M S) := fun h ↦
      hlive (H.subset_isolatedSample_liveSample_iff M S F |>.1 h |>.1)
    simp [hnot]

/-- Constant-probability specialization of simultaneous isolated
acceptance.  The forbidden union is disjoint from `F`, so writing the
exponent using `union \ F` is equivalent and convenient for later
combinatorial estimates. -/
theorem innerNewAcceptanceFamilyMass_const_eq
    (H : FiniteHypergraph V E) (M F : Finset E) (p : ℝ)
    (hF : H.IsMatching F) :
    H.innerNewAcceptanceFamilyMass M (fun _ ↦ p) F =
      if ∀ e ∈ F, H.InnerLive M e then
        p ^ F.card * (1 - p) ^
          (H.innerLiveConflictUnion M F \ F).card
      else 0 := by
  rw [H.innerNewAcceptanceFamilyMass_eq M (fun _ ↦ p) F hF]
  have hdis := H.disjoint_innerLiveConflictUnion_of_isMatching M F hF
  have hsdiff : H.innerLiveConflictUnion M F \ F =
      H.innerLiveConflictUnion M F := by
    exact sdiff_eq_left.mpr hdis.symm
  rw [hsdiff]
  simp

/-- In a `k`-uniform hypergraph of maximum degree at most `D`, the union of
the live conflict neighbourhoods of a finite edge family `F` has cardinality
at most `|F| k D`.  No matching assumption on `F` is needed for this union
bound. -/
theorem innerLiveConflictUnion_card_le
    (H : FiniteHypergraph V E) {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M F : Finset E) :
    (H.innerLiveConflictUnion M F).card ≤ F.card * k * D := by
  calc
    (H.innerLiveConflictUnion M F).card ≤
        ∑ e ∈ F, (H.innerLiveConflictNeighbors M e).card := by
      exact card_biUnion_le
    _ ≤ ∑ _e ∈ F, k * D := by
      apply sum_le_sum
      intro e he
      calc
        (H.innerLiveConflictNeighbors M e).card ≤
            H.conflictDegree e := by
          apply card_le_card
          intro f hf
          rw [mem_filter]
          have hf' := (H.mem_innerLiveConflictNeighbors M e f).1 hf
          exact ⟨mem_univ f, hf'.1.symm, hf'.2.2⟩
        _ ≤ k * D := H.conflictDegree_le_uniform_mul hunif hdeg e
    _ = F.card * k * D := by simp [Nat.mul_assoc]

/-- Quantitative constant-probability form of simultaneous isolated
acceptance.  For a currently live matching family `F`, its one-round
acceptance mass lies between the raw sampling mass times the worst possible
conflict-avoidance factor and the raw sampling mass itself. -/
theorem innerNewAcceptanceFamilyMass_const_mem_Icc
    (H : FiniteHypergraph V E) {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M F : Finset E) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hF : H.IsMatching F)
    (hlive : ∀ e ∈ F, H.InnerLive M e) :
    H.innerNewAcceptanceFamilyMass M (fun _ ↦ p) F ∈
      Set.Icc
        (p ^ F.card * (1 - p) ^ (F.card * k * D))
        (p ^ F.card) := by
  rw [H.innerNewAcceptanceFamilyMass_const_eq M F p hF, if_pos hlive]
  have hb₀ : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  have hb₁ : 1 - p ≤ 1 := by linarith
  have hcard :
      (H.innerLiveConflictUnion M F \ F).card ≤ F.card * k * D :=
    (card_le_card sdiff_subset).trans
      (H.innerLiveConflictUnion_card_le hunif hdeg M F)
  constructor
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hb₀ hb₁ hcard) (pow_nonneg hp₀ _)
  · simpa using mul_le_mul_of_nonneg_left
      (pow_le_one₀ hb₀ hb₁) (pow_nonneg hp₀ F.card)

/-- State-independent indicator form of the preceding estimate.  It also
covers a family that is not currently live: then simultaneous new
acceptance and both comparison endpoints vanish. -/
theorem innerNewAcceptanceFamilyMass_const_indicator_mem_Icc
    (H : FiniteHypergraph V E) {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M F : Finset E) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hF : H.IsMatching F) :
    H.innerNewAcceptanceFamilyMass M (fun _ ↦ p) F ∈
      Set.Icc
        (p ^ F.card * (1 - p) ^ (F.card * k * D) *
          (if ∀ e ∈ F, H.InnerLive M e then 1 else 0))
        (p ^ F.card *
          (if ∀ e ∈ F, H.InnerLive M e then 1 else 0)) := by
  by_cases hlive : ∀ e ∈ F, H.InnerLive M e
  · rw [if_pos hlive, mul_one, mul_one]
    exact H.innerNewAcceptanceFamilyMass_const_mem_Icc
      hunif hdeg M F hp₀ hp₁ hF hlive
  · rw [H.innerNewAcceptanceFamilyMass_const_eq M F p hF]
    simp [hlive]

/-- Real-valued finite inclusion--exclusion for the indicator that a
finite set is empty. -/
lemma indicator_eq_empty_eq_sum_powerset_neg_one_pow_card_real
    (N : Finset E) :
    (if N = ∅ then (1 : ℝ) else 0) =
      ∑ F ∈ N.powerset, (-1 : ℝ) ^ F.card := by
  have hInt := Finset.sum_powerset_neg_one_pow_card (x := N)
  exact_mod_cast hInt.symm

/-- Choosing `j` elements of a subset `N ⊆ K` is the same as summing the
subset indicator over all `j`-element subfamilies of `K`. -/
lemma choose_card_eq_sum_powersetCard_subset
    (N K : Finset E) (j : ℕ) (hNK : N ⊆ K) :
    N.card.choose j =
      ∑ F ∈ K.powersetCard j, if F ⊆ N then 1 else 0 := by
  have hfilter :
      (K.powersetCard j).filter (fun F ↦ F ⊆ N) =
        N.powersetCard j := by
    ext F
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hFK, hcard⟩, hFN⟩
      exact ⟨hFN, hcard⟩
    · rintro ⟨hFN, hcard⟩
      exact ⟨⟨hFN.trans hNK, hcard⟩, hFN⟩
  rw [← card_powersetCard j N, ← hfilter, card_eq_sum_ones,
    ← sum_filter]

/-- Real-valued version of `choose_card_eq_sum_powersetCard_subset`. -/
lemma natCast_choose_card_eq_sum_powersetCard_subset
    (N K : Finset E) (j : ℕ) (hNK : N ⊆ K) :
    (N.card.choose j : ℝ) =
      ∑ F ∈ K.powersetCard j, if F ⊆ N then 1 else 0 := by
  exact_mod_cast choose_card_eq_sum_powersetCard_subset N K j hNK

/-- Newly accepted edges through a fixed vertex in one inner step. -/
def innerNewAcceptedAt (H : FiniteHypergraph V E)
    (M S : Finset E) (v : V) : Finset E :=
  (H.isolatedSample (H.liveSample M S)).filter fun e ↦ v ∈ H.support e

@[simp] lemma mem_innerNewAcceptedAt
    (H : FiniteHypergraph V E) (M S : Finset E) (v : V) (e : E) :
    e ∈ H.innerNewAcceptedAt M S v ↔
      e ∈ H.isolatedSample (H.liveSample M S) ∧ v ∈ H.support e := by
  simp [innerNewAcceptedAt]

lemma innerNewAcceptedAt_card_le_one
    (H : FiniteHypergraph V E) (M S : Finset E) (v : V) :
    (H.innerNewAcceptedAt M S v).card ≤ 1 := by
  exact H.card_filter_isolatedSample_mem_support_le_one (H.liveSample M S) v

/-- At a previously uncovered vertex, remaining uncovered after one step is
equivalent to accepting no new incident edge. -/
lemma uncoveredBy_innerStep_iff_innerNewAcceptedAt_eq_empty
    (H : FiniteHypergraph V E) {M S : Finset E} {v : V}
    (hunc : H.UncoveredBy M v) :
    H.UncoveredBy (H.innerStep M S) v ↔ H.innerNewAcceptedAt M S v = ∅ := by
  constructor
  · intro hstep
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    exact hstep e (mem_union_right M (H.mem_innerNewAcceptedAt M S v e |>.1 he |>.1))
      (H.mem_innerNewAcceptedAt M S v e |>.1 he |>.2)
  · intro hempty e heStep hve
    rcases mem_union.mp heStep with heM | heNew
    · exact hunc e heM hve
    · have : e ∈ H.innerNewAcceptedAt M S v := by
        exact (H.mem_innerNewAcceptedAt M S v e).2 ⟨heNew, hve⟩
      simpa [hempty] using this

/-- Pointwise indicator identity behind the vertex drift formula. -/
lemma indicator_uncoveredBy_innerStep_eq_one_sub_card
    (H : FiniteHypergraph V E) {M S : Finset E} {v : V}
    (hunc : H.UncoveredBy M v) :
    (if H.UncoveredBy (H.innerStep M S) v then (1 : ℝ) else 0) =
      1 - (H.innerNewAcceptedAt M S v).card := by
  by_cases hstep : H.UncoveredBy (H.innerStep M S) v
  · have hempty :=
      (H.uncoveredBy_innerStep_iff_innerNewAcceptedAt_eq_empty hunc).1 hstep
    simp [hstep, hempty]
  · have hne : H.innerNewAcceptedAt M S v ≠ ∅ := fun hempty ↦
      hstep ((H.uncoveredBy_innerStep_iff_innerNewAcceptedAt_eq_empty hunc).2 hempty)
    have hpos : 0 < (H.innerNewAcceptedAt M S v).card :=
      card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
    have hle := H.innerNewAcceptedAt_card_le_one M S v
    have hone : (H.innerNewAcceptedAt M S v).card = 1 := by
      omega
    simp [hstep, hone]

/-- Expected number of newly accepted edges through `v` is the sum of their
individual conditional acceptance masses. -/
lemma sum_bernoulliMass_mul_innerNewAcceptedAt_card
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ) (v : V) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        ((H.innerNewAcceptedAt M S v).card : ℝ)) =
      ∑ e ∈ H.incidentEdges v, H.innerNewAcceptanceMass M p e := by
  have hcard (S : Finset E) :
      ((H.innerNewAcceptedAt M S v).card : ℝ) =
        ∑ e ∈ H.incidentEdges v,
          if e ∈ H.isolatedSample (H.liveSample M S) then 1 else 0 := by
    have hnat : (H.innerNewAcceptedAt M S v).card =
        ∑ e ∈ H.incidentEdges v,
          if e ∈ H.isolatedSample (H.liveSample M S) then (1 : ℕ) else 0 := by
      unfold innerNewAcceptedAt
      rw [card_eq_sum_ones]
      conv_rhs => rw [← sum_filter]
      congr 1
      ext e
      simp [incidentEdges, and_comm]
    exact_mod_cast hnat
  simp_rw [hcard, Finset.mul_sum]
  rw [sum_comm]
  unfold innerNewAcceptanceMass
  rfl

/-- Conditional mass that a vertex is uncovered after one step. -/
def innerUncoveredAfterStepMass (H : FiniteHypergraph V E)
    (M : Finset E) (p : E → ℝ) (v : V) : ℝ :=
  ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
    if H.UncoveredBy (H.innerStep M S) v then 1 else 0

/-- Exact one-vertex drift: an already covered vertex stays covered; an
uncovered vertex is newly covered with probability equal to the sum of the
mutually exclusive acceptance probabilities of its live incident edges. -/
theorem innerUncoveredAfterStepMass_eq
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ) (v : V) :
    H.innerUncoveredAfterStepMass M p v =
      if H.UncoveredBy M v then
        1 - ∑ e ∈ H.incidentEdges v, H.innerNewAcceptanceMass M p e
      else 0 := by
  unfold innerUncoveredAfterStepMass
  by_cases hunc : H.UncoveredBy M v
  · rw [if_pos hunc]
    calc
      (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
          if H.UncoveredBy (H.innerStep M S) v then 1 else 0) =
          ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
            (1 - (H.innerNewAcceptedAt M S v).card) := by
        apply sum_congr rfl
        intro S _
        rw [H.indicator_uncoveredBy_innerStep_eq_one_sub_card hunc]
      _ = (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S) -
          ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
            ((H.innerNewAcceptedAt M S v).card : ℝ) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro S _
        push_cast
        ring
      _ = 1 - ∑ e ∈ H.incidentEdges v,
          H.innerNewAcceptanceMass M p e := by
        rw [show (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S) = 1 by
          simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) p]
        rw [H.sum_bernoulliMass_mul_innerNewAcceptedAt_card]
  · rw [if_neg hunc]
    change ¬(∀ f ∈ M, v ∉ H.support f) at hunc
    push Not at hunc
    obtain ⟨f, hfM, hvf⟩ := hunc
    apply sum_eq_zero
    intro S _
    have hnot : ¬H.UncoveredBy (H.innerStep M S) v := fun hstep ↦
      hstep f (H.subset_innerStep M S hfM) hvf
    simp [hnot]

/-! ### Joint one-step drift -/

/-- Newly accepted edges whose support meets a prescribed vertex set. -/
def innerNewAcceptedMeeting (H : FiniteHypergraph V E)
    (M S : Finset E) (A : Finset V) : Finset E :=
  (H.isolatedSample (H.liveSample M S)).filter fun e ↦
    ¬Disjoint (H.support e) A

@[simp] lemma mem_innerNewAcceptedMeeting
    (H : FiniteHypergraph V E) (M S : Finset E) (A : Finset V) (e : E) :
    e ∈ H.innerNewAcceptedMeeting M S A ↔
      e ∈ H.isolatedSample (H.liveSample M S) ∧
        ¬Disjoint (H.support e) A := by
  simp [innerNewAcceptedMeeting]

/-- Provided all vertices of `A` were previously uncovered, they remain
jointly uncovered after one inner step exactly when no newly accepted edge
meets `A`. -/
lemma jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty
    (H : FiniteHypergraph V E) {M S : Finset E} {A : Finset V}
    (hunc : ∀ v ∈ A, H.UncoveredBy M v) :
    (∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v) ↔
      H.innerNewAcceptedMeeting M S A = ∅ := by
  constructor
  · intro hstep
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    obtain ⟨heNew, heMeet⟩ := (H.mem_innerNewAcceptedMeeting M S A e).1 he
    obtain ⟨v, hve, hvA⟩ := not_disjoint_iff.mp heMeet
    exact hstep v hvA e (mem_union_right M heNew) hve
  · intro hempty v hvA e heStep hve
    rcases mem_union.mp heStep with heM | heNew
    · exact hunc v hvA e heM hve
    · have heMeet : ¬Disjoint (H.support e) A :=
        not_disjoint_iff.mpr ⟨v, hve, hvA⟩
      have : e ∈ H.innerNewAcceptedMeeting M S A :=
        (H.mem_innerNewAcceptedMeeting M S A e).2 ⟨heNew, heMeet⟩
      simpa [hempty] using this

/-- The newly accepted edges meeting `A` inject into `A`: choose a meeting
vertex for each edge, and use the matching property of the isolated sample.
The proof avoids fixing a choice function by counting the disjoint nonempty
intersections directly. -/
lemma innerNewAcceptedMeeting_card_le
    (H : FiniteHypergraph V E) (M S : Finset E) (A : Finset V) :
    (H.innerNewAcceptedMeeting M S A).card ≤ A.card := by
  let N := H.innerNewAcceptedMeeting M S A
  have hpair : (N : Set E).PairwiseDisjoint fun e ↦ H.support e ∩ A := by
    intro e he f hf hef
    have heIso : e ∈ H.isolatedSample (H.liveSample M S) :=
      (H.mem_innerNewAcceptedMeeting M S A e).1 he |>.1
    have hfIso : f ∈ H.isolatedSample (H.liveSample M S) :=
      (H.mem_innerNewAcceptedMeeting M S A f).1 hf |>.1
    exact (H.isolatedSample_isMatching (H.liveSample M S)
      heIso hfIso hef).mono inter_subset_left inter_subset_left
  have hnonempty : ∀ e ∈ N, (H.support e ∩ A).Nonempty := by
    intro e he
    obtain ⟨v, hve, hvA⟩ := not_disjoint_iff.mp
      ((H.mem_innerNewAcceptedMeeting M S A e).1 he |>.2)
    exact ⟨v, mem_inter.mpr ⟨hve, hvA⟩⟩
  calc
    N.card = ∑ _e ∈ N, 1 := by simp
    _ ≤ ∑ e ∈ N, (H.support e ∩ A).card := by
      apply sum_le_sum
      intro e he
      exact (card_pos.mpr (hnonempty e he))
    _ = (N.biUnion fun e ↦ H.support e ∩ A).card :=
      (card_biUnion hpair).symm
    _ ≤ A.card := card_le_card (by
      intro v hv
      obtain ⟨e, heN, hvInter⟩ := mem_biUnion.mp hv
      exact (mem_inter.mp hvInter).2)

/-- The expected number of newly accepted edges meeting `A` is the sum of
the individual conditional acceptance masses over all edges meeting `A`. -/
lemma sum_bernoulliMass_mul_innerNewAcceptedMeeting_card
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ) (A : Finset V) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        ((H.innerNewAcceptedMeeting M S A).card : ℝ)) =
      ∑ e with ¬Disjoint (H.support e) A,
        H.innerNewAcceptanceMass M p e := by
  have hcard (S : Finset E) :
      ((H.innerNewAcceptedMeeting M S A).card : ℝ) =
        ∑ e with ¬Disjoint (H.support e) A,
          if e ∈ H.isolatedSample (H.liveSample M S) then 1 else 0 := by
    have hnat : (H.innerNewAcceptedMeeting M S A).card =
        ∑ e with ¬Disjoint (H.support e) A,
          if e ∈ H.isolatedSample (H.liveSample M S) then (1 : ℕ) else 0 := by
      unfold innerNewAcceptedMeeting
      rw [card_eq_sum_ones]
      conv_rhs => rw [← sum_filter]
      congr 1
      ext e
      simp [and_comm]
    exact_mod_cast hnat
  simp_rw [hcard, Finset.mul_sum]
  rw [sum_comm]
  unfold innerNewAcceptanceMass
  rfl

/-- All indexed edges whose support meets `A`. -/
def edgesMeeting (H : FiniteHypergraph V E) (A : Finset V) : Finset E :=
  univ.filter fun e ↦ ¬Disjoint (H.support e) A

@[simp] lemma mem_edgesMeeting
    (H : FiniteHypergraph V E) (A : Finset V) (e : E) :
    e ∈ H.edgesMeeting A ↔ ¬Disjoint (H.support e) A := by
  simp [edgesMeeting]

lemma innerNewAcceptedMeeting_subset_edgesMeeting
    (H : FiniteHypergraph V E) (M S : Finset E) (A : Finset V) :
    H.innerNewAcceptedMeeting M S A ⊆ H.edgesMeeting A := by
  intro e he
  exact (H.mem_edgesMeeting A e).2
    ((H.mem_innerNewAcceptedMeeting M S A e).1 he).2

/-- The `j`th binomial moment of the one-round accepted-meeting count is
the sum of the simultaneous-acceptance masses of all `j`-edge families
meeting `A`.  This is the exact bridge from the inner process to finite
all-order inclusion--exclusion. -/
theorem sum_bernoulliMass_mul_choose_innerNewAcceptedMeeting_card
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ)
    (A : Finset V) (j : ℕ) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        ((H.innerNewAcceptedMeeting M S A).card.choose j : ℝ)) =
      ∑ F ∈ (H.edgesMeeting A).powersetCard j,
        H.innerNewAcceptanceFamilyMass M p F := by
  have hchoose (S : Finset E) :
      ((H.innerNewAcceptedMeeting M S A).card.choose j : ℝ) =
        ∑ F ∈ (H.edgesMeeting A).powersetCard j,
          if F ⊆ H.innerNewAcceptedMeeting M S A then 1 else 0 :=
    natCast_choose_card_eq_sum_powersetCard_subset _ _ j
      (H.innerNewAcceptedMeeting_subset_edgesMeeting M S A)
  simp_rw [hchoose, Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro F hF
  unfold innerNewAcceptanceFamilyMass
  apply sum_congr rfl
  intro S _
  have hFmeet : F ⊆ H.edgesMeeting A :=
    (mem_powersetCard.mp hF).1
  have hiff :
      F ⊆ H.innerNewAcceptedMeeting M S A ↔
        F ⊆ H.isolatedSample (H.liveSample M S) := by
    constructor
    · intro h e heF
      exact ((H.mem_innerNewAcceptedMeeting M S A e).1 (h heF)).1
    · intro h e heF
      apply (H.mem_innerNewAcceptedMeeting M S A e).2
      exact ⟨h heF, (H.mem_edgesMeeting A e).1 (hFmeet heF)⟩
  by_cases hsub : F ⊆ H.innerNewAcceptedMeeting M S A
  · have hIso := hiff.mp hsub
    rw [if_pos hsub, if_pos hIso]
  · have hIso : ¬F ⊆ H.isolatedSample (H.liveSample M S) :=
      fun h ↦ hsub (hiff.mpr h)
    rw [if_neg hsub, if_neg hIso]

/-- A nonmatching family has zero simultaneous isolated-acceptance mass. -/
lemma innerNewAcceptanceFamilyMass_eq_zero_of_not_isMatching
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ)
    (F : Finset E) (hF : ¬H.IsMatching F) :
    H.innerNewAcceptanceFamilyMass M p F = 0 := by
  unfold innerNewAcceptanceFamilyMass
  apply sum_eq_zero
  intro S _
  have hnot : ¬F ⊆ H.isolatedSample (H.liveSample M S) := by
    intro hsub
    apply hF
    intro e heF f hfF hef
    exact H.isolatedSample_isMatching (H.liveSample M S)
      (hsub heF) (hsub hfF) hef
  simp [hnot]

/-- A set of at most `D` edges through each vertex has at most `|A| D`
edges meeting `A`.  Vertices of `A` outside `vertexSet` have degree zero,
so no containment hypothesis on `A` is needed. -/
lemma edgesMeeting_card_le_mul_degree
    (H : FiniteHypergraph V E) (A : Finset V) (D : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    (H.edgesMeeting A).card ≤ A.card * D := by
  have hdeg' (v : V) : H.edgeDegree v ≤ D := by
    by_cases hv : v ∈ H.vertexSet
    · exact hdeg v hv
    · have hno : ∀ e : E, v ∉ H.support e := by
        intro e hve
        exact hv (H.support_subset_vertexSet e hve)
      simp [edgeDegree, hno]
  have hsub : H.edgesMeeting A ⊆ A.biUnion H.incidentEdges := by
    intro e he
    obtain ⟨v, hve, hvA⟩ := not_disjoint_iff.mp
      ((H.mem_edgesMeeting A e).1 he)
    exact mem_biUnion.mpr ⟨v, hvA, (H.mem_incidentEdges v e).2 hve⟩
  calc
    (H.edgesMeeting A).card ≤ (A.biUnion H.incidentEdges).card :=
      card_le_card hsub
    _ ≤ ∑ v ∈ A, (H.incidentEdges v).card := card_biUnion_le
    _ = ∑ v ∈ A, H.edgeDegree v := by simp
    _ ≤ ∑ _v ∈ A, D := by
      apply sum_le_sum
      intro v _
      exact hdeg' v
    _ = A.card * D := by simp

/-- Edges which meet `A` in at least two vertices. -/
def multiMeetingEdges (H : FiniteHypergraph V E) (A : Finset V) : Finset E :=
  (H.edgesMeeting A).filter fun e ↦ 2 ≤ (H.support e ∩ A).card

/-- Edges meeting `A` in exactly one vertex, expressed as the complement of
the multiple-meeting exceptions inside `edgesMeeting`. -/
def singleMeetingEdges (H : FiniteHypergraph V E) (A : Finset V) : Finset E :=
  H.edgesMeeting A \ H.multiMeetingEdges A

@[simp] lemma mem_multiMeetingEdges
    (H : FiniteHypergraph V E) (A : Finset V) (e : E) :
    e ∈ H.multiMeetingEdges A ↔ 2 ≤ (H.support e ∩ A).card := by
  constructor
  · exact fun he ↦ (mem_filter.mp he).2
  · intro hcard
    have hne : (H.support e ∩ A).Nonempty :=
      nonempty_iff_ne_empty.mpr (by
        intro hempty
        simpa [hempty] using hcard)
    have hmeet : ¬Disjoint (H.support e) A :=
      not_disjoint_iff_nonempty_inter.mpr hne
    exact mem_filter.mpr ⟨(H.mem_edgesMeeting A e).2 hmeet, hcard⟩

lemma one_le_inter_card_of_mem_edgesMeeting
    (H : FiniteHypergraph V E) (A : Finset V) {e : E}
    (he : e ∈ H.edgesMeeting A) :
    1 ≤ (H.support e ∩ A).card := by
  exact card_pos.mpr (not_disjoint_iff_nonempty_inter.mp
    ((H.mem_edgesMeeting A e).1 he))

lemma inter_card_eq_one_of_mem_edgesMeeting_not_multi
    (H : FiniteHypergraph V E) (A : Finset V) {e : E}
    (he : e ∈ H.edgesMeeting A) (heMulti : e ∉ H.multiMeetingEdges A) :
    (H.support e ∩ A).card = 1 := by
  have hpos := H.one_le_inter_card_of_mem_edgesMeeting A he
  have hnot : ¬2 ≤ (H.support e ∩ A).card := fun htwo ↦
    heMulti ((H.mem_multiMeetingEdges A e).2 htwo)
  omega

/-- A nonexceptional edge meeting `A` enlarges `A` by exactly `k - 1`
vertices. -/
lemma card_union_support_eq_of_mem_edgesMeeting_not_multi
    (H : FiniteHypergraph V E) (A : Finset V) {e : E} {k : ℕ}
    (hunif : H.IsUniform k)
    (he : e ∈ H.edgesMeeting A) (heMulti : e ∉ H.multiMeetingEdges A) :
    (A ∪ H.support e).card = A.card + k - 1 := by
  have hinter : (A ∩ H.support e).card = 1 := by
    rw [inter_comm]
    exact H.inter_card_eq_one_of_mem_edgesMeeting_not_multi A he heMulti
  have hcount := card_union_add_card_inter A (H.support e)
  rw [hinter, hunif e] at hcount
  omega

lemma multiMeetingEdges_subset_edgesMeeting
    (H : FiniteHypergraph V E) (A : Finset V) :
    H.multiMeetingEdges A ⊆ H.edgesMeeting A := by
  exact filter_subset _ _

@[simp] lemma mem_singleMeetingEdges
    (H : FiniteHypergraph V E) (A : Finset V) (e : E) :
    e ∈ H.singleMeetingEdges A ↔
      e ∈ H.edgesMeeting A ∧ e ∉ H.multiMeetingEdges A := by
  simp [singleMeetingEdges]

/-- Every nonexceptional meeting edge has a unique anchor in `A`. -/
lemma existsUnique_anchor_of_mem_singleMeetingEdges
    (H : FiniteHypergraph V E) (A : Finset V) {e : E}
    (he : e ∈ H.singleMeetingEdges A) :
    ∃! v, v ∈ A ∧ v ∈ H.support e := by
  have hcard : (H.support e ∩ A).card = 1 :=
    H.inter_card_eq_one_of_mem_edgesMeeting_not_multi A
      ((H.mem_singleMeetingEdges A e).1 he |>.1)
      ((H.mem_singleMeetingEdges A e).1 he |>.2)
  obtain ⟨v, hv⟩ := card_eq_one.mp hcard
  refine ⟨v, ?_, ?_⟩
  · have : v ∈ H.support e ∩ A := by simp [hv]
    have this' := mem_inter.mp this
    exact ⟨this'.2, this'.1⟩
  · intro u hu
    have huInter : u ∈ H.support e ∩ A :=
      mem_inter.mpr ⟨hu.2, hu.1⟩
    have : u ∈ ({v} : Finset V) := by simpa [← hv] using huInter
    simpa using this

/-- Nonexceptional edges through a specified anchor vertex of `A`. -/
def singleMeetingAt (H : FiniteHypergraph V E)
    (A : Finset V) (v : V) : Finset E :=
  H.incidentEdges v ∩ H.singleMeetingEdges A

@[simp] lemma mem_singleMeetingAt
    (H : FiniteHypergraph V E) (A : Finset V) (v : V) (e : E) :
    e ∈ H.singleMeetingAt A v ↔
      v ∈ H.support e ∧ e ∈ H.singleMeetingEdges A := by
  simp [singleMeetingAt]

/-- At a vertex of `A`, only edges also meeting another vertex of `A` can
fail to belong to `singleMeetingAt`.  Pair-degree control therefore loses at
most `(A.card - 1) C` choices. -/
lemma edgeDegree_sub_pairError_le_singleMeetingAt_card
    (H : FiniteHypergraph V E) (A : Finset V) (v : V) (C : ℕ)
    (hvA : v ∈ A)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C) :
    H.edgeDegree v - (A.card - 1) * C ≤
      (H.singleMeetingAt A v).card := by
  let pairEdges : V → Finset E := fun u ↦
    (univ : Finset E).filter fun e ↦
      v ∈ H.support e ∧ u ∈ H.support e
  let bad : Finset E := H.incidentEdges v \ H.singleMeetingEdges A
  have hbadSub : bad ⊆ (A.erase v).biUnion pairEdges := by
    intro e heBad
    have heBad' := mem_sdiff.mp heBad
    have hve : v ∈ H.support e := (H.mem_incidentEdges v e).1 heBad'.1
    have heMeet : e ∈ H.edgesMeeting A := by
      apply (H.mem_edgesMeeting A e).2
      exact not_disjoint_iff.mpr ⟨v, hve, hvA⟩
    have heMulti : e ∈ H.multiMeetingEdges A := by
      by_contra hnot
      exact heBad'.2 ((H.mem_singleMeetingEdges A e).2 ⟨heMeet, hnot⟩)
    have htwo : 1 < (H.support e ∩ A).card := by
      exact (H.mem_multiMeetingEdges A e).1 heMulti
    have hvInter : v ∈ H.support e ∩ A := mem_inter.mpr ⟨hve, hvA⟩
    obtain ⟨u, huInter, huv⟩ := exists_mem_ne htwo v
    have huInter' := mem_inter.mp huInter
    exact mem_biUnion.mpr ⟨u, mem_erase.mpr ⟨huv, huInter'.2⟩,
      by simp [pairEdges, hve, huInter'.1]⟩
  have hpairEdges (u : V) (huv : u ≠ v) :
      (pairEdges u).card ≤ C := by
    by_cases hvV : v ∈ H.vertexSet
    · by_cases huV : u ∈ H.vertexSet
      · simpa [pairEdges, edgePairDegree, and_comm] using
          hpair v hvV u huV huv.symm
      · have hno : ∀ e : E, u ∉ H.support e := by
          intro e hue
          exact huV (H.support_subset_vertexSet e hue)
        simp [pairEdges, hno]
    · have hno : ∀ e : E, v ∉ H.support e := by
        intro e hve
        exact hvV (H.support_subset_vertexSet e hve)
      simp [pairEdges, hno]
  have hbadCard : bad.card ≤ (A.erase v).card * C := by
    calc
      bad.card ≤ ((A.erase v).biUnion pairEdges).card :=
        card_le_card hbadSub
      _ ≤ ∑ u ∈ A.erase v, (pairEdges u).card := card_biUnion_le
      _ ≤ ∑ _u ∈ A.erase v, C := by
        apply sum_le_sum
        intro u hu
        exact hpairEdges u (mem_erase.mp hu).1
      _ = (A.erase v).card * C := by simp
  have hpartition :
      bad.card + (H.singleMeetingAt A v).card = H.edgeDegree v := by
    simpa [bad, singleMeetingAt] using
      card_sdiff_add_card_inter (H.incidentEdges v)
        (H.singleMeetingEdges A)
  have herase : (A.erase v).card = A.card - 1 := card_erase_of_mem hvA
  rw [herase] at hbadCard
  omega

/-- At a distinct anchor `v`, at most `k C` nonexceptional choices conflict
with an already chosen edge `e`. -/
lemma singleMeetingAt_conflict_card_le
    (H : FiniteHypergraph V E) (A : Finset V) {v : V} {e : E}
    {k C : ℕ} (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C)
    (hvV : v ∈ H.vertexSet) (hve : v ∉ H.support e) :
    ((H.singleMeetingAt A v).filter fun f ↦ H.Conflicts f e).card ≤
      k * C := by
  calc
    ((H.singleMeetingAt A v).filter fun f ↦ H.Conflicts f e).card ≤
        H.conflictLink v e := by
      change
        ((H.singleMeetingAt A v).filter fun f ↦ H.Conflicts f e).card ≤
          ((univ : Finset E).filter fun f ↦
            v ∈ H.support f ∧ H.Conflicts f e).card
      apply card_le_card
      intro f hf
      have hf' := mem_filter.mp hf
      rw [mem_filter]
      exact ⟨mem_univ f, (H.mem_singleMeetingAt A v f).1 hf'.1 |>.1,
        hf'.2⟩
    _ ≤ k * C := H.conflictLink_le_uniform_mul hunif hpair hvV hve

/-- Union-bound form for sequential selection: if the new anchor `v` is
outside every previously selected edge in `G`, at most `|G| k C` of its
nonexceptional choices conflict with some edge of `G`. -/
lemma singleMeetingAt_conflicts_family_card_le
    (H : FiniteHypergraph V E) (A : Finset V) {v : V} (G : Finset E)
    {k C : ℕ} (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C)
    (hvV : v ∈ H.vertexSet) (hvG : ∀ e ∈ G, v ∉ H.support e) :
    ((H.singleMeetingAt A v).filter fun f ↦
        ∃ e ∈ G, H.Conflicts f e).card ≤
      G.card * (k * C) := by
  let badFor : E → Finset E := fun e ↦
    (H.singleMeetingAt A v).filter fun f ↦ H.Conflicts f e
  have hsub :
      (H.singleMeetingAt A v).filter (fun f ↦
          ∃ e ∈ G, H.Conflicts f e) ⊆ G.biUnion badFor := by
    intro f hf
    obtain ⟨hfAt, e, heG, hconf⟩ := mem_filter.mp hf
    exact mem_biUnion.mpr ⟨e, heG,
      mem_filter.mpr ⟨hfAt, hconf⟩⟩
  calc
    ((H.singleMeetingAt A v).filter fun f ↦
        ∃ e ∈ G, H.Conflicts f e).card ≤
        (G.biUnion badFor).card := card_le_card hsub
    _ ≤ ∑ e ∈ G, (badFor e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ G, k * C := by
      apply sum_le_sum
      intro e he
      exact H.singleMeetingAt_conflict_card_le A hunif hpair hvV (hvG e he)
    _ = G.card * (k * C) := by simp

/-- Exact sequential availability bound obtained by deleting all choices
that conflict with the previously selected family `G`. -/
lemma edgeDegree_sub_pairError_sub_familyConflict_le_availableSingleMeetingAt
    (H : FiniteHypergraph V E) (A : Finset V) {v : V} (G : Finset E)
    {k C : ℕ} (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C)
    (hvA : v ∈ A) (hvV : v ∈ H.vertexSet)
    (hvG : ∀ e ∈ G, v ∉ H.support e) :
    H.edgeDegree v - (A.card - 1) * C - G.card * (k * C) ≤
      ((H.singleMeetingAt A v).filter fun f ↦
        ∀ e ∈ G, ¬H.Conflicts f e).card := by
  let available : Finset E :=
    (H.singleMeetingAt A v).filter fun f ↦
      ∀ e ∈ G, ¬H.Conflicts f e
  let bad : Finset E :=
    (H.singleMeetingAt A v).filter fun f ↦
      ∃ e ∈ G, H.Conflicts f e
  have hcover : H.singleMeetingAt A v ⊆ available ∪ bad := by
    intro f hf
    by_cases havail : ∀ e ∈ G, ¬H.Conflicts f e
    · exact mem_union_left _ (mem_filter.mpr ⟨hf, havail⟩)
    · have hbad : ∃ e ∈ G, H.Conflicts f e := by
        push Not at havail
        exact havail
      exact mem_union_right _ (mem_filter.mpr ⟨hf, hbad⟩)
  have hcoverCard :
      (H.singleMeetingAt A v).card ≤ available.card + bad.card := by
    exact (card_le_card hcover).trans (card_union_le available bad)
  have hsingle :
      H.edgeDegree v - (A.card - 1) * C ≤
        (H.singleMeetingAt A v).card :=
    H.edgeDegree_sub_pairError_le_singleMeetingAt_card A v C hvA hpair
  have hbad : bad.card ≤ G.card * (k * C) := by
    exact H.singleMeetingAt_conflicts_family_card_le A G hunif hpair hvV hvG
  change H.edgeDegree v - (A.card - 1) * C - G.card * (k * C) ≤
    available.card
  omega

/-- The anchors contributed by a matching family of nonexceptional edges
are distinct, so their union has exactly the family cardinality. -/
lemma card_biUnion_support_inter_eq_of_matching_subset_singleMeeting
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A) :
    (F.biUnion fun e ↦ H.support e ∩ A).card = F.card := by
  have hdisjoint :
      ∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        Disjoint (H.support e ∩ A) (H.support f ∩ A) := by
    intro e he f hf hef
    exact (hF he hf hef).mono inter_subset_left inter_subset_left
  rw [card_biUnion hdisjoint]
  calc
    (∑ e ∈ F, (H.support e ∩ A).card) = ∑ _e ∈ F, 1 := by
      apply sum_congr rfl
      intro e he
      exact H.inter_card_eq_one_of_mem_edgesMeeting_not_multi A
        ((H.mem_singleMeetingEdges A e).1 (hFsingle he) |>.1)
        ((H.mem_singleMeetingEdges A e).1 (hFsingle he) |>.2)
    _ = F.card := by simp

/-- A matching family whose every edge meets `A` in exactly one vertex
enlarges `A` by exactly `k - 1` fresh vertices per edge.  This is the
cardinality profile used by the all-order survival hierarchy. -/
lemma card_union_biUnion_support_eq_of_matching_subset_singleMeeting
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A) :
    (A ∪ F.biUnion H.support).card = A.card + F.card * (k - 1) := by
  have hsupportCard : (F.biUnion H.support).card = F.card * k := by
    rw [card_biUnion hF]
    calc
      (∑ e ∈ F, (H.support e).card) = ∑ _e ∈ F, k := by
        apply sum_congr rfl
        intro e _
        exact hunif e
      _ = F.card * k := by simp
  have hinterEq :
      A ∩ F.biUnion H.support =
        F.biUnion (fun e ↦ A ∩ H.support e) := by
    ext v
    simp [and_left_comm, and_assoc]
  have hdisjoint :
      ∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        Disjoint (A ∩ H.support e) (A ∩ H.support f) := by
    intro e he f hf hef
    exact (hF he hf hef).mono inter_subset_right inter_subset_right
  have hinterCard : (A ∩ F.biUnion H.support).card = F.card := by
    rw [hinterEq, card_biUnion hdisjoint]
    calc
      (∑ e ∈ F, (A ∩ H.support e).card) = ∑ _e ∈ F, 1 := by
        apply sum_congr rfl
        intro e he
        rw [inter_comm]
        exact H.inter_card_eq_one_of_mem_edgesMeeting_not_multi A
          ((H.mem_singleMeetingEdges A e).1 (hFsingle he) |>.1)
          ((H.mem_singleMeetingEdges A e).1 (hFsingle he) |>.2)
      _ = F.card := by simp
  have hcount := card_union_add_card_inter A (F.biUnion H.support)
  rw [hinterCard, hsupportCard] at hcount
  have hkdecomp : k = (k - 1) + 1 := by omega
  rw [hkdecomp, Nat.mul_add, Nat.mul_one] at hcount
  omega

lemma edgesMeeting_eq_single_union_multi
    (H : FiniteHypergraph V E) (A : Finset V) :
    H.singleMeetingEdges A ∪ H.multiMeetingEdges A = H.edgesMeeting A := by
  exact sdiff_union_of_subset (H.multiMeetingEdges_subset_edgesMeeting A)

/-- Split any profile sum over meeting edges into the single- and
multiple-meeting parts. -/
lemma sum_edgesMeeting_eq_sum_single_add_sum_multi
    (H : FiniteHypergraph V E) (A : Finset V) (F : E → ℝ) :
    (∑ e ∈ H.edgesMeeting A, F e) =
      (∑ e ∈ H.singleMeetingEdges A, F e) +
        ∑ e ∈ H.multiMeetingEdges A, F e := by
  rw [← H.edgesMeeting_eq_single_union_multi A]
  have hdisj : Disjoint (H.singleMeetingEdges A) (H.multiMeetingEdges A) := by
    unfold singleMeetingEdges
    exact sdiff_disjoint
  exact sum_union hdisj

/-- Low pair degree bounds the number of edges which hit `A` more than
once.  The deliberately coarse `|A|² C` form is stable under all later
parameter substitutions. -/
lemma multiMeetingEdges_card_le_sq_mul_pairDegree
    (H : FiniteHypergraph V E) (A : Finset V) (C : ℕ)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    (H.multiMeetingEdges A).card ≤ A.card ^ 2 * C := by
  let pairEdges : V → V → Finset E := fun u v ↦
    (univ : Finset E).filter fun e ↦
      u ∈ H.support e ∧ v ∈ H.support e
  let cover : Finset E := A.biUnion fun u ↦
    (A.erase u).biUnion fun v ↦ pairEdges u v
  have hsub : H.multiMeetingEdges A ⊆ cover := by
    intro e he
    have htwo : 1 < (H.support e ∩ A).card := by
      exact (H.mem_multiMeetingEdges A e).1 he
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp htwo
    have hu' := mem_inter.mp hu
    have hv' := mem_inter.mp hv
    apply mem_biUnion.mpr
    refine ⟨u, hu'.2, mem_biUnion.mpr ⟨v, ?_, ?_⟩⟩
    · exact mem_erase.mpr ⟨huv.symm, hv'.2⟩
    · exact mem_filter.mpr ⟨mem_univ e, hu'.1, hv'.1⟩
  have hpair' : ∀ u v, u ≠ v → (pairEdges u v).card ≤ C := by
    intro u v huv
    by_cases hu : u ∈ H.vertexSet
    · by_cases hv : v ∈ H.vertexSet
      · simpa [pairEdges, edgePairDegree] using hpair u hu v hv huv
      · have hno : ∀ e : E, v ∉ H.support e := by
          intro e hve
          exact hv (H.support_subset_vertexSet e hve)
        simp [pairEdges, hno]
    · have hno : ∀ e : E, u ∉ H.support e := by
        intro e hue
        exact hu (H.support_subset_vertexSet e hue)
      simp [pairEdges, hno]
  calc
    (H.multiMeetingEdges A).card ≤ cover.card := card_le_card hsub
    _ ≤ ∑ u ∈ A, ((A.erase u).biUnion fun v ↦ pairEdges u v).card :=
      card_biUnion_le
    _ ≤ ∑ u ∈ A, ∑ v ∈ A.erase u, (pairEdges u v).card := by
      apply sum_le_sum
      intro u _
      exact card_biUnion_le
    _ ≤ ∑ _u ∈ A, ∑ _v ∈ A.erase _u, C := by
      apply sum_le_sum
      intro u _
      apply sum_le_sum
      intro v hv
      exact hpair' u v (mem_erase.mp hv).1.symm
    _ ≤ ∑ _u ∈ A, A.card * C := by
      apply sum_le_sum
      intro u _
      simp only [sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right C card_erase_le
    _ = A.card ^ 2 * C := by simp [pow_two, Nat.mul_assoc]

/-- Before imposing a uniform codegree cap, multiple-meeting edges are
controlled by the sum of the pair degrees over ordered distinct pairs in
`A`.  This form is useful when the codegree hypothesis is naturally stated
over the reals. -/
lemma multiMeetingEdges_card_le_sum_pairDegree
    (H : FiniteHypergraph V E) (A : Finset V) :
    (H.multiMeetingEdges A).card ≤
      ∑ u ∈ A, ∑ v ∈ A.erase u, H.edgePairDegree u v := by
  let pairEdges : V → V → Finset E := fun u v ↦
    (univ : Finset E).filter fun e ↦
      u ∈ H.support e ∧ v ∈ H.support e
  let cover : Finset E := A.biUnion fun u ↦
    (A.erase u).biUnion fun v ↦ pairEdges u v
  have hsub : H.multiMeetingEdges A ⊆ cover := by
    intro e he
    have htwo : 1 < (H.support e ∩ A).card := by
      exact (H.mem_multiMeetingEdges A e).1 he
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp htwo
    have hu' := mem_inter.mp hu
    have hv' := mem_inter.mp hv
    apply mem_biUnion.mpr
    refine ⟨u, hu'.2, mem_biUnion.mpr ⟨v, ?_, ?_⟩⟩
    · exact mem_erase.mpr ⟨huv.symm, hv'.2⟩
    · exact mem_filter.mpr ⟨mem_univ e, hu'.1, hv'.1⟩
  have hpairCard (u v : V) :
      (pairEdges u v).card = H.edgePairDegree u v := by
    rfl
  calc
    (H.multiMeetingEdges A).card ≤ cover.card := card_le_card hsub
    _ ≤ ∑ u ∈ A, ((A.erase u).biUnion fun v ↦ pairEdges u v).card :=
      card_biUnion_le
    _ ≤ ∑ u ∈ A, ∑ v ∈ A.erase u, (pairEdges u v).card := by
      apply sum_le_sum
      intro u _
      exact card_biUnion_le
    _ = ∑ u ∈ A, ∑ v ∈ A.erase u, H.edgePairDegree u v := by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      exact hpairCard u v

/-- Real-valued low codegree bounds the number of edges which meet `A` in
at least two vertices.  The statement is aligned with the asymptotic
near-regular hypotheses, so no floor or ceiling loss is introduced. -/
lemma natCast_multiMeetingEdges_card_le_sq_mul_pairDegree_real
    (H : FiniteHypergraph V E) (A : Finset V) (codegreeUpper : ℝ)
    (hcodegreeUpper₀ : 0 ≤ codegreeUpper)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) ≤ codegreeUpper) :
    ((H.multiMeetingEdges A).card : ℝ) ≤
      (A.card : ℝ) ^ 2 * codegreeUpper := by
  have hpairAll (u v : V) (huv : u ≠ v) :
      (H.edgePairDegree u v : ℝ) ≤ codegreeUpper := by
    by_cases hu : u ∈ H.vertexSet
    · by_cases hv : v ∈ H.vertexSet
      · exact hpair u hu v hv huv
      · have hno : ∀ e : E, v ∉ H.support e := by
          intro e hve
          exact hv (H.support_subset_vertexSet e hve)
        simp [edgePairDegree, hno, hcodegreeUpper₀]
    · have hno : ∀ e : E, u ∉ H.support e := by
        intro e hue
        exact hu (H.support_subset_vertexSet e hue)
      simp [edgePairDegree, hno, hcodegreeUpper₀]
  have hbase := H.multiMeetingEdges_card_le_sum_pairDegree A
  have hbaseReal :
      ((H.multiMeetingEdges A).card : ℝ) ≤
        ∑ u ∈ A, ∑ v ∈ A.erase u, (H.edgePairDegree u v : ℝ) := by
    exact_mod_cast hbase
  calc
    ((H.multiMeetingEdges A).card : ℝ) ≤
        ∑ u ∈ A, ∑ v ∈ A.erase u, (H.edgePairDegree u v : ℝ) := hbaseReal
    _ ≤ ∑ _u ∈ A, ∑ _v ∈ A.erase _u, codegreeUpper := by
      apply sum_le_sum
      intro u _
      apply sum_le_sum
      intro v hv
      exact hpairAll u v (mem_erase.mp hv).1.symm
    _ ≤ ∑ _u ∈ A, (A.card : ℝ) * codegreeUpper := by
      apply sum_le_sum
      intro u _
      simp only [sum_const, nsmul_eq_mul]
      have hcard : (A.erase u).card ≤ A.card := card_erase_le
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard) hcodegreeUpper₀
    _ = (A.card : ℝ) ^ 2 * codegreeUpper := by
      simp [pow_two]
      ring

/-- Double-count incidences between `A` and the edge index set. -/
lemma sum_edgeDegree_eq_sum_edgesMeeting_inter_card
    (H : FiniteHypergraph V E) (A : Finset V) :
    (∑ v ∈ A, H.edgeDegree v) =
      ∑ e ∈ H.edgesMeeting A, (H.support e ∩ A).card := by
  have hdegree (v : V) : H.edgeDegree v =
      ∑ e : E, if v ∈ H.support e then 1 else 0 := by
    unfold edgeDegree
    rw [card_eq_sum_ones, sum_filter]
  have hinter (e : E) :
      (∑ v ∈ A, if v ∈ H.support e then 1 else 0) =
        (H.support e ∩ A).card := by
    calc
      (∑ v ∈ A, if v ∈ H.support e then 1 else 0) =
          (A ∩ H.support e).card := by simp
      _ = (H.support e ∩ A).card := by rw [inter_comm]
  calc
    (∑ v ∈ A, H.edgeDegree v) =
        ∑ v ∈ A, ∑ e : E, if v ∈ H.support e then 1 else 0 := by
      apply sum_congr rfl
      intro v _
      exact hdegree v
    _ = ∑ e : E, ∑ v ∈ A, if v ∈ H.support e then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ e : E, (H.support e ∩ A).card := by
      apply sum_congr rfl
      intro e _
      exact hinter e
    _ = ∑ e ∈ H.edgesMeeting A, (H.support e ∩ A).card := by
      unfold edgesMeeting
      rw [sum_filter]
      apply sum_congr rfl
      intro e _
      by_cases hmeet : ¬Disjoint (H.support e) A
      · simp [hmeet]
      · have hdisj : Disjoint (H.support e) A := not_not.mp hmeet
        simp [hmeet, disjoint_iff_inter_eq_empty.mp hdisj]

/-- Incidence excess beyond one per meeting edge can only come from edges
meeting `A` at least twice. -/
lemma sum_edgeDegree_le_edgesMeeting_add_multi
    (H : FiniteHypergraph V E) (A : Finset V) {k : ℕ}
    (hunif : H.IsUniform k) :
    (∑ v ∈ A, H.edgeDegree v) ≤
      (H.edgesMeeting A).card + (H.multiMeetingEdges A).card * k := by
  rw [H.sum_edgeDegree_eq_sum_edgesMeeting_inter_card]
  calc
    (∑ e ∈ H.edgesMeeting A, (H.support e ∩ A).card) ≤
        ∑ e ∈ H.edgesMeeting A,
          (1 + if e ∈ H.multiMeetingEdges A then k else 0) := by
      apply sum_le_sum
      intro e he
      have hmeet := (H.mem_edgesMeeting A e).1 he
      have hpos : 1 ≤ (H.support e ∩ A).card :=
        card_pos.mpr (not_disjoint_iff_nonempty_inter.mp hmeet)
      have hle : (H.support e ∩ A).card ≤ k := calc
        (H.support e ∩ A).card ≤ (H.support e).card :=
          card_le_card inter_subset_left
        _ = k := hunif e
      by_cases hmulti : e ∈ H.multiMeetingEdges A
      · simp [hmulti]
        omega
      · have hnot : ¬ 2 ≤ (H.support e ∩ A).card := fun htwo ↦
          hmulti ((H.mem_multiMeetingEdges A e).2 htwo)
        simp [hmulti]
        omega
    _ = (H.edgesMeeting A).card +
        (H.multiMeetingEdges A).card * k := by
      rw [sum_add_distrib]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 1
      have hfilter :
          (H.edgesMeeting A).filter (fun e ↦ e ∈ H.multiMeetingEdges A) =
            H.multiMeetingEdges A := by
        ext e
        simp [multiMeetingEdges]
      rw [← sum_filter, hfilter]
      simp

/-- Near-regular lower degrees and low pair degree force many distinct edges
to meet `A`, up to the explicitly bounded multiple-intersection error. -/
lemma card_mul_degreeLower_le_edgesMeeting_add_pairError
    (H : FiniteHypergraph V E) (A : Finset V) {k degreeLower C : ℕ}
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    A.card * degreeLower ≤
      (H.edgesMeeting A).card + A.card ^ 2 * C * k := by
  calc
    A.card * degreeLower = ∑ _v ∈ A, degreeLower := by simp
    _ ≤ ∑ v ∈ A, H.edgeDegree v := by
      apply sum_le_sum
      intro v hv
      exact hlow v hv
    _ ≤ (H.edgesMeeting A).card +
        (H.multiMeetingEdges A).card * k :=
      H.sum_edgeDegree_le_edgesMeeting_add_multi A hunif
    _ ≤ (H.edgesMeeting A).card + A.card ^ 2 * C * k := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right k
          (H.multiMeetingEdges_card_le_sq_mul_pairDegree A C hpair)) _

/-- Real-valued near-regular lower degrees and codegrees force many
nonexceptional (single-meeting) edges.  This is the exact structural profile
needed by the fixed-length joint-moment comparison. -/
lemma natCast_singleMeetingEdges_card_ge_real
    (H : FiniteHypergraph V E) (A : Finset V) {k : ℕ}
    (degreeLower codegreeUpper : ℝ)
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ (H.edgeDegree v : ℝ))
    (hcodegreeUpper₀ : 0 ≤ codegreeUpper)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) ≤ codegreeUpper) :
    (A.card : ℝ) * degreeLower -
        (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1) ≤
      ((H.singleMeetingEdges A).card : ℝ) := by
  have hlowSum : (A.card : ℝ) * degreeLower ≤
      ∑ v ∈ A, (H.edgeDegree v : ℝ) := by
    calc
      (A.card : ℝ) * degreeLower = ∑ _v ∈ A, degreeLower := by simp
      _ ≤ ∑ v ∈ A, (H.edgeDegree v : ℝ) := by
        apply sum_le_sum
        intro v hv
        exact hlow v hv
  have hincidenceNat := H.sum_edgeDegree_le_edgesMeeting_add_multi A hunif
  have hincidence :
      (∑ v ∈ A, (H.edgeDegree v : ℝ)) ≤
        ((H.edgesMeeting A).card : ℝ) +
          ((H.multiMeetingEdges A).card : ℝ) * (k : ℝ) := by
    exact_mod_cast hincidenceNat
  have hdisj : Disjoint (H.singleMeetingEdges A) (H.multiMeetingEdges A) := by
    unfold singleMeetingEdges
    exact sdiff_disjoint
  have hcardNat :
      (H.edgesMeeting A).card =
        (H.singleMeetingEdges A).card + (H.multiMeetingEdges A).card := by
    rw [← H.edgesMeeting_eq_single_union_multi A,
      card_union_of_disjoint hdisj]
  have hcard :
      ((H.edgesMeeting A).card : ℝ) =
        ((H.singleMeetingEdges A).card : ℝ) +
          ((H.multiMeetingEdges A).card : ℝ) := by
    exact_mod_cast hcardNat
  have hmulti :=
    H.natCast_multiMeetingEdges_card_le_sq_mul_pairDegree_real
      A codegreeUpper hcodegreeUpper₀ hpair
  have hk₁₀ : 0 ≤ (k : ℝ) + 1 := by positivity
  calc
    (A.card : ℝ) * degreeLower -
          (A.card : ℝ) ^ 2 * codegreeUpper * ((k : ℝ) + 1) ≤
        (∑ v ∈ A, (H.edgeDegree v : ℝ)) -
          ((H.multiMeetingEdges A).card : ℝ) * ((k : ℝ) + 1) := by
      exact sub_le_sub hlowSum
        (mul_le_mul_of_nonneg_right hmulti hk₁₀)
    _ ≤ ((H.singleMeetingEdges A).card : ℝ) := by
      rw [hcard] at hincidence
      linarith

/-- The joint second Bernoulli moment of two distinct sampled coordinates. -/
lemma sum_bernoulliMass_mul_indicator_mem_mem
    (p : E → ℝ) {e f : E} (hef : e ≠ f) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ S ∧ f ∈ S then 1 else 0) = p e * p f := by
  calc
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ S ∧ f ∈ S then 1 else 0) =
        ∑ S ∈ (univ : Finset E).powerset with e ∈ S ∧ f ∈ S,
          FiniteNibble.bernoulliMass univ p S := by
      simp only [powerset_univ, sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases heS : e ∈ S <;> by_cases hfS : f ∈ S <;>
        simp [heS, hfS]
    _ = p e * p f :=
      FiniteNibble.sum_bernoulliMass_filter_mem_mem
        (mem_univ e) (mem_univ f) hef

/-- Expected number of ordered distinct pairs in the restriction of a
Bernoulli sample to `K`. -/
lemma sum_bernoulliMass_mul_sampled_offDiag_card
    (K : Finset E) (p : E → ℝ) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        (((K.filter fun e ↦ e ∈ S).offDiag.card : ℕ) : ℝ)) =
      ∑ z ∈ K.offDiag, p z.1 * p z.2 := by
  have hcard (S : Finset E) :
      (((K.filter fun e ↦ e ∈ S).offDiag.card : ℕ) : ℝ) =
        ∑ z ∈ K.offDiag, if z.1 ∈ S ∧ z.2 ∈ S then 1 else 0 := by
    have hset : (K.filter fun e ↦ e ∈ S).offDiag =
        K.offDiag.filter fun z ↦ z.1 ∈ S ∧ z.2 ∈ S := by
      ext z
      simp only [mem_offDiag, mem_filter]
      tauto
    rw [hset, card_eq_sum_ones]
    conv_rhs => rw [← sum_filter]
    norm_cast
  simp_rw [hcard, Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro z hz
  exact sum_bernoulliMass_mul_indicator_mem_mem p
    (mem_offDiag.mp hz).2.2

/-- Casting the cardinality of `offDiag` gives the real falling factorial. -/
lemma natCast_offDiag_card (K : Finset E) :
    (K.offDiag.card : ℝ) = (K.card : ℝ) * ((K.card : ℝ) - 1) := by
  have hnat : K.offDiag.card = K.card * (K.card - 1) := by
    rw [offDiag_card, Nat.mul_sub_left_distrib]
    simp
  rw [hnat]
  by_cases hK : K.card = 0
  · simp [hK]
  · rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hK)]
    norm_num

/-- Quadratic Bonferroni bound for the newly accepted matching edges meeting
`A`.  It is the exact `O((|A| D p)^2)` error used in the joint survival
recurrence. -/
theorem sum_bernoulliMass_mul_innerNewAcceptedMeeting_pairCount_le
    (H : FiniteHypergraph V E) (M : Finset E) (A : Finset V) (D : ℕ)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
        ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
        (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2) ≤
      ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 := by
  let K := H.edgesMeeting A
  have hsub (S : Finset E) :
      H.innerNewAcceptedMeeting M S A ⊆ K.filter fun e ↦ e ∈ S := by
    intro e he
    have heInfo := (H.mem_innerNewAcceptedMeeting M S A e).1 he
    have heSample : e ∈ S :=
      H.liveSample_subset_sample M S
        (H.isolatedSample_subset (H.liveSample M S) heInfo.1)
    exact mem_filter.mpr ⟨(H.mem_edgesMeeting A e).2 heInfo.2, heSample⟩
  have hoff (S : Finset E) :
      ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
          (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) =
        ((H.innerNewAcceptedMeeting M S A).offDiag.card : ℝ) := by
    rw [natCast_offDiag_card]
  have hmass₀ (S : Finset E) :
      0 ≤ FiniteNibble.bernoulliMass univ (fun _ : E ↦ p) S :=
    FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  calc
    (∑ S : Finset E, FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
        ((H.innerNewAcceptedMeeting M S A).card : ℝ) *
        (((H.innerNewAcceptedMeeting M S A).card : ℝ) - 1) / 2) =
        ∑ S : Finset E, FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          ((H.innerNewAcceptedMeeting M S A).offDiag.card : ℝ) / 2 := by
      apply sum_congr rfl
      intro S _
      rw [← hoff S]
      ring
    _ ≤ ∑ S : Finset E, FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          (((K.filter fun e ↦ e ∈ S).offDiag.card : ℕ) : ℝ) / 2 := by
      apply sum_le_sum
      intro S _
      have hcard := card_le_card (offDiag_mono (hsub S))
      have hcardR :
          ((H.innerNewAcceptedMeeting M S A).offDiag.card : ℝ) ≤
            (((K.filter fun e ↦ e ∈ S).offDiag.card : ℕ) : ℝ) := by
        exact_mod_cast hcard
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardR (hmass₀ S)) (by norm_num)
    _ = ((K.offDiag.card : ℝ) * p ^ 2) / 2 := by
      rw [← sum_div]
      rw [sum_bernoulliMass_mul_sampled_offDiag_card]
      simp [pow_two]
    _ ≤ ((((A.card * D : ℕ) : ℝ) * p) ^ 2) / 2 := by
      have hK := H.edgesMeeting_card_le_mul_degree A D hdeg
      have hKreal : (K.card : ℝ) ≤ ((A.card * D : ℕ) : ℝ) := by
        exact_mod_cast hK
      have hpSq : 0 ≤ p ^ 2 := sq_nonneg p
      rw [natCast_offDiag_card]
      have hfall : (K.card : ℝ) * ((K.card : ℝ) - 1) ≤
          ((A.card * D : ℕ) : ℝ) ^ 2 := by
        have hK₀ : 0 ≤ (K.card : ℝ) := Nat.cast_nonneg _
        nlinarith [sq_nonneg ((A.card * D : ℕ) : ℝ)]
      have := mul_le_mul_of_nonneg_right hfall hpSq
      nlinarith

/-! ### Joint uncovered moments and the forward tower identity -/

/-- Joint uncovered mass of a finite vertex set after `r` inner rounds. -/
def innerJointUncoveredMass (H : FiniteHypergraph V E)
    (w : Finset E → ℝ) (r : ℕ) (M : Finset E) (A : Finset V) : ℝ :=
  ∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
    if ∀ v ∈ A, H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
      then 1 else 0

@[simp] lemma innerJointUncoveredMass_zero
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (M : Finset E) (A : Finset V) :
    H.innerJointUncoveredMass w 0 M A =
      if ∀ v ∈ A, H.UncoveredBy M v then 1 else 0 := by
  simp [innerJointUncoveredMass, FiniteProduct.productMass]

/-- Every normalized nonnegative product law gives a joint uncovered mass
in the unit interval. -/
lemma innerJointUncoveredMass_mem_Icc
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (hw₀ : ∀ S, 0 ≤ w S) (hw : ∑ S, w S = 1)
    (r : ℕ) (M : Finset E) (A : Finset V) :
    H.innerJointUncoveredMass w r M A ∈ Set.Icc (0 : ℝ) 1 := by
  have hprod₀ (X : Fin r → Finset E) :
      0 ≤ FiniteProduct.productMass w X := by
    unfold FiniteProduct.productMass
    exact prod_nonneg fun i _ ↦ hw₀ (X i)
  constructor
  · unfold innerJointUncoveredMass
    apply sum_nonneg
    intro X _
    exact mul_nonneg (hprod₀ X) (by split <;> norm_num)
  · unfold innerJointUncoveredMass
    calc
      (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
          if ∀ v ∈ A,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0) ≤
          ∑ X : Fin r → Finset E, FiniteProduct.productMass w X := by
        apply sum_le_sum
        intro X _
        exact (by
          have hind :
              (if ∀ v ∈ A,
                  H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
                then (1 : ℝ) else 0) ≤ 1 := by
            split <;> norm_num
          simpa using mul_le_mul_of_nonneg_left hind (hprod₀ X))
      _ = 1 := sum_productMass_eq_one w hw r

/-- Bernoulli specialization of `innerJointUncoveredMass_mem_Icc`. -/
lemma innerJointUncoveredMass_bernoulli_mem_Icc
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (r : ℕ) (M : Finset E) (A : Finset V) :
    H.innerJointUncoveredMass (FiniteNibble.bernoulliMass univ p) r M A ∈
      Set.Icc (0 : ℝ) 1 := by
  apply H.innerJointUncoveredMass_mem_Icc
  · intro S
    exact FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  · simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) p

/-- Splitting a trajectory at its last coordinate gives the tower identity
needed for forward induction of all joint uncovered moments. -/
theorem innerJointUncoveredMass_succ_last
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) :
    H.innerJointUncoveredMass w (r + 1) M A =
      ∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        ∑ S : Finset E, w S *
          if ∀ v ∈ A,
              H.UncoveredBy
                (H.innerStep ((List.ofFn X).foldl H.innerStep M) S) v
            then 1 else 0 := by
  unfold innerJointUncoveredMass
  calc
    (∑ Y : Fin (r + 1) → Finset E, FiniteProduct.productMass w Y *
        if ∀ v ∈ A, H.UncoveredBy
            ((List.ofFn Y).foldl H.innerStep M) v then 1 else 0) =
        ∑ z : Finset E × (Fin r → Finset E),
          FiniteProduct.productMass w
              ((Fin.snocEquiv (fun _ : Fin (r + 1) ↦ Finset E)) z) *
            if ∀ v ∈ A, H.UncoveredBy
                ((List.ofFn
                  ((Fin.snocEquiv (fun _ : Fin (r + 1) ↦ Finset E)) z)).foldl
                    H.innerStep M) v then 1 else 0 :=
      (Fin.snocEquiv (fun _ : Fin (r + 1) ↦ Finset E)).sum_comp
        (fun Y ↦ FiniteProduct.productMass w Y *
          if ∀ v ∈ A,
            H.UncoveredBy ((List.ofFn Y).foldl H.innerStep M) v
          then 1 else 0) |>.symm
    _ = ∑ S : Finset E, ∑ X : Fin r → Finset E,
          (FiniteProduct.productMass w X * w S) *
            if ∀ v ∈ A,
                H.UncoveredBy
                  (H.innerStep ((List.ofFn X).foldl H.innerStep M) S) v
              then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro X _
      change
        ((∏ j : Fin (r + 1),
            w ((Fin.snoc X S : Fin (r + 1) → Finset E) j)) *
            if ∀ v ∈ A,
                H.UncoveredBy
                  ((List.ofFn
                    (Fin.snoc X S : Fin (r + 1) → Finset E)).foldl
                      H.innerStep M) v
              then 1 else 0) = _
      rw [Fin.prod_univ_castSucc, list_ofFn_snoc, List.foldl_append]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.foldl_cons,
        List.foldl_nil, FiniteProduct.productMass]
      change
        (FiniteProduct.productMass w X * w S) *
            (if ∀ v ∈ A,
                H.UncoveredBy
                  (H.innerStep ((List.ofFn X).foldl H.innerStep M) S) v
              then 1 else 0) =
          (FiniteProduct.productMass w X * w S) *
            (if ∀ v ∈ A,
                H.UncoveredBy
                  (H.innerStep ((List.ofFn X).foldl H.innerStep M) S) v
              then 1 else 0)
      rfl
    _ = ∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
          ∑ S : Finset E, w S *
            if ∀ v ∈ A,
                H.UncoveredBy
                  (H.innerStep ((List.ofFn X).foldl H.innerStep M) S) v
              then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring

/-- Bernoulli specialization of the last-round tower identity. -/
theorem innerJointUncoveredMass_bernoulli_succ_last
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) :
    H.innerJointUncoveredMass (FiniteNibble.bernoulliMass univ p) (r + 1) M A =
      ∑ X : Fin r → Finset E,
        FiniteProduct.productMass (FiniteNibble.bernoulliMass univ p) X *
          ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
            if ∀ v ∈ A,
                H.UncoveredBy
                  (H.innerStep ((List.ofFn X).foldl H.innerStep M) S) v
              then 1 else 0 := by
  exact H.innerJointUncoveredMass_succ_last
    (FiniteNibble.bernoulliMass univ p) r M A

/-! ### Joint-live trajectory identities -/

/-- Joint uncoveredness after a step implies joint uncoveredness before it. -/
lemma jointUncovered_of_innerStep
    (H : FiniteHypergraph V E) {M S : Finset E} {A : Finset V}
    (hstep : ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v) :
    ∀ v ∈ A, H.UncoveredBy M v := by
  intro v hvA e heM hve
  exact hstep v hvA e (H.subset_innerStep M S heM) hve

/-- Once some vertex of `A` is covered, no later inner step can make all of
`A` uncovered again. -/
lemma not_jointUncovered_innerStep
    (H : FiniteHypergraph V E) {M S : Finset E} {A : Finset V}
    (hnot : ¬∀ v ∈ A, H.UncoveredBy M v) :
    ¬∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v := by
  exact fun hstep ↦ hnot (H.jointUncovered_of_innerStep hstep)

/-- Under positive uniformity, joint uncoveredness of `A ∪ support e` is
equivalent to joint uncoveredness of `A` together with liveness of `e`. -/
lemma jointUncovered_union_support_iff
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (A : Finset V) (e : E) :
    (∀ v ∈ A ∪ H.support e, H.UncoveredBy M v) ↔
      (∀ v ∈ A, H.UncoveredBy M v) ∧ H.InnerLive M e := by
  rw [H.innerLive_iff_uncovered_of_uniform hk hunif M e]
  constructor
  · intro hall
    exact ⟨fun v hv ↦ hall v (mem_union_left _ hv),
      fun v hv ↦ hall v (mem_union_right _ hv)⟩
  · rintro ⟨hA, he⟩ v hv
    rcases mem_union.mp hv with hvA | hve
    · exact hA v hvA
    · exact he v hve

/-- Indicator form of `jointUncovered_union_support_iff`. -/
lemma jointUncovered_indicator_mul_innerLive_indicator
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (A : Finset V) (e : E) :
    (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        (if H.InnerLive M e then 1 else 0) =
      if ∀ v ∈ A ∪ H.support e, H.UncoveredBy M v then 1 else 0 := by
  have hiff := H.jointUncovered_union_support_iff hk hunif M A e
  by_cases hA : ∀ v ∈ A, H.UncoveredBy M v
  · by_cases he : H.InnerLive M e
    · have hU : ∀ v ∈ A ∪ H.support e, H.UncoveredBy M v :=
        hiff.mpr ⟨hA, he⟩
      rw [if_pos hA, if_pos he, if_pos hU]
      norm_num
    · have hnU : ¬∀ v ∈ A ∪ H.support e, H.UncoveredBy M v :=
        fun hU ↦ he (hiff.mp hU).2
      rw [if_pos hA, if_neg he, if_neg hnU]
      norm_num
  · have hnU : ¬∀ v ∈ A ∪ H.support e, H.UncoveredBy M v :=
      fun hU ↦ hA (hiff.mp hU).1
    rw [if_neg hA, if_neg hnU]
    norm_num

/-- Averaging the preceding pointwise identity over `r` independent inner
rounds gives exactly the joint uncovered mass on the enlarged vertex set. -/
theorem sum_productMass_mul_jointUncovered_mul_innerLive
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (e : E) :
    (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (if ∀ v ∈ A,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0) *
        (if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
          then 1 else 0)) =
      H.innerJointUncoveredMass w r M (A ∪ H.support e) := by
  unfold innerJointUncoveredMass
  apply sum_congr rfl
  intro X _
  calc
    (FiniteProduct.productMass w X *
        (if ∀ v ∈ A,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0)) *
        (if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
          then 1 else 0) =
        FiniteProduct.productMass w X *
          ((if ∀ v ∈ A,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0) *
          (if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
            then 1 else 0)) := by ring
    _ = FiniteProduct.productMass w X *
        (if ∀ v ∈ A ∪ H.support e,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0) := by
      rw [H.jointUncovered_indicator_mul_innerLive_indicator hk hunif]

/-- Sum the joint-live trajectory identity over any finite edge family. -/
theorem sum_productMass_mul_jointUncovered_mul_sum_innerLive
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (B : Finset E) :
    (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (if ∀ v ∈ A,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0) *
        ∑ e ∈ B,
          if H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
            then 1 else 0) =
      ∑ e ∈ B,
        H.innerJointUncoveredMass w r M (A ∪ H.support e) := by
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simpa [mul_assoc] using
    H.sum_productMass_mul_jointUncovered_mul_innerLive
      hk hunif w r M A e

/-- Family form of `jointUncovered_union_support_iff`: under positive
uniformity, all edges of `F` are live exactly when every vertex in the union
of their supports is still uncovered. -/
lemma jointUncovered_union_biUnion_support_iff
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (A : Finset V) (F : Finset E) :
    (∀ v ∈ A ∪ F.biUnion H.support, H.UncoveredBy M v) ↔
      (∀ v ∈ A, H.UncoveredBy M v) ∧
        ∀ e ∈ F, H.InnerLive M e := by
  constructor
  · intro hall
    refine ⟨fun v hv ↦ hall v (mem_union_left _ hv), ?_⟩
    intro e heF
    rw [H.innerLive_iff_uncovered_of_uniform hk hunif M e]
    intro v hve
    exact hall v (mem_union_right _ (mem_biUnion.mpr ⟨e, heF, hve⟩))
  · rintro ⟨hA, hlive⟩ v hv
    rcases mem_union.mp hv with hvA | hvF
    · exact hA v hvA
    · obtain ⟨e, heF, hve⟩ := mem_biUnion.mp hvF
      exact (H.innerLive_iff_uncovered_of_uniform hk hunif M e).mp
        (hlive e heF) v hve

/-- Indicator form of the family live/uncovered identity. -/
lemma jointUncovered_indicator_mul_familyLive_indicator
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (A : Finset V) (F : Finset E) :
    (if ∀ v ∈ A, H.UncoveredBy M v then (1 : ℝ) else 0) *
        (if ∀ e ∈ F, H.InnerLive M e then 1 else 0) =
      if ∀ v ∈ A ∪ F.biUnion H.support, H.UncoveredBy M v then 1 else 0 := by
  have hiff := H.jointUncovered_union_biUnion_support_iff hk hunif M A F
  by_cases hA : ∀ v ∈ A, H.UncoveredBy M v
  · by_cases hF : ∀ e ∈ F, H.InnerLive M e
    · have hU : ∀ v ∈ A ∪ F.biUnion H.support, H.UncoveredBy M v :=
        hiff.mpr ⟨hA, hF⟩
      rw [if_pos hA, if_pos hF, if_pos hU]
      norm_num
    · have hnU : ¬∀ v ∈ A ∪ F.biUnion H.support,
          H.UncoveredBy M v := fun hU ↦ hF (hiff.mp hU).2
      rw [if_pos hA, if_neg hF, if_neg hnU]
      norm_num
  · have hnU : ¬∀ v ∈ A ∪ F.biUnion H.support,
        H.UncoveredBy M v := fun hU ↦ hA (hiff.mp hU).1
    rw [if_neg hA, if_neg hnU]
    norm_num

/-- Averaged family version of the joint-live trajectory identity.  This is
the exact bridge needed when an all-order binomial moment is expanded as a
sum over finite edge families. -/
theorem sum_productMass_mul_jointUncovered_mul_familyLive
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E) :
    (∑ X : Fin r → Finset E, FiniteProduct.productMass w X *
        (if ∀ v ∈ A,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0) *
        (if ∀ e ∈ F,
            H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
          then 1 else 0)) =
      H.innerJointUncoveredMass w r M
        (A ∪ F.biUnion H.support) := by
  unfold innerJointUncoveredMass
  apply sum_congr rfl
  intro X _
  calc
    (FiniteProduct.productMass w X *
        (if ∀ v ∈ A,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0)) *
        (if ∀ e ∈ F,
            H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
          then 1 else 0) =
        FiniteProduct.productMass w X *
          ((if ∀ v ∈ A,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0) *
          (if ∀ e ∈ F,
              H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
            then 1 else 0)) := by ring
    _ = FiniteProduct.productMass w X *
        (if ∀ v ∈ A ∪ F.biUnion H.support,
            H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
          then 1 else 0) := by
      rw [H.jointUncovered_indicator_mul_familyLive_indicator hk hunif]

/-- Averaged fixed-family quantitative estimate.  After expanding a
binomial moment into matching edge families, each family contribution is
squeezed between a uniform conflict-avoidance factor times the enlarged
joint-survival mass and its raw sampling mass times that same survival
mass. -/
theorem sum_productMass_mul_jointUncovered_mul_innerNewAcceptanceFamilyMass_const_mem_Icc
    {H : FiniteHypergraph V E} {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    (hF : H.IsMatching F) :
    (∑ X : Fin r → Finset E,
        FiniteProduct.productMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) X *
          (if ∀ v ∈ A,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0) *
          H.innerNewAcceptanceFamilyMass
            ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F) ∈
      Set.Icc
        (p ^ F.card * (1 - p) ^ (F.card * k * D) *
          H.innerJointUncoveredMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
            (A ∪ F.biUnion H.support))
        (p ^ F.card *
          H.innerJointUncoveredMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
            (A ∪ F.biUnion H.support)) := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let lower : ℝ := p ^ F.card * (1 - p) ^ (F.card * k * D)
  let upper : ℝ := p ^ F.card
  let liveIndicator : Finset E → ℝ := fun N ↦
    if ∀ e ∈ F, H.InnerLive N e then 1 else 0
  let uncoveredIndicator : (Fin r → Finset E) → ℝ := fun X ↦
    if ∀ v ∈ A, H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
      then 1 else 0
  have hw₀ (S : Finset E) : 0 ≤ w S := by
    exact FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hprod₀ (X : Fin r → Finset E) :
      0 ≤ FiniteProduct.productMass w X := by
    unfold FiniteProduct.productMass
    exact prod_nonneg fun i _ ↦ hw₀ (X i)
  have hind₀ (X : Fin r → Finset E) : 0 ≤ uncoveredIndicator X := by
    dsimp [uncoveredIndicator]
    split_ifs <;> norm_num
  have hfamily (X : Fin r → Finset E) :
      H.innerNewAcceptanceFamilyMass
          ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F ∈
        Set.Icc
          (lower * liveIndicator ((List.ofFn X).foldl H.innerStep M))
          (upper * liveIndicator ((List.ofFn X).foldl H.innerStep M)) := by
    simpa [lower, upper, liveIndicator] using
      H.innerNewAcceptanceFamilyMass_const_indicator_mem_Icc
        hunif hdeg ((List.ofFn X).foldl H.innerStep M) F hp₀ hp₁ hF
  have htraj :
      (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * uncoveredIndicator X *
            liveIndicator ((List.ofFn X).foldl H.innerStep M)) =
        H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support) := by
    simpa [w, uncoveredIndicator, liveIndicator] using
      H.sum_productMass_mul_jointUncovered_mul_familyLive
        hk hunif w r M A F
  change
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X * uncoveredIndicator X *
        H.innerNewAcceptanceFamilyMass
          ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F) ∈
      Set.Icc
        (lower * H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support))
        (upper * H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support))
  constructor
  · calc
      lower * H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support) =
          ∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * uncoveredIndicator X *
              (lower * liveIndicator
                ((List.ofFn X).foldl H.innerStep M)) := by
        rw [← htraj, Finset.mul_sum]
        apply sum_congr rfl
        intro X _
        ring
      _ ≤ ∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * uncoveredIndicator X *
            H.innerNewAcceptanceFamilyMass
              ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F := by
        apply sum_le_sum
        intro X _
        exact mul_le_mul_of_nonneg_left (hfamily X).1
          (mul_nonneg (hprod₀ X) (hind₀ X))
  · calc
      (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * uncoveredIndicator X *
            H.innerNewAcceptanceFamilyMass
              ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F) ≤
          ∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * uncoveredIndicator X *
              (upper * liveIndicator
                ((List.ofFn X).foldl H.innerStep M)) := by
        apply sum_le_sum
        intro X _
        exact mul_le_mul_of_nonneg_left (hfamily X).2
          (mul_nonneg (hprod₀ X) (hind₀ X))
      _ = upper * H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support) := by
        rw [← htraj, Finset.mul_sum]
        apply sum_congr rfl
        intro X _
        ring

end FiniteHypergraph

end


end Erdos76

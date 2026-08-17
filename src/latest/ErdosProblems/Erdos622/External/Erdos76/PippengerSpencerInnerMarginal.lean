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
import ErdosProblems.Erdos622.External.Erdos76.PippengerSpencerInner
import ErdosProblems.Erdos622.External.Erdos76.PippengerSpencer

/-!
# Marginal recursion for the fixed-length inner matching generator

This file separates the finite-product probability calculation from the
geometric survival estimate in the Pippenger--Spencer inner generator.  The
main recursion bounds the acceptance mass of an edge by its one-round
acceptance probability times the expected number of rounds for which it is
still live.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- An edge is live relative to a partial matching when it is new and
disjoint from every edge already present. -/
def InnerLive (H : FiniteHypergraph V E) (M : Finset E) (e : E) : Prop :=
  e ∈ H.liveSample M univ

lemma mem_liveSample_iff (H : FiniteHypergraph V E) (M S : Finset E) (e : E) :
    e ∈ H.liveSample M S ↔ e ∈ S ∧ H.InnerLive M e := by
  simp [liveSample, InnerLive]

lemma not_innerLive_of_mem (H : FiniteHypergraph V E) {M : Finset E} {e : E}
    (he : e ∈ M) : ¬H.InnerLive M e := by
  simp [InnerLive, liveSample, he]

/-- If `e` was isolated in the full new sample and is live relative to the
old matching, it remains isolated after the live-edge filter. -/
lemma mem_isolatedSample_liveSample_of_mem_isolatedSample
    (H : FiniteHypergraph V E) {M S : Finset E} {e : E}
    (hlive : H.InnerLive M e) (he : e ∈ H.isolatedSample S) :
    e ∈ H.isolatedSample (H.liveSample M S) := by
  have heS : e ∈ S := H.isolatedSample_subset S he
  rw [isolatedSample, mem_filter] at he ⊢
  refine ⟨(H.mem_liveSample_iff M S e).2
    ⟨heS, hlive⟩, ?_⟩
  intro f hf hef
  exact he.2 f (H.liveSample_subset_sample M S hf) hef

/-- One altered Bernoulli sample succeeds at least as often after the live
filter as it does in isolation, provided the distinguished edge is live. -/
lemma trialAcceptanceMass_le_sum_innerStep_indicator
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    {M : Finset E} {e : E} (hlive : H.InnerLive M e) :
    FiniteNibble.trialAcceptanceMass H p e ≤
      ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ H.innerStep M S then 1 else 0 := by
  unfold FiniteNibble.trialAcceptanceMass
  apply sum_le_sum
  intro S _
  have hmass : 0 ≤ FiniteNibble.bernoulliMass univ p S :=
    FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
  by_cases he : e ∈ H.isolatedSample S
  · have he' : e ∈ H.innerStep M S := by
      exact mem_union_right M
        (H.mem_isolatedSample_liveSample_of_mem_isolatedSample hlive he)
    simp [he, he']
  · by_cases hstep : e ∈ H.innerStep M S <;> simp [he, hstep, hmass]

/-- The Markov recursion for the probability that `e` belongs to the partial
matching after a prescribed number of additional rounds. -/
def innerAcceptanceKernel (H : FiniteHypergraph V E)
    (w : Finset E → ℝ) : ℕ → Finset E → E → ℝ
  | 0, M, e => if e ∈ M then 1 else 0
  | n + 1, M, e =>
      ∑ S : Finset E, w S * H.innerAcceptanceKernel w n (H.innerStep M S) e

/-- Expected number of the next `n` rounds which begin with `e` live. -/
def innerLiveTimeKernel (H : FiniteHypergraph V E)
    (w : Finset E → ℝ) : ℕ → Finset E → E → ℝ
  | 0, _, _ => 0
  | n + 1, M, e =>
      (if H.InnerLive M e then 1 else 0) +
        ∑ S : Finset E, w S * H.innerLiveTimeKernel w n (H.innerStep M S) e

lemma innerAcceptanceKernel_nonneg
    (H : FiniteHypergraph V E) {w : Finset E → ℝ}
    (hw₀ : ∀ S, 0 ≤ w S) (n : ℕ) (M : Finset E) (e : E) :
    0 ≤ H.innerAcceptanceKernel w n M e := by
  induction n generalizing M with
  | zero =>
      simp only [innerAcceptanceKernel]
      split <;> norm_num
  | succ n ih =>
      simp only [innerAcceptanceKernel]
      exact sum_nonneg fun S _ ↦ mul_nonneg (hw₀ S) (ih (H.innerStep M S))

/-- The one-step kernel gains at least the one-round acceptance mass whenever
the edge is live. -/
lemma indicator_add_trialAcceptanceMass_mul_live_le_step
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (M : Finset E) (e : E) :
    (if e ∈ M then 1 else 0) +
        FiniteNibble.trialAcceptanceMass H p e *
          (if H.InnerLive M e then 1 else 0) ≤
      ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
        if e ∈ H.innerStep M S then 1 else 0 := by
  by_cases heM : e ∈ M
  · have hnotlive := H.not_innerLive_of_mem heM
    simp only [heM, hnotlive, if_true, if_false, mul_zero, add_zero]
    have hsum : ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S = 1 := by
      simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) p
    calc
      1 = ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S := hsum.symm
      _ = ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S *
          if e ∈ H.innerStep M S then 1 else 0 := by
        apply sum_congr rfl
        intro S _
        simp [H.subset_innerStep M S heM]
      _ ≤ _ := le_rfl
  · by_cases hlive : H.InnerLive M e
    · simpa [heM, hlive] using
        H.trialAcceptanceMass_le_sum_innerStep_indicator hp₀ hp₁ hlive
    · simp only [heM, hlive, if_false, mul_zero, add_zero]
      exact sum_nonneg fun S _ ↦ mul_nonneg
        (FiniteNibble.bernoulliMass_nonneg (subset_univ S)
          (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x))
        (by split <;> norm_num)

/-- Abstract survival-invariant form of the fixed-length marginal estimate.
If `q` is a lower bound for one-round acceptance of `e`, then acceptance
after `n` rounds is at least the initial indicator plus `q` times the expected
number of rounds which begin with `e` live. -/
theorem indicator_add_mul_innerLiveTimeKernel_le_innerAcceptanceKernel
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    {q : ℝ} {e : E}
    (hq : q ≤ FiniteNibble.trialAcceptanceMass H p e)
    (n : ℕ) (M : Finset E) :
    (if e ∈ M then 1 else 0) + q * H.innerLiveTimeKernel
        (FiniteNibble.bernoulliMass univ p) n M e ≤
      H.innerAcceptanceKernel (FiniteNibble.bernoulliMass univ p) n M e := by
  induction n generalizing M with
  | zero => simp [innerAcceptanceKernel, innerLiveTimeKernel]
  | succ n ih =>
      let w : Finset E → ℝ := FiniteNibble.bernoulliMass univ p
      have hw₀ (S : Finset E) : 0 ≤ w S :=
        FiniteNibble.bernoulliMass_nonneg (subset_univ S)
          (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
      have hstep :
          (if e ∈ M then 1 else 0) + q *
              (if H.InnerLive M e then 1 else 0) ≤
            ∑ S : Finset E, w S *
              if e ∈ H.innerStep M S then 1 else 0 := by
        calc
          _ ≤ (if e ∈ M then 1 else 0) +
                FiniteNibble.trialAcceptanceMass H p e *
                  (if H.InnerLive M e then 1 else 0) := by
              gcongr
          _ ≤ _ := H.indicator_add_trialAcceptanceMass_mul_live_le_step hp₀ hp₁ M e
      simp only [innerAcceptanceKernel, innerLiveTimeKernel]
      calc
        (if e ∈ M then 1 else 0) +
              q * ((if H.InnerLive M e then 1 else 0) +
                ∑ S, w S * H.innerLiveTimeKernel w n (H.innerStep M S) e) =
            ((if e ∈ M then 1 else 0) +
              q * (if H.InnerLive M e then 1 else 0)) +
                ∑ S, w S *
                  (q * H.innerLiveTimeKernel w n (H.innerStep M S) e) := by
              rw [mul_add, mul_sum]
              ring_nf
        _ ≤ (∑ S, w S * if e ∈ H.innerStep M S then 1 else 0) +
                ∑ S, w S *
                  (q * H.innerLiveTimeKernel w n (H.innerStep M S) e) :=
              add_le_add hstep le_rfl
        _ = ∑ S, w S *
              ((if e ∈ H.innerStep M S then 1 else 0) +
                q * H.innerLiveTimeKernel w n (H.innerStep M S) e) := by
              rw [← sum_add_distrib]
              apply sum_congr rfl
              intro S _
              ring
        _ ≤ ∑ S, w S *
              H.innerAcceptanceKernel w n (H.innerStep M S) e := by
              apply sum_le_sum
              intro S _
              exact mul_le_mul_of_nonneg_left (ih (H.innerStep M S)) (hw₀ S)

/-- `List.ofFn` sends a tuple extended at the right to list append. -/
lemma list_ofFn_snoc {A : Type*} : ∀ {n : ℕ} (X : Fin n → A) (a : A),
    List.ofFn (Fin.snoc X a : Fin (n + 1) → A) = List.ofFn X ++ [a]
  | 0, X, a => by
      change [(Fin.snoc X a : Fin 1 → A) (Fin.last 0)] = [a]
      rw [Fin.snoc_last]
  | n + 1, X, a => by
      conv_lhs => rw [List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ]
      rw [List.cons_append]
      congr 1
      have htail : (fun i : Fin (n + 1) ↦
            (Fin.snoc X a : Fin (n + 2) → A) i.succ) =
          (Fin.snoc (fun i : Fin n ↦ X i.succ) a : Fin (n + 1) → A) := by
        funext i
        induction i using Fin.lastCases with
        | last => simp
        | cast i =>
            rw [show i.castSucc.succ = (i.succ).castSucc by ext; simp,
              Fin.snoc_castSucc, Fin.snoc_castSucc]
      rw [htail, list_ofFn_snoc]

/-- The recursive acceptance kernel is exactly the explicit product
expectation of the fold over a tuple of samples. -/
lemma innerAcceptanceKernel_eq_sum_foldl
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (n : ℕ) (M : Finset E) (e : E) :
    H.innerAcceptanceKernel w n M e =
      ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
        if e ∈ (List.ofFn X).foldl H.innerStep M then 1 else 0 := by
  induction n generalizing M with
  | zero => simp [innerAcceptanceKernel, FiniteProduct.productMass]
  | succ n ih =>
      simp only [innerAcceptanceKernel]
      simp_rw [ih]
      calc
        (∑ S : Finset E, w S *
            ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
              if e ∈ (List.ofFn X).foldl H.innerStep (H.innerStep M S)
                then 1 else 0) =
            ∑ z : Finset E × (Fin n → Finset E),
              FiniteProduct.productMass w
                  ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ Finset E)) z) *
                if e ∈ (List.ofFn
                    ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ Finset E)) z)).foldl
                      H.innerStep M then 1 else 0 := by
          simp only [Fintype.sum_prod_type, Fin.consEquiv_apply,
            FiniteProduct.productMass, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.cons_succ, List.ofFn_succ, List.foldl_cons, mul_sum]
          apply sum_congr rfl
          intro S _
          apply sum_congr rfl
          intro X _
          ring
        _ = ∑ X : Fin (n + 1) → Finset E,
              FiniteProduct.productMass w X *
                if e ∈ (List.ofFn X).foldl H.innerStep M then 1 else 0 :=
          (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Finset E)).sum_comp
            (fun X ↦ FiniteProduct.productMass w X *
              if e ∈ (List.ofFn X).foldl H.innerStep M then 1 else 0)

/-- Up to an admissible time `r`, `innerState` is the left fold over the
first `r` samples. -/
lemma innerState_eq_foldl_prefix
    (H : FiniteHypergraph V E) {L : ℕ} (X : Fin L → Finset E) :
    ∀ {r : ℕ} (hr : r ≤ L),
      H.innerState X r =
        (List.ofFn (fun i : Fin r ↦ X (Fin.castLE hr i))).foldl H.innerStep ∅
  | 0, _ => by simp [innerState]
  | r + 1, hr => by
      have hrL : r < L := Nat.lt_of_succ_le hr
      have hrle : r ≤ L := Nat.le_of_lt hrL
      rw [innerState, dif_pos hrL, innerState_eq_foldl_prefix H X hrle]
      have hprefix : (fun i : Fin (r + 1) ↦ X (Fin.castLE hr i)) =
          (Fin.snoc (fun i : Fin r ↦ X (Fin.castLE hrle i))
            (X ⟨r, hrL⟩) : Fin (r + 1) → Finset E) := by
        funext i
        induction i using Fin.lastCases with
        | last => simp [Fin.castLE]
        | cast i => simp [Fin.castLE]
      rw [hprefix, list_ofFn_snoc, List.foldl_append]
      simp

/-- The public fixed-length generator is the corresponding fold over all
coordinates. -/
lemma innerMatching_eq_foldl
    (H : FiniteHypergraph V E) {L : ℕ} (X : Fin L → Finset E) :
    H.innerMatching X = (List.ofFn X).foldl H.innerStep ∅ := by
  rw [innerMatching, innerState_eq_foldl_prefix H X (le_refl L)]
  congr 2

/-- At the empty initial matching the recursive kernel is definitionally
the public finite-product acceptance mass. -/
lemma innerAcceptanceKernel_empty_eq_innerAcceptanceMass
    (H : FiniteHypergraph V E) (L : ℕ) (p : E → ℝ) (e : E) :
    H.innerAcceptanceKernel (FiniteNibble.bernoulliMass univ p) L ∅ e =
      H.innerAcceptanceMass L p e := by
  rw [innerAcceptanceKernel_eq_sum_foldl]
  unfold innerAcceptanceMass
  apply sum_congr rfl
  intro X _
  rw [innerMatching_eq_foldl]

/-- The accumulated expected live time, multiplied by any one-round
acceptance lower bound, is a lower bound for the public inner marginal. -/
theorem mul_innerLiveTimeKernel_empty_le_innerAcceptanceMass
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    {q : ℝ} {e : E}
    (hq : q ≤ FiniteNibble.trialAcceptanceMass H p e) (L : ℕ) :
    q * H.innerLiveTimeKernel (FiniteNibble.bernoulliMass univ p) L ∅ e ≤
      H.innerAcceptanceMass L p e := by
  rw [← H.innerAcceptanceKernel_empty_eq_innerAcceptanceMass L p e]
  simpa using H.indicator_add_mul_innerLiveTimeKernel_le_innerAcceptanceKernel
    hp₀ hp₁ hq L ∅

/-- A convenient interface for a separate survival calculation: it suffices
to lower-bound the expected live time by `ell`. -/
theorem mul_le_innerAcceptanceMass_of_liveTimeKernel_ge
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    {q ell : ℝ} {e : E} (hq₀ : 0 ≤ q)
    (hq : q ≤ FiniteNibble.trialAcceptanceMass H p e) (L : ℕ)
    (hlive : ell ≤
      H.innerLiveTimeKernel (FiniteNibble.bernoulliMass univ p) L ∅ e) :
    q * ell ≤ H.innerAcceptanceMass L p e := by
  calc
    q * ell ≤ q * H.innerLiveTimeKernel
        (FiniteNibble.bernoulliMass univ p) L ∅ e :=
      mul_le_mul_of_nonneg_left hlive hq₀
    _ ≤ H.innerAcceptanceMass L p e :=
      H.mul_innerLiveTimeKernel_empty_le_innerAcceptanceMass hp₀ hp₁ hq L

/-- Constant-probability form, using the elementary local union bound for
one alteration round. -/
theorem sub_mul_innerLiveTimeKernel_empty_le_innerAcceptanceMass_const
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (L : ℕ) (e : E) :
    (p - ((k * D : ℕ) : ℝ) * p ^ 2) *
        H.innerLiveTimeKernel
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) L ∅ e ≤
      H.innerAcceptanceMass L (fun _ ↦ p) e := by
  exact H.mul_innerLiveTimeKernel_empty_le_innerAcceptanceMass
    (fun _ ↦ hp₀) (fun _ ↦ hp₁)
    (FiniteNibble.trialAcceptanceMass_const_ge hunif hdeg hp₀ hp₁ e) L

/-- Constant-probability survival interface.  A quantitative proof only
needs to supply a lower bound for the accumulated live time. -/
theorem mul_le_innerAcceptanceMass_const_of_liveTimeKernel_ge
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p ell : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ p - ((k * D : ℕ) : ℝ) * p ^ 2)
    (L : ℕ) {e : E}
    (hlive : ell ≤ H.innerLiveTimeKernel
      (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) L ∅ e) :
    (p - ((k * D : ℕ) : ℝ) * p ^ 2) * ell ≤
      H.innerAcceptanceMass L (fun _ ↦ p) e := by
  exact H.mul_le_innerAcceptanceMass_of_liveTimeKernel_ge
    (fun _ ↦ hp₀) (fun _ ↦ hp₁) hq₀
    (FiniteNibble.trialAcceptanceMass_const_ge hunif hdeg hp₀ hp₁ e)
    L hlive

/-- The pathwise number of rounds which start with `e` live.  This is the
explicit random variable represented recursively by `innerLiveTimeKernel`. -/
def innerLiveCount (H : FiniteHypergraph V E) (e : E) :
    List (Finset E) → Finset E → ℝ
  | [], _ => 0
  | S :: samples, M =>
      (if H.InnerLive M e then 1 else 0) +
        H.innerLiveCount e samples (H.innerStep M S)

/-- A homogeneous finite product of normalized masses is normalized. -/
lemma sum_productMass_eq_one (w : Finset E → ℝ)
    (hw : ∑ S, w S = 1) (n : ℕ) :
    ∑ X : Fin n → Finset E, FiniteProduct.productMass w X = 1 := by
  simpa [FiniteProduct.productMass, FiniteProduct.mass] using
    (FiniteProduct.sum_mass
      (I := Fin n) (Omega := fun _ ↦ Finset E) (fun _ S ↦ w S)
      (fun _ ↦ hw))

/-- The live-time kernel is the ordinary finite-product expectation of the
pathwise live-round count. -/
lemma innerLiveTimeKernel_eq_sum_innerLiveCount
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (hw : ∑ S, w S = 1) (n : ℕ) (M : Finset E) (e : E) :
    H.innerLiveTimeKernel w n M e =
      ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
        H.innerLiveCount e (List.ofFn X) M := by
  induction n generalizing M with
  | zero => simp [innerLiveTimeKernel, innerLiveCount, FiniteProduct.productMass]
  | succ n ih =>
      let I : ℝ := if H.InnerLive M e then 1 else 0
      have hprod : ∑ X : Fin n → Finset E,
          FiniteProduct.productMass w X = 1 := sum_productMass_eq_one w hw n
      simp only [innerLiveTimeKernel]
      simp_rw [ih]
      calc
        I + ∑ S : Finset E, w S *
              ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
                H.innerLiveCount e (List.ofFn X) (H.innerStep M S) =
            ∑ S : Finset E, w S *
              (I + ∑ X : Fin n → Finset E,
                FiniteProduct.productMass w X *
                  H.innerLiveCount e (List.ofFn X) (H.innerStep M S)) := by
          simp_rw [mul_add]
          rw [sum_add_distrib, ← sum_mul, hw, one_mul]
        _ = ∑ S : Finset E, w S *
              ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
                (I + H.innerLiveCount e (List.ofFn X) (H.innerStep M S)) := by
          apply sum_congr rfl
          intro S _
          congr 1
          calc
            I + ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
                  H.innerLiveCount e (List.ofFn X) (H.innerStep M S) =
                I * (∑ X : Fin n → Finset E,
                  FiniteProduct.productMass w X) +
                  ∑ X : Fin n → Finset E, FiniteProduct.productMass w X *
                    H.innerLiveCount e (List.ofFn X) (H.innerStep M S) := by
              rw [hprod, mul_one]
            _ = _ := by
              rw [mul_sum, ← sum_add_distrib]
              apply sum_congr rfl
              intro X _
              ring
        _ = ∑ z : Finset E × (Fin n → Finset E),
              FiniteProduct.productMass w
                  ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ Finset E)) z) *
                H.innerLiveCount e (List.ofFn
                  ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ Finset E)) z)) M := by
          simp only [Fintype.sum_prod_type, Fin.consEquiv_apply,
            FiniteProduct.productMass, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.cons_succ, List.ofFn_succ, innerLiveCount, mul_sum, I]
          apply sum_congr rfl
          intro S _
          apply sum_congr rfl
          intro X _
          ring
        _ = ∑ X : Fin (n + 1) → Finset E,
              FiniteProduct.productMass w X *
                H.innerLiveCount e (List.ofFn X) M :=
          (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Finset E)).sum_comp
            (fun X ↦ FiniteProduct.productMass w X *
              H.innerLiveCount e (List.ofFn X) M)

/-- Bernoulli specialization of the explicit live-time expectation. -/
lemma innerLiveTimeKernel_bernoulli_eq_sum_innerLiveCount
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (n : ℕ) (M : Finset E) (e : E) :
    H.innerLiveTimeKernel (FiniteNibble.bernoulliMass univ p) n M e =
      ∑ X : Fin n → Finset E,
        FiniteProduct.productMass (FiniteNibble.bernoulliMass univ p) X *
          H.innerLiveCount e (List.ofFn X) M := by
  exact H.innerLiveTimeKernel_eq_sum_innerLiveCount _
    (by simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) p)
    n M e

end FiniteHypergraph

end

end Erdos76

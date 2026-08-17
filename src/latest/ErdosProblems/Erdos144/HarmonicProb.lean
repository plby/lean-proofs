/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos697.Erdos697Bernoulli

/-!
# Finite harmonic Bernoulli probability

This file packages the finite product measure in which an integer `n` is
selected independently with probability `1 / n`.  It contains only finite
sums.  In particular, no measure-theoretic completion or infinite product is
used here.

The event lemmas are deliberately stated for arbitrary predicates.  They are
the bookkeeping tools used by the random-set part of the proof of Erdős 144:
complement identities, union bounds, a finite Markov inequality, and a
Chernoff bound for the cardinality of the selected set.  The last section gives
elementary upper and lower estimates for reciprocal sums on `Finset.Ioc`.
-/

open scoped BigOperators

namespace Erdos144.HarmonicProb

noncomputable section

/-- The harmonic inclusion parameter. -/
def param (n : ℕ) : ℝ := 1 / (n : ℝ)

/-- Product weight of `T` in the harmonic Bernoulli model on `s`. -/
def weight (s T : Finset ℕ) : ℝ :=
  Erdos697.Bernoulli.weight s param T

/-- Probability of a predicate on subsets in the harmonic Bernoulli model. -/
def prob (s : Finset ℕ) (P : Finset ℕ → Prop) [DecidablePred P] : ℝ :=
  ∑ T ∈ s.powerset.filter P, weight s T

lemma param_nonneg (n : ℕ) : 0 ≤ param n := by
  simp [param]

lemma param_le_one {n : ℕ} (hn : 1 ≤ n) : param n ≤ 1 := by
  rw [param]
  exact (div_le_one₀ (by exact_mod_cast (Nat.zero_lt_of_lt hn))).2 (by exact_mod_cast hn)

lemma weight_nonneg {s T : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) :
    0 ≤ weight s T := by
  unfold weight Erdos697.Bernoulli.weight
  exact mul_nonneg
    (Finset.prod_nonneg fun n _ => param_nonneg n)
    (Finset.prod_nonneg fun n hn => by
      have hns : n ∈ s := (Finset.mem_sdiff.mp hn).1
      linarith [param_le_one (hs n hns)])

lemma prob_nonneg (s : Finset ℕ) (P : Finset ℕ → Prop) [DecidablePred P]
    (hs : ∀ n ∈ s, 1 ≤ n) : 0 ≤ prob s P := by
  unfold prob
  exact Finset.sum_nonneg fun T hT =>
    weight_nonneg hs

lemma prob_true (s : Finset ℕ) : prob s (fun _ => True) = 1 := by
  simp [prob, weight, Erdos697.Bernoulli.sum_weight_powerset]

/-- An event and its complement have total probability one. -/
lemma prob_add_prob_not (s : Finset ℕ) (P : Finset ℕ → Prop)
    [DecidablePred P] :
    prob s P + prob s (fun T => ¬ P T) = 1 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := s.powerset) (p := P) (f := fun T => weight s T)
  simpa [prob, weight] using
    hsplit.trans (Erdos697.Bernoulli.sum_weight_powerset s param)

lemma prob_not (s : Finset ℕ) (P : Finset ℕ → Prop)
    [DecidablePred P] :
    prob s (fun T => ¬ P T) = 1 - prob s P := by
  linarith [prob_add_prob_not s P]

lemma prob_le_one (s : Finset ℕ) (P : Finset ℕ → Prop)
    [DecidablePred P] (hs : ∀ n ∈ s, 1 ≤ n) : prob s P ≤ 1 := by
  have hnonneg : 0 ≤ prob s (fun T => ¬ P T) := prob_nonneg s _ hs
  linarith [prob_add_prob_not s P]

/-- Monotonicity with respect to inclusion of events. -/
lemma prob_mono (s : Finset ℕ) (P Q : Finset ℕ → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hs : ∀ n ∈ s, 1 ≤ n) (hPQ : ∀ T, P T → Q T) :
    prob s P ≤ prob s Q := by
  unfold prob
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    rcases Finset.mem_filter.mp hT with ⟨hTs, hPT⟩
    exact Finset.mem_filter.mpr ⟨hTs, hPQ T hPT⟩
  · intro T hT _
    exact weight_nonneg hs

/-- Two-event union bound. -/
lemma prob_or_le (s : Finset ℕ) (P Q : Finset ℕ → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hs : ∀ n ∈ s, 1 ≤ n) :
    prob s (fun T => P T ∨ Q T) ≤ prob s P + prob s Q := by
  classical
  let pset := s.powerset.filter P
  let qset := s.powerset.filter Q
  have hunion :
      s.powerset.filter (fun T => P T ∨ Q T) = pset ∪ qset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, pset, qset]
    aesop
  have hinter : 0 ≤ ∑ T ∈ pset ∩ qset, weight s T := by
    apply Finset.sum_nonneg
    intro T _
    exact weight_nonneg hs
  have hsum := Finset.sum_union_inter
    (s₁ := pset) (s₂ := qset) (f := fun T => weight s T)
  unfold prob
  rw [hunion]
  dsimp [pset, qset] at hsum ⊢
  linarith

/-- Union bound for a finite family of explicitly represented events. -/
lemma sum_biUnion_weight_le {κ : Type*} [DecidableEq κ]
    (s : Finset ℕ) (J : Finset κ) (E : κ → Finset (Finset ℕ))
    (hs : ∀ n ∈ s, 1 ≤ n) :
    (∑ T ∈ J.biUnion E, weight s T) ≤
      ∑ j ∈ J, ∑ T ∈ E j, weight s T := by
  classical
  refine Finset.induction_on J ?_ ?_
  · simp
  · intro j J hj ih
    have hunion_le :
        (∑ T ∈ E j ∪ J.biUnion E, weight s T) ≤
          (∑ T ∈ E j, weight s T) + ∑ T ∈ J.biUnion E, weight s T := by
      have hsum := Finset.sum_union_inter
        (s₁ := E j) (s₂ := J.biUnion E) (f := fun T => weight s T)
      have hinter : 0 ≤ ∑ T ∈ E j ∩ J.biUnion E, weight s T :=
        Finset.sum_nonneg fun _ _ => weight_nonneg hs
      linarith
    calc
      (∑ T ∈ (insert j J).biUnion E, weight s T) =
          ∑ T ∈ E j ∪ J.biUnion E, weight s T := by simp
      _ ≤ (∑ T ∈ E j, weight s T) + ∑ T ∈ J.biUnion E, weight s T :=
        hunion_le
      _ ≤ (∑ T ∈ E j, weight s T) +
          ∑ k ∈ J, ∑ T ∈ E k, weight s T := by
        gcongr
      _ = ∑ k ∈ insert j J, ∑ T ∈ E k, weight s T := by
        rw [Finset.sum_insert hj]

/-- Finite union bound, in predicate form. -/
lemma prob_exists_le_sum {κ : Type*} [DecidableEq κ]
    (s : Finset ℕ) (J : Finset κ) (P : κ → Finset ℕ → Prop)
    [∀ j, DecidablePred (P j)]
    [DecidablePred (fun T => ∃ j ∈ J, P j T)]
    (hs : ∀ n ∈ s, 1 ≤ n) :
    prob s (fun T => ∃ j ∈ J, P j T) ≤ ∑ j ∈ J, prob s (P j) := by
  classical
  let E : κ → Finset (Finset ℕ) := fun j => s.powerset.filter (P j)
  have heq :
      s.powerset.filter (fun T => ∃ j ∈ J, P j T) = J.biUnion E := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, E]
    aesop
  unfold prob
  rw [heq]
  simpa [E] using sum_biUnion_weight_le s J E hs

/-! ## Finite Markov and cardinality cutoff -/

/-- Markov's inequality on the finite harmonic product space. -/
lemma prob_le_expectation_div
    (s : Finset ℕ) (F : Finset ℕ → ℝ) (c : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hF : ∀ T ∈ s.powerset, 0 ≤ F T)
    (hc : 0 < c) :
    prob s (fun T => c ≤ F T) ≤
      (∑ T ∈ s.powerset, weight s T * F T) / c := by
  have hevent :
      prob s (fun T => c ≤ F T) * c ≤
        ∑ T ∈ s.powerset.filter (fun T => c ≤ F T), weight s T * F T := by
    unfold prob
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro T hT
    have hTs := (Finset.mem_filter.mp hT).1
    exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hT).2
      (weight_nonneg hs)
  have hsubset :
      (∑ T ∈ s.powerset.filter (fun T => c ≤ F T), weight s T * F T) ≤
        ∑ T ∈ s.powerset, weight s T * F T := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro T hTs _
    exact mul_nonneg (weight_nonneg hs) (hF T hTs)
  rw [le_div_iff₀ hc]
  exact hevent.trans hsubset

/-- Chernoff upper tail for the cardinality of the harmonic random set. -/
lemma card_upper_tail_chernoff
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    {K : ℕ} {r : ℝ} (hr : 1 < r)
    (hK : r * (∑ n ∈ s, param n) ≤ (K : ℝ)) :
    prob s (fun T => K ≤ T.card) ≤
      Real.exp
        (((-(r * ((r - 1) / (2 * r)))) +
            (1 / (1 - ((r - 1) / (2 * r))) - 1)) *
          (∑ n ∈ s, param n)) := by
  simpa [prob, weight] using
    (Erdos697.Bernoulli.upper_tail_chernoff s param
      (fun n _ => param_nonneg n) (fun n hn => param_le_one (hs n hn))
      (hEW := rfl) hr hK)

/-! ## Elementary reciprocal-sum estimates -/

lemma sum_Ioc_param_nonneg (u v : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ioc u v, param n := by
  exact Finset.sum_nonneg fun n _ => param_nonneg n

/-- Each term in `(u,v]` is at least `1/v`. -/
lemma card_div_right_le_sum_Ioc_param {u v : ℕ} (hv : 1 ≤ v) :
    ((Finset.Ioc u v).card : ℝ) / (v : ℝ) ≤
      ∑ n ∈ Finset.Ioc u v, param n := by
  have hv0 : 0 < (v : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hv)
  calc
    ((Finset.Ioc u v).card : ℝ) / (v : ℝ) =
        ∑ _n ∈ Finset.Ioc u v, (1 / (v : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ n ∈ Finset.Ioc u v, param n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnv : n ≤ v := (Finset.mem_Ioc.mp hn).2
      have hn0 : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_le_of_lt (Nat.zero_le u) (Finset.mem_Ioc.mp hn).1)
      dsimp [param]
      exact one_div_le_one_div_of_le hn0 (by exact_mod_cast hnv)

/-- Each term in `(u,v]` is at most `1/(u+1)`. -/
lemma sum_Ioc_param_le_card_div_left (u v : ℕ) :
    (∑ n ∈ Finset.Ioc u v, param n) ≤
      ((Finset.Ioc u v).card : ℝ) / (u + 1 : ℕ) := by
  have hu1 : 0 < ((u + 1 : ℕ) : ℝ) := by positivity
  calc
    (∑ n ∈ Finset.Ioc u v, param n) ≤
        ∑ _n ∈ Finset.Ioc u v, (1 / ((u + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hun : u + 1 ≤ n := Nat.succ_le_iff.mpr (Finset.mem_Ioc.mp hn).1
      dsimp [param]
      exact one_div_le_one_div_of_le hu1 (by exact_mod_cast hun)
    _ = ((Finset.Ioc u v).card : ℝ) / (u + 1 : ℕ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

lemma card_Ioc_eq_sub (u v : ℕ) :
    (Finset.Ioc u v).card = v - u := by
  exact Nat.card_Ioc u v

/-- Explicit interval lower bound, with the cardinality simplified. -/
lemma sub_div_right_le_sum_Ioc_param {u v : ℕ} (hv : 1 ≤ v) :
    ((v - u : ℕ) : ℝ) / (v : ℝ) ≤
      ∑ n ∈ Finset.Ioc u v, param n := by
  simpa [card_Ioc_eq_sub] using card_div_right_le_sum_Ioc_param (u := u) hv

/-- Explicit interval upper bound, with the cardinality simplified. -/
lemma sum_Ioc_param_le_sub_div_left (u v : ℕ) :
    (∑ n ∈ Finset.Ioc u v, param n) ≤
      ((v - u : ℕ) : ℝ) / (u + 1 : ℕ) := by
  simpa [card_Ioc_eq_sub] using sum_Ioc_param_le_card_div_left u v

/-- The reciprocal mass of `(u,2u]` is at least one half. -/
lemma one_half_le_sum_Ioc_param_double {u : ℕ} (hu : 1 ≤ u) :
    (1 / 2 : ℝ) ≤ ∑ n ∈ Finset.Ioc u (2 * u), param n := by
  have h := sub_div_right_le_sum_Ioc_param (u := u) (by omega : 1 ≤ 2 * u)
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hu))
  have hsub : 2 * u - u = u := by omega
  calc
    (1 / 2 : ℝ) = (u : ℝ) / (2 * (u : ℝ)) := by
      field_simp [hu0]
    _ = ((2 * u - u : ℕ) : ℝ) / ((2 * u : ℕ) : ℝ) := by
      rw [hsub]
      push_cast
      rfl
    _ ≤ ∑ n ∈ Finset.Ioc u (2 * u), param n := h

/-- A convenient global bound for the mean cardinality on `(u,v]`. -/
lemma sum_Ioc_param_le_one_add_log (u v : ℕ) :
    (∑ n ∈ Finset.Ioc u v, param n) ≤ 1 + Real.log (v : ℝ) := by
  have hsubset : Finset.Ioc u v ⊆ Finset.Icc 1 v := by
    intro n hn
    rcases Finset.mem_Ioc.mp hn with ⟨hun, hnv⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hnv⟩
  have hsum :
      (∑ n ∈ Finset.Ioc u v, param n) ≤
        ∑ n ∈ Finset.Icc 1 v, param n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n _ _
    exact param_nonneg n
  have hharm :
      (∑ n ∈ Finset.Icc 1 v, param n) ≤ 1 + Real.log (v : ℝ) := by
    simpa [param, one_div, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast] using harmonic_le_one_add_log v
  exact hsum.trans hharm

end

end Erdos144.HarmonicProb

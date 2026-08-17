/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicProb

/-!
# First moments in the finite harmonic Bernoulli model

This file proves the exact first-moment identity for an additive statistic of
a finite harmonic Bernoulli sample.  It also packages the Markov estimate for
the sum of the selected integers that is used in the finite Maier--Tenenbaum
argument.
-/

open scoped BigOperators

namespace Erdos144.HarmonicMoments

noncomputable section

open HarmonicProb

attribute [local instance] Classical.propDecidable

private theorem weight_insert_not_selected
    (s : Finset ℕ) (p : ℕ → ℝ) {a : ℕ} (ha : a ∉ s)
    {T : Finset ℕ} (hT : T ⊆ s) :
    Erdos697.Bernoulli.weight (insert a s) p T =
      (1 - p a) * Erdos697.Bernoulli.weight s p T := by
  have haT : a ∉ T := fun haT ↦ ha (hT haT)
  simp [Erdos697.Bernoulli.weight, ha, haT, Finset.insert_sdiff_of_notMem]
  ring

private theorem weight_insert_selected
    (s : Finset ℕ) (p : ℕ → ℝ) {a : ℕ} (ha : a ∉ s)
    {T : Finset ℕ} (hT : T ⊆ s) :
    Erdos697.Bernoulli.weight (insert a s) p (insert a T) =
      p a * Erdos697.Bernoulli.weight s p T := by
  have haT : a ∉ T := fun haT ↦ ha (hT haT)
  have hdiff : insert a s \ insert a T = s \ T := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  rw [Erdos697.Bernoulli.weight, Erdos697.Bernoulli.weight, hdiff]
  simp [haT]
  ring

/-- The exact first moment of an additive statistic under arbitrary finite
Bernoulli product weights.  No bounds on `p` are needed for this algebraic
identity. -/
theorem bernoulli_expectation_sum (I : Finset ℕ) (p f : ℕ → ℝ) :
    (∑ T ∈ I.powerset, Erdos697.Bernoulli.weight I p T * ∑ i ∈ T, f i) =
      ∑ i ∈ I, p i * f i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [Erdos697.Bernoulli.weight]
  | @insert a I ha ih =>
      rw [Finset.sum_powerset_insert ha, Finset.sum_insert ha]
      have hnot : ∀ T ∈ I.powerset, a ∉ T := by
        intro T hT haT
        exact ha (Finset.mem_powerset.mp hT haT)
      calc
        (∑ T ∈ I.powerset,
              Erdos697.Bernoulli.weight (insert a I) p T * ∑ i ∈ T, f i) +
            ∑ T ∈ I.powerset,
              Erdos697.Bernoulli.weight (insert a I) p (insert a T) *
                ∑ i ∈ insert a T, f i =
            (∑ T ∈ I.powerset,
              ((1 - p a) * Erdos697.Bernoulli.weight I p T) *
                ∑ i ∈ T, f i) +
            ∑ T ∈ I.powerset,
              (p a * Erdos697.Bernoulli.weight I p T) *
                (f a + ∑ i ∈ T, f i) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro T hT
            rw [weight_insert_not_selected I p ha (Finset.mem_powerset.mp hT)]
          · apply Finset.sum_congr rfl
            intro T hT
            rw [weight_insert_selected I p ha (Finset.mem_powerset.mp hT),
              Finset.sum_insert (hnot T hT)]
        _ = p a * f a +
            ∑ T ∈ I.powerset,
              Erdos697.Bernoulli.weight I p T * ∑ i ∈ T, f i := by
          rw [← Finset.sum_add_distrib]
          calc
            ∑ T ∈ I.powerset,
                (((1 - p a) * Erdos697.Bernoulli.weight I p T) *
                    ∑ i ∈ T, f i +
                  (p a * Erdos697.Bernoulli.weight I p T) *
                    (f a + ∑ i ∈ T, f i)) =
                ∑ T ∈ I.powerset,
                  (Erdos697.Bernoulli.weight I p T *
                    (p a * f a + ∑ i ∈ T, f i)) := by
                apply Finset.sum_congr rfl
                intro T _
                ring
            _ = p a * f a *
                  (∑ T ∈ I.powerset, Erdos697.Bernoulli.weight I p T) +
                ∑ T ∈ I.powerset,
                  Erdos697.Bernoulli.weight I p T * ∑ i ∈ T, f i := by
                simp_rw [mul_add]
                rw [Finset.sum_add_distrib, Finset.mul_sum]
                apply congrArg₂ (.+.)
                · apply Finset.sum_congr rfl
                  intro T _
                  ring
                · rfl
            _ = p a * f a +
                ∑ T ∈ I.powerset,
                  Erdos697.Bernoulli.weight I p T * ∑ i ∈ T, f i := by
                rw [Erdos697.Bernoulli.sum_weight_powerset]
                ring
        _ = p a * f a + ∑ i ∈ I, p i * f i := by rw [ih]

/-- Exact first moment of an additive statistic in the harmonic model. -/
theorem expectation_sum (I : Finset ℕ) (f : ℕ → ℝ) :
    (∑ T ∈ I.powerset, weight I T * ∑ i ∈ T, f i) =
      ∑ i ∈ I, param i * f i := by
  exact bernoulli_expectation_sum I param f

/-- In the harmonic model, the expected sum of the selected integers is the
cardinality of the ambient set (provided the ambient set avoids zero). -/
theorem expectation_selected_sum (I : Finset ℕ)
    (hI : ∀ i ∈ I, 1 ≤ i) :
    (∑ T ∈ I.powerset, weight I T * ∑ i ∈ T, (i : ℝ)) =
      (I.card : ℝ) := by
  rw [expectation_sum]
  calc
    (∑ i ∈ I, param i * (i : ℝ)) = ∑ _i ∈ I, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : (i : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt (hI i hi)))
      simp [param, hi0]
    _ = (I.card : ℝ) := by simp

/-- The expected cardinality is the reciprocal mass of the ambient set. -/
theorem expectation_card (I : Finset ℕ) :
    (∑ T ∈ I.powerset, weight I T * (T.card : ℝ)) =
      ∑ i ∈ I, param i := by
  simpa using expectation_sum I (fun _ ↦ (1 : ℝ))

/-- Markov's inequality for the sum of the selected integers, with its exact
first moment substituted. -/
theorem prob_selected_sum_gt_le_card_div
    (I : Finset ℕ) (hI : ∀ i ∈ I, 1 ≤ i)
    {xi : ℝ} (hxi : 0 < xi) {D : ℕ} (hD : 0 < D) :
    prob I (fun T ↦ xi * (D : ℝ) < ∑ i ∈ T, (i : ℝ)) ≤
      (I.card : ℝ) / (xi * (D : ℝ)) := by
  let F : Finset ℕ → ℝ := fun T ↦ ∑ i ∈ T, (i : ℝ)
  have hc : 0 < xi * (D : ℝ) :=
    mul_pos hxi (by exact_mod_cast hD)
  calc
    prob I (fun T ↦ xi * (D : ℝ) < ∑ i ∈ T, (i : ℝ)) ≤
        prob I (fun T ↦ xi * (D : ℝ) ≤ F T) := by
      apply prob_mono I _ _ hI
      intro T hT
      exact hT.le
    _ ≤ (∑ T ∈ I.powerset, weight I T * F T) /
          (xi * (D : ℝ)) := by
      apply prob_le_expectation_div I F (xi * (D : ℝ)) hI
      · intro T _
        exact Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg i
      · exact hc
    _ = (I.card : ℝ) / (xi * (D : ℝ)) := by
      rw [show (∑ T ∈ I.powerset, weight I T * F T) = (I.card : ℝ) by
        simpa [F] using expectation_selected_sum I hI]

/-- A subset of the integer interval `[1,D]` has at most `D` elements, so the
preceding Markov bound is at most `1 / xi`. -/
theorem card_div_xi_mul_le_inv
    (I : Finset ℕ) {xi : ℝ} (hxi : 0 < xi) {D : ℕ} (hD : 0 < D)
    (hID : I ⊆ Finset.Icc 1 D) :
    (I.card : ℝ) / (xi * (D : ℝ)) ≤ 1 / xi := by
  have hcardNat : I.card ≤ D := by
    have h := Finset.card_le_card hID
    simpa [Nat.card_Icc] using h
  have hcard : (I.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcardNat
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_le_div_iff₀ (mul_pos hxi hDreal) hxi]
  nlinarith

/-- Markov's `1/xi` upper bound for harmonic samples from `[1,D]`. -/
theorem prob_selected_sum_gt_le_inv
    (I : Finset ℕ) {xi : ℝ} (hxi : 0 < xi) {D : ℕ} (hD : 0 < D)
    (hID : I ⊆ Finset.Icc 1 D) :
    prob I (fun T ↦ xi * (D : ℝ) < ∑ i ∈ T, (i : ℝ)) ≤
      1 / xi := by
  have hI : ∀ i ∈ I, 1 ≤ i := fun i hi ↦ (Finset.mem_Icc.mp (hID hi)).1
  exact (prob_selected_sum_gt_le_card_div I hI hxi hD).trans
    (card_div_xi_mul_le_inv I hxi hD hID)

end

end Erdos144.HarmonicMoments

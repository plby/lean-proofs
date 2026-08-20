/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperClusterMass

/-!
# Erdős Problem 446: a marked-element moment inequality

This is the finite combinatorial engine in the proof of Ford's Lemma 3.3.
If deleting a marked element `p` costs at most a factor `c p`, then the
first three moments of the additive weight `sum w` are bounded by the first
three moments of `c * w`.  The statement is deliberately independent of
primes and divisor clusters; the arithmetic specialization is made in
`FordClusterLogMoments`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

section

variable {α : Type*} [DecidableEq α]

/-- The finite `r`th moment of an additive weight over all subsets. -/
noncomputable def powersetAdditiveMoment (P : Finset α)
    (F : Finset α → ℝ) (w : α → ℝ) (r : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, F S * (∑ p ∈ S, w p) ^ r

private lemma sum_subset_as_indicator (P S : Finset α) (hSP : S ⊆ P)
    (f : α → ℝ) :
    (∑ p ∈ S, f p) = ∑ p ∈ P, if p ∈ S then f p else 0 := by
  exact Finset.sum_subset_zero_on_sdiff hSP
    (fun p hp ↦ by simp [(Finset.mem_sdiff.mp hp).2])
    (fun p hp ↦ by simp [hp])

/-- Exchange the order of summation between a subset and a marked element
of that subset. -/
lemma sum_powerset_mul_sum_eq (P : Finset α) (F : Finset α → ℝ)
    (g : Finset α → α → ℝ) :
    (∑ S ∈ P.powerset, F S * ∑ p ∈ S, g S p) =
      ∑ p ∈ P, ∑ S ∈ P.powerset,
        if p ∈ S then F S * g S p else 0 := by
  calc
    (∑ S ∈ P.powerset, F S * ∑ p ∈ S, g S p) =
        ∑ S ∈ P.powerset, ∑ p ∈ P,
          if p ∈ S then F S * g S p else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSP : S ⊆ P := Finset.mem_powerset.mp hS
      rw [sum_subset_as_indicator P S hSP (g S), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpS : p ∈ S <;> simp [hpS]
    _ = ∑ p ∈ P, ∑ S ∈ P.powerset,
          if p ∈ S then F S * g S p else 0 := by
      rw [Finset.sum_comm]

private lemma erase_injective_on_mem (p : α) :
    Set.InjOn (fun S : Finset α ↦ S.erase p) {S | p ∈ S} := by
  intro S hS T hT hEq
  rw [Set.mem_setOf_eq] at hS hT
  calc
    S = insert p (S.erase p) := (Finset.insert_erase hS).symm
    _ = insert p (T.erase p) := by simpa using congrArg (insert p) hEq
    _ = T := Finset.insert_erase hT

/-- Sum the deletion estimate for one fixed marked element. -/
lemma markedDeletion_sum_le (P : Finset α) (F : Finset α → ℝ)
    (c : α → ℝ) (hF : ∀ S, S ⊆ P → 0 ≤ F S)
    (hc : ∀ p ∈ P, 0 ≤ c p)
    (hdelete : ∀ S ⊆ P, ∀ p ∈ S, F S ≤ c p * F (S.erase p))
    {p : α} (hpP : p ∈ P) (G : Finset α → ℝ)
    (hG : ∀ T, T ⊆ P → 0 ≤ G T) :
    (∑ S ∈ P.powerset, if p ∈ S then F S * G (S.erase p) else 0) ≤
      c p * ∑ T ∈ P.powerset, F T * G T := by
  let Q := P.powerset.filter fun S ↦ p ∈ S
  have hQsub : Q.image (fun S ↦ S.erase p) ⊆ P.powerset := by
    intro T hT
    obtain ⟨S, hSQ, rfl⟩ := Finset.mem_image.mp hT
    have hSP : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hSQ).1
    exact Finset.mem_powerset.mpr (Finset.erase_subset p S |>.trans hSP)
  have hEraseInj : Set.InjOn (fun S : Finset α ↦ S.erase p) Q := by
    intro S hS T hT
    apply erase_injective_on_mem p
    · exact (Finset.mem_filter.mp hS).2
    · exact (Finset.mem_filter.mp hT).2
  calc
    (∑ S ∈ P.powerset, if p ∈ S then F S * G (S.erase p) else 0) =
        ∑ S ∈ Q, F S * G (S.erase p) := by
      rw [show Q = P.powerset.filter (fun S ↦ p ∈ S) by rfl]
      rw [Finset.sum_filter]
    _ ≤ ∑ S ∈ Q, (c p * F (S.erase p)) * G (S.erase p) := by
      apply Finset.sum_le_sum
      intro S hSQ
      have hSP : S ⊆ P :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hSQ).1
      have hpS : p ∈ S := (Finset.mem_filter.mp hSQ).2
      exact mul_le_mul_of_nonneg_right (hdelete S hSP p hpS)
        (hG _ (Finset.erase_subset p S |>.trans hSP))
    _ = c p * ∑ T ∈ Q.image (fun S ↦ S.erase p), F T * G T := by
      rw [Finset.mul_sum, Finset.sum_image hEraseInj]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ ≤ c p * ∑ T ∈ P.powerset, F T * G T := by
      apply mul_le_mul_of_nonneg_left _ (hc p hpP)
      exact Finset.sum_le_sum_of_subset_of_nonneg hQsub (by
        intro T hTP hTnot
        have hTsub : T ⊆ P := Finset.mem_powerset.mp hTP
        exact mul_nonneg (hF T hTsub) (hG T hTsub))

/-- The first three additive moments obtained by repeated deletion.  This
finite statement is the algebraic form of the `log^3 a` expansion in Ford's
proof. -/
theorem powersetAdditiveMoment_three_le
    (P : Finset α) (F : Finset α → ℝ) (w c : α → ℝ)
    (hF : ∀ S, S ⊆ P → 0 ≤ F S)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hc : ∀ p ∈ P, 0 ≤ c p)
    (hdelete : ∀ S ⊆ P, ∀ p ∈ S, F S ≤ c p * F (S.erase p)) :
    powersetAdditiveMoment P F w 3 ≤
      ((∑ p ∈ P, c p * w p) ^ 3 +
          3 * (∑ p ∈ P, c p * w p) *
            (∑ p ∈ P, c p * w p ^ 2) +
          (∑ p ∈ P, c p * w p ^ 3)) *
        powersetAdditiveMoment P F w 0 := by
  let A : ℝ := ∑ p ∈ P, c p * w p
  let B : ℝ := ∑ p ∈ P, c p * w p ^ 2
  let C : ℝ := ∑ p ∈ P, c p * w p ^ 3
  let M : ℕ → ℝ := powersetAdditiveMoment P F w
  have hsum_nonneg (S : Finset α) (hSP : S ⊆ P) :
      0 ≤ ∑ p ∈ S, w p :=
    Finset.sum_nonneg fun p hp ↦ hw p (hSP hp)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun p hp ↦ mul_nonneg (hc p hp) (hw p hp)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun p hp ↦ mul_nonneg (hc p hp) (sq_nonneg _)
  have hM0 : 0 ≤ M 0 := by
    dsimp [M, powersetAdditiveMoment]
    exact Finset.sum_nonneg fun S hS ↦ by
      simpa using hF S (Finset.mem_powerset.mp hS)
  have hM1 : M 1 ≤ A * M 0 := by
    rw [show M 1 = ∑ S ∈ P.powerset,
        F S * ∑ p ∈ S, w p by
      simp [M, powersetAdditiveMoment]]
    rw [sum_powerset_mul_sum_eq P F (fun _ p ↦ w p)]
    calc
      (∑ p ∈ P, ∑ S ∈ P.powerset,
          if p ∈ S then F S * w p else 0) =
          ∑ p ∈ P, w p *
            (∑ S ∈ P.powerset, if p ∈ S then F S else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hpS : p ∈ S <;> simp [hpS, mul_comm]
      _ ≤ ∑ p ∈ P, w p * (c p * M 0) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (hw p hp)
        simpa only [mul_one, M, powersetAdditiveMoment, pow_zero] using
          markedDeletion_sum_le P F c hF hc hdelete hp
            (fun _ ↦ 1) (fun _ _ ↦ by positivity)
      _ = A * M 0 := by
        dsimp [A]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hM2 : M 2 ≤ (A ^ 2 + B) * M 0 := by
    rw [show M 2 = ∑ S ∈ P.powerset,
        F S * ((∑ p ∈ S, w p) * (∑ p ∈ S, w p)) by
      simp [M, powersetAdditiveMoment, pow_two]]
    rw [show (∑ S ∈ P.powerset,
        F S * ((∑ p ∈ S, w p) * (∑ p ∈ S, w p))) =
        ∑ S ∈ P.powerset,
          F S * ∑ p ∈ S, w p * (∑ q ∈ S, w q) by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_mul]
      ]
    rw [sum_powerset_mul_sum_eq P F
      (fun S p ↦ w p * (∑ q ∈ S, w q))]
    calc
      (∑ p ∈ P, ∑ S ∈ P.powerset,
          if p ∈ S then F S * (w p * ∑ q ∈ S, w q) else 0) =
          ∑ p ∈ P, w p *
            (∑ S ∈ P.powerset,
              if p ∈ S then F S * (∑ q ∈ S, w q) else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hpS : p ∈ S <;> simp [hpS]
        ring
      _ ≤ ∑ p ∈ P, w p *
          (c p * (M 1 + w p * M 0)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (hw p hp)
        have hdel := markedDeletion_sum_le P F c hF hc hdelete hp
          (fun T ↦ (∑ q ∈ T, w q) + w p)
          (fun T hTP ↦ add_nonneg (hsum_nonneg T hTP) (hw p hp))
        have hrewriteLeft :
            (∑ S ∈ P.powerset,
              if p ∈ S then F S * (∑ q ∈ S, w q) else 0) =
            ∑ S ∈ P.powerset,
              if p ∈ S then
                F S * ((∑ q ∈ S.erase p, w q) + w p) else 0 := by
          apply Finset.sum_congr rfl
          intro S hSP
          by_cases hpS : p ∈ S
          · simp only [hpS, if_true]
            rw [← Finset.sum_erase_add _ _ hpS]
          · simp [hpS]
        rw [hrewriteLeft]
        refine hdel.trans_eq ?_
        congr 1
        dsimp [M, powersetAdditiveMoment]
        simp only [pow_one, pow_zero, mul_one]
        calc
          (∑ T ∈ P.powerset, F T * ((∑ q ∈ T, w q) + w p)) =
              ∑ T ∈ P.powerset,
                (F T * (∑ q ∈ T, w q) + w p * F T) := by
            apply Finset.sum_congr rfl
            intro T hTP
            ring
          _ = (∑ T ∈ P.powerset, F T * ∑ q ∈ T, w q) +
                w p * ∑ T ∈ P.powerset, F T := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = A * M 1 + B * M 0 := by
        calc
          (∑ p ∈ P, w p * (c p * (M 1 + w p * M 0))) =
              ∑ p ∈ P,
                ((c p * w p) * M 1 + (c p * w p ^ 2) * M 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ = A * M 1 + B * M 0 := by
            dsimp [A, B]
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      _ ≤ A * (A * M 0) + B * M 0 := by
        gcongr
      _ = (A ^ 2 + B) * M 0 := by ring
  have hM3 : M 3 ≤ (A ^ 3 + 3 * A * B + C) * M 0 := by
    rw [show M 3 = ∑ S ∈ P.powerset,
        F S * ((∑ p ∈ S, w p) * (∑ p ∈ S, w p) ^ 2) by
      dsimp [M, powersetAdditiveMoment]
      apply Finset.sum_congr rfl
      intro S hS
      ring]
    rw [show (∑ S ∈ P.powerset,
        F S * ((∑ p ∈ S, w p) * (∑ p ∈ S, w p) ^ 2)) =
        ∑ S ∈ P.powerset,
          F S * ∑ p ∈ S, w p * (∑ q ∈ S, w q) ^ 2 by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_mul]
      ]
    rw [sum_powerset_mul_sum_eq P F
      (fun S p ↦ w p * (∑ q ∈ S, w q) ^ 2)]
    calc
      (∑ p ∈ P, ∑ S ∈ P.powerset,
          if p ∈ S then F S * (w p * (∑ q ∈ S, w q) ^ 2) else 0) =
          ∑ p ∈ P, w p *
            (∑ S ∈ P.powerset,
              if p ∈ S then F S * (∑ q ∈ S, w q) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hpS : p ∈ S <;> simp [hpS]
        ring
      _ ≤ ∑ p ∈ P, w p *
          (c p * (M 2 + 2 * w p * M 1 + w p ^ 2 * M 0)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (hw p hp)
        have hdel := markedDeletion_sum_le P F c hF hc hdelete hp
          (fun T ↦ ((∑ q ∈ T, w q) + w p) ^ 2)
          (fun T hTP ↦ sq_nonneg _)
        have hrewriteLeft :
            (∑ S ∈ P.powerset,
              if p ∈ S then F S * (∑ q ∈ S, w q) ^ 2 else 0) =
            ∑ S ∈ P.powerset,
              if p ∈ S then
                F S * ((∑ q ∈ S.erase p, w q) + w p) ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro S hSP
          by_cases hpS : p ∈ S
          · simp only [hpS, if_true]
            rw [← Finset.sum_erase_add _ _ hpS]
          · simp [hpS]
        rw [hrewriteLeft]
        refine hdel.trans_eq ?_
        congr 1
        dsimp [M, powersetAdditiveMoment]
        simp only [pow_zero, mul_one]
        calc
          (∑ T ∈ P.powerset, F T * ((∑ q ∈ T, w q) + w p) ^ 2) =
              ∑ T ∈ P.powerset,
                (F T * (∑ q ∈ T, w q) ^ 2 +
                  2 * w p * (F T * (∑ q ∈ T, w q)) +
                  w p ^ 2 * F T) := by
            apply Finset.sum_congr rfl
            intro T hTP
            ring
          _ = (∑ T ∈ P.powerset, F T * (∑ q ∈ T, w q) ^ 2) +
                2 * w p * (∑ T ∈ P.powerset,
                  F T * (∑ q ∈ T, w q)) +
                w p ^ 2 * ∑ T ∈ P.powerset, F T := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.mul_sum]
        simp only [pow_one]
      _ = A * M 2 + 2 * B * M 1 + C * M 0 := by
        calc
          (∑ p ∈ P, w p *
              (c p * (M 2 + 2 * w p * M 1 + w p ^ 2 * M 0))) =
              ∑ p ∈ P, ((c p * w p) * M 2 +
                (2 * (c p * w p ^ 2)) * M 1 +
                (c p * w p ^ 3) * M 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ = A * M 2 + 2 * B * M 1 + C * M 0 := by
            dsimp [A, B, C]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_mul]
            have hmid :
                (∑ p ∈ P, 2 * (c p * w p ^ 2) * M 1) =
                  (2 * ∑ p ∈ P, c p * w p ^ 2) * M 1 := by
              calc
                (∑ p ∈ P, 2 * (c p * w p ^ 2) * M 1) =
                    (∑ p ∈ P, 2 * (c p * w p ^ 2)) * M 1 := by
                  rw [Finset.sum_mul]
                _ = (2 * ∑ p ∈ P, c p * w p ^ 2) * M 1 := by
                  rw [Finset.mul_sum]
            rw [hmid]
            rw [Finset.sum_mul]
      _ ≤ A * ((A ^ 2 + B) * M 0) +
          2 * B * (A * M 0) + C * M 0 := by
        gcongr
      _ = (A ^ 3 + 3 * A * B + C) * M 0 := by ring
  simpa only [A, B, C, M] using hM3

end

end Erdos446

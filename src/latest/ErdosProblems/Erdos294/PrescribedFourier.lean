/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import UnitFractions.Fourier

/-!
# Prescribed-target Fourier identities for Erdős Problem 294

The existing `UnitFractions.Fourier` development uses the uniform weight
`p = 1 / 2` and detects sums equal to `1 / k`.  Liu--Sawhney Proposition 3.2
instead assigns an independent probability `p n` to each denominator and
detects a prescribed rational `x / Q`.  This file supplies the finite
algebraic identities needed for that extension.  No measure-theoretic
independence is required: the probability space is the powerset itself.
-/

open scoped BigOperators

namespace Erdos294.PrescribedFourier

open Complex Finset Real
open UnitFractions

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Product Bernoulli mass of the subset `B` of `A`.  The definition is
meaningful for every `B`; all probability sums below range over `A.powerset`.
-/
def subsetWeight (A B : Finset ℕ) (p : ℕ → ℝ) : ℝ :=
  (B.prod fun n => p n) * ((A \ B).prod fun n => 1 - p n)

lemma subsetWeight_nonneg {A B : Finset ℕ} {p : ℕ → ℝ}
    (hB : B ⊆ A) (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1) :
    0 ≤ subsetWeight A B p := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun n hn => hp0 n (hB hn)
  · exact Finset.prod_nonneg fun n hn =>
      sub_nonneg.mpr (hp1 n (Finset.mem_sdiff.mp hn).1)

/-- The Bernoulli masses of all subsets add to one. -/
lemma sum_subsetWeight (A : Finset ℕ) (p : ℕ → ℝ) :
    ∑ B ∈ A.powerset, subsetWeight A B p = 1 := by
  simp only [subsetWeight]
  rw [← Finset.prod_add (fun n => p n) (fun n => 1 - p n) A]
  simp

/-- Expected reciprocal sum under the finite Bernoulli mass. -/
def expectedReciprocal (A : Finset ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ n ∈ A, p n / n

/-- Complex-valued version of the Bernoulli mass. -/
def complexSubsetWeight (A B : Finset ℕ) (p : ℕ → ℝ) : ℂ :=
  subsetWeight A B p

/-- The finite Fourier transform of the Bernoulli reciprocal-sum law, twisted
by a prescribed real target `y`. -/
lemma fourier_generating_identity (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (y : ℝ) :
    ∑ B ∈ A.powerset,
        complexSubsetWeight A B p * e ((h : ℝ) * ((rec_sum B : ℝ) - y)) =
      e (-(h : ℝ) * y) *
        ∏ n ∈ A, ((1 - p n : ℝ) + p n * e ((h : ℝ) / n)) := by
  classical
  simp_rw [complexSubsetWeight]
  have hphase : ∀ B : Finset ℕ,
      e ((h : ℝ) * ((rec_sum B : ℝ) - y)) =
        e (-(h : ℝ) * y) * ∏ n ∈ B, e ((h : ℝ) / n) := by
    intro B
    calc
      e ((h : ℝ) * ((rec_sum B : ℝ) - y)) =
          e (-(h : ℝ) * y + (h : ℝ) * (rec_sum B : ℝ)) := by
            congr 1
            ring
      _ = e (-(h : ℝ) * y) * e ((h : ℝ) * (rec_sum B : ℝ)) := e_add
      _ = e (-(h : ℝ) * y) * ∏ n ∈ B, e ((h : ℝ) / n) := by
        congr 1
        rw [rec_sum, Rat.cast_sum, mul_sum, e_sum]
        apply Finset.prod_congr rfl
        intro n hn
        rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
        congr 1
        ring
  simp_rw [hphase]
  have hrearrange : ∀ B : Finset ℕ,
      (subsetWeight A B p : ℂ) *
          (e (-(h : ℝ) * y) * ∏ n ∈ B, e ((h : ℝ) / n)) =
        e (-(h : ℝ) * y) *
          ((∏ n ∈ B, (p n : ℂ) * e ((h : ℝ) / n)) *
            ∏ n ∈ A \ B, ((1 - p n : ℝ) : ℂ)) := by
    intro B
    simp only [subsetWeight]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hrearrange]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.prod_add (fun n => (p n : ℂ) * e ((h : ℝ) / n))
    (fun n => ((1 - p n : ℝ) : ℂ)) A]
  apply Finset.prod_congr rfl
  intro n hn
  ring

/-- Numerator obtained by putting the reciprocal sum over `B` on the common
denominator `lcmA A`. -/
def scaledNumerator (A B : Finset ℕ) : ℕ :=
  ∑ n ∈ B, lcmA A / n

lemma rec_sum_eq_scaledNumerator_div {A B : Finset ℕ}
    (hA : 0 ∉ A) (hB : B ⊆ A) :
    rec_sum B = (scaledNumerator A B : ℚ) / lcmA A := by
  have hQ0 : (lcmA A : ℚ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
  rw [rec_sum, scaledNumerator, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    intro hnzero
    exact hA (hB (hnzero ▸ hn))
  rw [Nat.cast_div (K := ℚ)]
  · field_simp
  · exact Finset.dvd_lcm (hB hn)
  · exact Nat.cast_ne_zero.mpr hn0

lemma phase_eq_scaledNumerator {A B : Finset ℕ}
    (hA : 0 ∉ A) (hB : B ⊆ A) {x : ℕ} (hx : x ≤ lcmA A) (h : ℤ) :
    e ((h : ℝ) * ((rec_sum B : ℝ) - (x : ℝ) / lcmA A)) =
      e ((h : ℝ) * ((scaledNumerator A B + lcmA A - x : ℕ) : ℝ) / lcmA A) := by
  have hQ0Q : (lcmA A : ℚ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
  have hQ0R : (lcmA A : ℝ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
  have hcast := congrArg (fun r : ℚ => (r : ℝ))
    (rec_sum_eq_scaledNumerator_div hA hB)
  have hrec : (rec_sum B : ℝ) = (scaledNumerator A B : ℝ) / lcmA A := by
    simpa [Rat.cast_div, Rat.cast_natCast] using hcast
  have hnatcast :
      ((scaledNumerator A B + lcmA A - x : ℕ) : ℝ) =
        (scaledNumerator A B : ℝ) + lcmA A - x := by
    rw [Nat.cast_sub]
    · push_cast
      rfl
    · omega
  rw [hrec, hnatcast]
  have harg :
      (h : ℝ) * ((scaledNumerator A B : ℝ) / lcmA A - (x : ℝ) / lcmA A) + h =
        (h : ℝ) * ((scaledNumerator A B : ℝ) + lcmA A - x) / lcmA A := by
    field_simp
    ring
  rw [← harg, e_add, e_int, mul_one]

/-- Total Bernoulli mass of subsets whose reciprocal numerator is congruent
to the prescribed `x` modulo the common denominator. -/
def congruenceWeight (A : Finset ℕ) (p : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ B ∈ A.powerset with lcmA A ∣ scaledNumerator A B + lcmA A - x,
    subsetWeight A B p

/-- Exact finite Fourier formula detecting the prescribed congruence class.
This is equation (3.1) of Liu--Sawhney before taking real parts. -/
lemma congruenceWeight_fourier (A : Finset ℕ) (p : ℕ → ℝ) (x : ℕ)
    (hA : 0 ∉ A) (hx : x ≤ lcmA A) :
    (congruenceWeight A p x : ℂ) =
      (1 / (lcmA A : ℂ)) *
        ∑ h ∈ valid_sum_range (lcmA A),
          e (-(h : ℝ) * ((x : ℝ) / lcmA A)) *
            ∏ n ∈ A, ((1 - p n : ℝ) + p n * e ((h : ℝ) / n)) := by
  have hQ0 : lcmA A ≠ 0 := lcm_ne_zero_of_zero_not_mem hA
  have hinterval :
      (-((lcmA A : ℕ) : ℤ) / 2 : ℤ) < (lcmA A : ℤ) / 2 := by
    apply Int.ediv_lt_of_lt_mul zero_lt_two
    apply lt_of_lt_of_le
    · rw [Right.neg_neg_iff, Int.natCast_pos]
      exact Nat.pos_iff_ne_zero.mpr hQ0
    · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
  let targetNumerator : Finset ℕ → ℕ := fun B =>
    scaledNumerator A B + lcmA A - x
  have horth : ∀ B ∈ A.powerset,
      (if lcmA A ∣ targetNumerator B then (1 : ℂ) else 0) =
        (1 / (lcmA A : ℂ)) *
          ∑ h ∈ valid_sum_range (lcmA A),
            e ((h : ℝ) * targetNumerator B / lcmA A) := by
    intro B hB
    have h := orthogonality (n := targetNumerator B) (m := lcmA A)
      hQ0 (I := valid_sum_range (lcmA A)) rfl hinterval
      (card_valid_sum_range (lcmA A))
    simpa [mul_comm] using h.symm
  calc
    (congruenceWeight A p x : ℂ) =
        ∑ B ∈ A.powerset,
          (subsetWeight A B p : ℂ) *
            (if lcmA A ∣ targetNumerator B then 1 else 0) := by
      simp only [congruenceWeight, Finset.sum_filter, targetNumerator]
      push_cast
      apply Finset.sum_congr rfl
      intro B hB
      split <;> simp_all
    _ = ∑ B ∈ A.powerset,
          (subsetWeight A B p : ℂ) *
            ((1 / (lcmA A : ℂ)) *
              ∑ h ∈ valid_sum_range (lcmA A),
                e ((h : ℝ) * targetNumerator B / lcmA A)) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [horth B hB]
    _ = (1 / (lcmA A : ℂ)) *
          ∑ h ∈ valid_sum_range (lcmA A),
            ∑ B ∈ A.powerset,
              (subsetWeight A B p : ℂ) *
                e ((h : ℝ) * targetNumerator B / lcmA A) := by
      calc
        ∑ B ∈ A.powerset,
            (subsetWeight A B p : ℂ) *
              ((1 / (lcmA A : ℂ)) *
                ∑ h ∈ valid_sum_range (lcmA A),
                  e ((h : ℝ) * targetNumerator B / lcmA A)) =
            (1 / (lcmA A : ℂ)) *
              ∑ B ∈ A.powerset,
                ∑ h ∈ valid_sum_range (lcmA A),
                  (subsetWeight A B p : ℂ) *
                    e ((h : ℝ) * targetNumerator B / lcmA A) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro B hB
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro h hh
              ring
        _ = (1 / (lcmA A : ℂ)) *
              ∑ h ∈ valid_sum_range (lcmA A),
                ∑ B ∈ A.powerset,
                  (subsetWeight A B p : ℂ) *
                    e ((h : ℝ) * targetNumerator B / lcmA A) := by
              congr 1
              rw [Finset.sum_comm]
    _ = (1 / (lcmA A : ℂ)) *
        ∑ h ∈ valid_sum_range (lcmA A),
          e (-(h : ℝ) * ((x : ℝ) / lcmA A)) *
            ∏ n ∈ A, ((1 - p n : ℝ) + p n * e ((h : ℝ) / n)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      rw [← fourier_generating_identity A p h ((x : ℝ) / lcmA A)]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.mem_powerset] at hB
      congr 1
      exact (phase_eq_scaledNumerator hA hB hx h).symm

end

end Erdos294.PrescribedFourier

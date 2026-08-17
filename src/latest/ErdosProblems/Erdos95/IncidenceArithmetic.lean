/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.TemporarySurfaces

/-!
# Real-power arithmetic for the strong incidence induction
-/

namespace Erdos95.IncidenceArithmetic

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.CellLines Erdos95.PartitionRemainders
open Erdos95.PartitionBookkeeping
open Erdos95.RpowBookkeeping Erdos95.GuthParameters

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

theorem rpow_half_sq {M : ℕ} (hM : 0 < M) :
    ((M : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (M : ℝ) := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hMR.le]
  norm_num

theorem richness_le_two_mul_rpow_half {M r : ℕ} (hM : 0 < M)
    (hrange : r ^ 2 ≤ 4 * M) :
    (r : ℝ) ≤ 2 * (M : ℝ) ^ ((1 : ℝ) / 2) := by
  have hrangeR : (r : ℝ) ^ 2 ≤ 4 * (M : ℝ) := by
    exact_mod_cast hrange
  have hsqrt := rpow_half_sq hM
  have hrnonneg : 0 ≤ (r : ℝ) := by positivity
  have hsnonneg : 0 ≤ (M : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  nlinarith

theorem rpow_half_mul_self {M : ℕ} (hM : 0 < M) :
    (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) =
      (M : ℝ) ^ ((3 : ℝ) / 2) := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  calc
    (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) =
        (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ (1 : ℝ) := by simp
    _ = (M : ℝ) ^ ((1 : ℝ) / 2 + 1) :=
      (Real.rpow_add hMR ((1 : ℝ) / 2) 1).symm
    _ = (M : ℝ) ^ ((3 : ℝ) / 2) := by congr 1 <;> ring

theorem rpow_three_halves_le_with_eta {M : ℕ} (hM : 0 < M)
    {η : ℝ} (hη : 0 ≤ η) :
    (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (M : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  exact Real.rpow_le_rpow_of_exponent_le hMone (by linarith)

/-- The chosen partition parameters make the total `p`-moment of all low
good cell line counts at most one sixteenth of the root moment. -/
theorem sixteen_mul_sum_low_cell_rpow_le
    {η : ℝ} (hη : 0 < η) (par : Parameters η)
    (L : Finset LineIndex) (S : Finset Space)
    (pCuts : Fin par.J → Poly3) (r : ℕ)
    (hdeg : (partitionPolynomial pCuts).totalDegree ≤ wallDegree par.k) :
    16 * (∑ sign ∈ lowSigns L S pCuts par.c r,
      ((cellLines L S pCuts sign).card : ℝ) ^
        ((3 : ℝ) / 2 + η)) ≤
      (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
  classical
  let T := lowSigns L S pCuts par.c r
  let a : (Fin par.J → Bool) → ℕ := fun sign ↦
    (cellLines L S pCuts sign).card
  have hetaExp : (3 : ℝ) / 2 + η - 1 = (1 : ℝ) / 2 + η := by ring
  have hp : 1 ≤ (3 : ℝ) / 2 + η := by linarith
  have hpoint : ∀ sign ∈ T, par.c * a sign ≤ L.card := by
    intro sign hsign
    have hgood := (mem_lowSigns_iff.mp hsign).1
    have hnotbad := mem_goodSigns_iff.mp hgood
    have hlt : par.c * (cellLines L S pCuts sign).card < L.card := by
      exact Nat.lt_of_not_ge (fun h ↦ hnotbad (mem_badSigns_iff.mpr h))
    exact hlt.le
  have hsum : ∑ sign ∈ T, a sign ≤ crossingBudget par.k * L.card := by
    calc
      ∑ sign ∈ T, a sign ≤
          ∑ sign : Fin par.J → Bool,
            (cellLines L S pCuts sign).card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (show T ⊆ (Finset.univ : Finset (Fin par.J → Bool)) by
            exact fun _ _ ↦ Finset.mem_univ _)
          (fun _ _ _ ↦ Nat.zero_le _)
      _ ≤ L.card * ((partitionPolynomial pCuts).totalDegree + 1) :=
        sum_card_cellLines_le L S pCuts
      _ ≤ L.card * crossingBudget par.k := by
        unfold crossingBudget
        gcongr
      _ = crossingBudget par.k * L.card := by ring
  have hmoment := sum_natCast_rpow_le_of_mul_le T a L.card par.c
    (crossingBudget par.k) ((3 : ℝ) / 2 + η) hp par.c_pos hpoint hsum
  have hcR : 0 < (par.c : ℝ) := by exact_mod_cast par.c_pos
  have hrewrite :
      (((L.card : ℝ) / (par.c : ℝ)) ^ ((1 : ℝ) / 2 + η)) *
          ((crossingBudget par.k * L.card : ℕ) : ℝ) =
        (((1 : ℝ) / (par.c : ℝ)) ^ ((1 : ℝ) / 2 + η) *
          (crossingBudget par.k : ℝ)) *
          (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
    by_cases hL : L.card = 0
    · have hexp : (3 : ℝ) / 2 + η ≠ 0 := by linarith
      simp [hL, Real.zero_rpow hexp]
    · have hLpos : 0 < L.card := Nat.pos_of_ne_zero hL
      have hLR : 0 < (L.card : ℝ) := by
        exact_mod_cast hLpos
      have hpow :
          (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) * (L.card : ℝ) =
            (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
        calc
          (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) * (L.card : ℝ) =
              (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) *
                (L.card : ℝ) ^ (1 : ℝ) := by simp
          _ = (L.card : ℝ) ^ ((1 : ℝ) / 2 + η + 1) :=
            (Real.rpow_add hLR ((1 : ℝ) / 2 + η) 1).symm
          _ = (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
            congr 1 <;> ring
      rw [Real.div_rpow hLR.le hcR.le]
      rw [Real.div_rpow (by positivity) hcR.le]
      simp only [Real.one_rpow]
      push_cast
      rw [← hpow]
      ring
  rw [hetaExp] at hmoment
  calc
    16 * (∑ sign ∈ T, ((a sign : ℕ) : ℝ) ^
        ((3 : ℝ) / 2 + η)) ≤
        16 * ((((L.card : ℝ) / (par.c : ℝ)) ^
          ((1 : ℝ) / 2 + η)) *
          ((crossingBudget par.k * L.card : ℕ) : ℝ)) := by gcongr
    _ = 16 * ((((1 : ℝ) / (par.c : ℝ)) ^
          ((1 : ℝ) / 2 + η) * (crossingBudget par.k : ℝ)) *
          (L.card : ℝ) ^ ((3 : ℝ) / 2 + η)) := by rw [hrewrite]
    _ ≤ 1 * (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := by
      have hnonneg :
          0 ≤ (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) :=
        Real.rpow_nonneg (by positivity) _
      have hmul := mul_le_mul_of_nonneg_right par.contraction hnonneg
      simpa only [mul_assoc] using hmul
    _ = (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) := one_mul _

end Erdos95.IncidenceArithmetic

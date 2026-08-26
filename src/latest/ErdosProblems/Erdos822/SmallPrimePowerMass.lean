/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1CofactorMass
import ErdosProblems.Erdos822.DivisibleSmallMass
import ErdosProblems.Erdos387.PrimeReciprocalBound

/-! # Removing oversized small-prime powers at the B1 cutoff -/

namespace Erdos822

open Filter
open scoped BigOperators Classical

def firstPrimePowerAbove (p y : ℕ) : ℕ := p ^ (Nat.log p y + 1)

noncomputable def smallPrimePowerBadFactors (N y : ℕ) : Finset ℕ :=
  (oddSmallFactors N).filter fun k ↦ ¬ SmallPrimePowersBounded k y

theorem smallPrimePowerBadFactors_subset_union {N y : ℕ} (hy : 0 < y) :
    smallPrimePowerBadFactors N y ⊆ (Nat.primesLE y).biUnion
      (fun p ↦ (oddSmallFactors N).filter fun k ↦ firstPrimePowerAbove p y ∣ k) := by
  intro k hk
  obtain ⟨hkodd, hkbad⟩ := Finset.mem_filter.mp hk
  simp only [SmallPrimePowersBounded, not_forall, not_le] at hkbad
  obtain ⟨p, hp, hpy, hpower⟩ := hkbad
  have hexp : Nat.log p y + 1 ≤ k.factorization p := by
    have h := (Nat.log_lt_iff_lt_pow hp.one_lt hy.ne').mpr hpower
    omega
  have hdiv : firstPrimePowerAbove p y ∣ k :=
    (Nat.pow_dvd_pow p hexp).trans (Nat.ordProj_dvd k p)
  exact Finset.mem_biUnion.mpr
    ⟨p, Nat.mem_primesLE.mpr ⟨hpy, hp⟩, Finset.mem_filter.mpr ⟨hkodd, hdiv⟩⟩

theorem sum_inv_smallPrimePowerBadFactors_le {N y : ℕ} (hy : 0 < y) :
    ∑ k ∈ smallPrimePowerBadFactors N y, (1 : ℝ) / k ≤
      (harmonic N : ℝ) * Nat.primeCounting y / y := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun k hk ↦ by positivity
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  calc
    (∑ k ∈ smallPrimePowerBadFactors N y, (1 : ℝ) / k) ≤
        ∑ k ∈ (Nat.primesLE y).biUnion
          (fun p ↦ (oddSmallFactors N).filter fun k ↦ firstPrimePowerAbove p y ∣ k),
          (1 : ℝ) / k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (smallPrimePowerBadFactors_subset_union hy) (fun k hk hnot ↦ by positivity)
    _ ≤ ∑ p ∈ Nat.primesLE y,
        ∑ k ∈ (oddSmallFactors N).filter (fun k ↦ firstPrimePowerAbove p y ∣ k),
          (1 : ℝ) / k :=
      sum_biUnion_le_sum _ _ _ (fun p hp k hk ↦ by positivity)
    _ ≤ ∑ _p ∈ Nat.primesLE y, (harmonic N : ℝ) / y := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (Nat.mem_primesLE.mp hp).2
      have hpower : y < firstPrimePowerAbove p y :=
        Nat.lt_pow_succ_log_self hprime.one_lt y
      calc
        (∑ k ∈ (oddSmallFactors N).filter (fun k ↦ firstPrimePowerAbove p y ∣ k),
            (1 : ℝ) / k) ≤
            (harmonic (N / firstPrimePowerAbove p y) : ℝ) / firstPrimePowerAbove p y :=
          sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div (pow_pos hprime.pos _)
        _ ≤ (harmonic N : ℝ) / firstPrimePowerAbove p y :=
          div_le_div_of_nonneg_right (harmonic_cast_mono (Nat.div_le_self _ _)) (by positivity)
        _ ≤ (harmonic N : ℝ) / y :=
          div_le_div_of_nonneg_left hH hyR (by exact_mod_cast hpower.le)
    _ = (harmonic N : ℝ) * Nat.primeCounting y / y := by
      simp [Nat.primesLE_card_eq_primeCounting]
      ring

theorem exists_smallPrimePowerBadFactors_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 2 ≤ y →
      (∑ k ∈ smallPrimePowerBadFactors N y, (1 : ℝ) / k) ≤
        C * (1 + Real.log (N : ℝ)) / Real.log (y : ℝ) := by
  obtain ⟨C, hC, hpi⟩ := Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  refine ⟨C, hC, ?_⟩
  intro N y hy
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun k hk ↦ by positivity
  calc
    (∑ k ∈ smallPrimePowerBadFactors N y, (1 : ℝ) / k) ≤
        (harmonic N : ℝ) * Nat.primeCounting y / y :=
      sum_inv_smallPrimePowerBadFactors_le (by omega)
    _ ≤ (harmonic N : ℝ) * (C * y / Real.log (y : ℝ)) / y := by gcongr; exact hpi y hy
    _ = C * (harmonic N : ℝ) / Real.log (y : ℝ) := by field_simp
    _ ≤ C * (1 + Real.log (N : ℝ)) / Real.log (y : ℝ) := by
      gcongr
      exact harmonic_le_one_add_log N

theorem eventually_sum_inv_smallPrimePowerBadFactors_le_log
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ k ∈ smallPrimePowerBadFactors N (b1Cutoff N), (1 : ℝ) / k) ≤
        ε * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_smallPrimePowerBadFactors_log_bound
  have hylog : Tendsto (fun N ↦ Real.log (b1Cutoff N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_b1Cutoff_atTop)
  filter_upwards [hylog.eventually_ge_atTop (2 * C / ε),
      tendsto_b1Cutoff_atTop.eventually_ge_atTop 2,
      eventually_ge_atTop 4] with N hylogN hy hN
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hlogy : 0 < Real.log (b1Cutoff N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b1Cutoff N by omega))
  have hcoeff : 2 * C ≤ ε * Real.log (b1Cutoff N : ℝ) := by
    have h := (div_le_iff₀ hε).mp hylogN
    nlinarith
  refine (hbound N (b1Cutoff N) hy).trans ?_
  apply (div_le_iff₀ hlogy).mpr
  have hmul := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ Real.log (N : ℝ) by linarith)
  nlinarith

#print axioms eventually_sum_inv_smallPrimePowerBadFactors_le_log

end Erdos822

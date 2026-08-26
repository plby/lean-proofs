import ErdosProblems.Erdos1164.LocalTime
import ErdosProblems.Erdos1165.TwoPointLogAvoidance

/-! # Last-exit decomposition and the logarithmic first-return tail -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.TwoPointLogAvoidance

/-- Probability of no strictly positive return through time `n`. -/
noncomputable abbrev noReturnProbability (n : ℕ) : ℝ := avoidanceProbability 0 n

/-- Truncated expected number of visits to zero, including time zero. -/
noncomputable def returnGreen (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), endpointProbabilityReal k 0

private theorem origin_lastExit_convolution (N : ℕ) :
    1 = ∑ k ∈ Finset.range (N + 1),
      endpointProbabilityReal k 0 * noReturnProbability (N - k) := by
  let pieces : Fin (N + 1) → Set StepPath := fun k ↦ lastVisitPiece 0 N (k, false)
  have hd : ((Finset.univ : Finset (Fin (N + 1))) : Set (Fin (N + 1))).PairwiseDisjoint
      pieces := by
    intro i _ j _ hij
    change Disjoint (pieces i) (pieces j)
    rw [Set.disjoint_left]
    intro w hwi hwj
    apply hij
    apply Fin.ext
    exact (mem_lastVisitPiece_time hwi).symm.trans (mem_lastVisitPiece_time hwj)
  have hu : (⋃ k ∈ (Finset.univ : Finset (Fin (N + 1))), pieces k) = Set.univ := by
    ext w
    simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_univ, iff_true]
    let k : Fin (N + 1) := ⟨lastPairVisit 0 N w, Nat.lt_succ_of_le (lastPairVisit_le 0 N w)⟩
    refine ⟨k, trivial, ?_⟩
    change lastPairVisit 0 N w = (k : ℕ) ∧ trajectory w k = 0
    exact ⟨rfl, (lastPairVisit_position 0 N w).elim id id⟩
  have hm := MeasureTheory.measureReal_biUnion_finset (μ := fairSteps)
    hd (fun k _ ↦ measurableSet_lastVisitPiece 0 N (k, false)) (fun _ _ ↦ by finiteness)
  rw [hu] at hm
  have h1 : fairSteps.real (Set.univ : Set StepPath) = 1 := by
    simp [measureReal_def]
  rw [h1] at hm
  calc
    1 = ∑ k : Fin (N + 1), fairSteps.real (pieces k) := hm
    _ = ∑ k : Fin (N + 1), endpointProbabilityReal k 0 * noReturnProbability (N - k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact lastVisitPiece_measureReal_false 0 N k
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ endpointProbabilityReal k 0 * noReturnProbability (N - k)) (N + 1)

/-- Monotonicity in the last-exit formula bounds the return tail by inverse
truncated Green mass. No limiting renewal theorem is used. -/
theorem noReturnProbability_mul_returnGreen_le_one (n : ℕ) :
    noReturnProbability n * returnGreen n ≤ 1 := by
  rw [origin_lastExit_convolution n]
  unfold returnGreen
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hq := avoidanceProbability_antitone 0 (Nat.sub_le n k)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hq (endpointProbabilityReal_nonneg k 0)

private theorem endpointProbabilityReal_even_zero (m : ℕ) :
    endpointProbabilityReal (2 * m) 0 = planarReturnProbability m := by
  rw [← simpleRandomWalk_endpoint_toReal]
  change (simpleRandomWalk {s | s (2 * m) = (0, 0)}).toReal = planarReturnProbability m
  rw [simpleRandomWalk_return_probability,
    ENNReal.toReal_ofReal (planarReturnProbability_pos m).le]

private theorem even_return_sum_le_green (m : ℕ) :
    (∑ j ∈ Finset.range m, endpointProbabilityReal (2 * (j + 1)) 0) ≤
      returnGreen (2 * m) := by
  have hi : Function.Injective (fun j : ℕ ↦ 2 * (j + 1)) := by
    intro i j hij
    dsimp only at hij
    omega
  have hs : (Finset.range m).image (fun j ↦ 2 * (j + 1)) ⊆ Finset.range (2 * m + 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hj
    omega
  unfold returnGreen
  rw [← Finset.sum_image (f := fun k : ℕ ↦ endpointProbabilityReal k 0)
    (s := Finset.range m) (g := fun j : ℕ ↦ 2 * (j + 1)) (fun _ _ _ _ h ↦ hi h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ ↦ endpointProbabilityReal_nonneg k 0)

theorem harmonic_le_four_mul_returnGreen (m : ℕ) :
    (harmonic m : ℝ) ≤ 4 * returnGreen (2 * m) := by
  have hterm : ∀ j ∈ Finset.range m,
      (1 : ℝ) / (4 * (j + 1 : ℕ)) ≤ endpointProbabilityReal (2 * (j + 1)) 0 := by
    intro j _
    rw [endpointProbabilityReal_even_zero]
    exact planarReturnProbability_lower_bound (Nat.succ_pos j)
  have hsum := Finset.sum_le_sum hterm
  have heq : (∑ j ∈ Finset.range m, (1 : ℝ) / (4 * (j + 1 : ℕ))) =
      (1 / 4 : ℝ) * (harmonic m : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_div, mul_inv_rev]
    ring
  rw [heq] at hsum
  have h := hsum.trans (even_return_sum_le_green m)
  linarith

/-- Explicit logarithmic no-return bound at even times. -/
theorem noReturnProbability_even_le (m : ℕ) (hm : 1 ≤ m) :
    noReturnProbability (2 * m) ≤ 4 / Real.log (m + 1 : ℝ) := by
  have hlog : 0 < Real.log (m + 1 : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m + 1))
  have hgreen : Real.log (m + 1 : ℝ) ≤ 4 * returnGreen (2 * m) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      (log_add_one_le_harmonic m).trans (harmonic_le_four_mul_returnGreen m)
  have hq : 0 ≤ noReturnProbability (2 * m) := avoidanceProbability_nonneg 0 _
  have hprod := mul_le_mul_of_nonneg_left hgreen hq
  have hbound := noReturnProbability_mul_returnGreen_le_one (2 * m)
  apply (le_div_iff₀ hlog).mpr
  nlinarith

/-- A single bound valid at every integer time, including the short-time cases. -/
theorem noReturnProbability_le (n : ℕ) :
    noReturnProbability n ≤ 12 / Real.log ((n + 2 : ℕ) : ℝ) := by
  have hnlog : 0 < Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n + 2))
  by_cases hn : 2 ≤ n
  · let m := n / 2
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hmn : 2 * m ≤ n := by dsimp [m]; omega
    have hnm : n ≤ 2 * m + 1 := by dsimp [m]; omega
    have hcube : n + 2 ≤ (m + 1) ^ 3 := by
      have hm2 : 1 ≤ m ^ 2 := Nat.succ_le_of_lt (pow_pos (by omega) 2)
      have hm3 : 1 ≤ m ^ 3 := Nat.succ_le_of_lt (pow_pos (by omega) 3)
      nlinarith
    have hmLog : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < m + 1))
    have hlogs : Real.log ((n + 2 : ℕ) : ℝ) ≤
        3 * Real.log ((m + 1 : ℕ) : ℝ) := by
      have h := Real.log_le_log
        (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))
        (show ((n + 2 : ℕ) : ℝ) ≤ (((m + 1 : ℕ) : ℝ) ^ 3) by exact_mod_cast hcube)
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hq := (avoidanceProbability_antitone 0 hmn).trans (noReturnProbability_even_le m hm)
    have hq' : noReturnProbability n * Real.log ((m + 1 : ℕ) : ℝ) ≤ 4 := by
      apply (le_div_iff₀ hmLog).mp
      simpa only [Nat.cast_add, Nat.cast_one] using hq
    have hmul := mul_le_mul_of_nonneg_left hlogs (avoidanceProbability_nonneg 0 n)
    apply (le_div_iff₀ hnlog).mpr
    nlinarith
  · have hsmall : n ≤ 1 := by omega
    have hlogle : Real.log ((n + 2 : ℕ) : ℝ) ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos
        (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))
      have hncast : (n : ℝ) ≤ 1 := by exact_mod_cast hsmall
      push_cast at h ⊢
      linarith
    apply (avoidanceProbability_le_one 0 n).trans
    apply (le_div_iff₀ hnlog).mpr
    linarith

end Erdos1164

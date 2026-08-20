/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovPykeBounds
import ErdosProblems.Erdos446.BlockCloseBounds
import ErdosProblems.Erdos446.IsolatedBlockFamily

/-!
# Erdős Problem 446: the finite lower-volume core

For the fixed-multiplicity argument Ford ultimately takes the number of
points and the number of equal cells to be the same.  Thus the two terminal
slacks in the Smirnov problem are both one.  This file records the exact
lower mass at that endpoint and the finite weighted Markov step which cuts
off the prefix energy.

Everything here is a finite sum.  In particular, there is no measure-theory
normalization hidden in the later lower-volume estimate.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- At the fixed-multiplicity parameters `u = w = 1`, Pyke's endpoint
formula evaluates the complete reciprocal-factorial Smirnov mass. -/
theorem smirnovOccupancyMass_one_eq {k : ℕ} (hk : 1 ≤ k) :
    smirnovOccupancyMass k 1 k =
      ((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ) := by
  have hprob := smirnovProbability_one_eq
    (k := k) (v := k) (w := 1) hk (by norm_num) (by omega)
  rw [smirnovProbability] at hprob
  norm_num at hprob
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hfac).2
  rw [mul_comm]
  convert hprob using 1 <;> push_cast <;> ring

/-- Equation (47a), in the equal-cell finite occupancy normalization.  The
left side is exactly `k ^ k` times `1 / (k+1)!`, the volume scale used in
Ford's statement. -/
theorem smirnovOccupancyMass_one_lower {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ k / ((k + 1).factorial : ℝ) ≤
      smirnovOccupancyMass k 1 k := by
  rw [smirnovOccupancyMass_one_eq hk, Nat.factorial_succ]
  push_cast
  have hkR : (0 : ℝ) < k := by positivity
  have hk1R : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hk1R' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hpow : (k : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) ^ k := by
    gcongr
    exact_mod_cast (Nat.le_succ k)
  have hnum :
      (k : ℝ) ^ k / ((k : ℝ) + 1) ≤
        ((k : ℝ) + 1) ^ (k - 1) := by
    apply (div_le_iff₀ hk1R').2
    calc
      (k : ℝ) ^ k ≤ ((k : ℝ) + 1) ^ k := by
        simpa only [Nat.cast_add, Nat.cast_one] using hpow
      _ = ((k : ℝ) + 1) ^ (k - 1) * ((k : ℝ) + 1) := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
  calc
    (k : ℝ) ^ k / (((k : ℝ) + 1) * (k.factorial : ℝ)) =
        ((k : ℝ) ^ k / ((k : ℝ) + 1)) /
          (k.factorial : ℝ) := by
      field_simp [hk1R'.ne', hfac.ne']
    _ ≤ (((k : ℝ) + 1) ^ (k - 1)) / (k.factorial : ℝ) :=
      div_le_div_of_nonneg_right hnum hfac.le

/-- Ford's prefix energy on an equal-cell occupancy vector.  The identity
`compositionPenalty_eq_sum_prefixTerm` expands it as
`sum_i 2^(prefix(i+1)-(i+1))`. -/
noncomputable def fixedLowerPrefixEnergy {k : ℕ}
    (c : Fin k → ℕ) : ℝ :=
  compositionPenalty c

theorem fixedLowerPrefixEnergy_nonneg {k : ℕ} (c : Fin k → ℕ) :
    0 ≤ fixedLowerPrefixEnergy c := by
  dsimp [fixedLowerPrefixEnergy, compositionPenalty]
  apply prefixProductMass_nonneg
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (compositionFactor_pos c i).le

/-- Smirnov occupancies whose prefix energy is at most `T`. -/
noncomputable def fixedLowerEnergyOccupancies (k : ℕ) (T : ℝ) :
    Finset (Fin k → ℕ) := by
  classical
  exact (smirnovOccupancies k 1 k).filter fun c ↦
    fixedLowerPrefixEnergy c ≤ T

theorem mem_fixedLowerEnergyOccupancies {k : ℕ} {T : ℝ}
    {c : Fin k → ℕ} :
    c ∈ fixedLowerEnergyOccupancies k T ↔
      c ∈ smirnovOccupancies k 1 k ∧ fixedLowerPrefixEnergy c ≤ T := by
  classical
  simp [fixedLowerEnergyOccupancies]

/-- Reciprocal-factorial mass after the prefix-energy cutoff. -/
noncomputable def fixedLowerEnergyMass (k : ℕ) (T : ℝ) : ℝ :=
  ∑ c ∈ fixedLowerEnergyOccupancies k T, 1 / compositionFactorial c

/-- First moment of the prefix energy on the one-slack Smirnov set. -/
noncomputable def fixedLowerPrefixEnergyMoment (k : ℕ) : ℝ :=
  ∑ c ∈ smirnovOccupancies k 1 k,
    fixedLowerPrefixEnergy c / compositionFactorial c

theorem inv_compositionFactorial_nonneg' {k : ℕ} (c : Fin k → ℕ) :
    0 ≤ 1 / compositionFactorial c := by
  apply one_div_nonneg.mpr
  dsimp [compositionFactorial]
  positivity

/-! ## The prefix cutoff already enforces Ford's endpoint caps -/

/-- If the `i`th Ford cap fails, the `i`th summand of the prefix energy is
at least `2^(M^2)`.  This is stronger than separately estimating endpoint
failures as in the continuous proof of (47b). -/
theorem two_pow_sq_le_compositionPrefixTerm_of_fordCap_failure
    {M k : ℕ} (hM : 1 ≤ M) (c : Fin k → ℕ) (i : Fin k)
    (hi : M * (M + i.val) < c i) :
    (2 : ℝ) ^ (M * M) ≤ compositionPrefixTerm c i := by
  let P : ℕ := ∑ q ∈ Finset.Iic i, c q
  have hci : c i ≤ P := by
    dsimp [P]
    exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le (c q))
      (Finset.mem_Iic.mpr le_rfl)
  have himul : i.val ≤ M * i.val := by
    calc
      i.val = 1 * i.val := by simp
      _ ≤ M * i.val := Nat.mul_le_mul_right i.val hM
  have hexp : M * M + (i.val + 1) ≤ P := by
    calc
      M * M + (i.val + 1) ≤ M * M + (M * i.val + 1) := by omega
      _ = M * (M + i.val) + 1 := by rw [Nat.mul_add]; omega
      _ ≤ c i := by omega
      _ ≤ P := hci
  have hpow :
      (2 : ℝ) ^ (M * M + (i.val + 1)) ≤ (2 : ℝ) ^ P := by
    gcongr <;> norm_num
  calc
    (2 : ℝ) ^ (M * M) =
        (2 : ℝ) ^ (M * M + (i.val + 1)) /
          (2 : ℝ) ^ (i.val + 1) := by
      rw [pow_add]
      field_simp
    _ ≤ (2 : ℝ) ^ P / (2 : ℝ) ^ (i.val + 1) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ = compositionPrefixTerm c i := by
      rfl

/-- Consequently every failure of Ford's endpoint cap has prefix energy at
least `2^(M^2)`. -/
theorem two_pow_sq_le_fixedLowerPrefixEnergy_of_not_fordCapped
    {M k : ℕ} (hM : 1 ≤ M) (c : Fin k → ℕ)
    (hc : ¬ IsFordCapped M c) :
    (2 : ℝ) ^ (M * M) ≤ fixedLowerPrefixEnergy c := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, M * (M + i.val) < c i := by
    simpa [IsFordCapped, not_forall, not_le] using hc
  have hterm :=
    two_pow_sq_le_compositionPrefixTerm_of_fordCap_failure hM c i hi
  rw [fixedLowerPrefixEnergy, compositionPenalty_eq_sum_prefixTerm]
  exact hterm.trans (Finset.single_le_sum
    (fun j _ ↦ by
      dsimp [compositionPrefixTerm]
      positivity)
    (Finset.mem_univ i))

/-- A cutoff strictly below `2^(M^2)` makes the endpoint caps automatic. -/
theorem isFordCapped_of_fixedLowerPrefixEnergy_lt_two_pow_sq
    {M k : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : T < (2 : ℝ) ^ (M * M))
    {c : Fin k → ℕ} (hc : fixedLowerPrefixEnergy c ≤ T) :
    IsFordCapped M c := by
  by_contra hcap
  have := two_pow_sq_le_fixedLowerPrefixEnergy_of_not_fordCapped hM c hcap
  linarith

theorem fixedLowerPrefixEnergyMoment_nonneg (k : ℕ) :
    0 ≤ fixedLowerPrefixEnergyMoment k := by
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (fixedLowerPrefixEnergy_nonneg c) (by
    dsimp [compositionFactorial]
    positivity)

/-- The exact finite Markov deletion used after (47c).  If the whole
Smirnov set has mass at least `L` and prefix-energy first moment at most
`A`, then the cutoff `energy ≤ T` retains mass at least `L - A/T`. -/
theorem fixedLowerEnergyMass_lower_of_moment
    {k : ℕ} {T L A : ℝ} (hT : 0 < T)
    (hmass : L ≤ smirnovOccupancyMass k 1 k)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤ A) :
    L - A / T ≤ fixedLowerEnergyMass k T := by
  classical
  let S := smirnovOccupancies k 1 k
  let G := fixedLowerEnergyOccupancies k T
  let B := S.filter fun c ↦ T < fixedLowerPrefixEnergy c
  let W : (Fin k → ℕ) → ℝ := fun c ↦ 1 / compositionFactorial c
  have hpartition :
      (∑ c ∈ S, W c) = (∑ c ∈ G, W c) + ∑ c ∈ B, W c := by
    rw [show G = S.filter (fun c ↦ fixedLowerPrefixEnergy c ≤ T) by rfl,
      show B = S.filter (fun c ↦ T < fixedLowerPrefixEnergy c) by rfl]
    rw [← Finset.sum_filter_add_sum_filter_not
      S (fun c ↦ fixedLowerPrefixEnergy c ≤ T) W]
    congr 2
    ext c
    simp only [Finset.mem_filter, not_le]
  have hbadMarkov :
      T * (∑ c ∈ B, W c) ≤ fixedLowerPrefixEnergyMoment k := by
    calc
      T * (∑ c ∈ B, W c) = ∑ c ∈ B, T * W c := by
        rw [Finset.mul_sum]
      _ ≤ ∑ c ∈ B,
          fixedLowerPrefixEnergy c / compositionFactorial c := by
        apply Finset.sum_le_sum
        intro c hc
        have hcT : T ≤ fixedLowerPrefixEnergy c :=
          (Finset.mem_filter.mp hc).2.le
        change T * (1 / compositionFactorial c) ≤
          fixedLowerPrefixEnergy c / compositionFactorial c
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hcT (by
            apply inv_nonneg.mpr
            have hcf : 0 ≤ compositionFactorial c := by
              unfold compositionFactorial
              positivity
            exact hcf)
      _ ≤ ∑ c ∈ S,
          fixedLowerPrefixEnergy c / compositionFactorial c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro c hcS hcB
          exact div_nonneg (fixedLowerPrefixEnergy_nonneg c) (by
            dsimp [compositionFactorial]
            positivity)
      _ = fixedLowerPrefixEnergyMoment k := by rfl
  have hbad : (∑ c ∈ B, W c) ≤ A / T := by
    apply (le_div_iff₀ hT).2
    simpa [mul_comm] using hbadMarkov.trans hmoment
  have hwhole : L ≤ ∑ c ∈ S, W c := by
    simpa [S, W, smirnovOccupancyMass] using hmass
  have hgood : L - A / T ≤ ∑ c ∈ G, W c := by
    rw [hpartition] at hwhole
    linarith
  simpa [G, W, fixedLowerEnergyMass] using hgood

/-! ## Simultaneous endpoint and energy deletion -/

/-- Failure mass of Ford's one-sided endpoint cap, restricted to the
one-slack Smirnov set. -/
noncomputable def fixedLowerCapFailureMass (M k : ℕ) : ℝ :=
  by
    classical
    exact ∑ c ∈ (smirnovOccupancies k 1 k).filter
        (fun c ↦ ¬ IsFordCapped M c),
      1 / compositionFactorial c

/-- Occupancies surviving both Ford's endpoint caps and the prefix-energy
cutoff. -/
noncomputable def fixedLowerRestrictedOccupancies
    (M k : ℕ) (T : ℝ) : Finset (Fin k → ℕ) := by
  classical
  exact (fixedLowerEnergyOccupancies k T).filter (IsFordCapped M)

theorem mem_fixedLowerRestrictedOccupancies
    {M k : ℕ} {T : ℝ} {c : Fin k → ℕ} :
    c ∈ fixedLowerRestrictedOccupancies M k T ↔
      c ∈ smirnovOccupancies k 1 k ∧
        fixedLowerPrefixEnergy c ≤ T ∧ IsFordCapped M c := by
  classical
  simp [fixedLowerRestrictedOccupancies, mem_fixedLowerEnergyOccupancies,
    and_assoc]

/-- Reciprocal-factorial mass of the simultaneous restriction. -/
noncomputable def fixedLowerRestrictedMass (M k : ℕ) (T : ℝ) : ℝ :=
  ∑ c ∈ fixedLowerRestrictedOccupancies M k T,
    1 / compositionFactorial c

/-- Finite inclusion-exclusion followed by Markov.  This is the exact
algebraic last step in (47): subtract the endpoint failures and the energy
tail from the one-slack Smirnov mass. -/
theorem fixedLowerRestrictedMass_lower
    {M k : ℕ} {T L A D : ℝ} (hT : 0 < T)
    (hmass : L ≤ smirnovOccupancyMass k 1 k)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤ A)
    (hcap : fixedLowerCapFailureMass M k ≤ D) :
    L - A / T - D ≤ fixedLowerRestrictedMass M k T := by
  classical
  let S := smirnovOccupancies k 1 k
  let G := fixedLowerEnergyOccupancies k T
  let R := fixedLowerRestrictedOccupancies M k T
  let C := S.filter fun c ↦ ¬ IsFordCapped M c
  let GC := G.filter fun c ↦ ¬ IsFordCapped M c
  let W : (Fin k → ℕ) → ℝ := fun c ↦ 1 / compositionFactorial c
  have henergy : L - A / T ≤ ∑ c ∈ G, W c := by
    simpa [G, W, fixedLowerEnergyMass] using
      fixedLowerEnergyMass_lower_of_moment hT hmass hmoment
  have hGpartition :
      (∑ c ∈ G, W c) = (∑ c ∈ R, W c) + ∑ c ∈ GC, W c := by
    rw [show R = G.filter (IsFordCapped M) by rfl,
      show GC = G.filter (fun c ↦ ¬ IsFordCapped M c) by rfl,
      ← Finset.sum_filter_add_sum_filter_not G (IsFordCapped M) W]
  have hGCsubset : GC ⊆ C := by
    intro c hc
    have hcData := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr
      ⟨(mem_fixedLowerEnergyOccupancies.mp hcData.1).1, hcData.2⟩
  have hGC : (∑ c ∈ GC, W c) ≤ D := by
    calc
      (∑ c ∈ GC, W c) ≤ ∑ c ∈ C, W c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hGCsubset
        intro c hcC hcGC
        exact inv_compositionFactorial_nonneg' c
      _ = fixedLowerCapFailureMass M k := by
        simp [C, S, W, fixedLowerCapFailureMass]
      _ ≤ D := hcap
  rw [hGpartition] at henergy
  have : L - A / T - D ≤ ∑ c ∈ R, W c := by linarith
  simpa [R, W, fixedLowerRestrictedMass] using this

/-- Every simultaneously restricted vector belongs to the concrete
positive isolated family once the numerical close-pair inequality holds at
the cutoff `T`. -/
theorem fixedLowerRestrictedOccupancies_subset_positiveIsolated
    {M k : ℕ} {T E Q : ℝ} (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    fixedLowerRestrictedOccupancies M k T ⊆
      positiveIsolatedCompositions M k E := by
  intro c hc
  have hcData := mem_fixedLowerRestrictedOccupancies.mp hc
  rw [mem_positiveIsolatedCompositions]
  constructor
  · rw [mem_cappedCompositions]
    exact ⟨(mem_smirnovOccupancies_iff_barrier.mp hcData.1).1,
      hcData.2.2⟩
  · rw [← hQdef]
    apply hquality.trans'
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg E)
    simpa [fixedLowerPrefixEnergy] using
      add_le_add_left (mul_le_mul_of_nonneg_left hcData.2.1 hQ) 1

/-- Consequently any closed lower bound for the restricted volume is a
lower bound for the exact good-composition mass consumed by
`IsolatedBlockFamily`. -/
theorem positiveIsolatedCompositions_mass_lower_of_restricted
    {M k : ℕ} {T E Q B : ℝ} (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * T) ≤ 4 / 3)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))
    (hB : B ≤ fixedLowerRestrictedMass M k T) :
    B ≤ ∑ c ∈ positiveIsolatedCompositions M k E,
      1 / compositionFactorial c := by
  exact hB.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fixedLowerRestrictedOccupancies_subset_positiveIsolated
      hQ hquality hQdef)
    (fun c hc _ ↦ inv_compositionFactorial_nonneg' c))

end Erdos446

/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerVolumeCore
import ErdosProblems.Erdos446.CappedCompositions

/-!
# Erdős Problem 446: endpoint caps in the one-slack lower family

At the specialization used for fixed multiplicity, every vector belongs to
`smirnovOccupancies k 1 k`.  Its strict prefix inequalities imply the
pointwise bound `c i ≤ i + 1`.  Consequently Ford's block cap

`c i ≤ M * (M + i)`

is automatic as soon as `M ≥ 1`.  Thus, for the actual capped family used
by the arithmetic construction, the endpoint-cap deletion has *zero* mass.
This is stronger than a small-coefficient estimate and removes an otherwise
unnecessary loss from the finite lower-volume assembly.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The cap predicate is finitary.  Naming its decidability instance keeps
later `Finset.filter` statements computational and avoids invoking global
classical choice merely to state them. -/
instance decidableIsFordCapped446 {K M : ℕ} (b : Fin K → ℕ) :
    Decidable (IsFordCapped M b) := by
  unfold IsFordCapped
  infer_instance

/-- A coordinate is no larger than the prefix ending at that coordinate. -/
theorem fixedLowerCoordinate_le_prefix {k : ℕ} (c : Fin k → ℕ)
    (i : Fin k) : c i ≤ occupancyPrefix c (i.val + 1) := by
  rw [occupancyPrefix]
  exact Finset.single_le_sum (fun j _hj ↦ Nat.zero_le (c j)) (by simp)

/-- The one-slack Smirnov inequalities give the sharp linear coordinate
cap `c i ≤ i + 1`. -/
theorem fixedLowerCoordinate_le_index_succ
    {k : ℕ} {c : Fin k → ℕ} (hc : c ∈ smirnovOccupancies k 1 k)
    (i : Fin k) : c i ≤ i.val + 1 := by
  have hpref := (mem_smirnovOccupancies.mp hc).2
    (i.val + 1) (by omega) (by omega)
  have hcoord := fixedLowerCoordinate_le_prefix c i
  omega

/-- Ford's one-sided block caps are automatic on the equal-cell, one-slack
Smirnov family. -/
theorem smirnovOccupancy_one_isFordCapped
    {M k : ℕ} (hM : 1 ≤ M) {c : Fin k → ℕ}
    (hc : c ∈ smirnovOccupancies k 1 k) : IsFordCapped M c := by
  intro i
  have hlinear := fixedLowerCoordinate_le_index_succ hc i
  have hmul : 1 * (1 + i.val) ≤ M * (M + i.val) :=
    Nat.mul_le_mul hM (Nat.add_le_add_right hM i.val)
  omega

/-- There are no cap failures inside the one-slack Smirnov family. -/
theorem fixedLowerCapFailures_eq_empty
    {M k : ℕ} (hM : 1 ≤ M) :
    (smirnovOccupancies k 1 k).filter
        (fun c ↦ ¬ IsFordCapped M c) = ∅ := by
  ext c
  constructor
  · intro hc
    have hcData := Finset.mem_filter.mp hc
    exact (hcData.2 (smirnovOccupancy_one_isFordCapped hM hcData.1)).elim
  · intro hc
    simp at hc

/-- The reciprocal-factorial cap-failure sum is exactly zero. -/
theorem sum_fixedLowerCapFailures_inv_factorial_eq_zero
    {M k : ℕ} (hM : 1 ≤ M) :
    (∑ c ∈ (smirnovOccupancies k 1 k).filter
        (fun c ↦ ¬ IsFordCapped M c),
      1 / compositionFactorial c) = 0 := by
  rw [fixedLowerCapFailures_eq_empty hM]
  simp

/-- Closed quantitative form: the cap-failure mass is bounded by any
nonnegative multiple of Ford's natural volume scale. -/
theorem sum_fixedLowerCapFailures_inv_factorial_le_scale
    {M k : ℕ} (hM : 1 ≤ M) {C : ℝ} (hC : 0 ≤ C) :
    (∑ c ∈ (smirnovOccupancies k 1 k).filter
        (fun c ↦ ¬ IsFordCapped M c),
      1 / compositionFactorial c) ≤
      C * (k : ℝ) ^ k / ((k + 1).factorial : ℝ) := by
  rw [sum_fixedLowerCapFailures_inv_factorial_eq_zero hM]
  positivity

/-- Any subfamily of the one-slack Smirnov family is unchanged by imposing
Ford's block cap.  This is the set-theoretic form used after the energy
cutoff. -/
theorem filter_isFordCapped_eq_self_of_subset_smirnov
    {M k : ℕ} (hM : 1 ≤ M) {S : Finset (Fin k → ℕ)}
    (hS : S ⊆ smirnovOccupancies k 1 k) :
    S.filter (IsFordCapped M) = S := by
  ext c
  simp only [Finset.mem_filter]
  constructor
  · exact And.left
  · intro hc
    exact ⟨hc, smirnovOccupancy_one_isFordCapped hM (hS hc)⟩

/-- Imposing Ford's cap after the prefix-energy cutoff changes nothing. -/
theorem fixedLowerRestrictedOccupancies_eq_energy
    {M k : ℕ} (hM : 1 ≤ M) (T : ℝ) :
    fixedLowerRestrictedOccupancies M k T =
      fixedLowerEnergyOccupancies k T := by
  ext c
  rw [mem_fixedLowerRestrictedOccupancies]
  constructor
  · intro hc
    exact mem_fixedLowerEnergyOccupancies.mpr ⟨hc.1, hc.2.1⟩
  · intro hc
    have hcData := mem_fixedLowerEnergyOccupancies.mp hc
    exact ⟨hcData.1, hcData.2,
      smirnovOccupancy_one_isFordCapped hM hcData.1⟩

theorem fixedLowerRestrictedMass_eq_energy
    {M k : ℕ} (hM : 1 ≤ M) (T : ℝ) :
    fixedLowerRestrictedMass M k T = fixedLowerEnergyMass k T := by
  rw [fixedLowerRestrictedMass, fixedLowerEnergyMass,
    fixedLowerRestrictedOccupancies_eq_energy hM T]

/-- Closed cap-and-Markov assembly: in the actual one-slack family the
only loss is the energy tail. -/
theorem fixedLowerRestrictedMass_lower_of_moment
    {M k : ℕ} (hM : 1 ≤ M) {T L A : ℝ} (hT : 0 < T)
    (hmass : L ≤ smirnovOccupancyMass k 1 k)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤ A) :
    L - A / T ≤ fixedLowerRestrictedMass M k T := by
  rw [fixedLowerRestrictedMass_eq_energy hM T]
  exact fixedLowerEnergyMass_lower_of_moment hT hmass hmoment

/-- Numerical Markov corollary at the natural cutoff `2*C`: a first-moment
bound by `C` times Ford's volume scale leaves at least half that scale. -/
theorem fixedLowerRestrictedMass_half_scale_of_moment
    {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) {C : ℝ} (hC : 0 < C)
    (hmoment : fixedLowerPrefixEnergyMoment k ≤
      C * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))) :
    (1 / 2 : ℝ) * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerRestrictedMass M k (2 * C) := by
  let L : ℝ := (k : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hlower :
      L - (C * L) / (2 * C) ≤ fixedLowerRestrictedMass M k (2 * C) :=
    fixedLowerRestrictedMass_lower_of_moment hM (mul_pos (by norm_num) hC)
      (by simpa [L] using smirnovOccupancyMass_one_lower hk)
      (by simpa [L] using hmoment)
  have hidentity : L - (C * L) / (2 * C) = (1 / 2 : ℝ) * L := by
    field_simp [hC.ne']
    ring
  rw [hidentity] at hlower
  simpa [L] using hlower

end Erdos446

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceBadPrimeCount

/-! # Genuine conditioned tuple distributions, including the bad-prime fallback -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem residueAvoidanceIndicator_nonneg (S : Finset ℕ) (N : Finset ℤ)
    (a : ResidueAssignment S) : 0 ≤ residueAvoidanceIndicator S N a := by
  unfold residueAvoidanceIndicator
  split_ifs <;> norm_num

theorem residueAvoidanceIndicator_le_one (S : Finset ℕ) (N : Finset ℤ)
    (a : ResidueAssignment S) : residueAvoidanceIndicator S N a ≤ 1 := by
  unfold residueAvoidanceIndicator
  split_ifs <;> norm_num

theorem SourceProbabilityData.tupleSurvivalMass_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) :
    0 ≤ D.tupleSurvivalMass S p a := by
  exact Finset.sum_nonneg fun n _hn => mul_nonneg (D.mass_nonneg p hp n)
    (residueAvoidanceIndicator_nonneg S _ a)

theorem SourceProbabilityData.tupleSurvivalMass_le_one {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) :
    D.tupleSurvivalMass S p a ≤ 1 := by
  rw [← D.mass_sum_one p hp]
  apply Finset.sum_le_sum
  intro n _hn
  exact mul_le_of_le_one_right (D.mass_nonneg p hp n) (residueAvoidanceIndicator_le_one S _ a)

theorem SourceProbabilityData.good_tupleSurvivalMass_lower {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : ResidueAssignment S) {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    (hgood : p ∉ D.badTuplePrimes S a) (hL : 2 ≤ Real.log (x : ℝ)) :
    residueSieveDensity S ^ D.dimension / 2 ≤ D.tupleSurvivalMass S p a := by
  classical
  have hσ := residueSieveDensity_pos (fun q hq => (hS q hq).one_lt)
  have hM := pow_pos hσ D.dimension
  have herror : |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1| ≤
      1 / Real.log (x : ℝ) ^ 3 := by
    apply le_of_not_gt
    intro hbad
    exact hgood (Finset.mem_filter.mpr ⟨hp, hbad⟩)
  have hr : 1 / Real.log (x : ℝ) ^ 3 ≤ (1 / 2 : ℝ) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3
    apply (div_le_iff₀ (by positivity : 0 < Real.log (x : ℝ) ^ 3)).mpr
    norm_num at hpow
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension := by
    linarith [(abs_le.mp herror).1]
  have h := (le_div_iff₀ hM).mp hhalf
  linarith

open scoped Classical in
def SourceProbabilityData.conditionedTupleMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    (p : ℕ) (n : ℤ) : ℝ :=
  if p ∈ D.badTuplePrimes S a then (if n = 0 then 1 else 0)
  else D.mass p n * residueAvoidanceIndicator S (D.residueTuple p n) a /
    D.tupleSurvivalMass S p a

theorem SourceProbabilityData.conditionedTupleMass_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (n : ℤ) :
    0 ≤ D.conditionedTupleMass S a p n := by
  classical
  unfold conditionedTupleMass
  split_ifs
  · norm_num
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (D.mass_nonneg p hp n)
      (residueAvoidanceIndicator_nonneg S _ a)) (D.tupleSurvivalMass_nonneg S a hp)

theorem SourceProbabilityData.conditionedTupleMass_eq_normalization {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hgood : p ∉ D.badTuplePrimes S a)
    (n : integerWeightWindow (sourceIntervalLength c x)) :
    D.conditionedTupleMass S a p n =
      normalizeFiniteWeight (fun m : integerWeightWindow (sourceIntervalLength c x) =>
        D.mass p m * residueAvoidanceIndicator S (D.residueTuple p m) a) n := by
  rw [conditionedTupleMass, if_neg hgood]
  simp only [normalizeFiniteWeight, tupleSurvivalMass]
  congr 1
  exact (Finset.sum_coe_sort (integerWeightWindow (sourceIntervalLength c x))
    (fun m : ℤ => D.mass p m * residueAvoidanceIndicator S (D.residueTuple p m) a)).symm

theorem SourceProbabilityData.conditionedTupleMass_sum_one {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : ResidueAssignment S) {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    (hL : 2 ≤ Real.log (x : ℝ)) (hy : 0 ≤ sourceIntervalLength c x) :
    (∑ n ∈ integerWeightWindow (sourceIntervalLength c x), D.conditionedTupleMass S a p n) = 1 := by
  classical
  by_cases hbad : p ∈ D.badTuplePrimes S a
  · have hzero : (0 : ℤ) ∈ integerWeightWindow (sourceIntervalLength c x) :=
      (mem_integerWeightWindow _ _).mpr (by simpa using hy)
    simp only [conditionedTupleMass, if_pos hbad, Finset.sum_ite_eq', if_pos hzero]
  · have hσ := residueSieveDensity_pos (fun q hq => (hS q hq).one_lt)
    have hlower := D.good_tupleSurvivalMass_lower hS a hp hbad hL
    have hpos : 0 < D.tupleSurvivalMass S p a :=
      (by positivity : 0 < residueSieveDensity S ^ D.dimension / 2).trans_le hlower
    simp only [conditionedTupleMass, if_neg hbad, ← Finset.sum_div]
    exact div_self hpos.ne'

theorem SourceProbabilityData.conditionedTupleMass_zero_of_outside {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    (hy : 0 ≤ sourceIntervalLength c x) {n : ℤ} (hn : sourceIntervalLength c x < |(n : ℝ)|) :
    D.conditionedTupleMass S a p n = 0 := by
  classical
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hn
    linarith
  simp only [conditionedTupleMass, if_neg hn0, D.mass_support p hp n hn,
    zero_mul, zero_div, ite_self]

theorem SourceProbabilityData.conditionedTupleMass_zero_of_not_survives {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hgood : p ∉ D.badTuplePrimes S a) {n : ℤ}
    (hn : ¬residueAssignmentAvoids S (D.residueTuple p n) a) :
    D.conditionedTupleMass S a p n = 0 := by
  simp only [conditionedTupleMass, if_neg hgood, residueAvoidanceIndicator, if_neg hn,
    mul_zero, zero_div]

theorem SourceProbabilityData.conditionedTupleMass_atom_bound {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (a : ResidueAssignment S) {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x)
    (hgood : p ∉ D.badTuplePrimes S a) (hL : 2 ≤ Real.log (x : ℝ)) (n : ℤ) :
    D.conditionedTupleMass S a p n ≤
      2 * (x : ℝ) ^ (-2 / 3 + e : ℝ) / residueSieveDensity S ^ D.dimension := by
  have hσ := residueSieveDensity_pos (fun q hq => (hS q hq).one_lt)
  have hM := pow_pos hσ D.dimension
  have hlower := D.good_tupleSurvivalMass_lower hS a hp hgood hL
  have hnum : D.mass p n * residueAvoidanceIndicator S (D.residueTuple p n) a ≤
      (x : ℝ) ^ (-2 / 3 + e : ℝ) :=
    (mul_le_of_le_one_right (D.mass_nonneg p hp n)
      (residueAvoidanceIndicator_le_one S _ a)).trans (D.mass_atom_bound p hp n)
  rw [conditionedTupleMass, if_neg hgood]
  calc
    _ ≤ (x : ℝ) ^ (-2 / 3 + e : ℝ) / (residueSieveDensity S ^ D.dimension / 2) :=
      div_le_div₀ (Real.rpow_nonneg (Nat.cast_nonneg x) _)
        hnum (by positivity) hlower
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.SourceProbabilityData.conditionedTupleMass_sum_one
#print axioms Erdos4b.FGKMT.SourceProbabilityData.conditionedTupleMass_atom_bound

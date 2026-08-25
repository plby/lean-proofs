import ErdosProblems.Erdos67.PrimeEstimates

/-!
# A global exponentially weighted prime tail

The first-square-block estimate in `PrimeEstimates` is iterated over the
blocks `(y^(j+1), y^(j+2)]`.  On the `j`-th block the original weight
`p^(-1/log y)` is at most `exp (-(j+1))`, hence at most `2^(-(j+1))`.
The resulting geometric series removes the upper cutoff completely.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos67.PrimeEstimates

noncomputable section

/-- The reciprocal prime mass of any interval contained in `(Z,Z^2]` is
bounded by the same absolute Mertens constant as the first square block. -/
theorem reciprocalPrimeInterval_le_log_two_add
    {Z U : ℕ} (hZ : 2 ≤ Z) (hZU : Z ≤ U) (hU : U ≤ Z ^ 2) :
    reciprocalPrimeInterval Z U ≤ Real.log 2 + 2 * mertensBound := by
  have hmass := reciprocalPrimeInterval_le_log_log_sub_add hZ hZU
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hZsqpos : (0 : ℝ) < (Z ^ 2 : ℕ) := by positivity
  have hlogUle : Real.log (U : ℝ) ≤ Real.log ((Z ^ 2 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hUpos)
      (by simpa only [Set.mem_Ioi] using hZsqpos)
      (by exact_mod_cast hU)
  have hlogUpos : 0 < Real.log (U : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hlogZsqpos : 0 < Real.log ((Z ^ 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z ^ 2 by omega))
  have hloglogUle :
      Real.log (Real.log (U : ℝ)) ≤
        Real.log (Real.log ((Z ^ 2 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hlogUpos)
      (by simpa only [Set.mem_Ioi] using hlogZsqpos) hlogUle
  have hsquare :
      Real.log (Real.log ((Z ^ 2 : ℕ) : ℝ)) -
          Real.log (Real.log (Z : ℝ)) = Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    rw [Real.log_mul (by norm_num) hlogZ.ne']
    ring
  calc
    reciprocalPrimeInterval Z U ≤
        Real.log (Real.log (U : ℝ)) -
          Real.log (Real.log (Z : ℝ)) + 2 * mertensBound := hmass
    _ ≤ Real.log (Real.log ((Z ^ 2 : ℕ) : ℝ)) -
          Real.log (Real.log (Z : ℝ)) + 2 * mertensBound := by linarith
    _ = Real.log 2 + 2 * mertensBound := by rw [hsquare]

/-- The fixed summand in `expWeightedPrimeTail y U`. -/
def expWeightedPrimeTerm (y p : ℕ) : ℝ :=
  (p : ℝ) ^ (-(1 : ℝ) - (Real.log (y : ℝ))⁻¹)

theorem expWeightedPrimeTail_eq_sum_term (y U : ℕ) :
    expWeightedPrimeTail y U =
      ∑ p ∈ primesInInterval y U, expWeightedPrimeTerm y p := rfl

theorem expWeightedPrimeTerm_nonneg (y p : ℕ) :
    0 ≤ expWeightedPrimeTerm y p := Real.rpow_nonneg (by positivity) _

/-- Splitting a weighted prime interval at an intermediate cutoff. -/
theorem expWeightedPrimeTail_split
    {y A B : ℕ} (hyA : y ≤ A) (hAB : A ≤ B) :
    expWeightedPrimeTail y B = expWeightedPrimeTail y A +
      ∑ p ∈ primesInInterval A B, expWeightedPrimeTerm y p := by
  classical
  have hset : primesInInterval y B =
      primesInInterval y A ∪ primesInInterval A B := by
    ext p
    simp only [mem_primesInInterval, Finset.mem_union]
    constructor
    · intro hp
      by_cases hpA : p ≤ A
      · exact Or.inl ⟨hp.1, hpA, hp.2.2⟩
      · exact Or.inr ⟨by omega, hp.2.1, hp.2.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1, hp.2.1.trans hAB, hp.2.2⟩
      · exact ⟨lt_of_le_of_lt hyA hp.1, hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (primesInInterval y A) (primesInInterval A B) := by
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have hle := (mem_primesInInterval.mp hpa).2.1
    have hlt := (mem_primesInInterval.mp hpb).1
    omega
  rw [expWeightedPrimeTail_eq_sum_term,
    expWeightedPrimeTail_eq_sum_term, hset, Finset.sum_union hdisj]

private theorem expWeightedPrimeTerm_le_geometric
    {y j p : ℕ} (hy : 2 ≤ y) (hp : y ^ (j + 1) < p) :
    expWeightedPrimeTerm y p ≤
      (1 / 2 : ℝ) ^ (j + 1) * (p : ℝ)⁻¹ := by
  have hyR : (0 : ℝ) < y := by positivity
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast Nat.zero_lt_of_lt hp
  have hpowR : (y : ℝ) ^ (j + 1) ≤ (p : ℝ) := by
    exact_mod_cast hp.le
  have hlogp :
      ((j + 1 : ℕ) : ℝ) * Real.log (y : ℝ) ≤ Real.log (p : ℝ) := by
    have hlog := Real.strictMonoOn_log.monotoneOn
      (show (y : ℝ) ^ (j + 1) ∈ Set.Ioi 0 by
        change 0 < (y : ℝ) ^ (j + 1)
        exact pow_pos hyR _)
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR) hpowR
    rw [Real.log_pow] at hlog
    exact hlog
  have hexpWeight :
      (p : ℝ) ^ (-(Real.log (y : ℝ))⁻¹) ≤
        Real.exp (-((j + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_def_of_pos hpR]
    apply Real.exp_le_exp.mpr
    have hinv : 0 < (Real.log (y : ℝ))⁻¹ := inv_pos.mpr hlogy
    calc
      Real.log (p : ℝ) * (-(Real.log (y : ℝ))⁻¹) ≤
          (((j + 1 : ℕ) : ℝ) * Real.log (y : ℝ)) *
            (-(Real.log (y : ℝ))⁻¹) :=
        mul_le_mul_of_nonpos_right hlogp (neg_nonpos.mpr hinv.le)
      _ = -((j + 1 : ℕ) : ℝ) := by field_simp
  have hhalf : Real.exp (-((j + 1 : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
    rw [show -((j + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * (-1 : ℝ) by ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_neg_one_lt_half.le _
  rw [expWeightedPrimeTerm, show -(1 : ℝ) - (Real.log (y : ℝ))⁻¹ =
      (-1 : ℝ) + (-(Real.log (y : ℝ))⁻¹) by ring,
    Real.rpow_add hpR, Real.rpow_neg_one]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right (hexpWeight.trans hhalf) (inv_nonneg.mpr hpR.le)

private theorem block_le_geometric
    {y j : ℕ} (hy : 2 ≤ y) :
    (∑ p ∈ primesInInterval (y ^ (j + 1)) (y ^ (j + 2)),
        expWeightedPrimeTerm y p) ≤
      (1 / 2 : ℝ) ^ (j + 1) *
        (Real.log 2 + 2 * mertensBound) := by
  have hz : 2 ≤ y ^ (j + 1) := by
    calc 2 ≤ y := hy
         _ ≤ y ^ (j + 1) := by
           exact Nat.le_pow (by omega)
  have hmass : reciprocalPrimeInterval (y ^ (j + 1)) (y ^ (j + 2)) ≤
      Real.log 2 + 2 * mertensBound := by
    apply reciprocalPrimeInterval_le_log_two_add hz
    · exact Nat.pow_le_pow_right (by omega : 0 < y) (by omega)
    · rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega : 0 < y) (by omega)
  calc
    (∑ p ∈ primesInInterval (y ^ (j + 1)) (y ^ (j + 2)),
        expWeightedPrimeTerm y p) ≤
        ∑ p ∈ primesInInterval (y ^ (j + 1)) (y ^ (j + 2)),
          (1 / 2 : ℝ) ^ (j + 1) * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact expWeightedPrimeTerm_le_geometric hy
        (mem_primesInInterval.mp hp).1
    _ = (1 / 2 : ℝ) ^ (j + 1) *
        reciprocalPrimeInterval (y ^ (j + 1)) (y ^ (j + 2)) := by
      rw [← Finset.mul_sum]
      rfl
    _ ≤ (1 / 2 : ℝ) ^ (j + 1) *
        (Real.log 2 + 2 * mertensBound) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)

private theorem geometric_shifted_sum_le_one (K : ℕ) :
    (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1)) ≤ 1 := by
  have hstrong :
      (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1)) =
        1 - (1 / 2 : ℝ) ^ K := by
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  rw [hstrong]
  exact sub_le_self _ (by positivity)

private theorem expWeightedPrimeTail_power_le
    {y : ℕ} (hy : 2 ≤ y) (K : ℕ) :
    expWeightedPrimeTail y (y ^ (K + 1)) ≤
      Real.log 2 + 2 * mertensBound := by
  have hC : 0 ≤ Real.log 2 + 2 * mertensBound :=
    add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg (by norm_num) mertensBound_nonneg)
  have hsum :
      expWeightedPrimeTail y (y ^ (K + 1)) ≤
        (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1)) *
          (Real.log 2 + 2 * mertensBound) := by
    induction K with
    | zero => simp [expWeightedPrimeTail, primesInInterval]
    | succ K ih =>
        rw [expWeightedPrimeTail_split
          (show y ≤ y ^ (K + 1) by exact Nat.le_pow (by omega))
          (Nat.pow_le_pow_right (by omega : 0 < y) (by omega))]
        rw [Finset.sum_range_succ, add_mul]
        exact add_le_add ih (block_le_geometric hy)
  calc
    expWeightedPrimeTail y (y ^ (K + 1)) ≤
        (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ (j + 1)) *
          (Real.log 2 + 2 * mertensBound) := hsum
    _ ≤ 1 * (Real.log 2 + 2 * mertensBound) :=
      mul_le_mul_of_nonneg_right (geometric_shifted_sum_le_one K) hC
    _ = Real.log 2 + 2 * mertensBound := one_mul _

/-- Uniform extension of the first-square-block estimate to every finite
upper cutoff.  The constant is independent of both `y` and `U`. -/
theorem expWeightedPrimeTail_le_log_two_add_global
    {y U : ℕ} (hy : 2 ≤ y) (_hyU : y ≤ U) :
    expWeightedPrimeTail y U ≤ Real.log 2 + 2 * mertensBound := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt U (show 1 < y by omega)
  have hKU : U ≤ y ^ (K + 1) := by
    exact hK.le.trans (Nat.pow_le_pow_right (by omega : 0 < y) (by omega))
  have hsubset : primesInInterval y U ⊆ primesInInterval y (y ^ (K + 1)) := by
    intro p hp
    have hpm := mem_primesInInterval.mp hp
    exact mem_primesInInterval.mpr ⟨hpm.1, hpm.2.1.trans hKU, hpm.2.2⟩
  calc
    expWeightedPrimeTail y U ≤ expWeightedPrimeTail y (y ^ (K + 1)) := by
      rw [expWeightedPrimeTail_eq_sum_term,
        expWeightedPrimeTail_eq_sum_term]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ expWeightedPrimeTerm_nonneg _ _)
    _ ≤ Real.log 2 + 2 * mertensBound :=
      expWeightedPrimeTail_power_le hy K

end

end Erdos67.PrimeEstimates

#print axioms Erdos67.PrimeEstimates.expWeightedPrimeTail_le_log_two_add_global

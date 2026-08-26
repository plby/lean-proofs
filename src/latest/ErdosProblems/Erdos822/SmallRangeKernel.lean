/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallRangeAnchor

/-! # The unconditional small-range weighted collision-kernel estimate -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_smallWeightedKernel_raw_bound {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ U : ℕ, Nat.log 2 N ≤ U →
      (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
        smallWeightedCommonDivisorKernel N m m' 2 U) ≤
          K * (N ^ 60 : ℕ) * Real.log (N : ℝ) ^ 2 := by
  obtain ⟨K, hK, hanchor⟩ := exists_eventually_smallGcdSingularAnchor_sum_bound hS C
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hanchor, eventually_sum_inv_gilCofactors_le_harmonic S C,
    eventually_ge_atTop 4] with N hanchor hmass hN
  intro U hLU
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hH : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log N
    linarith only [h, hlogN]
  have hpoint (m m' : ℕ) (hne : m' ≠ m) :
      smallWeightedCommonDivisorKernel N m m' 2 U =
        (N ^ 60 : ℕ) * (smallGcdSingularAnchorTerm N m m' U / m') := by
    unfold smallWeightedCommonDivisorKernel smallGcdSingularAnchorTerm
    have hne' : m ≠ m' := Ne.symm hne
    by_cases hcond : (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ shiftedCoefficientGcd m m' ≤ N ^ 3
    · rw [if_pos hcond, if_pos (And.intro hne' hcond)]
      push_cast
      ring
    · simp [hcond, hne']
  have hsum : (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
      smallGcdSingularAnchorTerm N m m' U / m') ≤ 2 * K * Real.log (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ gilCofactors N S C, ∑ m' ∈ gilCofactors N S C,
          smallGcdSingularAnchorTerm N m m' U / m' := by
        apply Finset.sum_le_sum
        intro m hm
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun m' hm' hnot ↦ div_nonneg (smallGcdSingularAnchorTerm_nonneg N m m' U) (by positivity))
      _ = ∑ m' ∈ gilCofactors N S C,
          (∑ m ∈ gilCofactors N S C, smallGcdSingularAnchorTerm N m m' U) / m' := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_div]
      _ ≤ ∑ m' ∈ gilCofactors N S C, (K * Real.log (N : ℝ)) / m' :=
        Finset.sum_le_sum fun m' hm' ↦ div_le_div_of_nonneg_right (hanchor m' U hm' hLU) (by positivity)
      _ = (K * Real.log (N : ℝ)) * ∑ m' ∈ gilCofactors N S C, (1 : ℝ) / m' := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m' hm'
        ring
      _ ≤ (K * Real.log (N : ℝ)) * (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmass.trans hH) (by positivity)
      _ = _ := by ring
  calc
    _ = (N ^ 60 : ℕ) *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          smallGcdSingularAnchorTerm N m m' U / m') := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro m' hm'
      exact hpoint m m' (Finset.mem_erase.mp hm').1
    _ ≤ (N ^ 60 : ℕ) * (2 * K * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem eventually_natLog_le_slowSieveCutoff {T : ℕ} (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, Nat.log 2 N ≤ Nat.nthRoot (4 * T) N := by
  filter_upwards [eventually_slowCutoff_log_cube_div_le_one hT,
    eventually_nthRoot_ge (4 * T) 2 (by omega), eventually_ge_atTop 2] with N hsmall hroot hN
  have hrootR : (0 : ℝ) < Nat.nthRoot (4 * T) N := by exact_mod_cast (by omega : 0 < Nat.nthRoot (4 * T) N)
  have hlog := natLog_two_le_two_realLog (by omega : 1 ≤ N)
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hcube : 2 * Real.log (N : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 3 := by
    nlinarith only [sq_nonneg (Real.log (N : ℝ)), pow_nonneg hlog0 3]
  have hbound := (div_le_iff₀ hrootR).mp hsmall
  have hfinal : (Nat.log 2 N : ℝ) ≤ Nat.nthRoot (4 * T) N := by
    linarith only [hlog, hcube, hbound]
  exact_mod_cast hfinal

theorem exists_eventually_smallWeightedCommonDivisorKernel_bound
    {S T : ℕ} (hS : 0 < S) (hT : 0 < T) (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (Real.log (2 : ℝ) / Real.log (Nat.nthRoot (4 * T) N : ℝ)) ^ 2 *
        (∑ m ∈ gilCofactors N S C, ∑ m' ∈ (gilCofactors N S C).erase m,
          smallWeightedCommonDivisorKernel N m m' 2 (Nat.nthRoot (4 * T) N)) ≤ K * (N ^ 60 : ℕ) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_smallWeightedKernel_raw_bound hS C
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨K * Real.log (2 : ℝ) ^ 2 * (8 * (T : ℝ)) ^ 2, by positivity, ?_⟩
  filter_upwards [hbound, eventually_natLog_le_slowSieveCutoff hT,
    eventually_nthRoot_ge (4 * T) 2 (by omega), eventually_ge_atTop 2] with N hbound hLU hroot hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlogU : 0 < Real.log (Nat.nthRoot (4 * T) N : ℝ) := Real.log_pos
    (by exact_mod_cast (by omega : 1 < Nat.nthRoot (4 * T) N))
  have hratio := log_div_log_slowSieveCutoff_le hT hroot
  have hsquare := pow_le_pow_left₀ (div_nonneg hlogN hlogU.le) hratio 2
  calc
    _ ≤ (Real.log (2 : ℝ) / Real.log (Nat.nthRoot (4 * T) N : ℝ)) ^ 2 *
        (K * (N ^ 60 : ℕ) * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound _ hLU) (sq_nonneg _)
    _ = (K * Real.log (2 : ℝ) ^ 2 *
        (Real.log (N : ℝ) / Real.log (Nat.nthRoot (4 * T) N : ℝ)) ^ 2) * (N ^ 60 : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare (by positivity)) (by positivity)

#print axioms exists_eventually_smallWeightedCommonDivisorKernel_bound

end Erdos822

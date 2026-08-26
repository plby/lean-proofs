/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.B1B5Mass
import ErdosProblems.Erdos822.SlowCutoffAsymptotic

/-! # Removing the truncation from B5 -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

noncomputable def primeDivisorReciprocalMass (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (1 : ℝ) / p

theorem primeDivisorReciprocalMass_shifted_le_trunc_add_tail
    {m U : ℕ} (hm : 0 < m) (hU : 2 ≤ U) :
    primeDivisorReciprocalMass (shiftedTotient m) ≤
      1 + shiftedTotientReciprocalMass m 2 U +
        ∑ p ∈ primeFactorsAbove (shiftedTotient m) U, (1 : ℝ) / p := by
  let n := shiftedTotient m
  have hn : n ≠ 0 := by dsimp [n, shiftedTotient]; omega
  have hsmall : (∑ p ∈ n.primeFactors.filter (· ≤ 2), (1 : ℝ) / p) ≤ 1 := by
    have hsub : n.primeFactors.filter (· ≤ 2) ⊆ {2} := by
      intro p hp
      have h := Finset.mem_filter.mp hp
      have hp2 := (Nat.prime_of_mem_primeFactors h.1).two_le
      simp only [Finset.mem_singleton]
      omega
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun p : ℕ ↦ (1 : ℝ) / p) (fun p hp hnot ↦ by positivity)
    norm_num at h ⊢
    linarith
  have hmiddle : n.primeFactors.filter (fun p ↦ 2 < p ∧ p ≤ U) =
      (Erdos851.sievePrimes 2 U).filter (· ∣ n) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Erdos851.mem_sievePrimes]
    tauto
  have hsplit : primeDivisorReciprocalMass n =
      (∑ p ∈ n.primeFactors.filter (· ≤ 2), (1 : ℝ) / p) +
      (∑ p ∈ n.primeFactors.filter (fun p ↦ 2 < p ∧ p ≤ U), (1 : ℝ) / p) +
      (∑ p ∈ primeFactorsAbove n U, (1 : ℝ) / p) := by
    unfold primeDivisorReciprocalMass primeFactorsAbove
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h2 : p ≤ 2
    · have hpU := h2.trans hU
      simp [h2, hpU, not_lt_of_ge h2, not_lt_of_ge hpU]
    · by_cases hpU : p ≤ U
      · simp [h2, hpU, lt_of_not_ge h2, not_lt_of_ge hpU]
      · simp [h2, hpU, lt_of_not_ge h2, lt_of_not_ge hpU]
  have hmidsum : (∑ p ∈ n.primeFactors.filter (fun p ↦ 2 < p ∧ p ≤ U), (1 : ℝ) / p) =
      shiftedTotientReciprocalMass m 2 U := by
    rw [hmiddle, Finset.sum_filter]
    rfl
  rw [hsplit, hmidsum]
  linarith only [hsmall]

theorem natLog_shifted_oddRaw_le_sixty_log {N m : ℕ}
    (hN : 4 ≤ N) (hm : m ∈ oddRawCofactors N) :
    (Nat.log 2 (shiftedTotient m) : ℝ) ≤ 60 * Real.log (N : ℝ) := by
  have hmpos := oddRawCofactors_pos hm
  have hspos : 0 < shiftedTotient m := by dsimp [shiftedTotient]; omega
  have hs := (shiftedTotient_le_two_mul m).trans
    (Nat.mul_le_mul_left 2 (oddRawCofactors_le_pow_twenty_eight hm))
  have hpower : (2 : ℝ) ^ Nat.log 2 (shiftedTotient m) ≤ shiftedTotient m := by
    exact_mod_cast Nat.pow_log_le_self 2 hspos.ne'
  have hlogpower := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 (shiftedTotient m)) hpower
  rw [Real.log_pow] at hlogpower
  have hlogshift : Real.log (shiftedTotient m : ℝ) ≤ Real.log 2 + 28 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast hspos) (show (shiftedTotient m : ℝ) ≤ 2 * (N : ℝ) ^ 28 by exact_mod_cast hs)
    simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (N : ℝ) ^ 28 ≠ 0),
      Real.log_pow, Nat.cast_ofNat] using h
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hhalf : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hone : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hK := Nat.cast_nonneg (α := ℝ) (Nat.log 2 (shiftedTotient m))
  nlinarith only [hlogpower, hlogshift, hlogN, hhalf, hone, hK]

theorem eventually_oddRaw_shifted_prime_tail_le_one {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ oddRawCofactors N,
      (∑ p ∈ primeFactorsAbove (shiftedTotient m) (Nat.nthRoot (4 * S) N), (1 : ℝ) / p) ≤ 1 := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_slowCutoff_log_cube_div_le_one hS,
    eventually_nthRoot_ge (4 * S) 2 (by omega),
    hlog.eventually_ge_atTop 60, eventually_ge_atTop 4] with N hcub hU hlogN hN
  intro m hm
  have hspos : 0 < shiftedTotient m := by
    have := oddRawCofactors_pos hm
    dsimp [shiftedTotient]
    omega
  have hlogsmall : 60 * Real.log (N : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 3 := by
    nlinarith only [hlogN, sq_nonneg (Real.log (N : ℝ))]
  calc
    _ ≤ (Nat.log 2 (shiftedTotient m) : ℝ) / Nat.nthRoot (4 * S) N :=
      sum_inv_primeFactorsAbove_le_log_div hspos (by omega)
    _ ≤ (60 * Real.log (N : ℝ)) / Nat.nthRoot (4 * S) N :=
      div_le_div_of_nonneg_right (natLog_shifted_oddRaw_le_sixty_log hN hm) (by positivity)
    _ ≤ (1 + Real.log (N : ℝ)) ^ 3 / Nat.nthRoot (4 * S) N :=
      div_le_div_of_nonneg_right hlogsmall (by positivity)
    _ ≤ 1 := hcub

theorem eventually_b1B5Cofactors_full_primeMass_le {S : ℕ} (hS : 0 < S) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ b1B5Cofactors N S C,
      primeDivisorReciprocalMass (shiftedTotient m) ≤ C + 2 := by
  filter_upwards [eventually_oddRaw_shifted_prime_tail_le_one hS,
    eventually_nthRoot_ge (4 * S) 2 (by omega)] with N htail hU
  intro m hm
  have hmraw := gcdSmoothB1Cofactors_subset_oddRaw N (b1B5Cofactors_subset_gcd N S C hm)
  have hsplit := primeDivisorReciprocalMass_shifted_le_trunc_add_tail (oddRawCofactors_pos hmraw) hU
  have htrunc := (Finset.mem_filter.mp hm).2
  have htail' := htail m hmraw
  linarith only [hsplit, htrunc, htail']

#print axioms eventually_b1B5Cofactors_full_primeMass_le

end Erdos822

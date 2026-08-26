/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.GILPartBounds
import ErdosProblems.Erdos822.CofactorRepresentation
import ErdosProblems.Erdos822.PrimeReciprocalUpper

/-! # Subpower and rough-part bounds for the medium range -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem roughPart_eq_self_of_primeFactors_gt {n y : ℕ} (hn : n ≠ 0)
    (hrough : ∀ p ∈ n.primeFactors, y < p) : roughPart n y = n := by
  apply Nat.eq_of_factorization_eq (roughPart_ne_zero n y) hn
  rw [factorization_roughPart]
  intro p
  simp only [roughFactorization, Finsupp.filter_apply]
  split_ifs with hp
  · rfl
  · symm
    apply not_ne_iff.mp
    intro hnot
    have hmem : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hnot
    exact hp (hrough p hmem)

theorem roughPart_eq_self_of_dvd_roughPart {n d y : ℕ}
    (hd : d ∣ roughPart n y) : roughPart d y = d := by
  have hdne : d ≠ 0 := by
    intro hz
    subst d
    exact roughPart_ne_zero n y (by simpa using hd)
  apply roughPart_eq_self_of_primeFactors_gt hdne
  intro p hp
  exact (mem_primeFactors_roughPart_iff.mp
    (Nat.primeFactors_mono hd (roughPart_ne_zero n y) hp)).2

theorem gilCofactors_subset_squarefreeLargeGcdFree (N S : ℕ) (C : ℝ) :
    gilCofactors N S C ⊆ squarefreeLargeGcdFreeOddCofactors N (b1Cutoff N) := by
  intro m hm
  exact mem_squarefreeLargeGcdFreeOddCofactors_iff.mpr
    ⟨gilCofactors_largeGcdFree hm, gilCofactors_largeSquarefree hm⟩

theorem eventually_five_pow_roughPart_card_pow_le (a : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, 0 < h → h ≤ 2 * N ^ 28 →
      (5 ^ (roughPart h (b1Cutoff N)).primeFactors.card) ^ a ≤ N := by
  filter_upwards [tendsto_b1Cutoff_atTop.eventually_ge_atTop ((5 ^ a) ^ 30),
    eventually_ge_atTop 2] with N hy hN
  intro h hh hhN
  have hbound := pow_primeFactors_card_le_of_prime_lower_bound
    (b := 5 ^ a) (Nat.pos_of_ne_zero (roughPart_ne_zero h (b1Cutoff N))) hN
    ((Nat.le_of_dvd hh (roughPart_dvd h (b1Cutoff N))).trans hhN)
    (fun p hp ↦ hy.trans (mem_primeFactors_roughPart_iff.mp hp).2.le)
  simpa only [← pow_mul, Nat.mul_comm] using hbound

theorem eventually_harmonic_pow_le_natCast (a : ℕ) :
    ∀ᶠ N : ℕ in atTop, (harmonic N : ℝ) ^ a ≤ N := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_const_mul_log_pow_div_natCast_le_one (2 ^ a) a,
    hlog, eventually_ge_atTop 1] with N hbound hlogN hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log N
    dsimp only [Function.comp_apply] at hlogN
    linarith only [h, hlogN]
  have hbound' := (div_le_iff₀ hNR).mp hbound
  calc
    _ ≤ (2 * Real.log (N : ℝ)) ^ a := pow_le_pow_left₀
      (by
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        exact Finset.sum_nonneg fun j hj ↦ by positivity) hH a
    _ = 2 ^ a * Real.log (N : ℝ) ^ a := mul_pow _ _ _
    _ ≤ N := by simpa using hbound'

theorem eventually_gil_roughWeight_mul_harmonic_four_le (S : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ gilCofactors N S C,
      (5 : ℝ) ^ (roughPart (shiftedTotient m) (b1Cutoff N)).primeFactors.card *
        (harmonic N : ℝ) ^ 4 ≤ N := by
  filter_upwards [eventually_five_pow_roughPart_card_pow_le 2,
    eventually_harmonic_pow_le_natCast 8] with N hW hH
  intro m hm
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  have hmpos := oddRawCofactors_pos hmraw
  have hspos : 0 < shiftedTotient m := by dsimp [shiftedTotient]; omega
  have hsle := (shiftedTotient_le_two_mul m).trans
    (Nat.mul_le_mul_left 2 (oddRawCofactors_le_pow_twenty_eight hmraw))
  have hW' : ((5 : ℝ) ^ (roughPart (shiftedTotient m) (b1Cutoff N)).primeFactors.card) ^ 2 ≤ N :=
    by exact_mod_cast hW _ hspos hsle
  have hprod := mul_le_mul hW' hH (by positivity) (by positivity : (0 : ℝ) ≤ N)
  have hnonneg : 0 ≤ (5 : ℝ) ^ (roughPart (shiftedTotient m) (b1Cutoff N)).primeFactors.card *
      (harmonic N : ℝ) ^ 4 := by positivity
  nlinarith only [hprod, hnonneg, Nat.cast_nonneg (α := ℝ) N]

#print axioms eventually_gil_roughWeight_mul_harmonic_four_le

end Erdos822

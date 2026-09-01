import ErdosProblems.Erdos697.Erdos697PrimeHarmonic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Omega bounds for Erdős Problem 1217

This file supplies the elementary number-theoretic estimates used in the
second-moment argument.  In particular, strict divisibility increases the
number of prime factors (with multiplicity), and the model stationary weight
`1 / (n * log n)` contracts on taking a nontrivial multiple.
-/

open scoped BigOperators ArithmeticFunction.Omega
open Filter

namespace Erdos1217.OmegaBound

noncomputable section

/-- Strict divisibility between positive naturals strictly increases the
number of prime factors counted with multiplicity. -/
theorem cardFactors_lt_of_dvd_of_lt {a b : ℕ} (ha : 0 < a)
    (hab : a ∣ b) (hlt : a < b) : Ω a < Ω b := by
  obtain ⟨c, rfl⟩ := hab
  have hc : 1 < c := by
    by_contra h
    have hc' : c ≤ 1 := Nat.le_of_not_gt h
    interval_cases c <;> simp_all
  have ha0 : a ≠ 0 := ha.ne'
  have hc0 : c ≠ 0 := (Nat.zero_lt_of_lt hc).ne'
  rw [ArithmeticFunction.cardFactors_mul ha0 hc0]
  have : 0 < Ω c :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hc
  omega

/-- Every step of a positive strict divisibility path raises `Ω` by at
least one, so the number of predecessors of its `j`-th vertex is at most the
prime-factor count of that vertex. -/
theorem index_le_cardFactors_of_strictDvdPath
    (u : ℕ → ℕ) (hpos : ∀ i, 0 < u i)
    (hstep : ∀ i, u i ∣ u (i + 1) ∧ u i < u (i + 1)) :
    ∀ j, j ≤ Ω (u j) := by
  intro j
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      have hlt : Ω (u j) < Ω (u (j + 1)) :=
        cardFactors_lt_of_dvd_of_lt (hpos j) (hstep j).1 (hstep j).2
      omega

/-- The model weight `1 / (n log n)` at `d*m` is at most `1/d` times its
value at `m`, when both factors are nontrivial. -/
theorem one_div_mul_log_mul_le {d m : ℕ} (hd : 2 ≤ d) (hm : 2 ≤ m) :
    1 / (((d * m : ℕ) : ℝ) * Real.log ((d * m : ℕ) : ℝ)) ≤
      (1 / (d : ℝ)) * (1 / ((m : ℝ) * Real.log (m : ℝ))) := by
  have hdR : (0 : ℝ) < d := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hdmR : (0 : ℝ) < (d * m : ℕ) := by positivity
  have hlogdm : 0 < Real.log ((d * m : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 4) (Nat.mul_le_mul hd hm))
  have hlogle : Real.log (m : ℝ) ≤ Real.log ((d * m : ℕ) : ℝ) := by
    apply Real.log_le_log hmR
    exact_mod_cast Nat.le_mul_of_pos_left m (Nat.zero_lt_of_lt hd)
  simp only [Nat.cast_mul] at hlogle ⊢
  calc
    1 / ((d : ℝ) * (m : ℝ) * Real.log ((d : ℝ) * (m : ℝ))) =
        (1 / (d : ℝ)) *
          (1 / ((m : ℝ) * Real.log ((d : ℝ) * (m : ℝ)))) := by
      field_simp
    _ ≤ (1 / (d : ℝ)) * (1 / ((m : ℝ) * Real.log (m : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply one_div_le_one_div_of_le (mul_pos hmR hlogm)
      exact mul_le_mul_of_nonneg_left hlogle hmR.le

/-- Nonnegativity of the summand in the weighted Omega moment. -/
theorem omegaLogKernel_nonneg (n : ℕ) :
    0 ≤ (Ω n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ))) := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp
  · have hn2 : 2 ≤ n := by omega
    positivity

/-! ## A finite first moment for `Ω` -/

private theorem cardFactors_eq_sum_prime_power_divisors (n : ℕ) :
    Ω n = ∑ p ∈ n.primeFactors,
      ((Finset.Ico 1 n).filter fun i ↦ p ^ i ∣ n).card := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  rw [Finsupp.sum]
  apply Finset.sum_congr
  · exact Nat.support_factorization n
  · intro p hp
    exact Nat.factorization_eq_card_pow_dvd n
      (Nat.prime_of_mem_primeFactors hp)

private theorem cardFactors_le_prime_power_occurrences
    {X n : ℕ} (hn : n ∈ Finset.Icc 1 X) :
    Ω n ≤ ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
      ∑ i ∈ Finset.Ico 1 X, if p ^ i ∣ n then 1 else 0 := by
  rw [cardFactors_eq_sum_prime_power_divisors]
  have hnData := Finset.mem_Icc.mp hn
  have hpf :
      n.primeFactors ⊆ (Finset.Icc 2 X).filter Nat.Prime := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨hprime.two_le,
          (Nat.le_of_dvd hnData.1
            (Nat.dvd_of_mem_primeFactors hp)).trans hnData.2⟩,
        hprime⟩
  calc
    (∑ p ∈ n.primeFactors,
      ((Finset.Ico 1 n).filter fun i ↦ p ^ i ∣ n).card) ≤
        ∑ p ∈ n.primeFactors,
          ∑ i ∈ Finset.Ico 1 X, if p ^ i ∣ n then 1 else 0 := by
            apply Finset.sum_le_sum
            intro p hp
            rw [Finset.card_eq_sum_ones]
            simp only [Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.Ico_subset_Ico_right hnData.2
            · intro i hi hnot
              split_ifs <;> omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hpf (by
      intro p hp hnot
      exact Finset.sum_nonneg fun i hi ↦ by split_ifs <;> omega)

private theorem sum_cardFactors_le_sum_prime_powers (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, Ω n ≤
      ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        ∑ i ∈ Finset.Ico 1 X, X / (p ^ i) := by
  let Ns := Finset.Icc 1 X
  let Ps := (Finset.Icc 2 X).filter Nat.Prime
  let Is := Finset.Ico 1 X
  have hpoint :
      ∀ n ∈ Ns,
        Ω n ≤
          ∑ p ∈ Ps, ∑ i ∈ Is, if p ^ i ∣ n then 1 else 0 := by
    intro n hn
    exact cardFactors_le_prime_power_occurrences
      (by simpa [Ns] using hn)
  calc
    ∑ n ∈ Ns, Ω n ≤
        ∑ n ∈ Ns,
          ∑ p ∈ Ps, ∑ i ∈ Is, if p ^ i ∣ n then 1 else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ p ∈ Ps,
          ∑ i ∈ Is, ∑ n ∈ Ns, if p ^ i ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Ps, ∑ i ∈ Is, X / (p ^ i) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      have hNs : Ns = Finset.Ioc 0 X := by
        ext n
        simp [Ns]
        omega
      rw [hNs, Finset.sum_boole]
      exact Nat.Ioc_filter_dvd_card_eq_div X (p ^ i)

private theorem sum_inv_prime_powers_le
    {p X : ℕ} (hp : p.Prime) :
    ∑ i ∈ Finset.Ico 1 X, (1 : ℝ) / (p : ℝ) ^ i ≤ 2 / p := by
  have hp0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hp1 : (1 : ℝ) / p < 1 := by
    rw [div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast hp.one_lt
  have hgeom :=
    geom_sum_Ico_le_of_lt_one (m := 1) (n := X) hp0 hp1
  have heq :
      ((1 : ℝ) / p) ^ 1 / (1 - (1 : ℝ) / p) =
        1 / ((p : ℝ) - 1) := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp [hpR]
  have hlast : (1 : ℝ) / ((p : ℝ) - 1) ≤ 2 / p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpminus : (0 : ℝ) < p - 1 := by linarith
    apply (div_le_div_iff₀ hpminus hpR).2
    linarith
  calc
    ∑ i ∈ Finset.Ico 1 X, (1 : ℝ) / (p : ℝ) ^ i =
        ∑ i ∈ Finset.Ico 1 X, ((1 : ℝ) / p) ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [one_div_pow]
    _ ≤ ((1 : ℝ) / p) ^ 1 / (1 - (1 : ℝ) / p) := hgeom
    _ = 1 / ((p : ℝ) - 1) := heq
    _ ≤ 2 / p := hlast

/-- A finite first-moment bound for `Ω`, expressed using the reciprocal-prime
sum already estimated by Mertens' theorem. -/
theorem sum_cardFactors_le_primeHarmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, Ω n : ℝ) ≤
      (X : ℝ) * 2 * Erdos697.PrimeHarmonic.sum X := by
  have hnat := sum_cardFactors_le_sum_prime_powers X
  have hcast :
      (∑ n ∈ Finset.Icc 1 X, Ω n : ℝ) ≤
        ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
          ∑ i ∈ Finset.Ico 1 X,
            ((X / (p ^ i) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (∑ n ∈ Finset.Icc 1 X, Ω n : ℝ) ≤ _ := hcast
    _ ≤ ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        ∑ i ∈ Finset.Ico 1 X, (X : ℝ) / (p : ℝ) ^ i := by
      gcongr with p hp i hi
      simpa only [Nat.cast_pow] using
        (Nat.cast_div_le (α := ℝ) (m := X) (n := p ^ i))
    _ ≤ ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        (X : ℝ) * (2 / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := sum_inv_prime_powers_le (X := X) (Finset.mem_filter.mp hp).2
      calc
        ∑ i ∈ Finset.Ico 1 X, (X : ℝ) / (p : ℝ) ^ i =
            (X : ℝ) * ∑ i ∈ Finset.Ico 1 X,
              (1 : ℝ) / (p : ℝ) ^ i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ ≤ (X : ℝ) * (2 / p) := by gcongr
    _ = (X : ℝ) * 2 * Erdos697.PrimeHarmonic.sum X := by
      unfold Erdos697.PrimeHarmonic.sum
      have hset : (Finset.Icc 2 X).filter Nat.Prime = Nat.primesLE X := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
        constructor
        · rintro ⟨⟨hp2, hpX⟩, hp⟩
          exact ⟨hpX, hp⟩
        · rintro ⟨hpX, hp⟩
          exact ⟨⟨hp.two_le, hpX⟩, hp⟩
      rw [hset, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-! ## Mertens on powers of two -/

/-- A fixed nonnegative bounded-error constant in reciprocal-prime Mertens. -/
def mertensError : ℝ :=
  Classical.choose Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

theorem mertensError_nonneg : 0 ≤ mertensError :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).1

theorem abs_primeHarmonic_sub_log_log_le {X : ℕ} (hX : 2 ≤ X) :
    |Erdos697.PrimeHarmonic.sum X -
        Real.log (Real.log (X : ℝ))| ≤ mertensError :=
  (Classical.choose_spec
    Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log).2 X hX

theorem primeHarmonic_two_pow_le (k : ℕ) :
    Erdos697.PrimeHarmonic.sum (2 ^ (k + 1)) ≤
      Real.log (k + 1 : ℕ) + mertensError := by
  have hpow2 : 2 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hkpow : 1 ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    exact (show 1 * 2 ≤ 2 ^ k * 2 from Nat.mul_le_mul_right 2 hkpow)
  have hM := abs_primeHarmonic_sub_log_log_le hpow2
  rw [abs_le] at hM
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    all_goals norm_num
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hinnerpos : 0 < Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hpow2)
  have hinnerle :
      Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) ≤ (k + 1 : ℕ) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hk0 : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
    calc
      ((k + 1 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hk0
        norm_num
        exact hlog2le
      _ = ((k + 1 : ℕ) : ℝ) := by ring
  have hloglogle :
      Real.log (Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) ≤
        Real.log (k + 1 : ℕ) :=
    Real.log_le_log hinnerpos hinnerle
  linarith

/-! ## Dyadic decomposition of the weighted Omega moment -/

/-- The summand in the second moment. -/
def omegaLogKernel (n : ℕ) : ℝ :=
  (Ω n : ℝ) * (1 / ((n : ℝ) * Real.log (n : ℝ)))

/-- The weighted Omega moment below a half-open natural cutoff. -/
def omegaLogSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 2 N, omegaLogKernel n

/-- The `k`-th dyadic block, namely `2^k ≤ n < 2^(k+1)`. -/
def omegaLogBlock (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), omegaLogKernel n

theorem omegaLogKernel_nonneg' (n : ℕ) : 0 ≤ omegaLogKernel n :=
  omegaLogKernel_nonneg n

private theorem omegaLogKernel_le_on_block {k n : ℕ} (hk : 1 ≤ k)
    (hn : n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1))) :
    omegaLogKernel n ≤
      (Ω n : ℝ) *
        (1 / (((2 ^ k : ℕ) : ℝ) * ((k : ℝ) * Real.log 2))) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hpowR : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
      (Finset.mem_Ico.mp hn).1)
  have hcast : (((2 ^ k : ℕ) : ℝ) ≤ (n : ℝ)) := by
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hlogpow :
      Real.log (((2 ^ k : ℕ) : ℝ)) = (k : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogle : (k : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    rw [← hlogpow]
    exact Real.log_le_log hpowR hcast
  have hdenpos :
      0 < (((2 ^ k : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) := by
    positivity
  have hdenle :
      (((2 ^ k : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) ≤
        (n : ℝ) * Real.log (n : ℝ) := by
    exact mul_le_mul hcast hlogle (by positivity) hnR.le
  unfold omegaLogKernel
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le hdenpos hdenle) (by positivity)

/-- Explicit Mertens bound for one dyadic block of the weighted Omega
moment. -/
theorem omegaLogBlock_le (k : ℕ) (hk : 1 ≤ k) :
    omegaLogBlock k ≤
      (4 / Real.log 2) *
        ((Real.log (k + 1 : ℕ) + mertensError) / (k : ℝ)) := by
  let D : ℝ := (((2 ^ k : ℕ) : ℝ) * ((k : ℝ) * Real.log 2))
  let X : ℕ := 2 ^ (k + 1)
  have hD : 0 ≤ 1 / D := by
    dsimp [D]
    positivity
  have hsubset : Finset.Ico (2 ^ k) X ⊆ Finset.Icc 1 X := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (by
          intro hn0
          subst n
          have : 0 < 2 ^ k := pow_pos (by norm_num) k
          omega), hn'.2.le⟩
  have hsumOmega :
      (∑ n ∈ Finset.Ico (2 ^ k) X, Ω n : ℝ) ≤
        ∑ n ∈ Finset.Icc 1 X, (Ω n : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun n hn hnot ↦ by positivity)
  have hfirst := sum_cardFactors_le_primeHarmonic X
  have hM := primeHarmonic_two_pow_le k
  have hMnonneg : 0 ≤ Erdos697.PrimeHarmonic.sum X := by
    unfold Erdos697.PrimeHarmonic.sum
    positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  calc
    omegaLogBlock k ≤
        ∑ n ∈ Finset.Ico (2 ^ k) X, (Ω n : ℝ) * (1 / D) := by
      unfold omegaLogBlock
      apply Finset.sum_le_sum
      intro n hn
      exact omegaLogKernel_le_on_block hk (by simpa [X] using hn)
    _ = (∑ n ∈ Finset.Ico (2 ^ k) X, (Ω n : ℝ)) * (1 / D) := by
      rw [Finset.sum_mul]
    _ ≤ (∑ n ∈ Finset.Icc 1 X, (Ω n : ℝ)) * (1 / D) := by
      exact mul_le_mul_of_nonneg_right hsumOmega hD
    _ ≤ ((X : ℝ) * 2 * Erdos697.PrimeHarmonic.sum X) * (1 / D) := by
      exact mul_le_mul_of_nonneg_right hfirst hD
    _ = (4 / Real.log 2) *
          (Erdos697.PrimeHarmonic.sum X / (k : ℝ)) := by
      dsimp [X, D]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    _ ≤ (4 / Real.log 2) *
          ((Real.log (k + 1 : ℕ) + mertensError) / (k : ℝ)) := by
      have hconst : 0 ≤ 4 / Real.log (2 : ℝ) := by positivity
      gcongr

/-- Dyadic blocks partition the natural interval from `2` to
`2^(K+1)`. -/
theorem omegaLogSum_two_pow_eq_sum_blocks (K : ℕ) :
    omegaLogSum (2 ^ (K + 1)) =
      ∑ k ∈ Finset.Ico 1 (K + 1), omegaLogBlock k := by
  induction K with
  | zero => simp [omegaLogSum, omegaLogBlock]
  | succ K ih =>
      change
        (∑ n ∈ Finset.Ico 2 (2 ^ (K + 2)), omegaLogKernel n) =
          ∑ k ∈ Finset.Ico 1 (K + 2), omegaLogBlock k
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ K + 1)]
      rw [← ih]
      unfold omegaLogSum omegaLogBlock
      rw [Finset.sum_Ico_consecutive]
      · simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
          (show 1 ≤ K + 1 by omega)
      · exact Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (by omega)

/-- The explicit constant in the dyadic weighted-Omega bound. -/
def omegaMomentConstant : ℝ :=
  (4 / Real.log 2) * (1 + mertensError)

theorem omegaMomentConstant_nonneg : 0 ≤ omegaMomentConstant := by
  unfold omegaMomentConstant
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact mul_nonneg (div_nonneg (by norm_num) hlog2.le)
    (by linarith [mertensError_nonneg])

private theorem sum_Ico_one_div_eq_harmonic (K : ℕ) :
    (∑ k ∈ Finset.Ico 1 (K + 1), (1 : ℝ) / k) =
      (harmonic K : ℝ) := by
  have hset : Finset.Ico 1 (K + 1) = Finset.Icc 1 K := by
    ext k
    simp
  rw [hset, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem harmonic_cast_le_one_add_log_succ (K : ℕ) :
    (harmonic K : ℝ) ≤ 1 + Real.log (K + 1 : ℕ) := by
  by_cases hK : K = 0
  · simp [hK]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hle : (K : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.le_succ K
  calc
    (harmonic K : ℝ) ≤ 1 + Real.log (K : ℝ) := harmonic_le_one_add_log K
    _ ≤ 1 + Real.log (K + 1 : ℕ) := by
      gcongr

/-- The weighted Omega moment has squared-double-logarithmic growth along
powers of two.  This nonnegative dyadic form is the one used in the
second-moment argument; arbitrary cutoffs are dominated by the next power of
two. -/
theorem omegaLogSum_two_pow_le (K : ℕ) :
    omegaLogSum (2 ^ (K + 1)) ≤
      omegaMomentConstant * (1 + Real.log (K + 1 : ℕ)) ^ 2 := by
  rw [omegaLogSum_two_pow_eq_sum_blocks]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ 4 / Real.log (2 : ℝ) := by positivity
  have hB : 0 ≤ 1 + mertensError := by
    linarith [mertensError_nonneg]
  have hpoint : ∀ k ∈ Finset.Ico 1 (K + 1),
      (4 / Real.log 2) *
          ((Real.log (k + 1 : ℕ) + mertensError) / (k : ℝ)) ≤
        (4 / Real.log 2) *
          ((1 + mertensError) * (1 + Real.log (K + 1 : ℕ)) *
            (1 / (k : ℝ))) := by
    intro k hk
    have hkData := Finset.mem_Ico.mp hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hkData.1
    have hKpos : (0 : ℝ) < (K + 1 : ℕ) := by positivity
    have hk1pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hlogk : 0 ≤ Real.log (k + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 1))
    have hlogK : 0 ≤ Real.log (K + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K + 1))
    have hkK : (k + 1 : ℕ) ≤ K + 1 := by omega
    have hlogle : Real.log (k + 1 : ℕ) ≤ Real.log (K + 1 : ℕ) :=
      Real.log_le_log hk1pos (by exact_mod_cast hkK)
    have hnum :
        Real.log (k + 1 : ℕ) + mertensError ≤
          (1 + mertensError) * (1 + Real.log (K + 1 : ℕ)) := by
      nlinarith [mertensError_nonneg]
    apply mul_le_mul_of_nonneg_left _ hA
    calc
      (Real.log (k + 1 : ℕ) + mertensError) / (k : ℝ) ≤
          ((1 + mertensError) * (1 + Real.log (K + 1 : ℕ))) /
            (k : ℝ) := div_le_div_of_nonneg_right hnum hkpos.le
      _ = (1 + mertensError) * (1 + Real.log (K + 1 : ℕ)) *
            (1 / (k : ℝ)) := by ring
  calc
    (∑ k ∈ Finset.Ico 1 (K + 1), omegaLogBlock k) ≤
        ∑ k ∈ Finset.Ico 1 (K + 1),
          (4 / Real.log 2) *
            ((Real.log (k + 1 : ℕ) + mertensError) / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact omegaLogBlock_le k (Finset.mem_Ico.mp hk).1
    _ ≤ ∑ k ∈ Finset.Ico 1 (K + 1),
        (4 / Real.log 2) *
          ((1 + mertensError) * (1 + Real.log (K + 1 : ℕ)) *
            (1 / (k : ℝ))) := Finset.sum_le_sum hpoint
    _ = omegaMomentConstant * (1 + Real.log (K + 1 : ℕ)) *
          (∑ k ∈ Finset.Ico 1 (K + 1), (1 : ℝ) / k) := by
      unfold omegaMomentConstant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = omegaMomentConstant * (1 + Real.log (K + 1 : ℕ)) *
          (harmonic K : ℝ) := by rw [sum_Ico_one_div_eq_harmonic]
    _ ≤ omegaMomentConstant * (1 + Real.log (K + 1 : ℕ)) *
          (1 + Real.log (K + 1 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left (harmonic_cast_le_one_add_log_succ K)
      exact mul_nonneg omegaMomentConstant_nonneg
        (add_nonneg zero_le_one
          (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K + 1))))
    _ = omegaMomentConstant * (1 + Real.log (K + 1 : ℕ)) ^ 2 := by ring

/-- Every natural cutoff is dominated by the dyadic cutoff immediately above
it.  Together with `omegaLogSum_two_pow_le`, this is the arbitrary-cutoff
interface used by applications. -/
theorem omegaLogSum_le_next_two_pow (N : ℕ) :
    omegaLogSum N ≤ omegaLogSum (2 ^ (Nat.log 2 N + 1)) := by
  unfold omegaLogSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnData := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr
      ⟨hnData.1, hnData.2.trans (Nat.lt_pow_succ_log_self (by norm_num) N)⟩
  · intro n hn hnot
    exact omegaLogKernel_nonneg' n

/-- An explicit arbitrary-cutoff consequence, retaining the harmless natural
dyadic logarithm. -/
theorem omegaLogSum_le (N : ℕ) :
    omegaLogSum N ≤
      omegaMomentConstant *
        (1 + Real.log (Nat.log 2 N + 1 : ℕ)) ^ 2 := by
  exact (omegaLogSum_le_next_two_pow N).trans
    (omegaLogSum_two_pow_le (Nat.log 2 N))

private theorem binaryLogScale_cast_le_three_mul_log {N : ℕ} (hN : 4 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hpowNat : 2 ^ Nat.log 2 N ≤ N :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowPos : (0 : ℝ) < ((2 ^ Nat.log 2 N : ℕ) : ℝ) := by positivity
  have hlogPow :
      Real.log (((2 ^ Nat.log 2 N : ℕ) : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hpowPos (by exact_mod_cast hpowNat)
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogPart : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow] at hlogPow
    have hnonneg : (0 : ℝ) ≤ Nat.log 2 N := by positivity
    have hhalf : ((Nat.log 2 N : ℕ) : ℝ) / 2 ≤ Real.log (N : ℝ) := by
      calc
        ((Nat.log 2 N : ℕ) : ℝ) / 2 =
            ((Nat.log 2 N : ℕ) : ℝ) * (1 / 2 : ℝ) := by ring
        _ ≤ ((Nat.log 2 N : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlogTwo hnonneg
        _ ≤ Real.log (N : ℝ) := by simpa using hlogPow
    linarith
  have hlogTwoStrict : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogNOne : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have h4N : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog4N := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4N
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4] at hlog4N
    linarith
  push_cast
  linarith

/-- The standard eventually-`O((log log N)^2)` formulation of the weighted
Omega estimate. -/
theorem exists_omegaLogSum_le_log_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      omegaLogSum N ≤ C * (Real.log (Real.log (N : ℝ))) ^ 2 := by
  have hLL : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ N : ℕ in atTop,
      1 + Real.log (3 : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    hLL.eventually (eventually_ge_atTop (1 + Real.log (3 : ℝ)))
  rw [eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  refine ⟨4 * omegaMomentConstant,
    mul_nonneg (by norm_num) omegaMomentConstant_nonneg,
    max 4 N₁, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left 4 N₁).trans hN
  have hNN₁ : N₁ ≤ N := (le_max_right 4 N₁).trans hN
  let L : ℝ := Real.log (Real.log (N : ℝ))
  have hL : 1 + Real.log (3 : ℝ) ≤ L := hN₁ N hNN₁
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 4) hN4)
  have hscalePos : (0 : ℝ) < ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
  have hscale := binaryLogScale_cast_le_three_mul_log hN4
  have hthreeLogPos : 0 < 3 * Real.log (N : ℝ) := by positivity
  have hlogScale :
      Real.log (Nat.log 2 N + 1 : ℕ) ≤
        Real.log (3 * Real.log (N : ℝ)) :=
    Real.log_le_log hscalePos hscale
  have hsplit :
      Real.log (3 * Real.log (N : ℝ)) = Real.log 3 + L := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogNpos.ne']
  have hlinear :
      1 + Real.log (Nat.log 2 N + 1 : ℕ) ≤ 2 * L := by
    rw [hsplit] at hlogScale
    linarith
  have hLnonneg : 0 ≤ L := by
    have hlog3nonneg : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hscaleLogNonneg :
      0 ≤ 1 + Real.log (Nat.log 2 N + 1 : ℕ) := by
    have : 0 ≤ Real.log (Nat.log 2 N + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Nat.log 2 N + 1))
    linarith
  calc
    omegaLogSum N ≤
        omegaMomentConstant *
          (1 + Real.log (Nat.log 2 N + 1 : ℕ)) ^ 2 := omegaLogSum_le N
    _ ≤ omegaMomentConstant * (2 * L) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ omegaMomentConstant_nonneg
      nlinarith
    _ = (4 * omegaMomentConstant) *
          (Real.log (Real.log (N : ℝ))) ^ 2 := by
      dsimp [L]
      ring

end

end Erdos1217.OmegaBound

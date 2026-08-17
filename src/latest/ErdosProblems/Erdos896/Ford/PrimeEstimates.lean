/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/-!
# Elementary prime estimates used in the Ford upper bound

The public sums in this file are indexed by `Nat.primesLE`, which is more
convenient for the finite combinatorial arguments in Ford's proof.  The
analytic input is the existing formalization of Mertens' first and second
theorems in `PrimeNumberTheoremAnd.IEANTN.Mertens`.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

/-- The reciprocal mass of the primes at most `x`. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

/-- The log-weighted reciprocal mass of the primes at most `x`. -/
noncomputable def primeLogWeightSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, Real.log p / p

/-- The second log moment of reciprocal prime mass. -/
noncomputable def primeLogSquareWeightSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, Real.log p ^ 2 / p

/-- The third log moment of reciprocal prime mass. -/
noncomputable def primeLogCubeWeightSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, Real.log p ^ 3 / p

/-- The reciprocal mass of the primes in the half-open interval `(x, y]`. -/
noncomputable def primeReciprocalIntervalSum (x y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE y \ Nat.primesLE x, (1 : ℝ) / p

/-- The triple prime sum occurring in Ford's denominator-removal argument. -/
noncomputable def primeTripleLcmSum (x : ℕ) : ℝ :=
  ∑ p₁ ∈ Nat.primesLE x,
    ∑ p₂ ∈ Nat.primesLE x,
      ∑ p₃ ∈ Nat.primesLE x,
        Real.log p₁ * Real.log p₂ * Real.log p₃ /
          (Nat.lcm p₁ (Nat.lcm p₂ p₃) : ℝ)

private lemma primeReciprocalSum_eq_mertensSum (x : ℕ) :
    primeReciprocalSum x =
      ∑ p ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊ with p.Prime, (1 : ℝ) / p := by
  rw [primeReciprocalSum, Nat.floor_natCast,
    Nat.primesLE_eq_filter_Ioc_zero, Finset.sum_filter]

private lemma primeLogWeightSum_eq_mertensSum (x : ℕ) :
    primeLogWeightSum x =
      ∑ p ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊ with p.Prime, Real.log p / p := by
  rw [primeLogWeightSum, Nat.floor_natCast,
    Nat.primesLE_eq_filter_Ioc_zero, Finset.sum_filter]

/-- Mertens' first theorem in the finite natural-indexed form used below. -/
theorem primeLogWeightSum_sub_log_le {x : ℕ} (hx : 1 ≤ x) :
    |primeLogWeightSum x - Real.log x| ≤ Real.log 4 + 4 := by
  rw [primeLogWeightSum_eq_mertensSum]
  exact Mertens.sum_log_prime_div_eq_log (by exact_mod_cast hx)

/-- Mertens' second theorem in the finite natural-indexed form used below. -/
theorem exists_primeReciprocalSum_sub_log_log_bound :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |primeReciprocalSum x - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx ↦ ?_⟩
  rw [primeReciprocalSum_eq_mertensSum]
  exact hC x (by exact_mod_cast hx)

/-- Weak Mertens' second theorem in asymptotic notation. -/
theorem primeReciprocalSum_sub_log_log_isBigO_one :
    (fun x : ℕ ↦ primeReciprocalSum x - Real.log (Real.log x)) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_primeReciprocalSum_sub_log_log_bound
  apply IsBigO.of_bound C
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hx ↦ hx⟩] with x hx
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using hC x hx

/-- The sharp error term in Mertens' second theorem.  This form is useful
for prime bins whose endpoints grow doubly exponentially. -/
theorem primeReciprocalSum_mertens_error_le {x : ℕ} (hx : 2 ≤ x) :
    |primeReciprocalSum x - Real.log (Real.log x) - Mertens.M| ≤
      (Real.log 4 + 6 + Mertens.E₁) / Real.log x := by
  rw [primeReciprocalSum_eq_mertensSum]
  simpa only [Mertens.E₂p] using
    (Mertens.E₂p.abs_le (x := (x : ℝ)) (by exact_mod_cast hx))

lemma primeReciprocalSum_nonneg (x : ℕ) : 0 ≤ primeReciprocalSum x := by
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- Reciprocal prime mass is monotone in its endpoint. -/
theorem primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro x y hxy
  unfold primeReciprocalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_mem_primesLE hp).trans hxy, Nat.prime_of_mem_primesLE hp⟩
  · intro p hp hpx
    positivity

/-- The reciprocal mass of the primes diverges. -/
theorem primeReciprocalSum_tendsto_atTop :
    Tendsto primeReciprocalSum atTop atTop := by
  obtain ⟨C, hC⟩ := exists_primeReciprocalSum_sub_log_log_bound
  have hloglog : Tendsto (fun x : ℕ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  rw [tendsto_atTop_atTop] at hloglog ⊢
  intro R
  obtain ⟨N, hN⟩ := hloglog (R + C)
  refine ⟨max N 2, fun n hn ↦ ?_⟩
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hmain := hN n hnN
  have herr := hC n hn2
  have hlower := (abs_le.mp herr).1
  linarith

private lemma primesLE_subset {x y : ℕ} (hxy : x ≤ y) :
    Nat.primesLE x ⊆ Nat.primesLE y := by
  intro p hp
  exact Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hp).trans hxy, Nat.prime_of_mem_primesLE hp⟩

/-- Interval reciprocal mass is the difference of the two partial sums. -/
theorem primeReciprocalIntervalSum_eq_sub {x y : ℕ} (hxy : x ≤ y) :
    primeReciprocalIntervalSum x y =
      primeReciprocalSum y - primeReciprocalSum x := by
  unfold primeReciprocalIntervalSum primeReciprocalSum
  rw [eq_sub_iff_add_eq]
  exact Finset.sum_sdiff (primesLE_subset hxy)

/-- The reciprocal mass of primes in `(U, 4U]` is `O(1 / log U)`, uniformly
from `U = 2` onward. -/
theorem exists_primeReciprocalIntervalSum_four_mul_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℕ, 2 ≤ U →
      primeReciprocalIntervalSum U (4 * U) ≤ C / Real.log U := by
  let A : ℝ := Real.log 4 + 4
  let C : ℝ := Real.log 4 + 2 * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun U hU ↦ ?_⟩
  have hUpos : 0 < U := by omega
  have hlogU : 0 < Real.log U := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hsub : Nat.primesLE U ⊆ Nat.primesLE (4 * U) :=
    primesLE_subset (by omega)
  have hweighted :
      Real.log U * primeReciprocalIntervalSum U (4 * U) ≤
        ∑ p ∈ Nat.primesLE (4 * U) \ Nat.primesLE U,
          Real.log p / p := by
    unfold primeReciprocalIntervalSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hpPrime := Nat.prime_of_mem_primesLE hp'.1
    have hUp : U < p := by
      by_contra hnot
      exact hp'.2 (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hnot, hpPrime⟩)
    have hlogle : Real.log U ≤ Real.log p := by
      have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hUpos
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hUR)
        (Set.mem_Ioi.mpr hpR) (by exact_mod_cast hUp.le)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    calc
      Real.log U * (1 / (p : ℝ)) = Real.log U / p := by ring
      _ ≤ Real.log p / p := div_le_div_of_nonneg_right hlogle hp0
  have hweightedEq :
      (∑ p ∈ Nat.primesLE (4 * U) \ Nat.primesLE U, Real.log p / p) =
        primeLogWeightSum (4 * U) - primeLogWeightSum U := by
    unfold primeLogWeightSum
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_sdiff hsub
  have he4 := primeLogWeightSum_sub_log_le (x := 4 * U) (by omega)
  have heU := primeLogWeightSum_sub_log_le (x := U) (by omega)
  have hupper4 :
      primeLogWeightSum (4 * U) ≤ Real.log (((4 * U : ℕ) : ℝ)) + A := by
    have := (abs_le.mp he4).2
    dsimp [A]
    linarith
  have hlowerU : Real.log U - A ≤ primeLogWeightSum U := by
    have := (abs_le.mp heU).1
    dsimp [A]
    linarith
  have hlogmul : Real.log (((4 * U : ℕ) : ℝ)) = Real.log 4 + Real.log U := by
    push_cast
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (U : ℝ) ≠ 0)]
  have hdiff :
      primeLogWeightSum (4 * U) - primeLogWeightSum U ≤ C := by
    dsimp [C]
    rw [hlogmul] at hupper4
    linarith
  apply (le_div_iff₀ hlogU).2
  calc
    primeReciprocalIntervalSum U (4 * U) * Real.log U =
        Real.log U * primeReciprocalIntervalSum U (4 * U) := by ring
    _ ≤ ∑ p ∈ Nat.primesLE (4 * U) \ Nat.primesLE U, Real.log p / p := hweighted
    _ = primeLogWeightSum (4 * U) - primeLogWeightSum U := hweightedEq
    _ ≤ C := hdiff

/-- Asymptotic form of the factor-four interval estimate. -/
theorem primeReciprocalIntervalSum_four_mul_isBigO_inv_log :
    (fun U : ℕ ↦ primeReciprocalIntervalSum U (4 * U)) =O[atTop]
      (fun U : ℕ ↦ 1 / Real.log U) := by
  obtain ⟨C, hC, h⟩ := exists_primeReciprocalIntervalSum_four_mul_le
  apply IsBigO.of_bound C
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hx ↦ hx⟩] with U hU
  have hlogU : 0 < Real.log U := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by unfold primeReciprocalIntervalSum; positivity),
    abs_of_pos (div_pos zero_lt_one hlogU)]
  simpa only [div_eq_mul_inv, one_mul] using h U hU

lemma primeLogWeightSum_nonneg (x : ℕ) : 0 ≤ primeLogWeightSum x := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)) (Nat.cast_nonneg p)

/-- A uniform version of `primeLogWeightSum = O(log)`, valid from `x = 2`
onward. -/
theorem exists_primeLogWeightSum_le_const_mul_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      primeLogWeightSum x ≤ C * Real.log x := by
  let A : ℝ := Real.log 4 + 4
  let C : ℝ := 1 + A / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog : Real.log 2 ≤ Real.log x := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (lt_of_lt_of_le (by norm_num) hxR) hxR
  have herr := primeLogWeightSum_sub_log_le (x := x) (by omega)
  have hupper : primeLogWeightSum x ≤ Real.log x + A := by
    have := (le_abs_self (primeLogWeightSum x - Real.log x)).trans herr
    dsimp [A]
    linarith
  have hAupper : A ≤ (A / Real.log 2) * Real.log x := by
    calc
      A = (A / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (A / Real.log 2) * Real.log x :=
        mul_le_mul_of_nonneg_left hlog (div_nonneg hA hlog2.le)
  calc
    primeLogWeightSum x ≤ Real.log x + A := hupper
    _ ≤ Real.log x + (A / Real.log 2) * Real.log x := add_le_add le_rfl hAupper
    _ = C * Real.log x := by dsimp [C]; ring

/-- The weighted prime sum has the expected first-Mertens growth. -/
theorem primeLogWeightSum_isBigO_log :
    primeLogWeightSum =O[atTop] (fun x : ℕ ↦ Real.log x) := by
  obtain ⟨C, hC, h⟩ := exists_primeLogWeightSum_le_const_mul_log
  apply IsBigO.of_bound C
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hx ↦ hx⟩] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primeLogWeightSum_nonneg x),
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))]
  exact h x hx

private lemma prime_lcm_triple_le
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    Real.log p * Real.log q * Real.log r /
        (Nat.lcm p (Nat.lcm q r) : ℝ) ≤
      (Real.log p / p) * (Real.log q / q) * (Real.log r / r) +
      (if p = q then Real.log p ^ 2 / p * (Real.log r / r) else 0) +
      (if p = r then Real.log p ^ 2 / p * (Real.log q / q) else 0) +
      (if q = r then Real.log q ^ 2 / q * (Real.log p / p) else 0) +
      (if p = q ∧ q = r then Real.log p ^ 3 / p else 0) := by
  by_cases hpq : p = q
  · subst q
    by_cases hpr : p = r
    · subst r
      simp only [Nat.lcm_self, if_pos rfl, true_and]
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
      ring_nf
      simp_all
      positivity
    · have hcop : p.Coprime r := (Nat.coprime_primes hp hr).2 hpr
      rw [hcop.lcm_eq_mul, Nat.lcm_eq_right (Nat.dvd_mul_right p r)]
      simp only [if_pos rfl, if_neg hpr, hpr, and_false]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
      have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr.one_le)
      push_cast
      field_simp
      ring_nf
      simp_all
      positivity
  · by_cases hpr : p = r
    · subst r
      have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
      rw [Nat.lcm_comm q p, hcop.lcm_eq_mul,
        Nat.lcm_eq_right (Nat.dvd_mul_right p q)]
      simp only [if_neg hpq, if_neg (Ne.symm hpq), if_pos rfl, hpq, false_and]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
      have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.one_le)
      push_cast
      field_simp
      ring_nf
      simp_all <;> positivity
    · by_cases hqr : q = r
      · subst r
        have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
        rw [Nat.lcm_self, hcop.lcm_eq_mul]
        simp only [if_neg hpq, if_neg hpr, if_pos rfl, hpq, false_and]
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
        have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.one_le)
        push_cast
        field_simp
        ring_nf <;> simp_all <;> positivity
      · have hqrCop : q.Coprime r := (Nat.coprime_primes hq hr).2 hqr
        have hpqCop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
        have hprCop : p.Coprime r := (Nat.coprime_primes hp hr).2 hpr
        rw [hqrCop.lcm_eq_mul, (hpqCop.mul_right hprCop).lcm_eq_mul]
        simp only [if_neg hpq, if_neg hpr, if_neg hqr, hpq, false_and,
          add_zero]
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
        have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
        push_cast
        field_simp
        ring_nf
        exact le_rfl

/-- Before applying Mertens, the triple-lcm sum is bounded by three elementary
log moments. -/
theorem primeTripleLcmSum_le_weightSums (x : ℕ) :
    primeTripleLcmSum x ≤
      primeLogWeightSum x ^ 3 +
        3 * primeLogSquareWeightSum x * primeLogWeightSum x +
        primeLogCubeWeightSum x := by
  let s := Nat.primesLE x
  calc
    primeTripleLcmSum x ≤
        ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
          ((Real.log p / p) * (Real.log q / q) * (Real.log r / r) +
          (if p = q then Real.log p ^ 2 / p * (Real.log r / r) else 0) +
          (if p = r then Real.log p ^ 2 / p * (Real.log q / q) else 0) +
          (if q = r then Real.log q ^ 2 / q * (Real.log p / p) else 0) +
          (if p = q ∧ q = r then Real.log p ^ 3 / p else 0)) := by
      unfold primeTripleLcmSum
      dsimp [s]
      gcongr with p hp q hq r hr
      exact prime_lcm_triple_le (Nat.prime_of_mem_primesLE hp)
        (Nat.prime_of_mem_primesLE hq) (Nat.prime_of_mem_primesLE hr)
    _ = primeLogWeightSum x ^ 3 +
        3 * primeLogSquareWeightSum x * primeLogWeightSum x +
        primeLogCubeWeightSum x := by
      dsimp [s]
      have hdiag :
          (∑ p ∈ Nat.primesLE x, ∑ q ∈ Nat.primesLE x,
            ∑ r ∈ Nat.primesLE x,
              if p = q ∧ q = r then Real.log p ^ 3 / p else 0) =
            ∑ p ∈ Nat.primesLE x, Real.log p ^ 3 / p := by
        apply Finset.sum_congr rfl
        intro p hp
        calc
          (∑ q ∈ Nat.primesLE x, ∑ r ∈ Nat.primesLE x,
              if p = q ∧ q = r then Real.log p ^ 3 / p else 0) =
              ∑ q ∈ Nat.primesLE x,
                if p = q then Real.log p ^ 3 / p else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hpq : p = q
            · subst q
              simp [hq]
            · simp [hpq]
          _ = Real.log p ^ 3 / p := by simp [hp]
      have hpair :
          (∑ p ∈ Nat.primesLE x, ∑ r ∈ Nat.primesLE x,
              Real.log p ^ 2 / p * (Real.log r / r)) =
            ∑ p ∈ Nat.primesLE x, ∑ r ∈ Nat.primesLE x,
              Real.log p / p * (Real.log r ^ 2 / r) := by
        rw [Finset.sum_comm]
        simp_rw [mul_comm]
      simp only [Finset.sum_add_distrib]
      rw [hdiag]
      simp [primeLogWeightSum, primeLogSquareWeightSum, primeLogCubeWeightSum,
        Finset.mul_sum, Finset.sum_mul, pow_three]
      simp_rw [mul_comm, mul_left_comm]
      rw [hpair]
      simp_rw [← Finset.mul_sum]
      ring

private lemma log_prime_le_log_of_le {p x : ℕ} (hp : p.Prime) (hpx : p ≤ x) :
    Real.log p ≤ Real.log x := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpxR : (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast hpx
  exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hpR)
    (Set.mem_Ioi.mpr (hpR.trans_le hpxR)) hpxR

/-- A second log weight can be pulled out at the endpoint. -/
theorem primeLogSquareWeightSum_le (x : ℕ) :
    primeLogSquareWeightSum x ≤ Real.log x * primeLogWeightSum x := by
  unfold primeLogSquareWeightSum primeLogWeightSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := Nat.prime_of_mem_primesLE hp
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hlogle := log_prime_le_log_of_le hpPrime (Nat.le_of_mem_primesLE hp)
  calc
    Real.log p ^ 2 / p = Real.log p * (Real.log p / p) := by ring
    _ ≤ Real.log x * (Real.log p / p) :=
      mul_le_mul_of_nonneg_right hlogle (div_nonneg hlogp (Nat.cast_nonneg p))

/-- Two extra log weights can be pulled out at the endpoint. -/
theorem primeLogCubeWeightSum_le (x : ℕ) :
    primeLogCubeWeightSum x ≤ Real.log x ^ 2 * primeLogWeightSum x := by
  unfold primeLogCubeWeightSum primeLogWeightSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := Nat.prime_of_mem_primesLE hp
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hlogx : 0 ≤ Real.log x := hlogp.trans (log_prime_le_log_of_le hpPrime
    (Nat.le_of_mem_primesLE hp))
  have hlogle := log_prime_le_log_of_le hpPrime (Nat.le_of_mem_primesLE hp)
  have hsq : Real.log p ^ 2 ≤ Real.log x ^ 2 := by nlinarith
  calc
    Real.log p ^ 3 / p = Real.log p ^ 2 * (Real.log p / p) := by ring
    _ ≤ Real.log x ^ 2 * (Real.log p / p) :=
      mul_le_mul_of_nonneg_right hsq (div_nonneg hlogp (Nat.cast_nonneg p))

/-- A fully endpoint-explicit reduction of the triple sum to Mertens' first
prime sum. -/
theorem primeTripleLcmSum_le_log_and_weight (x : ℕ) :
    primeTripleLcmSum x ≤
      primeLogWeightSum x ^ 3 +
        3 * Real.log x * primeLogWeightSum x ^ 2 +
        Real.log x ^ 2 * primeLogWeightSum x := by
  calc
    primeTripleLcmSum x ≤ primeLogWeightSum x ^ 3 +
        3 * primeLogSquareWeightSum x * primeLogWeightSum x +
        primeLogCubeWeightSum x := primeTripleLcmSum_le_weightSums x
    _ ≤ primeLogWeightSum x ^ 3 +
        3 * (Real.log x * primeLogWeightSum x) * primeLogWeightSum x +
        (Real.log x ^ 2 * primeLogWeightSum x) := by
      gcongr
      · exact primeLogWeightSum_nonneg x
      · exact primeLogSquareWeightSum_le x
      · exact primeLogCubeWeightSum_le x
    _ = _ := by ring

/-- A uniform `O(log³ x)` estimate, valid for every `x ≥ 2`. -/
theorem exists_primeTripleLcmSum_le_const_mul_log_cube :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      primeTripleLcmSum x ≤ C * Real.log x ^ 3 := by
  obtain ⟨C, hC, hW⟩ := exists_primeLogWeightSum_le_const_mul_log
  refine ⟨C ^ 3 + 3 * C ^ 2 + C, by positivity, fun x hx ↦ ?_⟩
  let L := Real.log x
  let W := primeLogWeightSum x
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hW0 : 0 ≤ W := primeLogWeightSum_nonneg x
  have hWL : W ≤ C * L := hW x hx
  calc
    primeTripleLcmSum x ≤ W ^ 3 + 3 * L * W ^ 2 + L ^ 2 * W :=
      primeTripleLcmSum_le_log_and_weight x
    _ ≤ (C * L) ^ 3 + 3 * L * (C * L) ^ 2 + L ^ 2 * (C * L) := by
      gcongr
    _ = (C ^ 3 + 3 * C ^ 2 + C) * Real.log x ^ 3 := by
      dsimp [L]
      ring

/-- The triple-lcm sum has the order required in Ford's denominator-removal
argument. -/
theorem primeTripleLcmSum_isBigO_log_pow_three :
    primeTripleLcmSum =O[atTop] (fun x : ℕ ↦ Real.log x ^ 3) := by
  obtain ⟨C, hC, h⟩ := exists_primeTripleLcmSum_le_const_mul_log_cube
  apply IsBigO.of_bound C
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hx ↦ hx⟩] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by unfold primeTripleLcmSum; positivity),
    abs_of_nonneg (pow_nonneg (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ x by omega))) 3)]
  exact h x hx

end Erdos896.Ford

import ErdosProblems.Erdos327.Analytic.WeightedMangoldt
import ErdosProblems.Erdos327.Analytic.PrimeRangeWeight
import ErdosProblems.Erdos327.Analytic.EulerProductBounds

namespace Erdos327.Analytic

open Finset Real

/-- The finite Euler product occurring in the factorial version of the
Halberstam--Richert inequality. -/
noncomputable def factorialFactorEulerProduct
    (w : ℕ → ℝ) (Y : ℕ) : ℝ :=
  Y.factorial.factorization.prod (fun p e ↦
    ∑ k ∈ range (e + 1), (w p / p) ^ k)

/-- The prime support of `Y!` is exactly the set of primes at most `Y`. -/
theorem factorial_primeFactors_eq_primesLE (Y : ℕ) :
    Y.factorial.primeFactors = Nat.primesLE Y := by
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hpdvd, _⟩
    exact ⟨hp.dvd_factorial.mp hpdvd, hp⟩
  · rintro ⟨hpY, hp⟩
    exact ⟨hp, hp.dvd_factorial.mpr hpY, Nat.factorial_ne_zero Y⟩

/-- The reciprocal weighted-prime mass over the odd part of the support
of `Y!`. -/
noncomputable def factorialOddPrimeMass
    (w : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE Y).erase 2, w p / p

private theorem factorial_localFactor_two_le
    {w : ℕ → ℝ} (hw0 : 0 ≤ w 2) (hw2 : w 2 ≤ 1)
    (e : ℕ) :
    (∑ k ∈ range (e + 1), (w 2 / (2 : ℝ)) ^ k) ≤ 2 := by
  have hr0 : 0 ≤ w 2 / (2 : ℝ) := by positivity
  have hr1 : w 2 / (2 : ℝ) < 1 := by linarith
  calc
    (∑ k ∈ range (e + 1), (w 2 / (2 : ℝ)) ^ k)
        ≤ (1 - w 2 / (2 : ℝ))⁻¹ :=
      geomSum_le_inv_one_sub hr0 hr1 (e + 1)
    _ ≤ 2 := by
      have hden : (1 / 2 : ℝ) ≤ 1 - w 2 / 2 := by linarith
      calc
        (1 - w 2 / 2)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) hden
        _ = 2 := by norm_num

private theorem factorial_localFactor_odd_le_exp
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2)
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∑ k ∈ range (e + 1), (w p / p) ^ k) ≤
      exp (w p / p + 38 / (p : ℝ) ^ 2) := by
  have hp3 : 3 ≤ p := by
    have hp2le := hp.two_le
    omega
  calc
    (∑ k ∈ range (e + 1), (w p / p) ^ k)
        ≤ 1 + w p / p + 38 / (p : ℝ) ^ 2 :=
      geomSum_le_one_add_linear_add_38_inv_sq
        (hw0 p) (hw p) (by exact_mod_cast hp3) (e + 1)
    _ ≤ exp (w p / p + 38 / (p : ℝ) ^ 2) := by
      linarith [add_one_le_exp (w p / p + 38 / (p : ℝ) ^ 2)]

/-- Uniform Euler-product bound.  The prime `2` costs at most `2`; all
odd primes are absorbed into a linear reciprocal-prime mass and the
absolute square-error reserve `38`. -/
theorem factorialFactorEulerProduct_le_two_mul_exp
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (Y : ℕ) :
    factorialFactorEulerProduct w Y ≤
      2 * exp (factorialOddPrimeMass w Y + 38) := by
  classical
  let s := (Nat.primesLE Y).erase 2
  have hsPrime : ∀ p ∈ s, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (mem_of_mem_erase hp)
  have hsSq :
      (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤ 1 := by
    simpa [one_div] using sum_prime_inv_sq_le_one s hsPrime
  have hsExp :
      (∏ p ∈ s, exp (w p / p + 38 / (p : ℝ) ^ 2)) ≤
        exp (factorialOddPrimeMass w Y + 38) := by
    rw [← exp_sum]
    apply exp_le_exp.mpr
    have hsum :
        (∑ p ∈ s, (w p / p + 38 / (p : ℝ) ^ 2)) =
          (∑ p ∈ s, w p / p) +
            38 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) := by
      rw [sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro p _
      ring
    rw [hsum]
    change
      (∑ p ∈ s, w p / p) +
          38 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤
        factorialOddPrimeMass w Y + 38
    unfold factorialOddPrimeMass
    change
      (∑ p ∈ s, w p / p) +
          38 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤
        (∑ p ∈ s, w p / p) + 38
    have h38 :
        38 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤ 38 :=
      mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 38) hsSq
    linarith
  unfold factorialFactorEulerProduct
  change
    (∏ p ∈ Y.factorial.primeFactors,
      ∑ k ∈ range (Y.factorial.factorization p + 1),
        (w p / p) ^ k) ≤ _
  rw [factorial_primeFactors_eq_primesLE]
  by_cases h2 : 2 ∈ Nat.primesLE Y
  · rw [← mul_prod_erase _ _ h2]
    have hprod0 :
        0 ≤ ∏ p ∈ s,
            ∑ k ∈ range (Y.factorial.factorization p + 1),
              (w p / p) ^ k := by
      apply prod_nonneg
      intro p hp
      exact sum_nonneg fun k _ ↦
        pow_nonneg (div_nonneg (hw0 p) (by positivity)) k
    have hprodle :
        (∏ p ∈ s,
            ∑ k ∈ range (Y.factorial.factorization p + 1),
              (w p / p) ^ k) ≤
          ∏ p ∈ s, exp (w p / p + 38 / (p : ℝ) ^ 2) := by
      apply prod_le_prod
      · intro p hp
        exact sum_nonneg fun k _ ↦
          pow_nonneg (div_nonneg (hw0 p) (by positivity)) k
      · intro p hp
        exact factorial_localFactor_odd_le_exp hw0 hw
          (hsPrime p hp) (ne_of_mem_erase hp)
    calc
      (∑ k ∈ range (Y.factorial.factorization 2 + 1),
          (w 2 / (2 : ℝ)) ^ k) *
          (∏ p ∈ s,
            ∑ k ∈ range (Y.factorial.factorization p + 1),
              (w p / p) ^ k)
          ≤ 2 * (∏ p ∈ s,
              ∑ k ∈ range (Y.factorial.factorization p + 1),
                (w p / p) ^ k) :=
            mul_le_mul_of_nonneg_right
              (factorial_localFactor_two_le (hw0 2) hw2 _) hprod0
      _ ≤ 2 * (∏ p ∈ s,
              exp (w p / p + 38 / (p : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hprodle (by norm_num)
      _ ≤ 2 * exp (factorialOddPrimeMass w Y + 38) := by
        gcongr
  · have hsEq : s = Nat.primesLE Y := by
      simp [s, h2]
    rw [show Nat.primesLE Y = s by exact hsEq.symm]
    calc
      (∏ p ∈ s,
          ∑ k ∈ range (Y.factorial.factorization p + 1),
            (w p / p) ^ k)
          ≤ ∏ p ∈ s,
              exp (w p / p + 38 / (p : ℝ) ^ 2) := by
            apply prod_le_prod
            · intro p hp
              exact sum_nonneg fun k _ ↦
                pow_nonneg (div_nonneg (hw0 p) (by positivity)) k
            · intro p hp
              exact factorial_localFactor_odd_le_exp hw0 hw
                (hsPrime p hp) (ne_of_mem_erase hp)
      _ ≤ 2 * exp (factorialOddPrimeMass w Y + 38) := by
        have hexp0 :
            0 ≤ exp (factorialOddPrimeMass w Y + 38) :=
          (exp_pos _).le
        exact hsExp.trans (by linarith)

/-- The reciprocal-prime exponent for a residual cutoff weight.  The first
tail contains primes `L ≤ p ≤ min X Y`, which carry weight `q`; the second
contains primes `min X Y < p ≤ Y`, which carry weight one. -/
noncomputable def residualPrimeExponent
    (L X : ℕ) (q : ℝ) (Y : ℕ) : ℝ :=
  q * primeInvTail (L - 1) (min X Y) +
    primeInvTail (min X Y) Y

theorem residualPrimeExponent_of_X_le_Y
    {L X Y : ℕ} {q : ℝ} (hXY : X ≤ Y) :
    residualPrimeExponent L X q Y =
      q * primeInvTail (L - 1) X + primeInvTail X Y := by
  simp [residualPrimeExponent, min_eq_left hXY]

theorem residualPrimeExponent_of_Y_le_X
    {L X Y : ℕ} {q : ℝ} (hYX : Y ≤ X) :
    residualPrimeExponent L X q Y =
      q * primeInvTail (L - 1) Y := by
  simp [residualPrimeExponent, min_eq_right hYX, primeInvTail]

/-- Exact decomposition of the odd weighted-prime mass for the residual
weight.  Keeping this identity in finite-prime-sum form avoids any hidden
asymptotic input. -/
theorem factorialOddPrimeMass_residualPrimeWeight
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y) :
    factorialOddPrimeMass (residualPrimeWeight L X q) Y =
      residualPrimeExponent L X q Y := by
  classical
  let T := min X Y
  let s := (Nat.primesLE Y).erase 2
  let A := Nat.primesLE T \ Nat.primesLE (L - 1)
  let B := Nat.primesLE Y \ Nat.primesLE T
  have hTY : T ≤ Y := min_le_right _ _
  have hTX : T ≤ X := min_le_left _ _
  have hLT : L ≤ T := le_min hLX hLY
  have hLm1 : 2 ≤ L - 1 := by omega
  have hAsub : A ⊆ s := by
    intro p hp
    have hpT : p ∈ Nat.primesLE T := (mem_sdiff.mp hp).1
    have hpPrime := Nat.prime_of_mem_primesLE hpT
    have hpY : p ∈ Nat.primesLE Y :=
      (Nat.mem_primesLE.mpr
        ⟨(Nat.le_of_mem_primesLE hpT).trans hTY, hpPrime⟩)
    have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      exact (mem_sdiff.mp hp).2
        (Nat.mem_primesLE.mpr ⟨hLm1, Nat.prime_two⟩)
    exact mem_erase.mpr ⟨hp2, hpY⟩
  have hBsub : B ⊆ s := by
    intro p hp
    have hpY : p ∈ Nat.primesLE Y := (mem_sdiff.mp hp).1
    have hpPrime := Nat.prime_of_mem_primesLE hpY
    have hpTnot : p ∉ Nat.primesLE T := (mem_sdiff.mp hp).2
    have hpTlt : T < p := by
      rw [Nat.mem_primesLE] at hpTnot
      simp only [hpPrime, and_true, not_le] at hpTnot
      exact hpTnot
    have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      omega
    exact mem_erase.mpr ⟨hp2, hpY⟩
  have hsA : s.filter (fun p ↦ p ∈ A) = A := by
    ext p
    simp only [mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨hAsub hp, hp⟩
  have hsB : s.filter (fun p ↦ p ∈ B) = B := by
    ext p
    simp only [mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨hBsub hp, hp⟩
  have hpoint (p : ℕ) (hp : p ∈ s) :
      residualPrimeWeight L X q p / p =
        (if p ∈ A then q / p else 0) +
          (if p ∈ B then 1 / (p : ℝ) else 0) := by
    have hpYmem : p ∈ Nat.primesLE Y := mem_of_mem_erase hp
    have hpY : p ≤ Y := Nat.le_of_mem_primesLE hpYmem
    have hpPrime := Nat.prime_of_mem_primesLE hpYmem
    have hp2ne : p ≠ 2 := ne_of_mem_erase hp
    have hp2lt : 2 < p := by
      have hp2le := hpPrime.two_le
      omega
    have hpA : p ∈ A ↔ L ≤ p ∧ p ≤ T := by
      simp only [A, mem_sdiff, Nat.mem_primesLE, hpPrime, and_true]
      omega
    have hpB : p ∈ B ↔ T < p ∧ p ≤ Y := by
      simp only [B, mem_sdiff, Nat.mem_primesLE, hpPrime, and_true]
      omega
    simp only [hpA, hpB]
    by_cases hpL : L ≤ p
    · by_cases hpT : p ≤ T
      · have hpX : p ≤ X := hpT.trans hTX
        simp [residualPrimeWeight, hpL, hpX, hpT,
          not_lt_of_ge hpL]
      · have hTp : T < p := Nat.lt_of_not_ge hpT
        have hXp : X < p := by
          by_contra h
          have hpX : p ≤ X := Nat.le_of_not_gt h
          exact hpT (le_min hpX hpY)
        simp [residualPrimeWeight, hpL, hTp, hpT, hpY,
          Nat.not_le.mpr hXp, not_lt_of_ge hpL]
    · have hpLtL : p < L := Nat.lt_of_not_ge hpL
      have hpT : p ≤ T := (Nat.le_of_lt hpLtL).trans hLT
      simp [residualPrimeWeight, hp2lt, hpLtL, hpL, hpT,
        not_lt_of_ge hpT]
  unfold factorialOddPrimeMass residualPrimeExponent primeInvTail
  change
    (∑ p ∈ s, residualPrimeWeight L X q p / p) =
      q * (∑ p ∈ A, 1 / (p : ℝ)) +
        ∑ p ∈ B, 1 / (p : ℝ)
  calc
    (∑ p ∈ s, residualPrimeWeight L X q p / p) =
        ∑ p ∈ s,
          ((if p ∈ A then q / p else 0) +
            (if p ∈ B then 1 / (p : ℝ) else 0)) :=
      sum_congr rfl hpoint
    _ = (∑ p ∈ A, q / p) +
        ∑ p ∈ B, 1 / (p : ℝ) := by
      rw [sum_add_distrib, Finset.sum_ite, Finset.sum_ite,
        sum_const_zero, sum_const_zero, add_zero, add_zero, hsA, hsB]
    _ = q * (∑ p ∈ A, 1 / (p : ℝ)) +
        ∑ p ∈ B, 1 / (p : ℝ) := by
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro p _
        ring

/-- Euler-product specialization for the residual cutoff weight. -/
theorem factorialFactorEulerProduct_residualPrimeWeight_le
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    factorialFactorEulerProduct (residualPrimeWeight L X q) Y ≤
      2 * exp (residualPrimeExponent L X q Y + 38) := by
  have hw0 :
      ∀ p, 0 ≤ residualPrimeWeight L X q p :=
    fun p ↦ residualPrimeWeight_nonneg hq0 p
  have hw :
      ∀ p, residualPrimeWeight L X q p ≤ 5 / 2 :=
    fun p ↦ residualPrimeWeight_le
      (hq1.trans (by norm_num : (1 : ℝ) ≤ 5 / 2))
      (by norm_num) p
  have hw2 :
      residualPrimeWeight L X q 2 ≤ 1 := by
    rw [residualPrimeWeight_two (by omega : 2 < L)]
  calc
    factorialFactorEulerProduct (residualPrimeWeight L X q) Y
        ≤ 2 * exp
            (factorialOddPrimeMass (residualPrimeWeight L X q) Y + 38) :=
      factorialFactorEulerProduct_le_two_mul_exp hw0 hw hw2 Y
    _ = 2 * exp (residualPrimeExponent L X q Y + 38) := by
      rw [factorialOddPrimeMass_residualPrimeWeight hL hLX hLY]

/-- The fully explicit one-variable residual mean estimate, before applying
Mertens' reciprocal-prime bounds.  Its constant is uniform in all three
cutoffs and in `q ∈ [0,1]`. -/
theorem residualFactorWeight_partialSum_le_exp
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    partialSum (factorWeight (residualPrimeWeight L X q)) Y ≤
      2 * ((log 4 + 5) * Y / log Y) *
        exp (residualPrimeExponent L X q Y + 38) := by
  have hw0 :
      ∀ p, 0 ≤ residualPrimeWeight L X q p :=
    fun p ↦ residualPrimeWeight_nonneg hq0 p
  have hw1 :
      ∀ p, residualPrimeWeight L X q p ≤ 1 :=
    fun p ↦ residualPrimeWeight_le hq1 le_rfl p
  have hbase :=
    factorWeight_partialSum_le_eulerProduct hw0 hw1 hY
  have hprod :=
    factorialFactorEulerProduct_residualPrimeWeight_le
      hL hLX hLY hq0 hq1
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff : 0 ≤ (log 4 + 5) * (Y : ℝ) / log Y := by
    positivity
  unfold factorialFactorEulerProduct at hprod
  calc
    partialSum (factorWeight (residualPrimeWeight L X q)) Y
        ≤ ((log 4 + 5) * Y / log Y) *
            Y.factorial.factorization.prod (fun p e ↦
              ∑ k ∈ range (e + 1),
                (residualPrimeWeight L X q p / p) ^ k) :=
      hbase
    _ ≤ ((log 4 + 5) * Y / log Y) *
          (2 * exp (residualPrimeExponent L X q Y + 38)) :=
      mul_le_mul_of_nonneg_left hprod hcoeff
    _ = 2 * ((log 4 + 5) * Y / log Y) *
          exp (residualPrimeExponent L X q Y + 38) := by ring

/-- Exact arithmetic interpretation of the residual factor-weight partial
sum: it is the `q`-moment of the cutoff factor count on odd-rough
integers. -/
theorem partialSum_residualPrimeWeight_eq
    {L X Y : ℕ} {q : ℝ} :
    partialSum (factorWeight (residualPrimeWeight L X q)) Y =
      ∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0 := by
  unfold partialSum
  apply sum_congr rfl
  intro n hn
  exact factorWeight_residualPrimeWeight
    (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)

/-- Residual moment estimate in the indicator form used by both the
centered-source and mixed arguments. -/
theorem residualMoment_le_exp
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((log 4 + 5) * Y / log Y) *
        exp (residualPrimeExponent L X q Y + 38) := by
  rw [← partialSum_residualPrimeWeight_eq]
  exact residualFactorWeight_partialSum_le_exp
    hL hLX hLY hY hq0 hq1

/-- The explicit Mertens upper envelope for a reciprocal-prime tail. -/
noncomputable def primeInvTailUpper (L X : ℕ) : ℝ :=
  log (log X) - log (log L) +
    (log 4 + 3) / log X + (log 4 + 3) / log L

theorem primeInvTail_le_primeInvTailUpper
    {L X : ℕ} (hL : 2 ≤ L) (hLX : L ≤ X) :
    primeInvTail L X ≤ primeInvTailUpper L X := by
  exact primeInvTail_le hL hLX

/-- Applying the explicit Mertens estimate to the two pieces of the
residual exponent.  This is the logarithmic form from which the two
residual regimes follow by taking `min X Y = X` or `min X Y = Y`. -/
theorem residualPrimeExponent_le_mertens
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hq0 : 0 ≤ q) :
    residualPrimeExponent L X q Y ≤
      q * primeInvTailUpper (L - 1) (min X Y) +
        primeInvTailUpper (min X Y) Y := by
  have hLm1 : 2 ≤ L - 1 := by omega
  have hLT : L - 1 ≤ min X Y := by
    omega
  have hTY : min X Y ≤ Y := min_le_right _ _
  have hT2 : 2 ≤ min X Y := by omega
  unfold residualPrimeExponent
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (primeInvTail_le_primeInvTailUpper hLm1 hLT) hq0)
    (primeInvTail_le_primeInvTailUpper hT2 hTY)

/-- Mertens-expanded residual moment estimate. -/
theorem residualMoment_le_mertens
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((log 4 + 5) * Y / log Y) *
        exp
          (q * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) := by
  have hbase := residualMoment_le_exp
    hL hLX hLY hY hq0 hq1
  have hexponent :
      residualPrimeExponent L X q Y + 38 ≤
        q * primeInvTailUpper (L - 1) (min X Y) +
          primeInvTailUpper (min X Y) Y + 38 := by
    linarith [residualPrimeExponent_le_mertens hL hLX hLY hq0]
  have hexp := exp_le_exp.mpr hexponent
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ 2 * ((log 4 + 5) * (Y : ℝ) / log Y) := by
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left hexp hcoeff)

/-- The centered-source residual specialization `q = 1/4`. -/
theorem sourceResidualMoment_le_mertens
    {L X Y : ℕ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then
          (1 / 4 : ℝ) ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((log 4 + 5) * Y / log Y) *
        exp
          ((1 / 4 : ℝ) *
              primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) := by
  exact residualMoment_le_mertens
    hL hLX hLY hY (by norm_num) (by norm_num)

/-- The mixed residual specialization, with its parameter `s` kept
explicit for later parameter selection. -/
theorem mixedResidualMoment_le_mertens
    {L X Y : ℕ} {s : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then
          s ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((log 4 + 5) * Y / log Y) *
        exp
          (s * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) :=
  residualMoment_le_mertens
    hL hLX hLY hY hs0 hs1

/-- Below the roughness cutoff, every odd prime in the factorial support
has residual weight zero. -/
theorem factorialOddPrimeMass_residualPrimeWeight_eq_zero_of_lt
    {L X Y : ℕ} {q : ℝ} (hYL : Y < L) :
    factorialOddPrimeMass (residualPrimeWeight L X q) Y = 0 := by
  classical
  unfold factorialOddPrimeMass
  apply sum_eq_zero
  intro p hp
  have hpYmem : p ∈ Nat.primesLE Y := mem_of_mem_erase hp
  have hpPrime := Nat.prime_of_mem_primesLE hpYmem
  have hpY := Nat.le_of_mem_primesLE hpYmem
  have hp2ne : p ≠ 2 := ne_of_mem_erase hp
  have hp2lt : 2 < p := by
    have hp2le := hpPrime.two_le
    omega
  rw [residualPrimeWeight_eq_zero_of_oddPrimeBelow hp2lt
    (hpY.trans_lt hYL)]
  simp

/-- The small-`Y` residual estimate.  It is stronger than both paper
residual error terms in this regime: the odd Euler product is bounded by
the absolute constant `exp 38`. -/
theorem residualMoment_le_small_cutoff
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hYL : Y < L) (hY : 2 ≤ Y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((log 4 + 5) * Y / log Y) * exp 38 := by
  have hw0 :
      ∀ p, 0 ≤ residualPrimeWeight L X q p :=
    fun p ↦ residualPrimeWeight_nonneg hq0 p
  have hw1 :
      ∀ p, residualPrimeWeight L X q p ≤ 1 :=
    fun p ↦ residualPrimeWeight_le hq1 le_rfl p
  have hw52 :
      ∀ p, residualPrimeWeight L X q p ≤ 5 / 2 :=
    fun p ↦ (hw1 p).trans (by norm_num)
  have hw2 :
      residualPrimeWeight L X q 2 ≤ 1 := by
    rw [residualPrimeWeight_two (by omega : 2 < L)]
  have hbase :=
    factorWeight_partialSum_le_eulerProduct hw0 hw1 hY
  have hprod :=
    factorialFactorEulerProduct_le_two_mul_exp hw0 hw52 hw2 Y
  rw [factorialOddPrimeMass_residualPrimeWeight_eq_zero_of_lt hYL] at hprod
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff : 0 ≤ (log 4 + 5) * (Y : ℝ) / log Y := by
    positivity
  rw [← partialSum_residualPrimeWeight_eq]
  unfold factorialFactorEulerProduct at hprod
  calc
    partialSum (factorWeight (residualPrimeWeight L X q)) Y
        ≤ ((log 4 + 5) * Y / log Y) *
            Y.factorial.factorization.prod (fun p e ↦
              ∑ k ∈ range (e + 1),
                (residualPrimeWeight L X q p / p) ^ k) :=
      hbase
    _ ≤ ((log 4 + 5) * Y / log Y) * (2 * exp (0 + 38)) :=
      mul_le_mul_of_nonneg_left hprod hcoeff
    _ = 2 * ((log 4 + 5) * Y / log Y) * exp 38 := by ring_nf

/-- A case split covering every `Y ≥ 2`, without ever applying Mertens to
a reversed interval. -/
theorem residualMoment_le_piecewise
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hY : 2 ≤ Y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      if L ≤ Y then
        2 * ((log 4 + 5) * Y / log Y) *
          exp
            (q * primeInvTailUpper (L - 1) (min X Y) +
              primeInvTailUpper (min X Y) Y + 38)
      else
        2 * ((log 4 + 5) * Y / log Y) * exp 38 := by
  by_cases hLY : L ≤ Y
  · rw [if_pos hLY]
    exact residualMoment_le_mertens
      hL hLX hLY hY hq0 hq1
  · rw [if_neg hLY]
    exact residualMoment_le_small_cutoff
      hL (Nat.lt_of_not_ge hLY) hY hq0 hq1

end Erdos327.Analytic

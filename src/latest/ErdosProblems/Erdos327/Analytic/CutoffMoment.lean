import ErdosProblems.Erdos327.Analytic.ResidualMean
import ErdosProblems.Erdos327.Analytic.WeightedMangoldtUniform
import ErdosProblems.Erdos327.Analytic.RoughCount

/-!
# Uniform cutoff moments

This file supplies the one-variable moments used in the centered maximal
tail argument.  All constants are independent of the moving cutoffs.
-/

namespace Erdos327.Analytic

open Finset Real

/-- The residual Euler-product estimate remains uniform when its interval
weight lies anywhere in `[0, 5/2]`. -/
theorem factorialFactorEulerProduct_residualPrimeWeight_uniform_le
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    factorialFactorEulerProduct (residualPrimeWeight L X q) Y ≤
      2 * exp (residualPrimeExponent L X q Y + 38) := by
  have hw0 :
      ∀ p, 0 ≤ residualPrimeWeight L X q p :=
    fun p ↦ residualPrimeWeight_nonneg hq0 p
  have hw :
      ∀ p, residualPrimeWeight L X q p ≤ 5 / 2 :=
    fun p ↦ residualPrimeWeight_le hq52 (by norm_num) p
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

/-- Uniform Halberstam--Richert residual moment for all
`0 ≤ q ≤ 5/2`. -/
theorem residualMoment_uniform_le_exp
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp (residualPrimeExponent L X q Y + 38) := by
  have hw0 :
      ∀ p, 0 ≤ residualPrimeWeight L X q p :=
    fun p ↦ residualPrimeWeight_nonneg hq0 p
  have hw :
      ∀ p, residualPrimeWeight L X q p ≤ 5 / 2 :=
    fun p ↦ residualPrimeWeight_le hq52 (by norm_num) p
  have hw2 :
      residualPrimeWeight L X q 2 ≤ 1 := by
    rw [residualPrimeWeight_two (by omega : 2 < L)]
  have hbase :=
    factorWeight_partialSum_le_eulerProduct_uniform hw0 hw hw2 hY
  have hprod :=
    factorialFactorEulerProduct_residualPrimeWeight_uniform_le
      hL hLX hLY hq0 hq52
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ (uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  rw [← partialSum_residualPrimeWeight_eq]
  unfold factorialFactorEulerProduct at hprod
  calc
    partialSum (factorWeight (residualPrimeWeight L X q)) Y
        ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
            Y.factorial.factorization.prod (fun p e ↦
              ∑ k ∈ range (e + 1),
                (residualPrimeWeight L X q p / p) ^ k) :=
      hbase
    _ ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          (2 * exp (residualPrimeExponent L X q Y + 38)) :=
      mul_le_mul_of_nonneg_left hprod hcoeff
    _ = 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp (residualPrimeExponent L X q Y + 38) := by ring

/-- Explicit Mertens version of the uniform residual moment. -/
theorem residualMoment_uniform_le_mertens
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (q * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) := by
  have hbase :=
    residualMoment_uniform_le_exp hL hLX hLY hY hq0 hq52
  have hexponent :
      residualPrimeExponent L X q Y + 38 ≤
        q * primeInvTailUpper (L - 1) (min X Y) +
          primeInvTailUpper (min X Y) Y + 38 := by
    linarith [residualPrimeExponent_le_mertens hL hLX hLY hq0]
  have hexp := exp_le_exp.mpr hexponent
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ 2 *
        ((uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y) := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  exact hbase.trans (mul_le_mul_of_nonneg_left hexp hcoeff)

/-- Full roughness implies the odd-prime roughness used by the residual
factor weight. -/
theorem rough_imp_oddRough
    {L n : ℕ} (hn : Rough L n) :
    OddRough L n := by
  intro p hpPrime hp2 hpL
  exact hn p hpPrime hpL

/-- The full-rough cutoff moment is bounded by the odd-rough moment. -/
theorem fullRoughMoment_le_oddRoughMoment
    {L X Y : ℕ} {q : ℝ} (hq0 : 0 ≤ q) :
    (∑ n ∈ Icc 1 Y,
        if Rough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      ∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0 := by
  apply sum_le_sum
  intro n hn
  by_cases hr : Rough L n
  · rw [if_pos hr, if_pos (rough_imp_oddRough hr)]
  · rw [if_neg hr]
    positivity

/-- Uniform Mertens bound for the full-rough centered cutoff moment. -/
theorem fullRoughMoment_uniform_le_mertens
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if Rough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (q * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) :=
  (fullRoughMoment_le_oddRoughMoment hq0).trans
    (residualMoment_uniform_le_mertens
      hL hLX hLY hY hq0 hq52)

/-- Odd reciprocal-prime baseline in the factorial support. -/
noncomputable def factorialOddPrimeBaseline (Y : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE Y).erase 2, 1 / (p : ℝ)

/-- Exponent for the unrestricted interval weight: every odd prime has
baseline weight one, and primes in `[L,min X Y]` receive the increment
`q - 1`. -/
noncomputable def intervalPrimeExponent
    (L X : ℕ) (q : ℝ) (Y : ℕ) : ℝ :=
  factorialOddPrimeBaseline Y +
    (q - 1) * primeInvTail (L - 1) (min X Y)

/-- Exact odd-prime mass decomposition for the unrestricted cutoff
weight. -/
theorem factorialOddPrimeMass_intervalPrimeWeight
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y) :
    factorialOddPrimeMass (intervalPrimeWeight L X q) Y =
      intervalPrimeExponent L X q Y := by
  classical
  let T := min X Y
  let s := (Nat.primesLE Y).erase 2
  let A := Nat.primesLE T \ Nat.primesLE (L - 1)
  have hTY : T ≤ Y := min_le_right _ _
  have hTX : T ≤ X := min_le_left _ _
  have hLT : L ≤ T := le_min hLX hLY
  have hLm1 : 2 ≤ L - 1 := by omega
  have hAsub : A ⊆ s := by
    intro p hp
    have hpT : p ∈ Nat.primesLE T := (mem_sdiff.mp hp).1
    have hpPrime := Nat.prime_of_mem_primesLE hpT
    have hpY : p ∈ Nat.primesLE Y :=
      Nat.mem_primesLE.mpr
        ⟨(Nat.le_of_mem_primesLE hpT).trans hTY, hpPrime⟩
    have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      exact (mem_sdiff.mp hp).2
        (Nat.mem_primesLE.mpr ⟨hLm1, Nat.prime_two⟩)
    exact mem_erase.mpr ⟨hp2, hpY⟩
  have hsA : s.filter (fun p ↦ p ∈ A) = A := by
    ext p
    simp only [mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨hAsub hp, hp⟩
  have hpoint (p : ℕ) (hp : p ∈ s) :
      intervalPrimeWeight L X q p / p =
        1 / (p : ℝ) +
          (if p ∈ A then (q - 1) / p else 0) := by
    have hpYmem : p ∈ Nat.primesLE Y := mem_of_mem_erase hp
    have hpY : p ≤ Y := Nat.le_of_mem_primesLE hpYmem
    have hpPrime := Nat.prime_of_mem_primesLE hpYmem
    have hpA : p ∈ A ↔ L ≤ p ∧ p ≤ T := by
      simp only [A, mem_sdiff, Nat.mem_primesLE, hpPrime, and_true]
      omega
    simp only [hpA]
    by_cases hpL : L ≤ p
    · by_cases hpT : p ≤ T
      · have hpX : p ≤ X := hpT.trans hTX
        simp [intervalPrimeWeight, hpL, hpX, hpT]
        ring
      · have hTp : T < p := Nat.lt_of_not_ge hpT
        have hXp : X < p := by
          by_contra h
          have hpX : p ≤ X := Nat.le_of_not_gt h
          exact hpT (le_min hpX hpY)
        simp [intervalPrimeWeight, hpL, hpT, Nat.not_le.mpr hXp]
    · have hpLtL : p < L := Nat.lt_of_not_ge hpL
      have hpT : p ≤ T := (Nat.le_of_lt hpLtL).trans hLT
      simp [intervalPrimeWeight, hpL, hpT]
  unfold factorialOddPrimeMass intervalPrimeExponent
  change
    (∑ p ∈ s, intervalPrimeWeight L X q p / p) =
      factorialOddPrimeBaseline Y +
        (q - 1) * (∑ p ∈ A, 1 / (p : ℝ))
  unfold factorialOddPrimeBaseline
  change
    (∑ p ∈ s, intervalPrimeWeight L X q p / p) =
      (∑ p ∈ s, 1 / (p : ℝ)) +
        (q - 1) * (∑ p ∈ A, 1 / (p : ℝ))
  calc
    (∑ p ∈ s, intervalPrimeWeight L X q p / p) =
        ∑ p ∈ s,
          (1 / (p : ℝ) +
            (if p ∈ A then (q - 1) / p else 0)) :=
      sum_congr rfl hpoint
    _ = (∑ p ∈ s, 1 / (p : ℝ)) +
        ∑ p ∈ A, (q - 1) / p := by
      rw [sum_add_distrib, Finset.sum_ite, sum_const_zero,
        add_zero, hsA]
    _ = (∑ p ∈ s, 1 / (p : ℝ)) +
        (q - 1) * (∑ p ∈ A, 1 / (p : ℝ)) := by
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro p _
      ring

/-- Euler-product bound for the unrestricted interval cutoff weight. -/
theorem factorialFactorEulerProduct_intervalPrimeWeight_uniform_le
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    factorialFactorEulerProduct (intervalPrimeWeight L X q) Y ≤
      2 * exp (intervalPrimeExponent L X q Y + 38) := by
  have hw0 : ∀ p, 0 ≤ intervalPrimeWeight L X q p := by
    intro p
    simp only [intervalPrimeWeight]
    split_ifs <;> positivity
  have hw : ∀ p, intervalPrimeWeight L X q p ≤ 5 / 2 := by
    intro p
    simp only [intervalPrimeWeight]
    split_ifs <;> linarith
  have hw2 : intervalPrimeWeight L X q 2 ≤ 1 := by
    simp [intervalPrimeWeight, show ¬L ≤ 2 by omega]
  calc
    factorialFactorEulerProduct (intervalPrimeWeight L X q) Y
        ≤ 2 * exp
            (factorialOddPrimeMass (intervalPrimeWeight L X q) Y + 38) :=
      factorialFactorEulerProduct_le_two_mul_exp hw0 hw hw2 Y
    _ = 2 * exp (intervalPrimeExponent L X q Y + 38) := by
      rw [factorialOddPrimeMass_intervalPrimeWeight hL hLX hLY]

/-- Exact interpretation of the unrestricted interval-weight partial
sum as a cutoff factor-count moment. -/
theorem partialSum_intervalPrimeWeight_eq
    {L X Y : ℕ} {q : ℝ} :
    partialSum (factorWeight (intervalPrimeWeight L X q)) Y =
      ∑ n ∈ Icc 1 Y, q ^ primeFactorCountBetween L X n := by
  unfold partialSum
  apply sum_congr rfl
  intro n hn
  exact factorWeight_intervalPrimeWeight
    (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)

/-- Uniform unrestricted cutoff moment for `0 ≤ q ≤ 5/2`. -/
theorem intervalMoment_uniform_le_exp
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y, q ^ primeFactorCountBetween L X n) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp (intervalPrimeExponent L X q Y + 38) := by
  have hw0 : ∀ p, 0 ≤ intervalPrimeWeight L X q p := by
    intro p
    simp only [intervalPrimeWeight]
    split_ifs <;> positivity
  have hw : ∀ p, intervalPrimeWeight L X q p ≤ 5 / 2 := by
    intro p
    simp only [intervalPrimeWeight]
    split_ifs <;> linarith
  have hw2 : intervalPrimeWeight L X q 2 ≤ 1 := by
    simp [intervalPrimeWeight, show ¬L ≤ 2 by omega]
  have hbase :=
    factorWeight_partialSum_le_eulerProduct_uniform hw0 hw hw2 hY
  have hprod :=
    factorialFactorEulerProduct_intervalPrimeWeight_uniform_le
      hL hLX hLY hq0 hq52
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ (uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  rw [← partialSum_intervalPrimeWeight_eq]
  unfold factorialFactorEulerProduct at hprod
  calc
    partialSum (factorWeight (intervalPrimeWeight L X q)) Y
        ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
            Y.factorial.factorization.prod (fun p e ↦
              ∑ k ∈ range (e + 1),
                (intervalPrimeWeight L X q p / p) ^ k) :=
      hbase
    _ ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          (2 * exp (intervalPrimeExponent L X q Y + 38)) :=
      mul_le_mul_of_nonneg_left hprod hcoeff
    _ = 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp (intervalPrimeExponent L X q Y + 38) := by ring

/-- Explicit upper envelope from Mertens' reciprocal-prime theorem. -/
noncomputable def primeInvSumUpper (Y : ℕ) : ℝ :=
  log (log Y) +
    Mertens.Weight.M (f := Mertens.Weight.prime) +
    (log 4 + 3) / log Y

theorem primeInvSum_le_primeInvSumUpper
    {Y : ℕ} (hY : 2 ≤ Y) :
    primeInvSum Y ≤ primeInvSumUpper Y :=
  primeInvSum_le hY

theorem factorialOddPrimeBaseline_le_primeInvSum (Y : ℕ) :
    factorialOddPrimeBaseline Y ≤ primeInvSum Y := by
  unfold factorialOddPrimeBaseline primeInvSum
  apply sum_le_sum_of_subset_of_nonneg (erase_subset 2 (Nat.primesLE Y))
  intro p hpY hpErase
  positivity

/-- Mertens upper envelope for the unrestricted interval exponent.  The
assumption `1 ≤ q` makes the cutoff-tail coefficient nonnegative. -/
theorem intervalPrimeExponent_le_mertens
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq1 : 1 ≤ q) :
    intervalPrimeExponent L X q Y ≤
      primeInvSumUpper Y +
        (q - 1) * primeInvTailUpper (L - 1) (min X Y) := by
  have hLm1 : 2 ≤ L - 1 := by omega
  have hLT : L - 1 ≤ min X Y := by omega
  unfold intervalPrimeExponent
  exact add_le_add
    ((factorialOddPrimeBaseline_le_primeInvSum Y).trans
      (primeInvSum_le_primeInvSumUpper hY))
    (mul_le_mul_of_nonneg_left
      (primeInvTail_le_primeInvTailUpper hLm1 hLT)
      (sub_nonneg.mpr hq1))

/-- Explicit Mertens form of the unrestricted centered cutoff moment. -/
theorem intervalMoment_uniform_le_mertens
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hq1 : 1 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y, q ^ primeFactorCountBetween L X n) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (primeInvSumUpper Y +
            (q - 1) * primeInvTailUpper (L - 1) (min X Y) + 38) := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq1
  have hbase :=
    intervalMoment_uniform_le_exp
      hL hLX hLY hY hq0 hq52
  have hexponent :
      intervalPrimeExponent L X q Y + 38 ≤
        primeInvSumUpper Y +
          (q - 1) * primeInvTailUpper (L - 1) (min X Y) + 38 := by
    linarith [intervalPrimeExponent_le_mertens
      hL hLX hLY hY hq1]
  have hexp := exp_le_exp.mpr hexponent
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ 2 *
        ((uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y) := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  exact hbase.trans (mul_le_mul_of_nonneg_left hexp hcoeff)

/-- Centered maximal-tail input without a roughness condition. -/
theorem centeredUnrestrictedCutoffMoment
    {L X Y : ℕ} {z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y, z ^ primeFactorCountBetween L X n) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (primeInvSumUpper Y +
            (z - 1) * primeInvTailUpper (L - 1) (min X Y) + 38) :=
  intervalMoment_uniform_le_mertens
    hL hLX hLY hY hz1 hz52

/-- Centered maximal-tail input with odd-prime roughness. -/
theorem centeredOddRoughCutoffMoment
    {L X Y : ℕ} {z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then z ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (z * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) :=
  residualMoment_uniform_le_mertens
    hL hLX hLY hY (le_trans (by norm_num) hz1) hz52

/-- Centered maximal-tail input with full roughness. -/
theorem centeredFullRoughCutoffMoment
    {L X Y : ℕ} {z : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) (hz1 : 1 ≤ z) (hz52 : z ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if Rough L n then z ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp
          (z * primeInvTailUpper (L - 1) (min X Y) +
            primeInvTailUpper (min X Y) Y + 38) :=
  fullRoughMoment_uniform_le_mertens
    hL hLX hLY hY (le_trans (by norm_num) hz1) hz52

/-- Uniform residual moment below the roughness cutoff.  No odd prime in
the factorial support carries a nonzero residual weight. -/
theorem residualMoment_uniform_le_small_cutoff
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hYL : Y < L) (hY : 2 ≤ Y)
    (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if OddRough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp 38 := by
  have hw0 :
      ∀ p, 0 ≤ residualPrimeWeight L X q p :=
    fun p ↦ residualPrimeWeight_nonneg hq0 p
  have hw :
      ∀ p, residualPrimeWeight L X q p ≤ 5 / 2 :=
    fun p ↦ residualPrimeWeight_le hq52 (by norm_num) p
  have hw2 :
      residualPrimeWeight L X q 2 ≤ 1 := by
    rw [residualPrimeWeight_two (by omega : 2 < L)]
  have hbase :=
    factorWeight_partialSum_le_eulerProduct_uniform hw0 hw hw2 hY
  have hprod :=
    factorialFactorEulerProduct_le_two_mul_exp hw0 hw hw2 Y
  rw [factorialOddPrimeMass_residualPrimeWeight_eq_zero_of_lt hYL] at hprod
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ (uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  rw [← partialSum_residualPrimeWeight_eq]
  unfold factorialFactorEulerProduct at hprod
  calc
    partialSum (factorWeight (residualPrimeWeight L X q)) Y
        ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
            Y.factorial.factorization.prod (fun p e ↦
              ∑ k ∈ range (e + 1),
                (residualPrimeWeight L X q p / p) ^ k) :=
      hbase
    _ ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          (2 * exp (0 + 38)) :=
      mul_le_mul_of_nonneg_left hprod hcoeff
    _ = 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp 38 := by ring_nf

/-- Full-rough small-cutoff moment, obtained from the odd-rough estimate. -/
theorem fullRoughMoment_uniform_le_small_cutoff
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hYL : Y < L) (hY : 2 ≤ Y)
    (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y,
        if Rough L n then q ^ primeFactorCountBetween L X n else 0) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp 38 :=
  (fullRoughMoment_le_oddRoughMoment hq0).trans
    (residualMoment_uniform_le_small_cutoff
      hL hYL hY hq0 hq52)

/-- Below `L`, the unrestricted interval weight is identically one on
the odd factorial support. -/
theorem factorialOddPrimeMass_intervalPrimeWeight_eq_baseline_of_lt
    {L X Y : ℕ} {q : ℝ} (hYL : Y < L) :
    factorialOddPrimeMass (intervalPrimeWeight L X q) Y =
      factorialOddPrimeBaseline Y := by
  unfold factorialOddPrimeMass factorialOddPrimeBaseline
  apply sum_congr rfl
  intro p hp
  have hpYmem : p ∈ Nat.primesLE Y := mem_of_mem_erase hp
  have hpY : p ≤ Y := Nat.le_of_mem_primesLE hpYmem
  have hpL : ¬L ≤ p := by omega
  simp [intervalPrimeWeight, hpL]

/-- Uniform unrestricted cutoff moment for `Y < L`.  The cutoff factor
count is actually zero here; the Euler-product proof records the same fact
without a separate factorization argument. -/
theorem intervalMoment_uniform_le_small_cutoff
    {L X Y : ℕ} {q : ℝ}
    (hL : 3 ≤ L) (hYL : Y < L) (hY : 2 ≤ Y)
    (hq0 : 0 ≤ q) (hq52 : q ≤ 5 / 2) :
    (∑ n ∈ Icc 1 Y, q ^ primeFactorCountBetween L X n) ≤
      2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
        exp (primeInvSumUpper Y + 38) := by
  have hw0 : ∀ p, 0 ≤ intervalPrimeWeight L X q p := by
    intro p
    simp only [intervalPrimeWeight]
    split_ifs <;> positivity
  have hw : ∀ p, intervalPrimeWeight L X q p ≤ 5 / 2 := by
    intro p
    simp only [intervalPrimeWeight]
    split_ifs <;> linarith
  have hw2 : intervalPrimeWeight L X q 2 ≤ 1 := by
    simp [intervalPrimeWeight, show ¬L ≤ 2 by omega]
  have hbase :=
    factorWeight_partialSum_le_eulerProduct_uniform hw0 hw hw2 hY
  have hprod :=
    factorialFactorEulerProduct_le_two_mul_exp hw0 hw hw2 Y
  rw [factorialOddPrimeMass_intervalPrimeWeight_eq_baseline_of_lt hYL] at hprod
  have hmass :
      factorialOddPrimeBaseline Y ≤ primeInvSumUpper Y :=
    (factorialOddPrimeBaseline_le_primeInvSum Y).trans
      (primeInvSum_le_primeInvSumUpper hY)
  have hexponent :
      factorialOddPrimeBaseline Y + 38 ≤ primeInvSumUpper Y + 38 := by
    linarith
  have hexp := exp_le_exp.mpr hexponent
  have hprod' :
      factorialFactorEulerProduct (intervalPrimeWeight L X q) Y ≤
        2 * exp (primeInvSumUpper Y + 38) :=
    hprod.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcoeff :
      0 ≤ (uniformWeightedMangoldtConstant + 1) * (Y : ℝ) / log Y := by
    positivity [uniformWeightedMangoldtConstant_nonneg]
  rw [← partialSum_intervalPrimeWeight_eq]
  unfold factorialFactorEulerProduct at hprod'
  calc
    partialSum (factorWeight (intervalPrimeWeight L X q)) Y
        ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
            Y.factorial.factorization.prod (fun p e ↦
              ∑ k ∈ range (e + 1),
                (intervalPrimeWeight L X q p / p) ^ k) :=
      hbase
    _ ≤ ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          (2 * exp (primeInvSumUpper Y + 38)) :=
      mul_le_mul_of_nonneg_left hprod' hcoeff
    _ = 2 * ((uniformWeightedMangoldtConstant + 1) * Y / log Y) *
          exp (primeInvSumUpper Y + 38) := by ring

/-- Every positive cutoff moment at `Y = 1` consists only of the term
`n = 1`. -/
theorem intervalMoment_one (L X : ℕ) (q : ℝ) :
    (∑ n ∈ Icc 1 1, q ^ primeFactorCountBetween L X n) = 1 := by
  simp [primeFactorCountBetween]

/-- The full-rough moment at `Y = 1` also consists only of `n = 1`. -/
theorem fullRoughMoment_one (L X : ℕ) (q : ℝ) :
    (∑ n ∈ Icc 1 1,
      if Rough L n then q ^ primeFactorCountBetween L X n else 0) = 1 := by
  have hrough : Rough L 1 := by
    intro p hpPrime hpL
    exact hpPrime.not_dvd_one
  simp [hrough, primeFactorCountBetween]

end Erdos327.Analytic

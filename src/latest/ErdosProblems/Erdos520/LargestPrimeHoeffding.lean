import ErdosProblems.Erdos520.AdaptiveHoeffding
import ErdosProblems.Erdos520.LargestPrimeDecomposition
import ErdosProblems.Erdos520.BonamiModel

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem520

/-!
# Stopped Hoeffding for the largest-prime sum

The coefficient multiplying the sign at a prime `p` only uses signs at
primes strictly below `p`.  This file packages that observation as a
finite predictable Rademacher transform and transfers the finite-cube
Hoeffding bound to the infinite product law `μ`.
-/

/-- Replace the first `n` Boolean coordinates of `old` by a finite vector. -/
def overwritePrefix {n : ℕ} (old : Omega) (v : Fin n → Bool) : Omega :=
  fun q => if hq : q < n then v ⟨q, hq⟩ else old q

/-- Restrict an infinite sign configuration to its first `n` coordinates. -/
def restrictPrefix (n : ℕ) (omega : Omega) : Fin n → Bool :=
  fun q => omega q

theorem measurable_restrictPrefix (n : ℕ) :
    Measurable (restrictPrefix n) := by
  simpa [restrictPrefix] using!
    (measurable_pi_lambda _ fun q : Fin n =>
      (measurable_pi_apply q.1 : Measurable (fun omega : Omega => omega q.1)))

@[simp] theorem overwritePrefix_apply_lt {n q : ℕ} (old : Omega)
    (v : Fin n → Bool) (hq : q < n) :
    overwritePrefix old v q = v ⟨q, hq⟩ := by
  simp [overwritePrefix, hq]

@[simp] theorem overwritePrefix_restrictPrefix_lt {n q : ℕ}
    (old omega : Omega) (hq : q < n) :
    overwritePrefix old (restrictPrefix n omega) q = omega q := by
  simp [overwritePrefix, restrictPrefix, hq]

/-- A strict smooth sum only sees coordinates at primes below its cutoff. -/
theorem Ψ'_eq_of_eq_on_primesBelow {omega omega' : Omega} {z p : ℕ}
    (h : ∀ q ∈ p.primesBelow, omega q = omega' q) :
    Ψ' omega z p = Ψ' omega' z p := by
  classical
  unfold Ψ'
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsq : Squarefree n
  · rw [f_eq_prod_primeFactors_of_squarefree omega hsq,
      f_eq_prod_primeFactors_of_squarefree omega' hsq]
    apply Finset.prod_congr rfl
    intro q hq
    have hsmooth := (Nat.mem_smoothNumbersUpTo.mp hn).2
    have hqbelow : q ∈ p.primesBelow :=
      Nat.primeFactors_subset_of_mem_smoothNumbers hsmooth hq
    unfold ε
    rw [h q hqbelow]
  · simp [f_eq_zero_of_not_squarefree, hsq]

/-- The coefficient at time `p` is obtained by filling only the already
revealed coordinates `q < p`. -/
noncomputable def largestPrimePredictableCoefficients
    (old : Omega) (x a b : ℕ) : PredictableCoefficients (b + 1) :=
  fun p past =>
    if p.1 ∈ freshPrimes a b then
      Ψ' (overwritePrefix old past) (x / p.1) p.1
    else 0

lemma largestPrime_coefficient_eq_fullPrefix (old : Omega)
    (x a b : ℕ) (v : Fin (b + 1) → Bool) (p : Fin (b + 1)) :
    largestPrimePredictableCoefficients old x a b p (finPast v p) =
      if p.1 ∈ freshPrimes a b then
        Ψ' (overwritePrefix old v) (x / p.1) p.1
      else 0 := by
  classical
  unfold largestPrimePredictableCoefficients
  split_ifs with hp
  · apply Ψ'_eq_of_eq_on_primesBelow
    intro q hq
    have hqp : q < p.1 := (Nat.mem_primesBelow.mp hq).1
    simp [finPast, overwritePrefix, hqp, hqp.trans p.2]
  · rfl

lemma freshPrimes_subset_range_succ (a b : ℕ) :
    freshPrimes a b ⊆ Finset.range (b + 1) := by
  intro p hp
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_freshPrimes.mp hp).2.2)

theorem predictableSum_largestPrimePredictableCoefficients
    (old : Omega) (x a b : ℕ) (v : Fin (b + 1) → Bool) :
    predictableSum (largestPrimePredictableCoefficients old x a b) v =
      largestPrimeMain (overwritePrefix old v) x a b := by
  classical
  unfold predictableSum largestPrimeMain
  have hsubset := freshPrimes_subset_range_succ a b
  have hfilter :
      (Finset.range (b + 1)).filter (fun p => p ∈ freshPrimes a b) =
        freshPrimes a b := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hsubset hp, hp⟩
  rw [Finset.sum_fin_eq_sum_range, ← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : p < b + 1 := Finset.mem_range.mp hp
  rw [dif_pos hpb]
  rw [largestPrime_coefficient_eq_fullPrefix]
  by_cases hpfresh : p ∈ freshPrimes a b
  · simp [hpfresh, coinSign, ε, overwritePrefix, hpb, mul_comm]
  · simp [hpfresh]

theorem predictableSquareSum_largestPrimePredictableCoefficients
    (old : Omega) (x a b : ℕ) (v : Fin (b + 1) → Bool) :
    predictableSquareSum (largestPrimePredictableCoefficients old x a b) v =
      largestPrimeQuadraticVariation (overwritePrefix old v) x a b := by
  classical
  unfold predictableSquareSum largestPrimeQuadraticVariation
  have hsubset := freshPrimes_subset_range_succ a b
  have hfilter :
      (Finset.range (b + 1)).filter (fun p => p ∈ freshPrimes a b) =
        freshPrimes a b := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hsubset hp, hp⟩
  rw [Finset.sum_fin_eq_sum_range, ← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : p < b + 1 := Finset.mem_range.mp hp
  rw [dif_pos hpb]
  rw [largestPrime_coefficient_eq_fullPrefix]
  by_cases hpfresh : p ∈ freshPrimes a b
  · simp [hpfresh]
  · simp [hpfresh]

/-- The largest-prime sum only depends on coordinates at most `b`. -/
theorem largestPrimeMain_overwritePrefix_restrictPrefix (old omega : Omega)
    (x a b : ℕ) :
    largestPrimeMain (overwritePrefix old (restrictPrefix (b + 1) omega)) x a b =
      largestPrimeMain omega x a b := by
  classical
  unfold largestPrimeMain
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : p < b + 1 := Nat.lt_succ_of_le (mem_freshPrimes.mp hp).2.2
  rw [ε]
  simp only [overwritePrefix_restrictPrefix_lt old omega hpb]
  congr 1
  apply Ψ'_eq_of_eq_on_primesBelow
  intro q hq
  have hqp : q < p := (Nat.mem_primesBelow.mp hq).1
  exact overwritePrefix_restrictPrefix_lt old omega (hqp.trans hpb)

/-- The predictable quadratic variation only depends on coordinates at most
`b`. -/
theorem largestPrimeQuadraticVariation_overwritePrefix_restrictPrefix
    (old omega : Omega) (x a b : ℕ) :
    largestPrimeQuadraticVariation
        (overwritePrefix old (restrictPrefix (b + 1) omega)) x a b =
      largestPrimeQuadraticVariation omega x a b := by
  classical
  unfold largestPrimeQuadraticVariation
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg (fun r : ℝ => |r| ^ 2)
  apply Ψ'_eq_of_eq_on_primesBelow
  intro q hq
  have hqp : q < p := (Nat.mem_primesBelow.mp hq).1
  have hpb : p < b + 1 := Nat.lt_succ_of_le (mem_freshPrimes.mp hp).2.2
  exact overwritePrefix_restrictPrefix_lt old omega (hqp.trans hpb)

/-- Under `μ`, every finite prefix has the finite product fair-coin law. -/
theorem map_restrictPrefix_mu (n : ℕ) :
    μ.map (restrictPrefix n) = Measure.pi (fun _ : Fin n => coin) := by
  let X : (i : Fin n) → Omega → Bool := fun i omega => omega i
  have hIndep : iIndepFun X μ := by
    exact iIndepFun_coordinates.precomp Fin.val_injective
  have hXmeas (i : Fin n) : AEMeasurable (X i) μ := by
    simpa [X] using!
      (measurable_pi_apply i.1 : Measurable (fun omega : Omega => omega i.1)).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
      (μ := μ) (f := X) hXmeas).mp hIndep
  calc
    μ.map (restrictPrefix n) = μ.map (fun omega i => X i omega) := by
      rfl
    _ = Measure.pi (fun i : Fin n => μ.map (X i)) := hmap
    _ = Measure.pi (fun _ : Fin n => coin) := by
      congr 1
      funext i
      simpa [μ, X] using!
        (Measure.infinitePi_map_eval (fun _ : ℕ => coin) i.1)

/-- Finite products of fair coins integrate by normalized counting measure. -/
theorem integral_fin_coin_eq_fintypeAverage (n : ℕ)
    (g : (Fin n → Bool) → ℝ) :
    ∫ v, g v ∂Measure.pi (fun _ : Fin n => coin) = fintypeAverage g := by
  rw [MeasureTheory.integral_fintype]
  · have hmass (v : Fin n → Bool) :
        (Measure.pi (fun _ : Fin n => coin)).real {v} =
          1 / (Fintype.card (Fin n → Bool) : ℝ) := by
      rw [Measure.real, Measure.pi_singleton]
      have hcoin (i : Fin n) : coin {v i} = (1 / 2 : ℝ≥0∞) := by
        cases v i <;> simp [coin]
      simp_rw [hcoin]
      rw [Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow]
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      norm_num
      rw [one_div_pow]
      simp [one_div]
    unfold fintypeAverage
    simp_rw [hmass, smul_eq_mul]
    simp_rw [show ∀ v : Fin n → Bool,
      1 / (Fintype.card (Fin n → Bool) : ℝ) * g v =
        g v / (Fintype.card (Fin n → Bool) : ℝ) by intro v; ring]
    rw [Finset.sum_div]
  · exact Integrable.of_finite

/-- Integration of a finite-prefix observable under `μ` is normalized finite
averaging. -/
theorem integral_comp_restrictPrefix_eq_fintypeAverage (n : ℕ)
    (g : (Fin n → Bool) → ℝ) :
    ∫ omega, g (restrictPrefix n omega) ∂μ = fintypeAverage g := by
  calc
    (∫ omega, g (restrictPrefix n omega) ∂μ) =
        ∫ v, g v ∂μ.map (restrictPrefix n) := by
      symm
      exact integral_map (measurable_restrictPrefix n).aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ v, g v ∂Measure.pi (fun _ : Fin n => coin) := by
      rw [map_restrictPrefix_mu]
    _ = fintypeAverage g := integral_fin_coin_eq_fintypeAverage n g

/-- On a genuine infinite configuration, the prefix transform is exactly the
largest-prime main term. -/
theorem predictableSum_restrictPrefix_eq_largestPrimeMain
    (old omega : Omega) (x a b : ℕ) :
    predictableSum (largestPrimePredictableCoefficients old x a b)
        (restrictPrefix (b + 1) omega) =
      largestPrimeMain omega x a b := by
  rw [predictableSum_largestPrimePredictableCoefficients]
  exact largestPrimeMain_overwritePrefix_restrictPrefix old omega x a b

/-- On a genuine infinite configuration, the prefix square sum is exactly
the predictable quadratic variation of the largest-prime main term. -/
theorem predictableSquareSum_restrictPrefix_eq_largestPrimeQuadraticVariation
    (old omega : Omega) (x a b : ℕ) :
    predictableSquareSum (largestPrimePredictableCoefficients old x a b)
        (restrictPrefix (b + 1) omega) =
      largestPrimeQuadraticVariation omega x a b := by
  rw [predictableSquareSum_largestPrimePredictableCoefficients]
  exact largestPrimeQuadraticVariation_overwritePrefix_restrictPrefix
    old omega x a b

/-- Integral (hence probability) form of stopped Hoeffding for the exact
largest-prime martingale transform. -/
theorem integral_largestPrime_stoppedTail_le (x a b : ℕ) {u T : ℝ}
    (hu : 0 ≤ u) (hT : 0 < T) :
    (∫ omega : Omega,
      if u ≤ |largestPrimeMain omega x a b| ∧
          largestPrimeQuadraticVariation omega x a b ≤ T
      then (1 : ℝ) else 0 ∂μ) ≤
      2 * Real.exp (-u ^ 2 / (2 * T)) := by
  let old : Omega := fun _ => false
  let coeff := largestPrimePredictableCoefficients old x a b
  let g : (Fin (b + 1) → Bool) → ℝ := fun v =>
    if u ≤ |predictableSum coeff v| ∧
        predictableSquareSum coeff v ≤ T then 1 else 0
  have heq :
      (fun omega : Omega =>
        if u ≤ |largestPrimeMain omega x a b| ∧
            largestPrimeQuadraticVariation omega x a b ≤ T
        then (1 : ℝ) else 0) =
      fun omega => g (restrictPrefix (b + 1) omega) := by
    funext omega
    dsimp [g, coeff]
    rw [predictableSum_restrictPrefix_eq_largestPrimeMain,
      predictableSquareSum_restrictPrefix_eq_largestPrimeQuadraticVariation]
  calc
    (∫ omega : Omega,
        if u ≤ |largestPrimeMain omega x a b| ∧
            largestPrimeQuadraticVariation omega x a b ≤ T
        then (1 : ℝ) else 0 ∂μ) =
        fintypeAverage g := by
      rw [heq]
      exact integral_comp_restrictPrefix_eq_fintypeAverage (b + 1) g
    _ ≤ 2 * Real.exp (-u ^ 2 / (2 * T)) := by
      exact predictable_absTail_average_le coeff hu hT

theorem measurable_largestPrimeMain (x a b : ℕ) :
    Measurable (fun omega : Omega => largestPrimeMain omega x a b) := by
  let old : Omega := fun _ => false
  let coeff := largestPrimePredictableCoefficients old x a b
  have heq : (fun omega : Omega => largestPrimeMain omega x a b) =
      fun omega => predictableSum coeff (restrictPrefix (b + 1) omega) := by
    funext omega
    exact (predictableSum_restrictPrefix_eq_largestPrimeMain
      old omega x a b).symm
  rw [heq]
  exact (measurable_of_finite (predictableSum coeff)).comp
    (measurable_restrictPrefix (b + 1))

theorem measurable_largestPrimeQuadraticVariation (x a b : ℕ) :
    Measurable
      (fun omega : Omega => largestPrimeQuadraticVariation omega x a b) := by
  let old : Omega := fun _ => false
  let coeff := largestPrimePredictableCoefficients old x a b
  have heq :
      (fun omega : Omega => largestPrimeQuadraticVariation omega x a b) =
      fun omega => predictableSquareSum coeff (restrictPrefix (b + 1) omega) := by
    funext omega
    exact (predictableSquareSum_restrictPrefix_eq_largestPrimeQuadraticVariation
      old omega x a b).symm
  rw [heq]
  exact (measurable_of_finite (predictableSquareSum coeff)).comp
    (measurable_restrictPrefix (b + 1))

/-- Stopped Hoeffding as a direct probability bound under the model law
`μ`.  No martingale or concentration hypothesis remains in this statement. -/
theorem largestPrime_stoppedTail_measureReal_le (x a b : ℕ) {u T : ℝ}
    (hu : 0 ≤ u) (hT : 0 < T) :
    μ.real {omega : Omega |
      u ≤ |largestPrimeMain omega x a b| ∧
        largestPrimeQuadraticVariation omega x a b ≤ T} ≤
      2 * Real.exp (-u ^ 2 / (2 * T)) := by
  have hs : MeasurableSet {omega : Omega |
      u ≤ |largestPrimeMain omega x a b| ∧
        largestPrimeQuadraticVariation omega x a b ≤ T} :=
    (measurableSet_le measurable_const (measurable_largestPrimeMain x a b).abs).inter
      (measurableSet_le (measurable_largestPrimeQuadraticVariation x a b)
        measurable_const)
  rw [← integral_indicator_one hs]
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using!
    integral_largestPrime_stoppedTail_le x a b hu hT

end Erdos.Problem520

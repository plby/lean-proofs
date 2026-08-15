/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import BoundedGaps.BombieriVinogradov.Analytic.PrimeCountingLogSaving
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic

/-!
# Uniform prime residue estimates for Erdős Problem 697

This file extracts a pointwise prime-counting estimate from the audited
aggregate logarithmic-saving theorem in `BoundedGaps`, then supplies the
finite Abel-summation interface used to pass to reciprocal-prime weights.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos697.PrimeResidues

noncomputable section

open BoundedGaps.Maynard

private theorem progressionDiscrepancy_nonneg (x q a : ℕ) :
    0 ≤ progressionDiscrepancy x q a := by
  unfold progressionDiscrepancy
  positivity

private theorem maxProgressionDiscrepancy_nonneg (x q : ℕ) :
    0 ≤ maxProgressionDiscrepancy x q := by
  unfold maxProgressionDiscrepancy
  split_ifs with hq
  · obtain ⟨a, ha⟩ := coprimeResidues_nonempty hq
    exact (progressionDiscrepancy_nonneg x q a).trans
      (Finset.le_sup' (progressionDiscrepancy x q) ha)
  · exact le_rfl

private theorem progressionDiscrepancy_le_max
    {x q a : ℕ} (hq : 0 < q) (ha : a ∈ coprimeResidues q) :
    progressionDiscrepancy x q a ≤ maxProgressionDiscrepancy x q := by
  rw [maxProgressionDiscrepancy, dif_pos hq]
  exact Finset.le_sup' (progressionDiscrepancy x q) ha

/-- A pointwise version of the logarithmic-saving prime-count estimate.
The constants are uniform in the endpoint, modulus, and reduced residue. -/
theorem exists_progressionDiscrepancy_le_logSaving :
    ∀ A : ℝ, 0 ≤ A →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          ∀ q : ℕ, 1 ≤ q →
            (q : ℝ) ≤ Real.sqrt (x : ℝ) /
                Real.rpow (Real.log (x : ℝ)) (A + 5) →
              ∀ a ∈ coprimeResidues q,
                progressionDiscrepancy x q a ≤
                  C * (x : ℝ) /
                    Real.rpow (Real.log (x : ℝ)) A := by
  intro A hA
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_sum_maxProgressionDiscrepancy_le_logSaving_allCutoffs A hA
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro x hx q hq hqrange a ha
  have hqpos : 0 < q := by omega
  have hqmem : q ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr ⟨hq, le_rfl⟩
  have hmaxle : maxProgressionDiscrepancy x q ≤
      ∑ d ∈ Finset.Icc 1 q, maxProgressionDiscrepancy x d := by
    exact Finset.single_le_sum
      (fun d _ => maxProgressionDiscrepancy_nonneg x d) hqmem
  exact (progressionDiscrepancy_le_max hqpos ha).trans
    (hmaxle.trans (hbound x hx q hqrange))

/-- The signed coefficient whose cumulative sum is the prime-count
discrepancy in one residue class. -/
def centeredPrimeCoefficient (q a n : ℕ) : ℝ :=
  (if n.Prime ∧ n % q = a % q then 1 else 0) -
    (q.totient : ℝ)⁻¹ * (if n.Prime then 1 else 0)

theorem sum_centeredPrimeCoefficient (x q a : ℕ) :
    (∑ n ∈ Finset.Icc 0 x, centeredPrimeCoefficient q a n) =
      (primeCountUpTo x q a : ℝ) -
        (primeCountTotal x : ℝ) / (q.totient : ℝ) := by
  classical
  unfold centeredPrimeCoefficient
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hprogression :
      (∑ n ∈ Finset.Icc 0 x,
        if n.Prime ∧ n % q = a % q then (1 : ℝ) else 0) =
        (primeCountUpTo x q a : ℝ) := by
    unfold primeCountUpTo
    rw [Nat.range_succ_eq_Icc_zero, Finset.card_eq_sum_ones]
    push_cast
    simp only [Finset.sum_filter]
  have htotal :
      (∑ n ∈ Finset.Icc 0 x, if n.Prime then (1 : ℝ) else 0) =
        (primeCountTotal x : ℝ) := by
    unfold primeCountTotal
    rw [← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_eq_filter_Icc_zero, Finset.card_eq_sum_ones]
    push_cast
    simp only [Finset.sum_filter]
  rw [hprogression, htotal]
  simp only [div_eq_mul_inv]
  ring

/-- Exact finite partial summation for the weight `1/(n-1)`.  This is the
form consumed by the uniform weighted-residue estimate. -/
theorem centeredPrimeWeight_Ioc_eq_abel
    {L U q a : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) - 1)⁻¹ * centeredPrimeCoefficient q a n) =
      (((U : ℝ) - 1)⁻¹ *
          ((primeCountUpTo U q a : ℝ) -
            (primeCountTotal U : ℝ) / (q.totient : ℝ))) -
      (((L : ℝ) - 1)⁻¹ *
          ((primeCountUpTo L q a : ℝ) -
            (primeCountTotal L : ℝ) / (q.totient : ℝ))) +
      ∫ t in Set.Ioc (L : ℝ) U,
        ((t - 1)⁻¹ ^ 2) *
          ((primeCountUpTo ⌊t⌋₊ q a : ℝ) -
            (primeCountTotal ⌊t⌋₊ : ℝ) / (q.totient : ℝ)) := by
  let f : ℝ → ℝ := fun t => (t - 1)⁻¹
  have hDiff : ∀ t ∈ Set.Icc (L : ℝ) U,
      DifferentiableAt ℝ f t := by
    intro t ht
    dsimp [f]
    fun_prop (disch := linarith [show (1 : ℝ) < L by exact_mod_cast (by omega : 1 < L), ht.1])
  have hDeriv : ∀ t : ℝ, 1 < t → deriv f t = -((t - 1)⁻¹ ^ 2) := by
    intro t ht
    have hne : t - 1 ≠ 0 := by linarith
    have hcomp := (hasDerivAt_inv hne).comp t
      ((hasDerivAt_id t).sub_const 1)
    simpa [f, Function.comp_def, inv_pow, one_div, neg_div] using hcomp.deriv
  have hLreal : (1 : ℝ) < L := by
    exact_mod_cast (show 1 < L by omega)
  have hDerivIntegrable : IntegrableOn (deriv f)
      (Set.Icc (L : ℝ) U) := by
    refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousWithinAt.congr ?_
        (fun y hy => hDeriv y (hLreal.trans_le hy.1))
        (hDeriv t (hLreal.trans_le ht.1))
    · have ht1 : 1 < t := lt_of_lt_of_le
        hLreal ht.1
      have hne : t - 1 ≠ 0 := by linarith
      exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    (centeredPrimeCoefficient q a) hLU hDiff hDerivIntegrable
  rw [sum_centeredPrimeCoefficient, sum_centeredPrimeCoefficient] at hAbel
  have hIntegral :
      (∫ t in Set.Ioc (L : ℝ) U,
        deriv f t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, centeredPrimeCoefficient q a k) =
        -(∫ t in Set.Ioc (L : ℝ) U,
          ((t - 1)⁻¹ ^ 2) *
            ((primeCountUpTo ⌊t⌋₊ q a : ℝ) -
              (primeCountTotal ⌊t⌋₊ : ℝ) / (q.totient : ℝ))) := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht1 : 1 < t := hLreal.trans ht.1
    rw [hDeriv t ht1, sum_centeredPrimeCoefficient]
    ring
  rw [hAbel, hIntegral]
  simp only [f]
  ring

/-- The Abel kernel occurring in `centeredPrimeWeight_Ioc_eq_abel` is
interval-integrable. -/
theorem intervalIntegrable_centeredPrimeAbelKernel
    {L U q a : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    IntervalIntegrable
      (fun t : ℝ => ((t - 1)⁻¹ ^ 2) *
        ((primeCountUpTo ⌊t⌋₊ q a : ℝ) -
          (primeCountTotal ⌊t⌋₊ : ℝ) / (q.totient : ℝ)))
      volume (L : ℝ) U := by
  let f : ℝ → ℝ := fun t => (t - 1)⁻¹
  let c : ℕ → ℝ := centeredPrimeCoefficient q a
  have hLreal : (1 : ℝ) < L := by
    exact_mod_cast (show 1 < L by omega)
  have hDeriv : ∀ t : ℝ, 1 < t → deriv f t = -((t - 1)⁻¹ ^ 2) := by
    intro t ht
    have hne : t - 1 ≠ 0 := by linarith
    have hcomp := (hasDerivAt_inv hne).comp t
      ((hasDerivAt_id t).sub_const 1)
    simpa [f, Function.comp_def, inv_pow, one_div, neg_div] using hcomp.deriv
  have hDerivIntegrable : IntegrableOn (deriv f)
      (Set.Icc (L : ℝ) U) := by
    refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousWithinAt.congr ?_
        (fun y hy => hDeriv y (hLreal.trans_le hy.1))
        (hDeriv t (hLreal.trans_le ht.1))
    have ht1 : 1 < t := hLreal.trans_le ht.1
    have hne : t - 1 ≠ 0 := by linarith
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hProduct : IntegrableOn
      (fun t : ℝ => deriv f t *
        ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)
      (Set.Icc (L : ℝ) U) :=
    integrableOn_mul_sum_Icc c (a := (L : ℝ)) (b := (U : ℝ))
      (m := 0) (by positivity) hDerivIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast hLU)]
  apply hProduct.neg.congr_fun _ measurableSet_Icc
  intro t ht
  change -(deriv f t *
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, centeredPrimeCoefficient q a n)) = _
  rw [hDeriv t (hLreal.trans_le ht.1), sum_centeredPrimeCoefficient]
  ring

/-- A logarithmic-square saving in prime counts becomes a reciprocal-prime
residue error of order `1 / log L`.  Endpoint errors are left visible; in
applications the same count estimate makes them smaller still. -/
theorem abs_centeredPrimeWeight_Ioc_le
    {L U q a : ℕ} {C : ℝ}
    (hL : 4 ≤ L) (hLU : L ≤ U) (hC : 0 ≤ C)
    (hdisc : ∀ n ∈ Finset.Icc L U,
      |(primeCountUpTo n q a : ℝ) -
          (primeCountTotal n : ℝ) / (q.totient : ℝ)| ≤
        C * (n : ℝ) / Real.log (n : ℝ) ^ 2) :
    |∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) - 1)⁻¹ * centeredPrimeCoefficient q a n| ≤
      ((U : ℝ) - 1)⁻¹ *
          |(primeCountUpTo U q a : ℝ) -
            (primeCountTotal U : ℝ) / (q.totient : ℝ)| +
      ((L : ℝ) - 1)⁻¹ *
          |(primeCountUpTo L q a : ℝ) -
            (primeCountTotal L : ℝ) / (q.totient : ℝ)| +
      16 * C / Real.log (L : ℝ) := by
  have hLtwo : 2 ≤ L := by omega
  have hLreal : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hLone : (1 : ℝ) < L := by linarith
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos hLone
  have hLUreal : (L : ℝ) ≤ U := by exact_mod_cast hLU
  rw [centeredPrimeWeight_Ioc_eq_abel hLtwo hLU]
  let D : ℕ → ℝ := fun n =>
    (primeCountUpTo n q a : ℝ) -
      (primeCountTotal n : ℝ) / (q.totient : ℝ)
  let K : ℝ → ℝ := fun t => ((t - 1)⁻¹ ^ 2) * D ⌊t⌋₊
  have hKernelIntegrable : IntervalIntegrable K volume (L : ℝ) U := by
    simpa [K, D] using
      (intervalIntegrable_centeredPrimeAbelKernel (q := q) (a := a) hLtwo hLU)
  have hMajorantIntegrable : IntervalIntegrable
      (fun t : ℝ => 16 * C * (t⁻¹ / Real.log t ^ 2))
      volume (L : ℝ) U := by
    apply IntervalIntegrable.const_mul
    exact (ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt (by
        have htIcc : t ∈ Set.Icc (L : ℝ) U := by
          simpa [Set.uIcc_of_le hLUreal] using ht
        have ht0 : t ≠ 0 := by linarith [htIcc.1]
        have hlog : Real.log t ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
            (by linarith [htIcc.1])
        have hlogsq : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
        fun_prop))
  have hPointwise (t : ℝ) (ht : t ∈ Set.Icc (L : ℝ) U) :
      ‖K t‖ ≤ 16 * C * (t⁻¹ / Real.log t ^ 2) := by
    have ht4 : 4 ≤ t := hLreal.trans ht.1
    have htpos : 0 < t := by linarith
    have ht1 : 1 < t := by linarith
    have hnL : L ≤ ⌊t⌋₊ := Nat.le_floor ht.1
    have hnU : ⌊t⌋₊ ≤ U := by
      have hfloorle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
      exact_mod_cast hfloorle.trans ht.2
    have hnmem : ⌊t⌋₊ ∈ Finset.Icc L U :=
      Finset.mem_Icc.mpr ⟨hnL, hnU⟩
    have hn4 : 4 ≤ ⌊t⌋₊ := hL.trans hnL
    have hnpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (by omega : 0 < ⌊t⌋₊)
    have hlogn : 0 < Real.log (⌊t⌋₊ : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < ⌊t⌋₊ by omega))
    have hnle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have htlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have hplusle : (⌊t⌋₊ : ℝ) + 1 ≤ 2 * (⌊t⌋₊ : ℝ) := by
      exact_mod_cast (show ⌊t⌋₊ + 1 ≤ 2 * ⌊t⌋₊ by omega)
    have ht2n : t ≤ 2 * (⌊t⌋₊ : ℝ) := (le_of_lt htlt).trans hplusle
    have hlogtle : Real.log t ≤ Real.log (2 * (⌊t⌋₊ : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact htpos)
        (by simp only [Set.mem_Ioi]; positivity) ht2n
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hlogtle
    have hlog2le : Real.log 2 ≤ Real.log (⌊t⌋₊ : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; norm_num)
        (by simp only [Set.mem_Ioi]; exact hnpos)
        (by exact_mod_cast (show 2 ≤ ⌊t⌋₊ by omega))
    have hlogcompare : Real.log t ≤ 2 * Real.log (⌊t⌋₊ : ℝ) := by
      linarith
    have hratio :
        (⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ) ^ 2 ≤
          4 * t / Real.log t ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hlogn) (sq_pos_of_pos (Real.log_pos ht1))]
      have hlogsq : Real.log t ^ 2 ≤
          4 * Real.log (⌊t⌋₊ : ℝ) ^ 2 := by
        have hfactor : 0 ≤
            (2 * Real.log (⌊t⌋₊ : ℝ) - Real.log t) *
              (Real.log t + 2 * Real.log (⌊t⌋₊ : ℝ)) :=
          mul_nonneg (sub_nonneg.mpr hlogcompare)
            (add_nonneg (Real.log_pos ht1).le (by positivity))
        nlinarith
      nlinarith
    have hkernel : (t - 1)⁻¹ ^ 2 ≤ 4 * t⁻¹ ^ 2 := by
      have htminus : 0 < t - 1 := by linarith
      have ht_sq : 0 < t ^ 2 := sq_pos_of_pos htpos
      have htminus_sq : 0 < (t - 1) ^ 2 := sq_pos_of_pos htminus
      rw [inv_pow, inv_pow, ← one_div, ← div_eq_mul_inv]
      rw [div_le_div_iff₀ htminus_sq ht_sq]
      nlinarith [sq_nonneg (t - 2)]
    have hD := hdisc ⌊t⌋₊ hnmem
    have hDnonneg : 0 ≤ C * (⌊t⌋₊ : ℝ) /
        Real.log (⌊t⌋₊ : ℝ) ^ 2 := by positivity
    have hratioC : C * (⌊t⌋₊ : ℝ) /
          Real.log (⌊t⌋₊ : ℝ) ^ 2 ≤
        C * (4 * t / Real.log t ^ 2) := by
      calc
        C * (⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ) ^ 2 =
            C * ((⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ) ^ 2) := by ring
        _ ≤ C * (4 * t / Real.log t ^ 2) :=
          mul_le_mul_of_nonneg_left hratio hC
    dsimp [K]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      (t - 1)⁻¹ ^ 2 * |D ⌊t⌋₊| ≤
          (t - 1)⁻¹ ^ 2 *
            (C * (⌊t⌋₊ : ℝ) /
              Real.log (⌊t⌋₊ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa [D] using hD) (sq_nonneg _)
      _ ≤ (4 * t⁻¹ ^ 2) *
            (C * (4 * t / Real.log t ^ 2)) := by
        exact mul_le_mul hkernel hratioC hDnonneg (by positivity)
      _ = 16 * C * (t⁻¹ / Real.log t ^ 2) := by
        field_simp
        ring
  have hIntegral : |∫ t in Set.Ioc (L : ℝ) U, K t| ≤
      16 * C / Real.log (L : ℝ) := by
    rw [← intervalIntegral.integral_of_le hLUreal]
    calc
      |∫ t in (L : ℝ)..(U : ℝ), K t| =
          ‖∫ t in (L : ℝ)..(U : ℝ), K t‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ t in (L : ℝ)..(U : ℝ), ‖K t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hLUreal
      _ ≤ ∫ t in (L : ℝ)..(U : ℝ),
          16 * C * (t⁻¹ / Real.log t ^ 2) :=
        intervalIntegral.integral_mono_on hLUreal hKernelIntegrable.norm
          hMajorantIntegrable hPointwise
      _ = 16 * C * ((Real.log (L : ℝ))⁻¹ -
          (Real.log (U : ℝ))⁻¹) := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_div_log_sq hLone
            (hLone.trans_le hLUreal)]
      _ ≤ 16 * C / Real.log (L : ℝ) := by
        have hlogU : 0 < Real.log (U : ℝ) :=
          Real.log_pos (hLone.trans_le hLUreal)
        have hinvU : 0 ≤ (Real.log (U : ℝ))⁻¹ := inv_nonneg.mpr hlogU.le
        have h16C : 0 ≤ 16 * C := mul_nonneg (by norm_num) hC
        have := mul_le_mul_of_nonneg_left
          (sub_le_self (Real.log (L : ℝ))⁻¹ hinvU) h16C
        simpa [div_eq_mul_inv] using this
  have hUinv : 0 ≤ ((U : ℝ) - 1)⁻¹ := by
    exact (inv_pos.mpr (sub_pos.mpr (hLone.trans_le hLUreal))).le
  have hLinv : 0 ≤ ((L : ℝ) - 1)⁻¹ := by positivity
  dsimp [D, K] at hIntegral ⊢
  calc
    |((U : ℝ) - 1)⁻¹ * D U -
        ((L : ℝ) - 1)⁻¹ * D L +
        (∫ t in Set.Ioc (L : ℝ) U,
          ((t - 1)⁻¹ ^ 2) * D ⌊t⌋₊)| ≤
      |((U : ℝ) - 1)⁻¹ * D U| +
        |((L : ℝ) - 1)⁻¹ * D L| +
        |∫ t in Set.Ioc (L : ℝ) U,
          ((t - 1)⁻¹ ^ 2) * D ⌊t⌋₊| := by
      calc
        _ ≤ |((U : ℝ) - 1)⁻¹ * D U -
              ((L : ℝ) - 1)⁻¹ * D L| +
            |∫ t in Set.Ioc (L : ℝ) U,
              ((t - 1)⁻¹ ^ 2) * D ⌊t⌋₊| := abs_add_le _ _
        _ ≤ (|((U : ℝ) - 1)⁻¹ * D U| +
              |((L : ℝ) - 1)⁻¹ * D L|) +
            |∫ t in Set.Ioc (L : ℝ) U,
              ((t - 1)⁻¹ ^ 2) * D ⌊t⌋₊| :=
          add_le_add (abs_sub _ _) le_rfl
        _ = _ := by ring
    _ ≤ ((U : ℝ) - 1)⁻¹ * |D U| +
        ((L : ℝ) - 1)⁻¹ * |D L| +
        16 * C / Real.log (L : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hUinv, abs_of_nonneg hLinv]
      linarith
    _ = _ := by rfl

end

end Erdos697.PrimeResidues

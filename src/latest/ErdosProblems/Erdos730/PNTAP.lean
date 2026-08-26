/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.AnalyticInputs
import PrimeNumberTheoremAnd.Consequences

/-!
# Erdős 730: fixed-modulus prime number theorem in arithmetic progressions

This file derives the unweighted residue-class prime count used by the
Erdős 730 development from `chebyshev_asymptotic_pnt`, the weighted PNT in
arithmetic progressions proved by `PrimeNumberTheoremAnd`.
-/

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace Erdos730.FullDensity

noncomputable def thetaAP (A a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime,
    if p % A = a then Real.log p else 0

noncomputable def primeAPCountingReal (A a : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % A = a).card : ℝ)

noncomputable def apPrimes (A a : ℕ) (x : ℝ) : Finset ℕ :=
  (Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % A = a

lemma thetaAP_eq_sum_apPrimes (A a : ℕ) (x : ℝ) :
    thetaAP A a x = ∑ p ∈ apPrimes A a x, Real.log p := by
  rw [thetaAP, apPrimes, ← Finset.sum_filter]
  congr 1
  ext p
  simp [and_assoc]

lemma primeAPCountingReal_eq_card_apPrimes (A a : ℕ) (x : ℝ) :
    primeAPCountingReal A a x = (apPrimes A a x).card := by
  rfl

lemma card_filter_prime_Iic (n : ℕ) :
    ((Iic n).filter Nat.Prime).card = n.primeCounting := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp

lemma thetaAP_nonneg (A a : ℕ) (x : ℝ) : 0 ≤ thetaAP A a x := by
  rw [thetaAP_eq_sum_apPrimes]
  exact Finset.sum_nonneg fun p hp => Real.log_nonneg <| by
    have hprime := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast hprime.one_lt.le

lemma thetaAP_le_count_mul_log (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    thetaAP A a x ≤ primeAPCountingReal A a x * Real.log x := by
  rw [thetaAP_eq_sum_apPrimes, primeAPCountingReal_eq_card_apPrimes]
  calc
    ∑ p ∈ apPrimes A a x, Real.log p
        ≤ ∑ _p ∈ apPrimes A a x, Real.log x := by
          apply Finset.sum_le_sum
          intro p hp
          apply Real.strictMonoOn_log.monotoneOn
          · have hprime := (Finset.mem_filter.mp hp).2.1
            exact (show (0 : ℝ) < p by exact_mod_cast hprime.pos)
          · exact (show (0 : ℝ) < x by linarith)
          · exact (Nat.cast_le.mpr (Finset.mem_Icc.mp
              (Finset.mem_filter.mp hp).1).2).trans (Nat.floor_le (by linarith))
    _ = (apPrimes A a x).card * Real.log x := by simp

lemma integrableOn_thetaAP_div_id_mul_log_sq (A a : ℕ) (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t => thetaAP A a t / (t * Real.log t ^ 2))
      (Set.Icc 2 x) MeasureTheory.volume := by
  conv => arg 1; ext t
          rw [thetaAP, div_eq_mul_one_div, mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have htlog : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 <| by
    simp
    grind
  fun_prop (disch := assumption)

lemma primeAPCountingReal_eq_thetaAP_div_log_add_integral
    (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    primeAPCountingReal A a x =
      thetaAP A a x / Real.log x +
        ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2) := by
  rw [primeAPCountingReal, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  let b : ℕ → ℝ := Set.indicator
    {n : ℕ | n.Prime ∧ n % A = a} (fun n => Real.log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * b n
  · refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs with h
    · have hnlog : Real.log n ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.1.pos) (mod_cast h.1.ne_one)
      simp [b, h, hnlog]
    · simp [b, h]
  rw [sum_mul_eq_sub_integral_mul₁ b (f := fun n => (Real.log n)⁻¹)
      (by simp [b]) (by simp [b]), ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in 2..x, deriv (fun y => (Real.log y)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * Real.log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by
        simp [Real.deriv_inv_log, field]
    simp [-Real.deriv_inv_log, int_deriv, b, Set.indicator_apply, Finset.sum_filter, thetaAP]
    grind
  · intro z ⟨hz, _⟩
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := assumption)
  · refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ =>
      ContinuousWithinAt.congr ?_ (fun _ _ => Real.deriv_inv_log_apply)
        Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by
      fun_prop (disch := assumption)

lemma thetaAP_le_theta (A a : ℕ) (x : ℝ) :
    thetaAP A a x ≤ Chebyshev.theta x := by
  rw [thetaAP, Chebyshev.theta_eq_sum_Icc]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · exact le_rfl
  · exact Real.log_nonneg <| by
      have hprime := (Finset.mem_filter.mp hp).2
      exact_mod_cast hprime.one_lt.le

lemma integral_thetaAP_div_log_sq_isLittleO (A a : ℕ) :
    (fun x => ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2))
      =o[atTop] (fun x => x / Real.log x) := by
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO
    Chebyshev.integral_theta_div_log_sq_isLittleO
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hapInt : IntervalIntegrable
      (fun t => thetaAP A a t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (integrableOn_thetaAP_div_id_mul_log_sq A a x)
  have hthetaInt : IntervalIntegrable
      (fun t => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hapNonneg :
      0 ≤ ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      exact div_nonneg (thetaAP_nonneg A a t) <| mul_nonneg
        (by linarith [ht.1]) (sq_nonneg _)
  have hthetaNonneg :
      0 ≤ ∫ t in 2..x, Chebyshev.theta t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      exact div_nonneg (Chebyshev.theta_nonneg t) <| mul_nonneg
        (by linarith [ht.1]) (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hapNonneg,
    abs_of_nonneg hthetaNonneg, one_mul]
  exact intervalIntegral.integral_mono_on hx hapInt hthetaInt fun t ht => by
    exact div_le_div_of_nonneg_right (thetaAP_le_theta A a t) <|
      mul_nonneg (by linarith [ht.1]) (sq_nonneg _)

lemma thetaAP_asymptotic {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A)
    (haA : a < A) :
    thetaAP A a ~[atTop] (fun x : ℝ => x / A.totient) := by
  simpa only [thetaAP] using! chebyshev_asymptotic_pnt hA ha haA

lemma thetaAP_div_id_tendsto {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A)
    (haA : a < A) :
    Tendsto (fun x : ℝ => thetaAP A a x / x) atTop
      (𝓝 ((A.totient : ℝ)⁻¹)) := by
  have htot : (A.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hA).ne'
  have hden : ∀ᶠ x : ℝ in atTop, x / (A.totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx htot
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hden).mp
    (thetaAP_asymptotic hA ha haA)
  convert h.div_const (A.totient : ℝ) using 1
  · funext x
    simp only [Pi.div_apply]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  · field_simp

theorem primeAPCountingReal_normalized_tendsto {A a : ℕ}
    (hA : 0 < A) (ha : a.Coprime A) (haA : a < A) :
    Tendsto
      (fun x : ℝ =>
        primeAPCountingReal A a x / (x / Real.log x))
      atTop (𝓝 ((A.totient : ℝ)⁻¹)) := by
  have hint := (integral_thetaAP_div_log_sq_isLittleO A a).tendsto_div_nhds_zero
  have hsum := (thetaAP_div_id_tendsto hA ha haA).add hint
  simpa only [add_zero] using hsum.congr' <| by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [primeAPCountingReal_eq_thetaAP_div_log_add_integral A a hx]
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field

lemma primeAPCount_eq_primeAPCountingReal (A a N : ℕ) (haA : a < A) :
    (primeAPCount A a N : ℝ) = primeAPCountingReal A a N := by
  rw [primeAPCount, primeAPCountingReal, Nat.floor_natCast]
  norm_cast
  apply congrArg Finset.card
  ext p
  simp [Nat.mod_eq_of_lt haA]

theorem pntAPInputAtModulus (A : ℕ) (hA : 0 < A) :
    PNTAPInputAtModulus A := by
  refine ⟨hA, fun a haA ha => ?_⟩
  have h := (primeAPCountingReal_normalized_tendsto hA ha haA).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext N
  rw [primeAPCount_eq_primeAPCountingReal A a N haA]
  rfl

theorem requiredFixedModulusPNTAPInput :
    RequiredFixedModulusPNTAPInput := by
  exact ⟨pntAPInputAtModulus 1 (by norm_num),
    pntAPInputAtModulus 222138 (by norm_num),
    pntAPInputAtModulus 148092 (by norm_num)⟩

end Erdos730.FullDensity

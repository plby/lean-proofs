/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Measure
import Mathlib.NumberTheory.Chebyshev

/-!
# Prime reciprocal sums on Ford's logarithmic divisor union

This file supplies the prime-sum estimate used in the analytic part of
Ford's Lemma 3.2.  The proof is based only on Chebyshev's estimate for
`theta`: a ratio-two interval of primes above `Q` has reciprocal mass
`O(1 / log Q)`.  An averaging argument over the logarithmic divisor union
then replaces the number of divisor intervals by their union measure `L`.
-/

namespace Erdos896.Ford

open MeasureTheory
open scoped BigOperators Nat.Prime

/-- Primes in the closed multiplicative interval `[M,2M]`, with the harmless
additional finite cutoff `T`. -/
def ratioTwoPrimes (T M : ℕ) : Finset ℕ :=
  (T + 1).primesBelow.filter fun p ↦ M ≤ p ∧ p ≤ 2 * M

@[simp]
theorem mem_ratioTwoPrimes {T M p : ℕ} :
    p ∈ ratioTwoPrimes T M ↔ p.Prime ∧ p ≤ T ∧ M ≤ p ∧ p ≤ 2 * M := by
  simp [ratioTwoPrimes, Nat.mem_primesBelow, and_left_comm, and_assoc]

/-- Chebyshev's theta bound gives a uniform reciprocal-mass estimate in a
ratio-two interval.  The explicit constant is inessential for Ford's use. -/
theorem sum_inv_ratioTwoPrimes_le (T M : ℕ) (hM : 2 ≤ M) :
    (∑ p ∈ ratioTwoPrimes T M, ((p : ℝ)⁻¹)) ≤
      2 * Real.log 4 / Real.log M := by
  have hMpos : (0 : ℝ) < M := by positivity
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hden : 0 < (M : ℝ) * Real.log M := mul_pos hMpos hlogM
  calc
    (∑ p ∈ ratioTwoPrimes T M, ((p : ℝ)⁻¹)) ≤
        ∑ p ∈ ratioTwoPrimes T M,
          Real.log p / ((M : ℝ) * Real.log M) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := mem_ratioTwoPrimes.mp hp
      have hpM : (M : ℝ) ≤ p := by exact_mod_cast hpdata.2.2.1
      have hlogMp : Real.log (M : ℝ) ≤ Real.log (p : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hMpos) (Set.mem_Ioi.mpr (lt_of_lt_of_le hMpos hpM)) hpM
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ (lt_of_lt_of_le hMpos hpM) hden).mpr
      nlinarith
    _ ≤ ∑ p ∈ (2 * M).primesLE,
          Real.log p / ((M : ℝ) * Real.log M) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpdata := mem_ratioTwoPrimes.mp hp
        exact Nat.mem_primesLE.mpr ⟨hpdata.2.2.2, hpdata.1⟩
      · intro p _ _
        exact div_nonneg (Real.log_natCast_nonneg p) hden.le
    _ = Chebyshev.theta ((2 * M : ℕ) : ℝ) /
          ((M : ℝ) * Real.log M) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log (2 * M)]
      exact (Finset.sum_div _ _ _).symm
    _ ≤ (Real.log 4 * ((2 * M : ℕ) : ℝ)) /
          ((M : ℝ) * Real.log M) := by
      exact div_le_div_of_nonneg_right
        (Chebyshev.theta_le_log4_mul_x (x := ((2 * M : ℕ) : ℝ)) (by positivity)) hden.le
    _ = 2 * Real.log 4 / Real.log M := by
      push_cast
      field_simp

/-- A real-endpoint version of `ratioTwoPrimes`, also imposing the fixed
lower cutoff `Q`. -/
noncomputable def realRatioTwoPrimes (T Q : ℕ) (R : ℝ) : Finset ℕ :=
  (T + 1).primesBelow.filter fun p ↦
    Q ≤ p ∧ R ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R

@[simp]
theorem mem_realRatioTwoPrimes {T Q p : ℕ} {R : ℝ} :
    p ∈ realRatioTwoPrimes T Q R ↔
      p.Prime ∧ p ≤ T ∧ Q ≤ p ∧ R ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R := by
  simp [realRatioTwoPrimes, Nat.mem_primesBelow, and_left_comm, and_assoc]

/-- Uniform reciprocal mass in a real ratio-two interval.  Passing from `R`
to `max Q ⌈R⌉₊` only enlarges the interval, so the natural-endpoint estimate
applies without rounding losses. -/
theorem sum_inv_realRatioTwoPrimes_le (T Q : ℕ) (R : ℝ) (hQ : 2 ≤ Q) :
    (∑ p ∈ realRatioTwoPrimes T Q R, ((p : ℝ)⁻¹)) ≤
      2 * Real.log 4 / Real.log Q := by
  let M := max Q ⌈R⌉₊
  have hQM : Q ≤ M := Nat.le_max_left _ _
  have hM : 2 ≤ M := hQ.trans hQM
  have hsubset : realRatioTwoPrimes T Q R ⊆ ratioTwoPrimes T M := by
    intro p hp
    have hpdata := mem_realRatioTwoPrimes.mp hp
    apply mem_ratioTwoPrimes.mpr
    refine ⟨hpdata.1, hpdata.2.1, ?_, ?_⟩
    · exact max_le hpdata.2.2.1 (Nat.ceil_le.mpr hpdata.2.2.2.1)
    · have hRceil : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      have hceilM : (⌈R⌉₊ : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.le_max_right Q ⌈R⌉₊
      have hpupper := hpdata.2.2.2.2
      have hRM : R ≤ (M : ℝ) := hRceil.trans hceilM
      have hpMreal : (p : ℝ) ≤ 2 * (M : ℝ) :=
        hpupper.trans (mul_le_mul_of_nonneg_left hRM (by norm_num))
      exact_mod_cast hpMreal
  have hsumsubset :
      (∑ p ∈ realRatioTwoPrimes T Q R, ((p : ℝ)⁻¹)) ≤
        ∑ p ∈ ratioTwoPrimes T M, ((p : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p _ _
    positivity
  have hQpos : (0 : ℝ) < Q := by positivity
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hMpos : (0 : ℝ) < M := by positivity
  have hlogQM : Real.log (Q : ℝ) ≤ Real.log (M : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hQpos) (Set.mem_Ioi.mpr hMpos) (by exact_mod_cast hQM)
  calc
    (∑ p ∈ realRatioTwoPrimes T Q R, ((p : ℝ)⁻¹)) ≤
        ∑ p ∈ ratioTwoPrimes T M, ((p : ℝ)⁻¹) := hsumsubset
    _ ≤ 2 * Real.log 4 / Real.log M := sum_inv_ratioTwoPrimes_le T M hM
    _ ≤ 2 * Real.log 4 / Real.log Q := by
      exact div_le_div_of_nonneg_left (by positivity) hlogQ hlogQM

/-! ## Logarithmic neighborhoods -/

/-- The closed neighborhood of logarithmic radius `(log 2)/2`. -/
def centeredLogNeighborhood (x : ℝ) : Set ℝ :=
  Set.Icc (x - Real.log 2 / 2) (x + Real.log 2 / 2)

theorem measurableSet_centeredLogNeighborhood (x : ℝ) :
    MeasurableSet (centeredLogNeighborhood x) := measurableSet_Icc

/-- Every point of a union of intervals of length `log 2` sees at least half
that length of the union inside its centered `log 2` neighborhood.  This is
the geometric fact that lets the averaging proof count union measure rather
than the number of divisor intervals. -/
theorem half_log_two_le_volume_inter_centeredLogNeighborhood
    {a : ℕ} {x : ℝ} (hx : x ∈ logDivisorUnion a (Real.log 2)) :
    Real.log 2 / 2 ≤
      volume.real
        (logDivisorUnion a (Real.log 2) ∩ centeredLogNeighborhood x) := by
  obtain ⟨d, hd, hleft, hright⟩ := mem_logDivisorUnion.mp hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfinite :
      volume (logDivisorUnion a (Real.log 2) ∩ centeredLogNeighborhood x) ≠ ⊤ := by
    exact ne_of_lt <| measure_lt_top_mono Set.inter_subset_right (by
      simp [centeredLogNeighborhood])
  by_cases hmid : x ≤ Real.log d - Real.log 2 / 2
  · have hsmall :
        Set.Ico x (x + Real.log 2 / 2) ⊆
          logDivisorUnion a (Real.log 2) ∩ centeredLogNeighborhood x := by
      intro t ht
      have htx := ht.1
      have htu := ht.2
      constructor
      · apply mem_logDivisorUnion.mpr
        refine ⟨d, hd, ?_, ?_⟩
        · exact hleft.trans (by linarith)
        · linarith
      · exact ⟨by linarith, htu.le⟩
    calc
      Real.log 2 / 2 =
          volume.real (Set.Ico x (x + Real.log 2 / 2)) := by
        rw [Real.volume_real_Ico_of_le (by linarith)]
        ring
      _ ≤ volume.real
          (logDivisorUnion a (Real.log 2) ∩ centeredLogNeighborhood x) :=
        measureReal_mono hsmall hfinite
  · have hsmall :
        Set.Ico (x - Real.log 2 / 2) x ⊆
          logDivisorUnion a (Real.log 2) ∩ centeredLogNeighborhood x := by
      intro t ht
      have htl := ht.1
      have htx := ht.2
      constructor
      · apply mem_logDivisorUnion.mpr
        refine ⟨d, hd, ?_, htx.trans hright⟩
        linarith
      · exact ⟨htl, by linarith⟩
    calc
      Real.log 2 / 2 =
          volume.real (Set.Ico (x - Real.log 2 / 2) x) := by
        rw [Real.volume_real_Ico_of_le (by linarith)]
        ring
      _ ≤ volume.real
          (logDivisorUnion a (Real.log 2) ∩ centeredLogNeighborhood x) :=
        measureReal_mono hsmall hfinite

/-! ## The finite prime set and its averaging kernel -/

/-- The finite set of primes occurring in Ford's logarithmic-union sum.
The real parameter `u` is the logarithm of Ford's product `c*y`; keeping it
as a translate makes the estimate independent of positivity conventions for
that product. -/
noncomputable def logUnionPrimes (T Q a : ℕ) (u : ℝ) : Finset ℕ :=
  by
    classical
    exact (T + 1).primesBelow.filter fun p ↦
      Q ≤ p ∧ u - Real.log p ∈ logDivisorUnion a (Real.log 2)

@[simp]
theorem mem_logUnionPrimes {T Q a p : ℕ} {u : ℝ} :
    p ∈ logUnionPrimes T Q a u ↔
      p.Prime ∧ p ≤ T ∧ Q ≤ p ∧
        u - Real.log p ∈ logDivisorUnion a (Real.log 2) := by
  classical
  simp only [logUnionPrimes, Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpT, hpprime⟩, hQp, hU⟩
    exact ⟨hpprime, Nat.le_of_lt_succ (by simpa using hpT), hQp, hU⟩
  · rintro ⟨hpprime, hpT, hQp, hU⟩
    exact ⟨⟨by omega, hpprime⟩, hQp, hU⟩

/-- The averaging kernel attached to a prime. -/
noncomputable def primeLogKernel (u : ℝ) (p : ℕ) (t : ℝ) : ℝ := by
  classical
  exact if t ∈ centeredLogNeighborhood (u - Real.log p) then (p : ℝ)⁻¹ else 0

theorem primeLogKernel_nonneg (u : ℝ) (p : ℕ) (t : ℝ) :
    0 ≤ primeLogKernel u p t := by
  classical
  simp only [primeLogKernel]
  split_ifs <;> positivity

/-- The support of the averaging kernels at a fixed logarithmic point. -/
noncomputable def nearbyLogUnionPrimes (T Q a : ℕ) (u t : ℝ) : Finset ℕ := by
  classical
  exact (logUnionPrimes T Q a u).filter
    fun p : ℕ ↦ t ∈ centeredLogNeighborhood (u - Real.log (p : ℝ))

@[simp]
theorem mem_nearbyLogUnionPrimes {T Q a p : ℕ} {u t : ℝ} :
    p ∈ nearbyLogUnionPrimes T Q a u t ↔
      p ∈ logUnionPrimes T Q a u ∧
        t ∈ centeredLogNeighborhood (u - Real.log (p : ℝ)) := by
  classical
  simp [nearbyLogUnionPrimes]

/-- At a fixed logarithmic point `t`, the primes whose averaging kernels are
nonzero lie in one real ratio-two interval. -/
theorem nearby_logUnionPrimes_subset_realRatioTwoPrimes
    (T Q a : ℕ) (u t : ℝ) :
    nearbyLogUnionPrimes T Q a u t ⊆
      realRatioTwoPrimes T Q (Real.exp (u - t - Real.log 2 / 2)) := by
  classical
  intro p hp
  have hpS := (mem_nearbyLogUnionPrimes.mp hp).1
  have hpdata := mem_logUnionPrimes.mp hpS
  have hnear := (mem_nearbyLogUnionPrimes.mp hp).2
  change
    u - Real.log (p : ℝ) - Real.log 2 / 2 ≤ t ∧
      t ≤ u - Real.log (p : ℝ) + Real.log 2 / 2 at hnear
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpdata.1.pos
  have hexplogp : Real.exp (Real.log (p : ℝ)) = p := Real.exp_log hp_pos
  have hlog2exp : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  apply mem_realRatioTwoPrimes.mpr
  refine ⟨hpdata.1, hpdata.2.1, hpdata.2.2.1, ?_, ?_⟩
  · rw [← hexplogp, Real.exp_le_exp]
    linarith [hnear.1]
  · have hupper :
        Real.log (p : ℝ) ≤ u - t + Real.log 2 / 2 := by
      linarith [hnear.2]
    have hexpidentity :
        Real.exp (u - t + Real.log 2 / 2) =
          2 * Real.exp (u - t - Real.log 2 / 2) := by
      calc
        Real.exp (u - t + Real.log 2 / 2) =
            Real.exp ((u - t - Real.log 2 / 2) + Real.log 2) := by
              congr 1 <;> ring
        _ = Real.exp (u - t - Real.log 2 / 2) * Real.exp (Real.log 2) :=
          Real.exp_add _ _
        _ = 2 * Real.exp (u - t - Real.log 2 / 2) := by
          rw [hlog2exp]
          ring
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) := hexplogp.symm
      _ ≤ Real.exp (u - t + Real.log 2 / 2) := Real.exp_le_exp.mpr hupper
      _ = 2 * Real.exp (u - t - Real.log 2 / 2) := hexpidentity

/-- Uniform pointwise bound for the sum of averaging kernels. -/
theorem sum_primeLogKernel_le (T Q a : ℕ) (u t : ℝ) (hQ : 2 ≤ Q) :
    (∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t) ≤
      2 * Real.log 4 / Real.log Q := by
  classical
  rw [show (∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t) =
      ∑ p ∈ nearbyLogUnionPrimes T Q a u t,
        ((p : ℝ)⁻¹) by
    rw [nearbyLogUnionPrimes, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    simp [primeLogKernel]]
  calc
    (∑ p ∈ nearbyLogUnionPrimes T Q a u t,
      ((p : ℝ)⁻¹)) ≤
        ∑ p ∈ realRatioTwoPrimes T Q
          (Real.exp (u - t - Real.log 2 / 2)), ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (nearby_logUnionPrimes_subset_realRatioTwoPrimes T Q a u t)
      intro p _ _
      positivity
    _ ≤ 2 * Real.log 4 / Real.log Q :=
      sum_inv_realRatioTwoPrimes_le T Q _ hQ

theorem integrable_primeLogKernel (a p : ℕ) (u : ℝ) :
    Integrable (primeLogKernel u p)
      (volume.restrict (logDivisorUnion a (Real.log 2))) := by
  classical
  have hglobal : Integrable (primeLogKernel u p) volume := by
    rw [show primeLogKernel u p =
      ((centeredLogNeighborhood (u - Real.log p)).indicator
        (fun _ : ℝ ↦ (p : ℝ)⁻¹)) by
          funext t
          simp [primeLogKernel, Set.indicator]]
    have hne : volume (centeredLogNeighborhood (u - Real.log p)) ≠ ⊤ := by
      simp [centeredLogNeighborhood]
    exact (integrableOn_const (s := centeredLogNeighborhood (u - Real.log p)) hne).integrable_indicator
      (measurableSet_centeredLogNeighborhood _)
  exact hglobal.mono_measure volume.restrict_le_self

/-- Exact integral of one averaging kernel over the logarithmic divisor
union. -/
theorem integral_primeLogKernel (a p : ℕ) (u : ℝ) :
    (∫ t in logDivisorUnion a (Real.log 2), primeLogKernel u p t) =
      volume.real
          (logDivisorUnion a (Real.log 2) ∩
            centeredLogNeighborhood (u - Real.log p)) * (p : ℝ)⁻¹ := by
  classical
  rw [show primeLogKernel u p =
      (centeredLogNeighborhood (u - Real.log p)).indicator
        (fun _ : ℝ ↦ (p : ℝ)⁻¹) by
          funext t
          simp [primeLogKernel, Set.indicator]]
  rw [setIntegral_indicator (measurableSet_centeredLogNeighborhood _), setIntegral_const]
  simp [smul_eq_mul]

/-- Ford's logarithmic-union prime reciprocal estimate, with an explicit
absolute constant.  This is the prime-sum input to the upper-bound part of
Lemma 3.2. -/
theorem sum_inv_logUnionPrimes_le
    (T Q a : ℕ) (u : ℝ) (ha : 1 ≤ a) (hQ : 2 ≤ Q) :
    (∑ p ∈ logUnionPrimes T Q a u, ((p : ℝ)⁻¹)) ≤
      (4 * Real.log 4 / Real.log 2) * L a (Real.log 2) / Real.log Q := by
  classical
  let U := logDivisorUnion a (Real.log 2)
  let K := 2 * Real.log 4 / Real.log Q
  have ha0 : a ≠ 0 := Nat.one_le_iff_ne_zero.mp ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hkernel (p : ℕ) (hp : p ∈ logUnionPrimes T Q a u) :
      Integrable (primeLogKernel u p) (volume.restrict U) := by
    simpa [U] using integrable_primeLogKernel a p u
  have hsum_integrable :
      Integrable (fun t ↦ ∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t)
        (volume.restrict U) :=
    integrable_finset_sum _ hkernel
  have hconst_integrable :
      Integrable (fun _ : ℝ ↦ K) (volume.restrict U) := by
    change IntegrableOn (fun _ : ℝ ↦ K) U volume
    exact integrableOn_const (divisorLogMeasure_ne_top ha0 (Real.log 2))
  have hlower :
      (Real.log 2 / 2) *
          (∑ p ∈ logUnionPrimes T Q a u, ((p : ℝ)⁻¹)) ≤
        ∫ t in U, ∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t := by
    calc
      (Real.log 2 / 2) *
          (∑ p ∈ logUnionPrimes T Q a u, ((p : ℝ)⁻¹)) =
          ∑ p ∈ logUnionPrimes T Q a u,
            (Real.log 2 / 2) * (p : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ logUnionPrimes T Q a u,
          ∫ t in U, primeLogKernel u p t := by
        apply Finset.sum_le_sum
        intro p hp
        have hpdata := mem_logUnionPrimes.mp hp
        rw [show (∫ t in U, primeLogKernel u p t) =
            volume.real
                (logDivisorUnion a (Real.log 2) ∩
                  centeredLogNeighborhood (u - Real.log p)) * (p : ℝ)⁻¹ by
          simpa [U] using integral_primeLogKernel a p u]
        exact mul_le_mul_of_nonneg_right
          (half_log_two_le_volume_inter_centeredLogNeighborhood hpdata.2.2.2)
          (by positivity)
      _ = ∫ t in U, ∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t := by
        exact (integral_finset_sum _ hkernel).symm
  have hupper :
      (∫ t in U, ∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t) ≤
        L a (Real.log 2) * K := by
    calc
      (∫ t in U, ∑ p ∈ logUnionPrimes T Q a u, primeLogKernel u p t) ≤
          ∫ _t in U, K := by
        apply integral_mono hsum_integrable hconst_integrable
        intro t
        simpa [K] using sum_primeLogKernel_le T Q a u t hQ
      _ = L a (Real.log 2) * K := by
        rw [setIntegral_const]
        simp [U, L_eq_volume_real, smul_eq_mul]
  have hcombined := hlower.trans hupper
  dsimp [K] at hcombined
  calc
    (∑ p ∈ logUnionPrimes T Q a u, ((p : ℝ)⁻¹)) =
        (2 / Real.log 2) *
          ((Real.log 2 / 2) *
            (∑ p ∈ logUnionPrimes T Q a u, ((p : ℝ)⁻¹))) := by
      field_simp
    _ ≤ (2 / Real.log 2) *
        (L a (Real.log 2) * (2 * Real.log 4 / Real.log Q)) := by
      exact mul_le_mul_of_nonneg_left hcombined (by positivity)
    _ = (4 * Real.log 4 / Real.log 2) * L a (Real.log 2) / Real.log Q := by
      field_simp
      ring

end Erdos896.Ford

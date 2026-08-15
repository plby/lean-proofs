/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RoughHarmonicEstimate
import Mathlib.NumberTheory.Chebyshev

/-!
# Rough integers in a short multiplicative interval

The large-component divisor switch in BNPZ needs more than a cumulative
rough harmonic bound.  Its complementary divisor lies in a multiplicative
interval, and the reciprocal mass of that interval must gain one factor of
`1 / log z`.

This file starts from the elementary least-prime-factor injection
`m ↦ (m / minFac m, minFac m)`.  The quotient is still `z`-rough, while the
prime fiber is controlled by Chebyshev's upper bound for `π(x)`.  This gives
the required short-interval estimate using the cumulative rough harmonic
bound already proved in `RoughHarmonicEstimate.lean`.
-/

namespace Erdos387

open scoped BigOperators Nat.Prime

open Finset Nat Real

namespace RoughHarmonic

/-- Positive `z`-rough integers in the half-open interval `(A,U]`. -/
noncomputable def roughPositiveIoc (z A U : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc A U).filter (IsZRough z)

theorem mem_roughPositiveIoc {z A U m : ℕ} :
    m ∈ roughPositiveIoc z A U ↔ A < m ∧ m ≤ U ∧ IsZRough z m := by
  simp [roughPositiveIoc, and_assoc]

/-- Candidate least-prime-factor pairs for rough integers up to `U`.

The first coordinate is itself rough and at most `U / z`; the second is a
prime between `z` and `U / a`.
-/
noncomputable def roughPrimeQuotientPairs (z U : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (roughPositiveUpTo z (U / z)).biUnion fun a =>
    ((Nat.primesLE (U / a)).filter fun p => z ≤ p).image fun p => (a, p)

private theorem minFac_pair_in_roughPrimeQuotientPairs
    {z A U m : ℕ} (hz : 0 < z) (hA : 1 ≤ A)
    (hm : m ∈ roughPositiveIoc z A U) :
    (m / m.minFac, m.minFac) ∈ roughPrimeQuotientPairs z U := by
  classical
  rw [mem_roughPositiveIoc] at hm
  obtain ⟨hAm, hmU, hrough⟩ := hm
  have hmOne : m ≠ 1 := by omega
  have hmPos : 0 < m := by omega
  let p := m.minFac
  let a := m / p
  have hp : p.Prime := Nat.minFac_prime hmOne
  have hpd : p ∣ m := Nat.minFac_dvd m
  have hap : a * p = m := Nat.div_mul_cancel hpd
  have hpz : z ≤ p := by
    by_contra hnot
    exact hrough p hp (Nat.lt_of_not_ge hnot) hpd
  have haPos : 0 < a := Nat.div_pos (Nat.le_of_dvd hmPos hpd) hp.pos
  have haLe : a ≤ U / z := by
    apply (Nat.le_div_iff_mul_le hz).2
    calc
      a * z ≤ a * p := Nat.mul_le_mul_left a hpz
      _ = m := hap
      _ ≤ U := hmU
  have haRough : IsZRough z a := by
    intro q hq hqz hqa
    exact hrough q hq hqz (hqa.trans (Nat.div_dvd_of_dvd hpd))
  have hpLe : p ≤ U / a := by
    apply (Nat.le_div_iff_mul_le haPos).2
    calc
      p * a = a * p := Nat.mul_comm _ _
      _ = m := hap
      _ ≤ U := hmU
  change (a, p) ∈ roughPrimeQuotientPairs z U
  rw [roughPrimeQuotientPairs, Finset.mem_biUnion]
  refine ⟨a, ?_, ?_⟩
  · rw [mem_roughPositiveUpTo_iff]
    exact ⟨haPos, haLe, haRough⟩
  · rw [Finset.mem_image]
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_filter, Nat.mem_primesLE]
    exact ⟨⟨hpLe, hp⟩, hpz⟩

private theorem minFac_pair_injOn_roughPositiveIoc
    {z A U : ℕ} (hA : 1 ≤ A) :
    Set.InjOn (fun m : ℕ => (m / m.minFac, m.minFac))
      (roughPositiveIoc z A U : Set ℕ) := by
  intro m hm n hn heq
  have hmData := (mem_roughPositiveIoc.mp hm)
  have hnData := (mem_roughPositiveIoc.mp hn)
  have hmOne : m ≠ 1 := by omega
  have hnOne : n ≠ 1 := by omega
  have hmDvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hnDvd : n.minFac ∣ n := Nat.minFac_dvd n
  calc
    m = (m / m.minFac) * m.minFac := (Nat.div_mul_cancel hmDvd).symm
    _ = (n / n.minFac) * n.minFac := by
      exact congrArg (fun t : ℕ × ℕ => t.1 * t.2) heq
    _ = n := Nat.div_mul_cancel hnDvd

/-- The least-prime-factor map reduces the rough interval count to prime
fibers over rough quotients. -/
theorem card_roughPositiveIoc_le_primeFibers
    {z A U : ℕ} (hz : 0 < z) (hA : 1 ≤ A) :
    (roughPositiveIoc z A U).card ≤
      ∑ a ∈ roughPositiveUpTo z (U / z),
        ((Nat.primesLE (U / a)).filter fun p => z ≤ p).card := by
  classical
  let f : ℕ → ℕ × ℕ := fun m => (m / m.minFac, m.minFac)
  have hcardImage :
      ((roughPositiveIoc z A U).image f).card =
        (roughPositiveIoc z A U).card :=
    Finset.card_image_of_injOn (minFac_pair_injOn_roughPositiveIoc hA)
  have hsubset : (roughPositiveIoc z A U).image f ⊆
      roughPrimeQuotientPairs z U := by
    intro ap hap
    rw [Finset.mem_image] at hap
    obtain ⟨m, hm, rfl⟩ := hap
    exact minFac_pair_in_roughPrimeQuotientPairs hz hA hm
  calc
    (roughPositiveIoc z A U).card =
        ((roughPositiveIoc z A U).image f).card := hcardImage.symm
    _ ≤ (roughPrimeQuotientPairs z U).card := Finset.card_le_card hsubset
    _ ≤ ∑ a ∈ roughPositiveUpTo z (U / z),
          (((Nat.primesLE (U / a)).filter fun p => z ≤ p).image
            fun p => (a, p)).card := by
      exact Finset.card_biUnion_le
    _ = ∑ a ∈ roughPositiveUpTo z (U / z),
          ((Nat.primesLE (U / a)).filter fun p => z ≤ p).card := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.card_image_of_injective]
      intro p q hpq
      exact congrArg Prod.snd hpq

/-- A uniform Chebyshev upper bound for the prime-counting function, in
the exact integer form needed for the prime fibers above. -/
theorem exists_uniform_primeCounting_le_div_log :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t := by
  have hevent :=
    Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) (by norm_num)
  obtain ⟨x, hx⟩ := Filter.eventually_atTop.mp hevent
  obtain ⟨N, hxN⟩ := exists_nat_ge x
  refine ⟨Real.log 4 + 1, ?_, N, ?_⟩
  · have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  · intro t hNt
    have hxt : x ≤ (t : ℝ) := hxN.trans (by exact_mod_cast hNt)
    simpa only [Nat.floor_natCast] using hx (t : ℝ) hxt

/-- A prime fiber over a fixed quotient `a` gains the Chebyshev factor
`1 / log z`.  The real quotient on the right deliberately dominates the
integer quotient indexing `primesLE`. -/
theorem card_primeFiber_le_div_log
    {C : ℝ} {N z U a : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (ha : 0 < a) :
    ((((Nat.primesLE (U / a)).filter fun p => z ≤ p).card : ℕ) : ℝ) ≤
      C * ((U : ℝ) / a) / Real.log z := by
  by_cases hzt : z ≤ U / a
  · have hcountNat :
        ((Nat.primesLE (U / a)).filter fun p => z ≤ p).card ≤
          Nat.primeCounting (U / a) := by
      calc
        ((Nat.primesLE (U / a)).filter fun p => z ≤ p).card ≤
            (Nat.primesLE (U / a)).card := Finset.card_filter_le _ _
        _ = Nat.primeCounting (U / a) := Nat.primesLE_card_eq_primeCounting _
    have hcount :
        ((((Nat.primesLE (U / a)).filter fun p => z ≤ p).card : ℕ) : ℝ) ≤
          (Nat.primeCounting (U / a) : ℝ) := by
      exact_mod_cast hcountNat
    have hcheb' := hcheb (U / a) (hzN.trans hzt)
    have hlogz : 0 < Real.log (z : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < z by omega)
    have hlogMono : Real.log (z : ℝ) ≤ Real.log (U / a : ℕ) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by
          change (0 : ℝ) < (z : ℝ)
          exact_mod_cast (show 0 < z by omega))
        (by
          change (0 : ℝ) < ((U / a : ℕ) : ℝ)
          exact_mod_cast (show 0 < U / a by omega))
        (by exact_mod_cast hzt)
    have hcastDiv : ((U / a : ℕ) : ℝ) ≤ (U : ℝ) / a :=
      Nat.cast_div_le
    have hdenom :
        C * (U / a : ℕ) / Real.log (U / a : ℕ) ≤
          C * (U / a : ℕ) / Real.log z := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hC.le (by positivity)) hlogz hlogMono
    have hnumer :
        C * (U / a : ℕ) / Real.log z ≤
          C * ((U : ℝ) / a) / Real.log z := by
      apply (div_le_div_iff_of_pos_right hlogz).2
      exact mul_le_mul_of_nonneg_left hcastDiv hC.le
    exact hcount.trans (hcheb'.trans (hdenom.trans hnumer))
  · have hempty :
        (Nat.primesLE (U / a)).filter (fun p => z ≤ p) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨hp, hzp⟩
      exact hzt (hzp.trans (Nat.mem_primesLE.mp hp).1)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- The number of rough integers in `(A,U]` is bounded by a rough harmonic
mass times the Chebyshev factor `U / log z`. -/
theorem card_roughPositiveIoc_le_roughMass_div_log
    {C : ℝ} {N z A U : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hA : 1 ≤ A) :
    ((roughPositiveIoc z A U).card : ℝ) ≤
      (C * (U : ℝ) / Real.log z) *
        roughReciprocalMass z (U / z) := by
  let R := roughPositiveUpTo z (U / z)
  have hcountNat := card_roughPositiveIoc_le_primeFibers
    (z := z) (A := A) (U := U) (by omega) hA
  have hcount : ((roughPositiveIoc z A U).card : ℝ) ≤
      ∑ a ∈ R,
        ((((Nat.primesLE (U / a)).filter fun p => z ≤ p).card : ℕ) : ℝ) := by
    exact_mod_cast hcountNat
  calc
    ((roughPositiveIoc z A U).card : ℝ) ≤
        ∑ a ∈ R,
          ((((Nat.primesLE (U / a)).filter fun p => z ≤ p).card : ℕ) : ℝ) :=
      hcount
    _ ≤ ∑ a ∈ R, C * ((U : ℝ) / a) / Real.log z := by
      apply Finset.sum_le_sum
      intro a haR
      have haPos := (mem_roughPositiveUpTo_iff.mp haR).1
      exact card_primeFiber_le_div_log hC hcheb hzN hz haPos
    _ = (C * (U : ℝ) / Real.log z) *
          roughReciprocalMass z (U / z) := by
      unfold roughReciprocalMass
      change (∑ a ∈ R, C * ((U : ℝ) / a) / Real.log z) =
        (C * (U : ℝ) / Real.log z) * ∑ a ∈ R, (1 : ℝ) / a
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- Reciprocal mass of positive `z`-rough integers in `(A,U]`. -/
noncomputable def roughReciprocalIocMass (z A U : ℕ) : ℝ :=
  ∑ m ∈ roughPositiveIoc z A U, (1 : ℝ) / m

/-- On `(A,U]`, every reciprocal is at most `1/A`. -/
theorem roughReciprocalIocMass_le_card_div
    {z A U : ℕ} (hA : 1 ≤ A) :
    roughReciprocalIocMass z A U ≤
      ((roughPositiveIoc z A U).card : ℝ) / A := by
  unfold roughReciprocalIocMass
  calc
    (∑ m ∈ roughPositiveIoc z A U, (1 : ℝ) / m) ≤
        ∑ _m ∈ roughPositiveIoc z A U, (1 : ℝ) / A := by
      apply Finset.sum_le_sum
      intro m hm
      have hAm := (mem_roughPositiveIoc.mp hm).1.le
      exact one_div_le_one_div_of_le
        (by exact_mod_cast (show 0 < A by omega)) (by exact_mod_cast hAm)
    _ = ((roughPositiveIoc z A U).card : ℝ) / A := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The short-interval rough reciprocal estimate.  For a multiplicative
interval with bounded `U/A`, this is `O(H(z,U/z) / log z)`. -/
theorem roughReciprocalIocMass_le_roughMass_div_log
    {C : ℝ} {N z A U : ℕ}
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hA : 1 ≤ A) :
    roughReciprocalIocMass z A U ≤
      (C * ((U : ℝ) / A) / Real.log z) *
        roughReciprocalMass z (U / z) := by
  have hcard := card_roughPositiveIoc_le_roughMass_div_log
    (U := U) hC hcheb hzN hz hA
  have hfirst := roughReciprocalIocMass_le_card_div
    (z := z) (U := U) hA
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hdivide := (div_le_div_iff_of_pos_right hAReal).2 hcard
  calc
    roughReciprocalIocMass z A U ≤
        ((roughPositiveIoc z A U).card : ℝ) / A := hfirst
    _ ≤ ((C * (U : ℝ) / Real.log z) *
          roughReciprocalMass z (U / z)) / A := hdivide
    _ = (C * ((U : ℝ) / A) / Real.log z) *
          roughReciprocalMass z (U / z) := by ring

/-- Uniform short-interval bound, exposing only absolute constants. -/
theorem exists_uniform_roughReciprocalIocMass_le_roughMass_div_log :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ (z A U : ℕ), N ≤ z → 2 ≤ z → 1 ≤ A →
        roughReciprocalIocMass z A U ≤
          (C * ((U : ℝ) / A) / Real.log z) *
            roughReciprocalMass z (U / z) := by
  obtain ⟨C, hC, N, hcheb⟩ := exists_uniform_primeCounting_le_div_log
  refine ⟨C, hC, N, ?_⟩
  intro z A U hzN hz hA
  exact roughReciprocalIocMass_le_roughMass_div_log
    hC hcheb hzN hz hA

/-- The fully explicit version obtained by inserting the uniform cumulative
rough harmonic envelope. -/
theorem exists_uniform_roughReciprocalIocMass_le_envelope :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∃ N : ℕ,
      ∀ (z A U : ℕ), N ≤ z → 2 ≤ z → 1 ≤ A →
        roughReciprocalIocMass z A U ≤
          (C * ((U : ℝ) / A) / Real.log z) *
            roughLogRatioEnvelope K z (U / z) := by
  obtain ⟨C, hC, N, hshort⟩ :=
    exists_uniform_roughReciprocalIocMass_le_roughMass_div_log
  obtain ⟨K, hK, hglobal⟩ :=
    exists_uniform_roughReciprocalMass_le_envelope
  refine ⟨C, K, hC, hK, N, ?_⟩
  intro z A U hzN hz hA
  have hbase := hshort z A U hzN hz hA
  have hlogz : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  have hcoef : 0 ≤ C * ((U : ℝ) / A) / Real.log z := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (hglobal z (U / z) hz) hcoef)

end RoughHarmonic

end Erdos387

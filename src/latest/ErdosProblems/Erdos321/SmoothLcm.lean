import ErdosProblems.Erdos321.RoughPrimePartition
import Mathlib.NumberTheory.Chebyshev

namespace Erdos321

open Nat

/-- Every prime factor of a smooth denominator is at most the cutoff. -/
theorem prime_le_of_dvd_smoothDenominator
    {N Q n p : ℕ} (hn : n ∈ smoothDenominators N Q)
    (hp : p.Prime) (hpdvd : p ∣ n) : p ≤ Q := by
  have hnInterval := (Finset.mem_sdiff.mp hn).1
  have hnBounds := Finset.mem_Icc.mp hnInterval
  have hpN : p ≤ N := (Nat.le_of_dvd hnBounds.1 hpdvd).trans hnBounds.2
  by_contra hpQ
  have hpLarge : p ∈ largePrimeSet N Q := by
    rw [largePrimeSet, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpN⟩, hp⟩
  have hnFiber : n ∈ largePrimeFiber N p := by
    rw [largePrimeFiber, Finset.mem_filter]
    exact ⟨hnInterval, hpdvd⟩
  exact (Finset.mem_sdiff.mp hn).2
    (Finset.mem_biUnion.mpr ⟨p, hpLarge, hnFiber⟩)

/-- Integer envelope containing every possible prime power from a smooth
number: one copy of each prime up to `Q`, plus all higher prime-power layers
occurring up to `N`. -/
def smoothLCMEnvelope (N Q : ℕ) : ℕ :=
  primorial Q * (lcmUpto N / primorial N)

private theorem factorization_primorial_of_prime_le
    {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    (primorial n).factorization p = 1 := by
  rw [primorial_eq_prod_primesLE, factorization_prod_apply]
  · calc
      (∑ x ∈ primesLE n, x.factorization p) = p.factorization p := by
        apply Finset.sum_eq_single p
        · intro q hq hqp
          have hqprime := prime_of_mem_primesLE hq
          rw [hqprime.factorization]
          simp [hqp]
        · intro hpnot
          exact (hpnot (mem_primesLE.mpr ⟨hpn, hp⟩)).elim
      _ = 1 := by rw [hp.factorization]; simp
  · intro q hq
    exact (prime_of_mem_primesLE hq).ne_zero

private theorem smoothLCMEnvelope_pos (N Q : ℕ) :
    0 < smoothLCMEnvelope N Q := by
  have hdiv := primorial_dvd_lcmUpto N
  have hquot : 0 < lcmUpto N / primorial N :=
    Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos N) hdiv) (primorial_pos N)
  exact Nat.mul_pos (primorial_pos Q) hquot

private theorem smoothLCMEnvelope_factorization
    {N Q p : ℕ} (hp : p.Prime) (hpQ : p ≤ Q) (hQN : Q ≤ N) :
    (smoothLCMEnvelope N Q).factorization p = p.log N := by
  have hpN : p ≤ N := hpQ.trans hQN
  have hlog : 1 ≤ p.log N := Nat.log_pos hp.one_lt hpN
  have hprimQ := factorization_primorial_of_prime_le hp hpQ
  have hprimN := factorization_primorial_of_prime_le hp hpN
  have hquotPosNat : 0 < lcmUpto N / primorial N :=
    Nat.div_pos
      (Nat.le_of_dvd (lcmUpto_pos N) (primorial_dvd_lcmUpto N))
      (primorial_pos N)
  rw [smoothLCMEnvelope,
    Nat.factorization_mul (primorial_pos Q).ne' hquotPosNat.ne']
  change (primorial Q).factorization p +
    (lcmUpto N / primorial N).factorization p = p.log N
  rw [Nat.factorization_div (primorial_dvd_lcmUpto N), Finsupp.coe_tsub, Pi.sub_apply,
    factorization_lcmUpto N hp, hprimQ, hprimN]
  omega

/-- The LCM of the smooth block divides an explicit prime-power envelope. -/
theorem denominatorLCM_smooth_dvd_envelope
    {N Q : ℕ} (hQN : Q ≤ N) :
    denominatorLCM (smoothDenominators N Q) ∣ smoothLCMEnvelope N Q := by
  rw [denominatorLCM, Finset.lcm_dvd_iff]
  intro n hn
  have hnBounds := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1
  have hn0 : n ≠ 0 := (Nat.ne_of_gt hnBounds.1)
  have hEnv0 : smoothLCMEnvelope N Q ≠ 0 :=
    (smoothLCMEnvelope_pos N Q).ne'
  change n ∣ smoothLCMEnvelope N Q
  rw [← Nat.factorization_le_iff_dvd hn0 hEnv0]
  intro p
  by_cases he : n.factorization p = 0
  · simp [he]
  have hp : p.Prime := by
    by_contra hpNot
    exact he ((Nat.factorization_eq_zero_iff n p).2 (Or.inl hpNot))
  have hpdvd : p ∣ n := Nat.dvd_of_factorization_pos he
  have hpQ : p ≤ Q := prime_le_of_dvd_smoothDenominator hn hp hpdvd
  rw [smoothLCMEnvelope_factorization hp hpQ hQN]
  have hpowdvd : p ^ n.factorization p ∣ n :=
    (hp.pow_dvd_iff_le_factorization hn0).2 le_rfl
  exact Nat.le_log_of_pow_le hp.one_lt
    ((Nat.le_of_dvd hnBounds.1 hpowdvd).trans hnBounds.2)

/-- Exact logarithmic smooth-LCM bound in Chebyshev coordinates. -/
theorem log_denominatorLCM_smooth_le
    {N Q : ℕ} (hQN : Q ≤ N) :
    Real.log (denominatorLCM (smoothDenominators N Q)) ≤
      Chebyshev.theta Q + (Chebyshev.psi N - Chebyshev.theta N) := by
  have hdiv := denominatorLCM_smooth_dvd_envelope hQN
  have hEnvPos : 0 < smoothLCMEnvelope N Q := smoothLCMEnvelope_pos N Q
  have hDPos : 0 < denominatorLCM (smoothDenominators N Q) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rcases Finset.lcm_eq_zero_iff.mp hzero with ⟨n, hn, hn0⟩
    exact (Nat.ne_of_gt
      (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1) hn0
  have hLogLe : Real.log (denominatorLCM (smoothDenominators N Q)) ≤
      Real.log (smoothLCMEnvelope N Q) :=
    Real.log_le_log (by exact_mod_cast hDPos)
      (by exact_mod_cast Nat.le_of_dvd hEnvPos hdiv)
  calc
    Real.log (denominatorLCM (smoothDenominators N Q)) ≤
        Real.log (smoothLCMEnvelope N Q) := hLogLe
    _ = Real.log (primorial Q) +
        (Real.log (lcmUpto N) - Real.log (primorial N)) := by
      have hPQ0 : primorial Q ≠ 0 := (primorial_pos Q).ne'
      have hPN0 : primorial N ≠ 0 := (primorial_pos N).ne'
      have hLN0 : lcmUpto N ≠ 0 := (lcmUpto_pos N).ne'
      have hQuot0 : lcmUpto N / primorial N ≠ 0 :=
        (Nat.div_pos
          (Nat.le_of_dvd (lcmUpto_pos N) (primorial_dvd_lcmUpto N))
          (primorial_pos N)).ne'
      rw [smoothLCMEnvelope, Nat.cast_mul,
        Real.log_mul (Nat.cast_ne_zero.mpr hPQ0)
          (Nat.cast_ne_zero.mpr hQuot0),
        Nat.cast_div (primorial_dvd_lcmUpto N)
          (Nat.cast_ne_zero.mpr hPN0),
        Real.log_div (Nat.cast_ne_zero.mpr hLN0)
          (Nat.cast_ne_zero.mpr hPN0)]
    _ = Chebyshev.theta Q +
        (Chebyshev.psi N - Chebyshev.theta N) := by
      rw [Chebyshev.psi_eq_log_lcmUpto,
        Chebyshev.theta_eq_log_primorial,
        Chebyshev.theta_eq_log_primorial]
      norm_num

/-- Explicit elementary estimate used by the upper recurrence. -/
theorem log_denominatorLCM_smooth_le_explicit
    {N Q : ℕ} (hQN : Q ≤ N) (hQ : 1 ≤ Q) (hN : 1 ≤ N) :
    Real.log (denominatorLCM (smoothDenominators N Q)) ≤
      Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
        2 * Real.sqrt N * Real.log N := by
  calc
    _ ≤ Chebyshev.theta Q + (Chebyshev.psi N - Chebyshev.theta N) :=
      log_denominatorLCM_smooth_le hQN
    _ ≤ (Real.log 4 * Q + 2 * Real.sqrt Q * Real.log Q) +
        2 * Real.sqrt N * Real.log N := by
      have ht := Chebyshev.theta_le_log4_mul_x (x := (Q : ℝ)) (by positivity)
      have he := Chebyshev.psi_sub_theta_le (x := (N : ℝ)) (by exact_mod_cast hN)
      have hExtra : 0 ≤ 2 * Real.sqrt (Q : ℝ) * Real.log Q := by
        positivity
      linarith
    _ ≤ _ := by
      have hExtra : 0 ≤ 2 * Real.sqrt (Q : ℝ) * Real.log Q := by
        positivity
      linarith

end Erdos321

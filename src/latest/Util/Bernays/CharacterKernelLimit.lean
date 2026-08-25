import Util.Bernays.PrimeThetaLimits
import Util.Bernays.LocalKernelBounds
import Util.Bernays.RamifiedEulerCorrection

/-!
# Linear asymptotic of the quadratic-character logarithmic kernel
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def ramifiedPrimeLog {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow, if χ p = 0 then log p else 0

theorem ramifiedPrimeLog_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {N : ℕ} (hN : q ≤ N) :
    ramifiedPrimeLog χ N = ∑ p ∈ q.primeFactors, log p := by
  have hset : ((N + 1).primesBelow.filter fun p : ℕ => χ p = 0) = q.primeFactors := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hz⟩ := Finset.mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primesBelow hp
      exact Nat.mem_primeFactors.mpr ⟨hprime,
        (char_prime_eq_zero_iff χ ⟨p, hprime⟩).mp hz, NeZero.ne q⟩
    · intro hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd).trans hN
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩,
        (char_prime_eq_zero_iff χ ⟨p, hprime⟩).mpr hdvd⟩
  rw [ramifiedPrimeLog, ← Finset.sum_filter, hset]

theorem ramifiedPrimeLog_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    Tendsto (fun N : ℕ => ramifiedPrimeLog χ N / (N : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
    (∑ p ∈ q.primeFactors, log p)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop q] with N hN
  simp only [Function.comp_def, ramifiedPrimeLog_eq χ hN, div_eq_mul_inv]

theorem quadratic_allowedPrimeLog_identity {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (N : ℕ) :
    localAllowedPrimeLog (fun p : ℕ => χ p = -1) N =
      (Chebyshev.theta (N : ℝ) + realCharacterTheta χ N + ramifiedPrimeLog χ N) / 2 := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  simp only [Nat.primesLE, realCharacterTheta, ramifiedPrimeLog, localAllowedPrimeLog,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ₂ p with h | h | h
  · norm_num [h]
  · norm_num [h]
  · norm_num [h]

theorem localAllowedPrimeLog_div_tendsto_half {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => localAllowedPrimeLog (fun p : ℕ => χ p = -1) N / (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have h := ((theta_div_tendsto_one.add (realCharacterTheta_div_tendsto_zero χ hχ)).add
    (ramifiedPrimeLog_div_tendsto_zero χ)).div_const 2
  simp only [add_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp only
    rw [quadratic_allowedPrimeLog_identity χ hχ₂]
    ring

theorem localLogMass_div_tendsto_half {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => localLogMass (fun p : ℕ => χ p = -1) N / (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have hbase := localAllowedPrimeLog_div_tendsto_half χ hχ₂ hχ
  have hupper := hbase.add (primePowerError_div_tendsto_zero.const_mul 2)
  simp only [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hbase hupper
  · intro N
    exact
      (div_le_div_of_nonneg_right (localLogMass_prime_bounds (fun p : ℕ => χ p = -1) N).1
        (Nat.cast_nonneg N))
  · intro N
    have h := div_le_div_of_nonneg_right
      (localLogMass_prime_bounds (fun p : ℕ => χ p = -1) N).2 (Nat.cast_nonneg N)
    simpa only [add_div, mul_div_assoc] using h

end Bernays

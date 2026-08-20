import ErdosProblems.Erdos387.AnalyticInputs
import Mathlib.NumberTheory.Primorial

/-!
# Auxiliary primes for the odd-prime Elliott sieve

For a fixed odd prime `ell`, this file packages the rational primes

`q < t`,  `q ≡ -1 (mod ell²)`.

The fixed-modulus prime number theorem supplies a positive proportion of
`t / log t` such primes.  Elementary lemmas record pairwise coprimality,
coprimality to every power of the rational ray support `ell`, and the
Chebyshev product bound needed by the medium-range sieve.
-/

open scoped BigOperators

namespace Erdos980.ElliottTail.OddAuxiliaryPrimes

open Filter Finset Real

noncomputable section

variable (ell : ℕ) [Fact ell.Prime]

/-- The fixed progression modulus `ell²`. -/
def auxiliaryModulus : ℕ := ell ^ 2

/-- The natural representative of `-1 mod ell²`. -/
def auxiliaryResidue : ℕ := auxiliaryModulus ell - 1

/-- Auxiliary primes strictly below `t` and congruent to `-1 mod ell²`. -/
def oddAuxiliaryPrimes (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter fun q =>
    q.Prime ∧ q % auxiliaryModulus ell = auxiliaryResidue ell

@[simp] theorem mem_oddAuxiliaryPrimes {t q : ℕ} :
    q ∈ oddAuxiliaryPrimes ell t ↔
      q < t ∧ q.Prime ∧
        q % auxiliaryModulus ell = auxiliaryResidue ell := by
  simp [oddAuxiliaryPrimes, and_assoc]

theorem oddAuxiliaryPrimes_prime {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) : q.Prime :=
  ((mem_oddAuxiliaryPrimes (ell := ell)).mp hq).2.1

theorem oddAuxiliaryPrimes_lt {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) : q < t :=
  ((mem_oddAuxiliaryPrimes (ell := ell)).mp hq).1

theorem oddAuxiliaryPrimes_modEq {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) :
    q % auxiliaryModulus ell = auxiliaryResidue ell :=
  ((mem_oddAuxiliaryPrimes (ell := ell)).mp hq).2.2

theorem auxiliaryModulus_pos : 0 < auxiliaryModulus ell := by
  exact pow_pos (Fact.out : Nat.Prime ell).pos _

theorem auxiliaryResidue_lt : auxiliaryResidue ell < auxiliaryModulus ell := by
  unfold auxiliaryResidue
  exact Nat.sub_lt (auxiliaryModulus_pos ell) zero_lt_one

theorem auxiliaryResidue_coprime_modulus :
    Nat.Coprime (auxiliaryResidue ell) (auxiliaryModulus ell) := by
  have hM : 1 ≤ auxiliaryModulus ell := (auxiliaryModulus_pos ell)
  rw [auxiliaryResidue, Nat.coprime_self_sub_left hM]
  exact Nat.coprime_one_left _

/-- The progression condition in divisibility form. -/
theorem auxiliaryModulus_dvd_add_one {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) :
    auxiliaryModulus ell ∣ q + 1 := by
  let M := auxiliaryModulus ell
  have hM : 0 < M := auxiliaryModulus_pos ell
  have hmod : q % M = M - 1 := by
    simpa [M, auxiliaryResidue] using oddAuxiliaryPrimes_modEq ell hq
  refine ⟨q / M + 1, ?_⟩
  have hdivision := Nat.mod_add_div q M
  rw [hmod] at hdivision
  calc
    q + 1 = (M - 1 + M * (q / M)) + 1 :=
      congrArg (· + 1) hdivision.symm
    _ = M * (q / M + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- An auxiliary prime is different from the cyclotomic prime. -/
theorem oddAuxiliaryPrimes_ne_ell (hellOdd : Odd ell) {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) : q ≠ ell := by
  intro hqell
  subst q
  have hell3 : 3 ≤ ell := by
    have hell2 := (Fact.out : Nat.Prime ell).two_le
    rcases hellOdd with ⟨k, hk⟩
    omega
  have helllt : ell < auxiliaryModulus ell := by
    simp only [auxiliaryModulus, pow_two]
    nlinarith
  have hmod := oddAuxiliaryPrimes_modEq ell hq
  rw [Nat.mod_eq_of_lt helllt] at hmod
  simp only [auxiliaryResidue, auxiliaryModulus, pow_two] at hmod
  have hsq : ell + 2 ≤ ell * ell := by nlinarith
  omega

/-- Auxiliary primes are coprime to `ell`. -/
theorem oddAuxiliaryPrimes_coprime_ell (hellOdd : Odd ell) {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) : Nat.Coprime q ell := by
  have hqprime := oddAuxiliaryPrimes_prime ell hq
  rw [hqprime.coprime_iff_not_dvd]
  intro hdiv
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime ell)).mp hdiv with hq1 | hqell
  · exact hqprime.ne_one hq1
  · exact oddAuxiliaryPrimes_ne_ell ell hellOdd hq hqell

/-- Consequently auxiliary primes are coprime to every rational power of
the ray support, in particular to the exponent `2*ell` occurring in the
primary ray modulus. -/
theorem oddAuxiliaryPrimes_coprime_ell_pow (hellOdd : Odd ell)
    {t q n : ℕ} (hq : q ∈ oddAuxiliaryPrimes ell t) :
    Nat.Coprime q (ell ^ n) :=
  (oddAuxiliaryPrimes_coprime_ell ell hellOdd hq).pow_right n

theorem oddAuxiliaryPrimes_coprime_primaryRaySupport
    (hellOdd : Odd ell) {t q : ℕ}
    (hq : q ∈ oddAuxiliaryPrimes ell t) :
    Nat.Coprime q (ell ^ (2 * ell)) :=
  oddAuxiliaryPrimes_coprime_ell_pow ell hellOdd hq

/-- Distinct auxiliary primes are coprime. -/
theorem oddAuxiliaryPrimes_pairwise_coprime (t : ℕ) :
    (oddAuxiliaryPrimes ell t : Set ℕ).Pairwise Nat.Coprime := by
  intro q hq r hr hne
  have hqprime := oddAuxiliaryPrimes_prime ell hq
  have hrprime := oddAuxiliaryPrimes_prime ell hr
  rw [hqprime.coprime_iff_not_dvd]
  intro hdiv
  rcases (Nat.dvd_prime hrprime).mp hdiv with hq1 | hqr
  · exact hqprime.ne_one hq1
  · exact hne hqr

/-- The auxiliary-prime family is monotone in its strict upper cutoff. -/
theorem oddAuxiliaryPrimes_mono {s t : ℕ} (hst : s ≤ t) :
    oddAuxiliaryPrimes ell s ⊆ oddAuxiliaryPrimes ell t := by
  intro q hq
  rw [mem_oddAuxiliaryPrimes] at hq ⊢
  exact ⟨hq.1.trans_le hst, hq.2⟩

/-! ## Product bound -/

/-- The auxiliary primes form a subset of all primes at most `t`. -/
theorem oddAuxiliaryPrimes_subset_primesLE (t : ℕ) :
    oddAuxiliaryPrimes ell t ⊆ Nat.primesLE t := by
  intro q hq
  exact Nat.mem_primesLE.mpr
    ⟨(oddAuxiliaryPrimes_lt ell hq).le,
      oddAuxiliaryPrimes_prime ell hq⟩

/-- Chebyshev's elementary primorial estimate gives the uniform product
bound required in the medium sieve. -/
theorem oddAuxiliaryPrimes_prod_le_four_pow (t : ℕ) :
    (oddAuxiliaryPrimes ell t).prod id ≤ 4 ^ t := by
  calc
    (oddAuxiliaryPrimes ell t).prod id ≤ (Nat.primesLE t).prod id := by
      apply Finset.prod_le_prod_of_subset_of_one_le
        (oddAuxiliaryPrimes_subset_primesLE ell t)
      · intro q hq
        exact Nat.zero_le q
      · intro q hq _
        exact (Nat.mem_primesLE.mp hq).2.one_le
    _ = primorial t := (primorial_eq_prod_primesLE t).symm
    _ ≤ 4 ^ t := primorial_le_four_pow t

/-! ## Fixed-modulus PNT lower bound -/

/-- A dyadic subfamily ending at `t-1`; it is contained in the strict
cutoff family and is the set to which `PNT_fixed_modulus` is applied. -/
def oddAuxiliaryDyadicPrimes (t : ℕ) : Finset ℕ :=
  Erdos387.primeIntervalAP (auxiliaryModulus ell) (auxiliaryResidue ell)
    (((t - 1 : ℕ) : ℝ) / 2) ((t - 1 : ℕ) : ℝ)

theorem oddAuxiliaryDyadicPrimes_subset (t : ℕ) :
    oddAuxiliaryDyadicPrimes ell t ⊆ oddAuxiliaryPrimes ell t := by
  intro q hq
  rw [oddAuxiliaryDyadicPrimes, Erdos387.primeIntervalAP] at hq
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast] at hq
  rw [mem_oddAuxiliaryPrimes]
  exact ⟨by omega, hq.2⟩

/-- A convenient explicit positive density constant. -/
def auxiliaryPrimeDensity : ℝ :=
  1 / (8 * Nat.totient (auxiliaryModulus ell) : ℝ)

theorem auxiliaryPrimeDensity_pos : 0 < auxiliaryPrimeDensity ell := by
  have hφ : 0 < Nat.totient (auxiliaryModulus ell) :=
    Nat.totient_pos.mpr (auxiliaryModulus_pos ell)
  unfold auxiliaryPrimeDensity
  positivity

private theorem tendsto_half_pred_atTop :
    Tendsto (fun t : ℕ => ((t - 1 : ℕ) : ℝ) / 2) atTop atTop := by
  have hpred : Tendsto (fun t : ℕ => t - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro n
    refine ⟨n + 1, ?_⟩
    intro b hb
    omega
  exact (tendsto_natCast_atTop_atTop.comp hpred).atTop_div_const (by norm_num)

/-- The fixed-progression PNT supplies eventually at least
`c_ell * t / log t` auxiliary primes. -/
theorem eventually_auxiliaryPrimeDensity_mul_div_log_le_card
    (hellOdd : Odd ell) :
    ∀ᶠ t : ℕ in atTop,
      auxiliaryPrimeDensity ell * (t : ℝ) / Real.log (t : ℝ) ≤
        ((oddAuxiliaryPrimes ell t).card : ℝ) := by
  let M := auxiliaryModulus ell
  let a := auxiliaryResidue ell
  have hM : 1 ≤ M := auxiliaryModulus_pos ell
  have haM : a < M := auxiliaryResidue_lt ell
  have hacop : Nat.Coprime a M := auxiliaryResidue_coprime_modulus ell
  obtain ⟨x₀, hx₀, hPNT⟩ :=
    Erdos387.PNT_fixed_modulus M a hM haM hacop
      1 (by norm_num) (1 / 2) (by norm_num)
  have hxevent : ∀ᶠ t : ℕ in atTop,
      x₀ ≤ ((t - 1 : ℕ) : ℝ) / 2 :=
    tendsto_half_pred_atTop.eventually (eventually_ge_atTop x₀)
  filter_upwards [hxevent, eventually_ge_atTop 5] with t htx ht5
  let y : ℝ := ((t - 1 : ℕ) : ℝ) / 2
  have hy3 : 3 ≤ y := hx₀.trans htx
  have hypos : 0 < y := by linarith
  have htpos : 0 < (t : ℝ) := by positivity
  have ht1 : 1 ≤ t := by omega
  have hcastpred : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) ht1)
  have htwo_y : 2 * y = ((t - 1 : ℕ) : ℝ) := by
    dsimp [y]
    ring
  have hyv : y < ((t - 1 : ℕ) : ℝ) := by
    rw [← htwo_y]
    linarith
  have hlen : (1 : ℝ) * y ≤ ((t - 1 : ℕ) : ℝ) - y := by
    rw [← htwo_y]
    linarith
  have hestimate := hPNT y htx y ((t - 1 : ℕ) : ℝ)
    le_rfl hyv (by rw [htwo_y]) hlen
  change
    |((oddAuxiliaryDyadicPrimes ell t).card : ℝ) -
        (((t - 1 : ℕ) : ℝ) - y) /
          ((Nat.totient M : ℝ) * Real.log y)| ≤
      (1 / 2 : ℝ) * (((t - 1 : ℕ) : ℝ) - y) /
        ((Nat.totient M : ℝ) * Real.log y) at hestimate
  have hφnat : 0 < Nat.totient M := Nat.totient_pos.mpr hM
  have hφ : (0 : ℝ) < Nat.totient M := by exact_mod_cast hφnat
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hden : 0 < (Nat.totient M : ℝ) * Real.log y := mul_pos hφ hlogy
  have hmain :
      (((t - 1 : ℕ) : ℝ) - y) /
          ((Nat.totient M : ℝ) * Real.log y) =
        y / ((Nat.totient M : ℝ) * Real.log y) := by
    rw [← htwo_y]
    ring
  rw [hmain] at hestimate
  have hlower :
      y / (2 * ((Nat.totient M : ℝ) * Real.log y)) ≤
        ((oddAuxiliaryDyadicPrimes ell t).card : ℝ) := by
    have hneg := (abs_le.mp hestimate).1
    have herr : (1 / 2 : ℝ) * (((t - 1 : ℕ) : ℝ) - y) /
        ((Nat.totient M : ℝ) * Real.log y) =
      y / (2 * ((Nat.totient M : ℝ) * Real.log y)) := by
      rw [← htwo_y]
      ring
    rw [herr] at hneg
    have htwice :
        y / ((Nat.totient M : ℝ) * Real.log y) =
          2 * (y / (2 * ((Nat.totient M : ℝ) * Real.log y))) := by
      ring
    rw [htwice] at hneg
    linarith
  have hyt : (t : ℝ) / 4 ≤ y := by
    have hyformula : y = ((t : ℝ) - 1) / 2 := by
      dsimp [y]
      rw [hcastpred]
    rw [hyformula]
    linarith
  have hy_le_t : y ≤ (t : ℝ) := by
    have hyformula : y = ((t : ℝ) - 1) / 2 := by
      dsimp [y]
      rw [hcastpred]
    rw [hyformula]
    linarith
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (by norm_num; omega)
  have hlogle : Real.log y ≤ Real.log (t : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hypos htpos hy_le_t
  have hcompare :
      auxiliaryPrimeDensity ell * (t : ℝ) / Real.log (t : ℝ) ≤
        y / (2 * ((Nat.totient M : ℝ) * Real.log y)) := by
    have hMdef : M = auxiliaryModulus ell := rfl
    rw [auxiliaryPrimeDensity, ← hMdef]
    have hleft :
        (1 / (8 * (Nat.totient M : ℝ))) * (t : ℝ) /
            Real.log (t : ℝ) =
          (t : ℝ) / (8 * (Nat.totient M : ℝ) * Real.log (t : ℝ)) := by
      ring
    rw [hleft]
    calc
      (t : ℝ) / (8 * (Nat.totient M : ℝ) * Real.log (t : ℝ)) ≤
          y / (2 * (Nat.totient M : ℝ) * Real.log (t : ℝ)) := by
        have hfactor :
            0 < 2 * (Nat.totient M : ℝ) * Real.log (t : ℝ) := by
          positivity
        have hrewrite :
            (t : ℝ) / (8 * (Nat.totient M : ℝ) * Real.log (t : ℝ)) =
              ((t : ℝ) / 4) /
                (2 * (Nat.totient M : ℝ) * Real.log (t : ℝ)) := by
          ring
        rw [hrewrite]
        exact (div_le_div_iff_of_pos_right hfactor).2 hyt
      _ ≤ y / (2 * ((Nat.totient M : ℝ) * Real.log y)) := by
        apply div_le_div_of_nonneg_left hypos.le (by positivity)
        nlinarith
  exact hcompare.trans (hlower.trans (by
    exact_mod_cast Finset.card_le_card
      (oddAuxiliaryDyadicPrimes_subset ell t)))

end

end Erdos980.ElliottTail.OddAuxiliaryPrimes

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldExceptionalCharacter
import BoundedGaps.BombieriVinogradov.Analytic.SquarePrincipalCharacterUniqueness
import BoundedGaps.BombieriVinogradov.Analytic.SquareNonprincipalZeroFreeRegion
import Mathlib.Data.Nat.Totient

/-!
# One exceptional prime at a bounded conductor scale

The same-modulus real-zero uniqueness theorem is lifted to primitive
characters with arbitrary conductor at most `Q`, by inducing to the LCM.
One prime divisor of the sole possible exceptional conductor then removes
all these near-one real zeros. There is no appeal to a Siegel constant and
no claim that this is already the full progression-distribution estimate.
-/

namespace Erdos4b.FGKMT

noncomputable section

open BoundedGaps.Maynard

/-- A near-one real zero at one common bounded-conductor scale. -/
def hasBoundedNearRealZero (M Q : ℕ)
    (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  psi.modulus ≤ Q ∧ ∃ beta : ℝ,
    0 < beta ∧ beta < 1 ∧
      1 - 1 / ((M : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * 2)) ≤ beta ∧
        DirichletCharacter.LFunction psi.character (beta : ℂ) = 0

private theorem realZero_changeLevel
    {q d : ℕ} [NeZero q] [NeZero d] (hqd : q ∣ d)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    IsNonprincipalNontrivialLFunctionZero (chi.changeLevel hqd) (beta : ℂ) := by
  apply (isNonprincipalNontrivialLFunctionZero_iff _ _).2
  refine ⟨?_, ?_, by simpa using hbeta0, by simpa using hbeta1⟩
  · exact fun h => hchi ((DirichletCharacter.changeLevel_eq_one_iff hqd).mp h)
  · rw [DirichletCharacter.LFunction_changeLevel hqd chi (.inl hchi), hzero, zero_mul]

private theorem nearRealZero_lower_at_lcm
    {M Q q1 q2 : ℕ} (hM : 2 ≤ M)
    (hq1 : 0 < q1) (hq2 : 0 < q2) (h1Q : q1 ≤ Q) (h2Q : q2 ≤ Q)
    {beta : ℝ}
    (hbeta : 1 - 1 / ((M : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * 2)) ≤ beta) :
    1 - 1 / ((M : ℝ) ^ 2 * Real.log ((Nat.lcm q1 q2 : ℝ) * 2)) ≤ beta := by
  have hNpos : 0 < Nat.lcm q1 q2 := Nat.lcm_pos hq1 hq2
  have hNone : (1 : ℝ) ≤ Nat.lcm q1 q2 := by exact_mod_cast hNpos
  have hNle : Nat.lcm q1 q2 ≤ q1 * q2 :=
    Nat.le_of_dvd (Nat.mul_pos hq1 hq2) (Nat.lcm_dvd_mul q1 q2)
  have hNQ : (Nat.lcm q1 q2 : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hprod : q1 * q2 ≤ Q * Q := Nat.mul_le_mul h1Q h2Q
    have hpow : Nat.lcm q1 q2 ≤ Q ^ 2 := by simpa [pow_two] using hNle.trans hprod
    exact_mod_cast hpow
  have hlogpos : 0 < Real.log ((Nat.lcm q1 q2 : ℝ) * 2) :=
    Real.log_pos (by linarith)
  have hlogle : Real.log ((Nat.lcm q1 q2 : ℝ) * 2) ≤
      Real.log ((Q : ℝ) ^ 2 * 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hinv :
      1 / ((M : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * 2)) ≤
        1 / ((M : ℝ) ^ 2 * Real.log ((Nat.lcm q1 q2 : ℝ) * 2)) :=
    one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hMpos) hlogpos)
      (mul_le_mul_of_nonneg_left hlogle (sq_nonneg _))
  linarith

/-- The zero-free constant is fixed before the conductor cutoff is chosen. -/
theorem exists_boundedNearRealZero_subsingleton :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ Q : ℕ,
      Set.Subsingleton {psi : GoldfeldPrimitiveRealCharacter |
        hasBoundedNearRealZero M Q psi} := by
  obtain ⟨M, hM, hsame⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_of_sq_eq_one_of_im_eq_zero
  refine ⟨M, hM, ?_⟩
  intro Q psi1 hpsi1 psi2 hpsi2
  rcases hpsi1 with ⟨h1Q, beta1, hb10, hb11, hnear1, hz1⟩
  rcases hpsi2 with ⟨h2Q, beta2, hb20, hb21, hnear2, hz2⟩
  let d := Nat.lcm psi1.modulus psi2.modulus
  let : NeZero d :=
    ⟨Nat.lcm_ne_zero (NeZero.ne psi1.modulus) (NeZero.ne psi2.modulus)⟩
  let chi1 := psi1.character.changeLevel (Nat.dvd_lcm_left psi1.modulus psi2.modulus)
  let chi2 := psi2.character.changeLevel (Nat.dvd_lcm_right psi1.modulus psi2.modulus)
  have hs1 : chi1 ^ 2 = 1 := by
    dsimp [chi1]
    rw [← map_pow, psi1.sq_eq_one, map_one]
  have hs2 : chi2 ^ 2 = 1 := by
    dsimp [chi2]
    rw [← map_pow, psi2.sq_eq_one, map_one]
  have hzero1 : IsNonprincipalNontrivialLFunctionZero chi1 (beta1 : ℂ) :=
    realZero_changeLevel (Nat.dvd_lcm_left psi1.modulus psi2.modulus)
      psi1.character psi1.ne_one hb10 hb11 hz1
  have hzero2 : IsNonprincipalNontrivialLFunctionZero chi2 (beta2 : ℂ) :=
    realZero_changeLevel (Nat.dvd_lcm_right psi1.modulus psi2.modulus)
      psi2.character psi2.ne_one hb20 hb21 hz2
  have hregion1 := nearRealZero_lower_at_lcm hM
    (NeZero.pos psi1.modulus) (NeZero.pos psi2.modulus) h1Q h2Q hnear1
  have hregion2 := nearRealZero_lower_at_lcm hM
    (NeZero.pos psi1.modulus) (NeZero.pos psi2.modulus) h1Q h2Q hnear2
  have heq : chi1 = chi2 := hsame d chi1 chi2 (beta1 : ℂ) (beta2 : ℂ)
    hs1 hs2 hzero1 hzero2 (by simp) (by simp)
    (by simpa [d] using hregion1) (by simpa [d] using hregion2)
  by_contra hne
  exact ((goldfeldPrimitiveRealCharacter_distinct_iff_ne psi1 psi2).2 hne) heq

/-- Deleting one prime excludes the possible near-one real zero at every
conductor coprime to that prime. The constant remains uniform in `Q`. -/
theorem exists_exceptionalPrime_realZeros :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∃ B : ℕ, 1 ≤ B ∧ B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ psi : GoldfeldPrimitiveRealCharacter,
          Nat.Coprime psi.modulus B → ¬ hasBoundedNearRealZero M Q psi := by
  classical
  obtain ⟨M, hM, hsingle⟩ := exists_boundedNearRealZero_subsingleton
  refine ⟨M, hM, ?_⟩
  intro Q hQ
  by_cases hex : ∃ psi : GoldfeldPrimitiveRealCharacter, hasBoundedNearRealZero M Q psi
  · obtain ⟨psi0, hpsi0⟩ := hex
    let B := psi0.modulus.minFac
    have hBprime : B.Prime := Nat.minFac_prime (ne_of_gt psi0.modulus_gt_one)
    have hBdvd : B ∣ psi0.modulus := Nat.minFac_dvd _
    have hBQ : B ≤ Q :=
      (Nat.le_of_dvd (NeZero.pos psi0.modulus) hBdvd).trans hpsi0.1
    refine ⟨B, hBprime.one_le, hBQ, Or.inr hBprime, ?_⟩
    intro psi hcop hnear
    have heq : psi = psi0 := hsingle Q hnear hpsi0
    subst psi
    exact (hBprime.coprime_iff_not_dvd.mp hcop.symm) hBdvd
  · refine ⟨1, le_rfl, by omega, Or.inl rfl, ?_⟩
    intro psi _ hnear
    exact hex ⟨psi, hnear⟩

private theorem nearRegion_lower_mono
    {M A q Q : ℕ} (hM : 2 ≤ M) (hMA : M ≤ A)
    (hq : 0 < q) (hqQ : q ≤ Q) (t : ℝ) :
    1 - 1 / ((M : ℝ) ^ 2 * Real.log ((q : ℝ) * (|t| + 2))) ≤
      1 - 1 / ((A : ℝ) ^ 2 * Real.log ((Q : ℝ) * (|t| + 2))) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMA' : (M : ℝ) ≤ A := by exact_mod_cast hMA
  have hfactor : 0 < |t| + 2 := by positivity
  have hlog0 : 0 < Real.log ((q : ℝ) * (|t| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg t])
  have hlogle : Real.log ((q : ℝ) * (|t| + 2)) ≤
      Real.log ((Q : ℝ) * (|t| + 2)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hqQ' hfactor.le)
  have hpow : (M : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 :=
    pow_le_pow_left₀ hM0.le hMA' 2
  have hdenle :
      (M : ℝ) ^ 2 * Real.log ((q : ℝ) * (|t| + 2)) ≤
        (A : ℝ) ^ 2 * Real.log ((Q : ℝ) * (|t| + 2)) :=
    mul_le_mul hpow hlogle hlog0.le (sq_nonneg _)
  have hinv := one_div_le_one_div_of_le
    (mul_pos (sq_pos_of_pos hM0) hlog0) hdenle
  linarith

/-- An effective logarithmic zero-free region for every permitted primitive
nonprincipal character, including its nonreal zeros. The one exceptional
prime is chosen once for the whole conductor range. -/
theorem exists_exceptionalPrime_primitiveZeroFree :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∃ B : ℕ, 1 ≤ B ∧ B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ (q : ℕ) [NeZero q], 1 < q → q ≤ Q →
          ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
            Nat.Coprime q B → ∀ rho : ℂ,
              IsNonprincipalNontrivialLFunctionZero chi rho →
                rho.re < 1 - 1 / ((A : ℝ) ^ 2 *
                  Real.log ((Q : ℝ) ^ 2 * (|rho.im| + 2))) := by
  obtain ⟨M, hM, hprime⟩ := exists_exceptionalPrime_realZeros
  obtain ⟨N, hN, hnonreal⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_im_eq_zero_of_sq_eq_one
  obtain ⟨K, hK, hnonsquare⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_re_lt_of_sq_ne_one
  let A := max M (max N K)
  have hMA : M ≤ A := le_max_left _ _
  have hNA : N ≤ A := (le_max_left N K).trans (le_max_right M _)
  have hKA : K ≤ A := (le_max_right N K).trans (le_max_right M _)
  refine ⟨A, hM.trans hMA, ?_⟩
  intro Q hQ
  obtain ⟨B, hB1, hBQ, hB, hremove⟩ := hprime Q hQ
  refine ⟨B, hB1, hBQ, hB, ?_⟩
  intro q _ hq hqQ chi hprimitive hcop rho hzero
  by_contra hnot
  have hnear := le_of_not_gt hnot
  have hqQsq : q ≤ Q ^ 2 := hqQ.trans (by nlinarith)
  have hlocal (J : ℕ) (hJ : 2 ≤ J) (hJA : J ≤ A) :
      1 - 1 / ((J : ℝ) ^ 2 * Real.log ((q : ℝ) * (|rho.im| + 2))) ≤ rho.re := by
    have hcompare := nearRegion_lower_mono hJ hJA (by omega : 0 < q) hqQsq rho.im
    exact hcompare.trans (by simpa using hnear)
  by_cases hsquare : chi ^ 2 = 1
  · have him : rho.im = 0 := hnonreal q chi rho hsquare hzero (hlocal N hN hNA)
    have hordinary := (isNonprincipalNontrivialLFunctionZero_iff chi rho).1 hzero
    let psi : GoldfeldPrimitiveRealCharacter :=
      ⟨q, hq, chi, hprimitive, hordinary.1, hsquare⟩
    apply hremove psi hcop
    refine ⟨hqQ, rho.re, hordinary.2.2.1, hordinary.2.2.2, ?_, ?_⟩
    · have hcompare := nearRegion_lower_mono hM hMA
        (by positivity : 0 < Q ^ 2) (le_rfl : Q ^ 2 ≤ Q ^ 2) 0
      have hrealnear :
          1 - 1 / ((A : ℝ) ^ 2 * Real.log ((Q : ℝ) ^ 2 * 2)) ≤ rho.re := by
        simpa [him] using hnear
      apply le_trans ?_ hrealnear
      simpa using hcompare
    · have hrho : (rho.re : ℂ) = rho := by
        apply Complex.ext <;> simp [him]
      change DirichletCharacter.LFunction chi (rho.re : ℂ) = 0
      rw [hrho]
      exact hordinary.2.1
  · exact (not_lt_of_ge (hlocal K hK hKA)) (hnonsquare q chi rho hsquare hzero)

/-- Any deleted prime, including a small one, loses at most a factor two
in the prime-mass normalization. -/
theorem exceptionalPrime_totient_ratio {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    (1 / 2 : ℝ) ≤ (Nat.totient B : ℝ) / B ∧
      (Nat.totient B : ℝ) / B ≤ 1 := by
  rcases hB with rfl | hB
  · norm_num
  · have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB.two_le
    have hBpos : (0 : ℝ) < B := by linarith
    rw [Nat.totient_prime hB, Nat.cast_sub hB.one_le, Nat.cast_one]
    constructor
    · apply (le_div_iff₀ hBpos).2
      linarith
    · apply (div_le_one hBpos).2
      linarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_realZeros
#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_primitiveZeroFree
#print axioms Erdos4b.FGKMT.exceptionalPrime_totient_ratio

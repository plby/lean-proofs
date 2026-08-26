/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SquarefreeMassTransfer
import ErdosProblems.Erdos822.CollisionAdmissibility
import ErdosProblems.Erdos822.LargeGcdFreeBasic

/-!
# The growing-cutoff B4 condition

The published argument does not require m to be coprime to its totient.
It only removes cofactors for which a prime above the growing cutoff divides
both m and φ(m).  This file records that honest finite filter and the
local coprimality consequences used in the common-divisor argument.
-/

namespace Erdos822

/-- Every divisor supported above the cutoff of a common shifted
coefficient is coprime to the B4 cofactor. -/
theorem commonDivisor_coprime_cofactor_of_largeGcdFree
    {N y h m m' : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Nat.Coprime h m := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpg
  have hpdata : p ∣ h ∧ p ∣ m :=
    ⟨dvd_trans hpg (Nat.gcd_dvd_left _ _),
      dvd_trans hpg (Nat.gcd_dvd_right _ _)⟩
  have hpshift : p ∣ shiftedTotient m := by
    exact dvd_trans hpdata.1 (dvd_trans hh (by
      unfold shiftedCoefficientGcd
      exact Nat.gcd_dvd_left _ _))
  exact not_dvd_of_dvd_shiftedTotient_of_largeGcdFree
    hm hp (hlarge p hp hpdata.1) hpshift hpdata.2

/-- The same common divisor is coprime to the full totient. -/
theorem commonDivisor_coprime_totient_of_largeGcdFree
    {N y h m m' : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Nat.Coprime h (Nat.totient m) := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpg
  have hpdata : p ∣ h ∧ p ∣ Nat.totient m :=
    ⟨dvd_trans hpg (Nat.gcd_dvd_left _ _),
      dvd_trans hpg (Nat.gcd_dvd_right _ _)⟩
  have hpshift : p ∣ shiftedTotient m := by
    exact dvd_trans hpdata.1 (dvd_trans hh (by
      unfold shiftedCoefficientGcd
      exact Nat.gcd_dvd_left _ _))
  have hpm : p ∣ m := by
    apply (Nat.dvd_add_iff_left hpdata.2).mpr
    simpa [shiftedTotient] using hpshift
  exact (mem_largeGcdFreeOddCofactors_iff.mp hm).2
    p hp (hlarge p hp hpdata.1) ⟨hpm, hpdata.2⟩

/-- Coprimality with a large-supported common divisor passes to every
cofactor divisor. -/
theorem commonDivisor_coprime_leftFactor_of_largeGcdFree
    {N y h m m' l : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hlm : l ∣ m)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Nat.Coprime h l := by
  exact Nat.Coprime.of_dvd_right hlm
    (commonDivisor_coprime_cofactor_of_largeGcdFree hm hh hlarge)

/-- The totient of every cofactor divisor is also invertible modulo a
large-supported common divisor. -/
theorem commonDivisor_coprime_totient_leftFactor_of_largeGcdFree
    {N y h m m' l : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hlm : l ∣ m)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Nat.Coprime h (Nat.totient l) := by
  exact Nat.Coprime.of_dvd_right (Nat.totient_dvd_of_dvd hlm)
    (commonDivisor_coprime_totient_of_largeGcdFree hm hh hlarge)

/-- The B4 condition supplies precisely the conditional p-freeness needed
when a repeated large prime divides a shifted coefficient. -/
theorem not_dvd_of_sq_dvd_shiftedTotient_of_largeGcdFree
    {N y p m : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hp : p.Prime) (hyp : y < p)
    (hpsq : p ^ 2 ∣ shiftedTotient m) :
    ¬ p ∣ m := by
  apply not_dvd_of_dvd_shiftedTotient_of_largeGcdFree hm hp hyp
  exact dvd_trans (dvd_pow_self p (by omega : 2 ≠ 0)) hpsq

/-- The squarefree correction may be imposed on the genuine B4 family
without strengthening B4 to global coprimality. -/
theorem sum_inv_largeSquarefree_largeGcdFree_ge
    {N y : ℕ} {R D : ℝ}
    (hN : 2 ≤ N) (hy1 : 1 ≤ y) (hyN : y < N ^ 21)
    (hraw : R ≤
      ∑ m ∈ largeGcdFreeOddCofactors N y, (1 : ℝ) / m)
    (hD :
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) ≤ D) :
    R - D ≤
      ∑ m ∈ largeSquarefreeFilter
          (largeGcdFreeOddCofactors N y) y,
        (1 : ℝ) / m := by
  apply sum_inv_largeSquarefreeFilter_ge hN hy1 hyN
    (largeGcdFreeOddCofactors_subset_oddRaw N y)
  · intro m hm p hp hyp hpsq
    exact not_dvd_of_sq_dvd_shiftedTotient_of_largeGcdFree
      hm hp hyp hpsq
  · exact hraw
  · exact hD

/-- The corrected B4 family, with repeated large shifted prime factors
removed. -/
noncomputable def squarefreeLargeGcdFreeOddCofactors
    (N y : ℕ) : Finset ℕ :=
  largeSquarefreeFilter (largeGcdFreeOddCofactors N y) y

@[simp]
theorem mem_squarefreeLargeGcdFreeOddCofactors_iff
    {N y m : ℕ} :
    m ∈ squarefreeLargeGcdFreeOddCofactors N y ↔
      m ∈ largeGcdFreeOddCofactors N y ∧
        ∀ p : ℕ, p.Prime → y < p →
          ¬ p ^ 2 ∣ shiftedTotient m := by
  simp [squarefreeLargeGcdFreeOddCofactors]

theorem squarefreeLargeGcdFreeOddCofactors_subset_largeGcdFree
    (N y : ℕ) :
    squarefreeLargeGcdFreeOddCofactors N y ⊆
      largeGcdFreeOddCofactors N y := by
  intro m hm
  exact (mem_squarefreeLargeGcdFreeOddCofactors_iff.mp hm).1

theorem squarefreeLargeGcdFreeOddCofactors_subset_oddRaw
    (N y : ℕ) :
    squarefreeLargeGcdFreeOddCofactors N y ⊆
      oddRawCofactors N := by
  exact Set.Subset.trans
    (squarefreeLargeGcdFreeOddCofactors_subset_largeGcdFree N y)
    (largeGcdFreeOddCofactors_subset_oddRaw N y)

/-- Every divisor of the shifted coefficient whose prime factors are all
above the cutoff is squarefree on the corrected B4 family. -/
theorem squarefree_of_dvd_shiftedTotient_of_squarefreeLargeGcdFree
    {N y m h : ℕ}
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedTotient m)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Squarefree h := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hph : p ∣ h := dvd_trans (dvd_mul_right p p) hpp
  have hpsq : p ^ 2 ∣ shiftedTotient m := by
    rw [pow_two]
    exact dvd_trans hpp hh
  exact (mem_squarefreeLargeGcdFreeOddCofactors_iff.mp hm).2
    p hp (hlarge p hp hph) hpsq

end Erdos822

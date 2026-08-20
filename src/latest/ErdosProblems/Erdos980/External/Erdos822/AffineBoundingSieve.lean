/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.AffineCRT

/-!
# A finite bounding sieve for two affine forms

This is the direct finite input needed by the Brun upper sieve.  The
underlying parameters are the initial interval [0,X); fiber weights mean the
two-affine product need not be injective.
-/

namespace Erdos822

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

/-- Parameters below X for which a squarefree sieve divisor divides the
two-affine product. -/
def divisibleTwoAffineCandidates
    (a s b t X d : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun n ↦ d ∣ twoAffineProduct a s b t n

/-- Parameters below X for which the two-affine product avoids every
prime in the sieve product. -/
def siftedTwoAffineCandidates
    (a s b t X z Y : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun n ↦
    Nat.Coprime (Erdos387.sievePrimeProduct z Y)
      (twoAffineProduct a s b t n)

/-- The initial-interval bounding sieve for two affine forms.  The explicit
admissibility hypothesis records that every sieving prime avoids both
slopes. -/
noncomputable def twoAffineBoundingSieve
    (a s b t X z Y : ℕ) (hz : 2 ≤ z)
    (hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b) :
    BoundingSieve := by
  classical
  let I := Finset.range X
  exact
    { support := I.image (twoAffineProduct a s b t)
      prodPrimes := Erdos387.sievePrimeProduct z Y
      prodPrimes_squarefree := Erdos387.sievePrimeProduct_squarefree z Y
      weights := fun q ↦
        ((I.filter fun n ↦ twoAffineProduct a s b t n = q).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := X
      nu := twoAffineNu a s b t
      nu_mult := twoAffineNu_mult a s b t
      nu_pos_of_prime := by
        intro p hp hpDiv
        rw [twoAffineNu_prime hp]
        exact div_pos
          (by exact_mod_cast
            twoAffineLocalNu_pos_of_not_dvd_left hp (hadmissible p hp hpDiv).1)
          (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hpDiv
        have hpMem := Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpDiv
        have hzp : z < p := (Erdos387.mem_sievePrimes.mp hpMem).2.1
        exact (twoAffineNu_pos_lt_one_of_not_dvd hp
          (hz.trans_lt hzp) (hadmissible p hp hpDiv).1
          (hadmissible p hp hpDiv).2).2 }

theorem twoAffineBoundingSieve_totalMass
    {a s b t X z Y : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b} :
    (twoAffineBoundingSieve a s b t X z Y hz hadmissible).totalMass = X := rfl

/-- The abstract multiple sum is the cardinality of the corresponding
divisibility subset of the parameter interval. -/
theorem twoAffineBoundingSieve_multSum
    {a s b t X z Y d : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b} :
    (twoAffineBoundingSieve a s b t X z Y hz hadmissible).multSum d =
      ((divisibleTwoAffineCandidates a s b t X d).card : ℝ) := by
  classical
  let I := Finset.range X
  let f := twoAffineProduct a s b t
  rw [BoundingSieve.multSum]
  change (∑ q ∈ I.image f,
      if d ∣ q then ((I.filter fun n ↦ f n = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦ d ∣ q,
          (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦ d ∣ f n).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

/-- The weighted sifted sum is the number of parameters for which both
forms avoid every sieving prime. -/
theorem twoAffineBoundingSieve_siftedSum
    {a s b t X z Y : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b} :
    (twoAffineBoundingSieve a s b t X z Y hz hadmissible).siftedSum =
      ((siftedTwoAffineCandidates a s b t X z Y).card : ℝ) := by
  classical
  let I := Finset.range X
  let f := twoAffineProduct a s b t
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image f,
      if Nat.Coprime (Erdos387.sievePrimeProduct z Y) q then
        ((I.filter fun n ↦ f n = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z Y) q,
          (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z Y) (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

/-- Exact CRT interpretation of the multiple subset for every squarefree
modulus. -/
theorem divisibleTwoAffineCandidates_eq_modularPreimage_of_squarefree
    {a s b t X d : ℕ} (hsq : Squarefree d) :
    divisibleTwoAffineCandidates a s b t X d =
      Erdos387.modularPreimage X d
        (affineAssignmentResidues a s b t d) := by
  classical
  ext n
  simp only [divisibleTwoAffineCandidates, Erdos387.modularPreimage,
    Finset.mem_filter, Finset.mem_range]
  refine and_congr_right fun _hn ↦ ?_
  exact squarefree_dvd_twoAffineProduct_iff_mod_mem hsq

/-- Exact CRT interpretation for divisors of the standard prime product. -/
theorem divisibleTwoAffineCandidates_eq_modularPreimage
    {a s b t X z Y d : ℕ}
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    divisibleTwoAffineCandidates a s b t X d =
      Erdos387.modularPreimage X d
        (affineAssignmentResidues a s b t d) := by
  apply divisibleTwoAffineCandidates_eq_modularPreimage_of_squarefree
  exact Squarefree.squarefree_of_dvd hd
    (Erdos387.sievePrimeProduct_squarefree z Y)

/-- The initial-interval multiple count has its expected local-density main
term and at most one endpoint error per CRT class for every positive
squarefree modulus. -/
theorem abs_card_divisibleTwoAffineCandidates_sub_density_of_squarefree
    {a s b t X d : ℕ} (hsq : Squarefree d) (hdPos : 0 < d) :
    |↑(divisibleTwoAffineCandidates a s b t X d).card -
        (twoAffineNuClasses a s b t d : ℝ) * X / d| ≤
      twoAffineNuClasses a s b t d := by
  rw [divisibleTwoAffineCandidates_eq_modularPreimage_of_squarefree hsq,
    ← card_affineAssignmentResidues a s b t d]
  exact Erdos387.abs_card_modularPreimage_sub_density hdPos _
    (fun _r hr ↦ affineAssignmentResidues_lt hsq hr)

/-- The same endpoint estimate for divisors of the standard prime product. -/
theorem abs_card_divisibleTwoAffineCandidates_sub_density
    {a s b t X z Y d : ℕ}
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |↑(divisibleTwoAffineCandidates a s b t X d).card -
        (twoAffineNuClasses a s b t d : ℝ) * X / d| ≤
      twoAffineNuClasses a s b t d := by
  apply abs_card_divisibleTwoAffineCandidates_sub_density_of_squarefree
  · exact Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  · exact Erdos387.pos_of_dvd_sievePrimeProduct hd

/-- The bounding-sieve remainder is bounded by the number of simultaneous
affine bad classes. -/
theorem twoAffineBoundingSieve_abs_rem_le_nuClasses
    {a s b t X z Y d : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b}
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(twoAffineBoundingSieve a s b t X z Y hz hadmissible).rem d| ≤
      twoAffineNuClasses a s b t d := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  rw [BoundingSieve.rem, twoAffineBoundingSieve_multSum,
    twoAffineBoundingSieve_totalMass]
  change
    |↑(divisibleTwoAffineCandidates a s b t X d).card -
        twoAffineNu a s b t d * (X : ℝ)| ≤
      (twoAffineNuClasses a s b t d : ℝ)
  rw [twoAffineNu_squarefree hsq]
  simpa [mul_div_assoc, mul_comm, mul_left_comm] using
    abs_card_divisibleTwoAffineCandidates_sub_density
      (a := a) (s := s) (b := b) (t := t) (X := X) hd

/-- The abstract error sum is controlled by the explicit number of affine
CRT classes. -/
theorem twoAffineBoundingSieve_errSum_le_nuClasses
    {a s b t X z Y : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b}
    (mu : ℕ → ℝ) :
    (twoAffineBoundingSieve a s b t X z Y hz hadmissible).errSum mu ≤
      ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
        |mu d| * twoAffineNuClasses a s b t d := by
  rw [BoundingSieve.errSum]
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (twoAffineBoundingSieve_abs_rem_le_nuClasses
      (a := a) (s := s) (b := b) (t := t) (X := X) (z := z) (Y := Y)
      (Nat.mem_divisors.mp hd).1)
    (abs_nonneg (mu d))

/-- Finite upper-sieve application to the actual cardinality of the affine
sifted parameter set. -/
theorem twoAffineBoundingSieve_upper_cardinality_bound
    {a s b t X z Y : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b}
    (muPlus : ℕ → ℝ)
    (hmu : BoundingSieve.IsUpperMoebiusOnProdPrimes
      (s := twoAffineBoundingSieve a s b t X z Y hz hadmissible) muPlus) :
    ((siftedTwoAffineCandidates a s b t X z Y).card : ℝ) ≤
      (X : ℝ) *
          (twoAffineBoundingSieve a s b t X z Y hz hadmissible).mainSum muPlus +
        ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
          |muPlus d| * twoAffineNuClasses a s b t d := by
  let sieve := twoAffineBoundingSieve a s b t X z Y hz hadmissible
  have herr := twoAffineBoundingSieve_errSum_le_nuClasses
    (a := a) (s := s) (b := b) (t := t) (X := X) (z := z) (Y := Y)
    (hz := hz) (hadmissible := hadmissible) muPlus
  calc
    ((siftedTwoAffineCandidates a s b t X z Y).card : ℝ) =
        sieve.siftedSum := by
      exact twoAffineBoundingSieve_siftedSum.symm
    _ ≤ sieve.totalMass * sieve.mainSum muPlus + sieve.errSum muPlus :=
      sieve.siftedSum_le_totalMass_mainSum_add_errSum muPlus hmu
    _ ≤ (X : ℝ) * sieve.mainSum muPlus +
          ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
            |muPlus d| * twoAffineNuClasses a s b t d := by
      rw [show sieve.totalMass = (X : ℝ) by
        exact twoAffineBoundingSieve_totalMass]
      linarith

/-- The two conventions for a finite prime interval used by problems 387 and
851 agree after replacing the closed upper endpoint by its predecessor. -/
theorem erdos387_sievePrimes_eq_erdos851_sievePrimes
    {z Y : ℕ} (hY : 0 < Y) :
    Erdos387.sievePrimes z Y = Erdos851.sievePrimes z (Y - 1) := by
  ext p
  rw [Erdos387.mem_sievePrimes, Erdos851.mem_sievePrimes]
  constructor
  · rintro ⟨hp, hzp, hpY⟩
    exact ⟨hzp, by omega, hp⟩
  · rintro ⟨hzp, hpY, hp⟩
    exact ⟨hp, hzp, by omega⟩

/-- At a successor upper endpoint, the prime factors of the 387 sieve
product are exactly the half-open interval primes used by the Euler product
API. -/
theorem primeFactors_erdos387_sievePrimeProduct_succ (z y : ℕ) :
    (Erdos387.sievePrimeProduct z (y + 1)).primeFactors =
      Erdos851.sievePrimes z y := by
  unfold Erdos387.sievePrimeProduct
  rw [erdos387_sievePrimes_eq_erdos851_sievePrimes (by omega : 0 < y + 1)]
  simp only [Nat.add_sub_cancel]
  exact Nat.primeFactors_prod fun p hp ↦
    (Erdos851.mem_sievePrimes.mp hp).2.2

/-- The local Euler product of an admissible two-affine sieve is literally
the already-formalized pair-shift Euler product at the absolute determinant.
-/
theorem twoAffine_localEulerProduct_eq_pairShift
    {a s b t z Y : ℕ} (hY : 0 < Y)
    (hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b) :
    (∏ p ∈ Erdos387.sievePrimes z Y, (1 - twoAffineNu a s b t p)) =
      Erdos851.localEulerProduct
        (Erdos851.pairShiftDensity (affineDetNat a s b t)) z (Y - 1) := by
  rw [Erdos851.localEulerProduct,
    ← erdos387_sievePrimes_eq_erdos851_sievePrimes hY]
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp : p.Prime := (Erdos387.mem_sievePrimes.mp hpMem).1
  have hpDiv : p ∣ Erdos387.sievePrimeProduct z Y := by
    unfold Erdos387.sievePrimeProduct
    exact Finset.dvd_prod_of_mem id hpMem
  rw [twoAffineNu_eq_pairShiftDensity_of_not_dvd hp
    (hadmissible p hp hpDiv).1 (hadmissible p hp hpDiv).2]

/-- The abstract bounding-sieve Euler product at a successor endpoint is the
pair-shift Euler product for the affine determinant. -/
theorem twoAffineBoundingSieve_finiteEulerProduct_eq_pairShift
    {a s b t X z y : ℕ}
    {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z (y + 1) → ¬ p ∣ a ∧ ¬ p ∣ b} :
    Erdos387.finiteEulerProduct
        (twoAffineBoundingSieve a s b t X z (y + 1) hz hadmissible).prodPrimes.primeFactors
        (fun p ↦ (twoAffineBoundingSieve a s b t X z (y + 1) hz hadmissible).nu p) =
      Erdos851.localEulerProduct
        (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y := by
  change
    Erdos387.finiteEulerProduct
      (Erdos387.sievePrimeProduct z (y + 1)).primeFactors
      (fun p ↦ twoAffineNu a s b t p) =
      Erdos851.localEulerProduct
        (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y
  rw [Erdos387.finiteEulerProduct,
    primeFactors_erdos387_sievePrimeProduct_succ]
  simp only [Erdos851.localEulerProduct]
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp : p.Prime := (Erdos851.mem_sievePrimes.mp hpMem).2.2
  have hpDiv : p ∣ Erdos387.sievePrimeProduct z (y + 1) := by
    unfold Erdos387.sievePrimeProduct
    rw [erdos387_sievePrimes_eq_erdos851_sievePrimes (by omega : 0 < y + 1)]
    simp only [Nat.add_sub_cancel]
    exact Finset.dvd_prod_of_mem id hpMem
  rw [twoAffineNu_eq_pairShiftDensity_of_not_dvd hp
    (hadmissible p hp hpDiv).1 (hadmissible p hp hpDiv).2]

/-- A completely explicit finite upper bound obtained by taking Brun's even
truncation beyond the number of available sieve primes.  Later quantitative
applications replace this deliberately large depth by a short truncation;
this theorem is the exact checked bridge from the affine candidate count to
the determinant Euler product. -/
theorem siftedTwoAffineCandidates_full_brun_upper_bound
    {a s b t X z y : ℕ} {hz : 2 ≤ z}
    {hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z (y + 1) → ¬ p ∣ a ∧ ¬ p ∣ b} :
    let sieve := twoAffineBoundingSieve a s b t X z (y + 1) hz hadmissible
    let L := 2 * sieve.prodPrimes.primeFactors.card
    ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) ≤
      (X : ℝ) *
          Erdos851.localEulerProduct
            (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y +
        ∑ d ∈ (Erdos387.sievePrimeProduct z (y + 1)).divisors,
          |Erdos387.brunUpperWeight L d| *
            twoAffineNuClasses a s b t d := by
  dsimp only
  let sieve := twoAffineBoundingSieve a s b t X z (y + 1) hz hadmissible
  let L := 2 * sieve.prodPrimes.primeFactors.card
  have hL : Even L := by
    dsimp [L]
    exact even_two_mul _
  have hcard : sieve.prodPrimes.primeFactors.card ≤ L := by
    dsimp [L]
    omega
  have hupper := twoAffineBoundingSieve_upper_cardinality_bound
    (a := a) (s := s) (b := b) (t := t) (X := X) (z := z) (Y := y + 1)
    (hz := hz) (hadmissible := hadmissible)
    (Erdos387.brunUpperWeight L)
    (Erdos387.brunUpperWeight_isUpperOnProdPrimes sieve hL)
  change ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) ≤
      (X : ℝ) * sieve.mainSum (Erdos387.brunUpperWeight L) +
        ∑ d ∈ (Erdos387.sievePrimeProduct z (y + 1)).divisors,
          |Erdos387.brunUpperWeight L d| * twoAffineNuClasses a s b t d
    at hupper
  rw [Erdos387.boundingSieve_mainSum_brunUpperWeight_eq_euler_of_card_le
    sieve hcard,
    twoAffineBoundingSieve_finiteEulerProduct_eq_pairShift] at hupper
  exact hupper

/-- Consequently the affine local product has the standard two-dimensional
upper bound by the square of the one-shift product and the determinant
singular factor. -/
theorem twoAffine_localEulerProduct_le_pairShift_bound
    {a s b t z Y : ℕ} (hz : 2 ≤ z) (hY : 0 < Y)
    (hadmissible : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ¬ p ∣ a ∧ ¬ p ∣ b) :
    (∏ p ∈ Erdos387.sievePrimes z Y, (1 - twoAffineNu a s b t p)) ≤
      Erdos851.localEulerProduct Erdos851.oneShiftDensity z (Y - 1) ^ 2 *
        Erdos851.singularFactor (affineDetNat a s b t) z (Y - 1) := by
  rw [twoAffine_localEulerProduct_eq_pairShift hY hadmissible]
  exact Erdos851.pairShift_localEulerProduct_le
    (affineDetNat a s b t) hz

end Erdos822

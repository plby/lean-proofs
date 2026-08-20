/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import ErdosProblems.Erdos999.CRTProduct

/-!
# Congruence fibres for pairs of reduced residues

This file isolates the finite Chinese-remainder calculation used in the
Pollington--Vaughan overlap estimate.  If the two moduli are written as
`g * a` and `g * b`, with `a` and `b` coprime, the common ambient modulus is
`g * a * b`.  We count pairs of reduced residues in a fibre of

`b * A - a * B` modulo that ambient modulus.
-/

namespace Erdos999

open scoped BigOperators

/-- Pairs of reduced residues in one congruence fibre.  The parameters describe
the two moduli as `g * a` and `g * b`; in applications `a.Coprime b`. -/
def congruenceFiber (g a b : ℕ) (c : ℤ) :
    Finset (Fin (g * a) × Fin (g * b)) := by
  classical
  exact Finset.univ.filter fun z ↦
    (g * a).Coprime (z.1 : ℕ) ∧
      (g * b).Coprime (z.2 : ℕ) ∧
      (b : ZMod (g * a * b)) * (z.1 : ℕ) -
          (a : ZMod (g * a * b)) * (z.2 : ℕ) = c

/-- Cardinality of `congruenceFiber`. -/
def congruenceFiberCount (g a b : ℕ) (c : ℤ) : ℕ :=
  (congruenceFiber g a b c).card

@[simp] theorem mem_congruenceFiber_iff {g a b : ℕ}
    {c : ℤ} {z : Fin (g * a) × Fin (g * b)} :
    z ∈ congruenceFiber g a b c ↔
      (g * a).Coprime (z.1 : ℕ) ∧
      (g * b).Coprime (z.2 : ℕ) ∧
      (b : ZMod (g * a * b)) * (z.1 : ℕ) -
          (a : ZMod (g * a * b)) * (z.2 : ℕ) = c := by
  classical
  simp [congruenceFiber]

/-- The prime-power contribution at an equal-valuation prime. -/
def equalPrimeFactor (g c : ℕ) (p : ℕ) : ℕ :=
  p ^ (g.factorization p - 1) * (if p ∣ c then p - 1 else p - 2)

/-- The expected local product for a congruence fibre.  Primes dividing `a*b`
are the unequal-valuation primes.  At all other primes of `g`, the two
valuations are equal and the factor is `p-1` or `p-2` according as `p ∣ c`.

The value is zero unless `c` is coprime to every unequal-valuation prime. -/
def congruenceFiberLocalProduct (g a b : ℕ) (c : ℤ) : ℕ :=
  if (a * b).Coprime c.natAbs then
    ∏ p ∈ g.primeFactors,
      p ^ (g.factorization p - 1) *
        (if p ∣ a * b then p - 1
          else if p ∣ c.natAbs then p - 1 else p - 2)
  else 0

/-- Split form of `congruenceFiberLocalProduct`, separating primes whose
valuation is unequal in the two original denominators from the primes whose
valuation is equal. -/
theorem congruenceFiberLocalProduct_eq_split (g a b : ℕ) (c : ℤ) :
    congruenceFiberLocalProduct g a b c =
      if (a * b).Coprime c.natAbs then
        (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b),
            p ^ (g.factorization p - 1) * (p - 1)) *
          ∏ p ∈ g.primeFactors.filter (fun p ↦ ¬p ∣ a * b),
            equalPrimeFactor g c.natAbs p
      else 0 := by
  classical
  by_cases hcop : (a * b).Coprime c.natAbs
  · rw [congruenceFiberLocalProduct, if_pos hcop, if_pos hcop]
    calc
      (∏ p ∈ g.primeFactors,
          p ^ (g.factorization p - 1) *
            (if p ∣ a * b then p - 1
              else if p ∣ c.natAbs then p - 1 else p - 2)) =
          (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b),
            p ^ (g.factorization p - 1) *
              (if p ∣ a * b then p - 1
                else if p ∣ c.natAbs then p - 1 else p - 2)) *
          ∏ p ∈ g.primeFactors.filter (fun p ↦ ¬p ∣ a * b),
            p ^ (g.factorization p - 1) *
              (if p ∣ a * b then p - 1
                else if p ∣ c.natAbs then p - 1 else p - 2) :=
        (Finset.prod_filter_mul_prod_filter_not g.primeFactors
          (fun p ↦ p ∣ a * b) (fun p ↦
            p ^ (g.factorization p - 1) *
              (if p ∣ a * b then p - 1
                else if p ∣ c.natAbs then p - 1 else p - 2))).symm
      _ = _ := by
        apply congrArg₂ (· * ·)
        · apply Finset.prod_congr rfl
          intro p hp
          simp [(Finset.mem_filter.mp hp).2]
        · apply Finset.prod_congr rfl
          intro p hp
          simp [(Finset.mem_filter.mp hp).2, equalPrimeFactor]
  · simp [congruenceFiberLocalProduct, hcop]

private lemma congruence_of_mem_fiber {g a b : ℕ}
    {c : ℤ} {z : Fin (g * a) × Fin (g * b)}
    (hz : z ∈ congruenceFiber g a b c) :
    (b : ZMod (g * a * b)) * (z.1 : ℕ) -
        (a : ZMod (g * a * b)) * (z.2 : ℕ) = c :=
  (mem_congruenceFiber_iff.mp hz).2.2

private lemma linear_modEq_of_mem_fiber {g a b : ℕ}
    {c : ℤ} {z : Fin (g * a) × Fin (g * b)}
    (hz : z ∈ congruenceFiber g a b c) :
    (b * (z.1 : ℕ) : ℤ) ≡ (a * (z.2 : ℕ) : ℤ) + c [ZMOD g * a * b] := by
  have heq := congruence_of_mem_fiber hz
  have hadd :
      (b : ZMod (g * a * b)) * (z.1 : ℕ) =
        (a : ZMod (g * a * b)) * (z.2 : ℕ) + c := by
    linear_combination heq
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (by
    simpa [Nat.cast_ofNat, Nat.cast_mul] using hadd)

/-- If an unequal-valuation prime divides the fibre value, the reduced fibre
is empty. -/
theorem congruenceFiber_eq_empty_of_prime_dvd_unequal
    {g a b : ℕ} (hab : a.Coprime b) {c : ℤ}
    {p : ℕ} (hp : p.Prime) (hpab : p ∣ a * b) (hpc : (p : ℤ) ∣ c) :
    congruenceFiber g a b c = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro z hz
  have hcopA := (mem_congruenceFiber_iff.mp hz).1
  have hcopB := (mem_congruenceFiber_iff.mp hz).2.1
  have hpmod : p ∣ g * a * b := by
    simpa [Nat.mul_assoc] using dvd_mul_of_dvd_right hpab g
  have hlin := (linear_modEq_of_mem_fiber hz).of_dvd
    (Int.natCast_dvd_natCast.2 hpmod)
  rcases hp.dvd_mul.mp hpab with hpa | hpb
  · have hpnb : ¬p ∣ b := fun hpb ↦
      (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb) hab
    have hright : (p : ℤ) ∣ (a * (z.2 : ℕ) : ℤ) + c :=
      dvd_add (Int.natCast_dvd_natCast.2 (dvd_mul_of_dvd_left hpa _)) hpc
    have hleftZ : (p : ℤ) ∣ (b * (z.1 : ℕ) : ℤ) :=
      hlin.dvd_iff.mpr hright
    have hleft : p ∣ b * (z.1 : ℕ) := Int.natCast_dvd_natCast.1 hleftZ
    have hpA : p ∣ (z.1 : ℕ) := (hp.dvd_mul.mp hleft).resolve_left hpnb
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (dvd_mul_of_dvd_right hpa g) hpA) hcopA
  · have hpna : ¬p ∣ a := fun hpa ↦
      (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb) hab
    have hleft : (p : ℤ) ∣ (b * (z.1 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (dvd_mul_of_dvd_left hpb _)
    have hright : (p : ℤ) ∣ (a * (z.2 : ℕ) : ℤ) + c :=
      hlin.dvd_iff.mp hleft
    have haBZ : (p : ℤ) ∣ (a * (z.2 : ℕ) : ℤ) :=
      by
        have := dvd_sub hright hpc
        simpa using this
    have haB : p ∣ a * (z.2 : ℕ) := Int.natCast_dvd_natCast.1 haBZ
    have hpB : p ∣ (z.2 : ℕ) := (hp.dvd_mul.mp haB).resolve_left hpna
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (dvd_mul_of_dvd_right hpb g) hpB) hcopB

theorem congruenceFiberCount_eq_zero_of_prime_dvd_unequal
    {g a b : ℕ} (hab : a.Coprime b) {c : ℤ}
    {p : ℕ} (hp : p.Prime) (hpab : p ∣ a * b) (hpc : (p : ℤ) ∣ c) :
    congruenceFiberCount g a b c = 0 := by
  rw [congruenceFiberCount,
    congruenceFiber_eq_empty_of_prime_dvd_unequal hab hp hpab hpc]
  simp

/-- Two members of the same fibre have first coordinates congruent modulo
`a`.  This is the elementary cancellation step behind the bound by `g`. -/
theorem first_modEq_of_mem_congruenceFiber {g a b : ℕ}
    (hab : a.Coprime b) {c : ℤ}
    {x y : Fin (g * a) × Fin (g * b)}
    (hx : x ∈ congruenceFiber g a b c)
    (hy : y ∈ congruenceFiber g a b c) :
    (x.1 : ℕ) ≡ (y.1 : ℕ) [MOD a] := by
  have heq :
      (b : ZMod (g * a * b)) * (x.1 : ℕ) +
          (a : ZMod (g * a * b)) * (y.2 : ℕ) =
        (b : ZMod (g * a * b)) * (y.1 : ℕ) +
          (a : ZMod (g * a * b)) * (x.2 : ℕ) := by
    have hx' := congruence_of_mem_fiber hx
    have hy' := congruence_of_mem_fiber hy
    apply_fun fun t ↦ t +
      (a : ZMod (g * a * b)) * (x.2 : ℕ) +
      (a : ZMod (g * a * b)) * (y.2 : ℕ) at hx'
    apply_fun fun t ↦ t +
      (a : ZMod (g * a * b)) * (x.2 : ℕ) +
      (a : ZMod (g * a * b)) * (y.2 : ℕ) at hy'
    simp only [sub_add_cancel, add_assoc] at hx' hy'
    linear_combination hx' - hy'
  have heqNat :
      b * (x.1 : ℕ) + a * (y.2 : ℕ) ≡
        b * (y.1 : ℕ) + a * (x.2 : ℕ) [MOD g * a * b] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [Nat.cast_add, Nat.cast_mul] using heq
  have heqA := heqNat.of_dvd (by exact dvd_mul_of_dvd_left (dvd_mul_left a g) b)
  have hzeroX : a * (x.2 : ℕ) ≡ 0 [MOD a] :=
    (dvd_mul_right a (x.2 : ℕ)).modEq_zero_nat
  have hzeroY : a * (y.2 : ℕ) ≡ 0 [MOD a] :=
    (dvd_mul_right a (y.2 : ℕ)).modEq_zero_nat
  have hmul : b * (x.1 : ℕ) ≡ b * (y.1 : ℕ) [MOD a] := by
    calc
      b * (x.1 : ℕ) ≡ b * (x.1 : ℕ) + a * (y.2 : ℕ) [MOD a] := by
        simpa using (hzeroY.add_left (b * (x.1 : ℕ))).symm
      _ ≡ b * (y.1 : ℕ) + a * (x.2 : ℕ) [MOD a] := heqA
      _ ≡ b * (y.1 : ℕ) [MOD a] := by
        simpa using hzeroX.add_left (b * (y.1 : ℕ))
  exact hmul.cancel_left_of_coprime hab.gcd_eq_one

/-- Two members of the same fibre have second coordinates congruent modulo
`b`. -/
theorem second_modEq_of_mem_congruenceFiber {g a b : ℕ}
    (hab : a.Coprime b) {c : ℤ}
    {x y : Fin (g * a) × Fin (g * b)}
    (hx : x ∈ congruenceFiber g a b c)
    (hy : y ∈ congruenceFiber g a b c) :
    (x.2 : ℕ) ≡ (y.2 : ℕ) [MOD b] := by
  have heq :
      (b : ZMod (g * a * b)) * (x.1 : ℕ) +
          (a : ZMod (g * a * b)) * (y.2 : ℕ) =
        (b : ZMod (g * a * b)) * (y.1 : ℕ) +
          (a : ZMod (g * a * b)) * (x.2 : ℕ) := by
    have hx' := congruence_of_mem_fiber hx
    have hy' := congruence_of_mem_fiber hy
    apply_fun fun t ↦ t +
      (a : ZMod (g * a * b)) * (x.2 : ℕ) +
      (a : ZMod (g * a * b)) * (y.2 : ℕ) at hx'
    apply_fun fun t ↦ t +
      (a : ZMod (g * a * b)) * (x.2 : ℕ) +
      (a : ZMod (g * a * b)) * (y.2 : ℕ) at hy'
    simp only [sub_add_cancel, add_assoc] at hx' hy'
    linear_combination hx' - hy'
  have heqNat :
      b * (x.1 : ℕ) + a * (y.2 : ℕ) ≡
        b * (y.1 : ℕ) + a * (x.2 : ℕ) [MOD g * a * b] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [Nat.cast_add, Nat.cast_mul] using heq
  have heqB := heqNat.of_dvd (dvd_mul_left b (g * a))
  have hzeroX : b * (x.1 : ℕ) ≡ 0 [MOD b] :=
    (dvd_mul_right b (x.1 : ℕ)).modEq_zero_nat
  have hzeroY : b * (y.1 : ℕ) ≡ 0 [MOD b] :=
    (dvd_mul_right b (y.1 : ℕ)).modEq_zero_nat
  have hmul : a * (x.2 : ℕ) ≡ a * (y.2 : ℕ) [MOD b] := by
    calc
      a * (x.2 : ℕ) ≡ b * (y.1 : ℕ) + a * (x.2 : ℕ) [MOD b] := by
        simpa [Nat.add_comm] using (hzeroY.add_right (a * (x.2 : ℕ))).symm
      _ ≡ b * (x.1 : ℕ) + a * (y.2 : ℕ) [MOD b] := heqB.symm
      _ ≡ a * (y.2 : ℕ) [MOD b] := by
        simpa using hzeroX.add_right (a * (y.2 : ℕ))
  exact hmul.cancel_left_of_coprime hab.symm.gcd_eq_one

private def firstBlock {g a b : ℕ} (ha : 0 < a)
    (c : ℤ) (z : ↑(congruenceFiber g a b c)) : Fin g :=
  ⟨(z.1.1 : ℕ) / a, (Nat.div_lt_iff_lt_mul ha).2 (by
    simpa [Nat.mul_comm] using z.1.1.isLt)⟩

private def secondBlock {g a b : ℕ} (hb : 0 < b)
    (c : ℤ) (z : ↑(congruenceFiber g a b c)) : Fin g :=
  ⟨(z.1.2 : ℕ) / b, (Nat.div_lt_iff_lt_mul hb).2 (by
    simpa [Nat.mul_comm] using z.1.2.isLt)⟩

private lemma block_sum_modEq {g a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) {c : ℤ}
    (x y : ↑(congruenceFiber g a b c)) :
    (firstBlock ha c x : ℕ) + (secondBlock hb c y : ℕ) ≡
      (firstBlock ha c y : ℕ) + (secondBlock hb c x : ℕ) [MOD g] := by
  have hfirst := first_modEq_of_mem_congruenceFiber hab x.2 y.2
  have hsecond := second_modEq_of_mem_congruenceFiber hab x.2 y.2
  rw [Nat.ModEq] at hfirst hsecond
  have heq :
      (b : ZMod (g * a * b)) * (x.1.1 : ℕ) +
          (a : ZMod (g * a * b)) * (y.1.2 : ℕ) =
        (b : ZMod (g * a * b)) * (y.1.1 : ℕ) +
          (a : ZMod (g * a * b)) * (x.1.2 : ℕ) := by
    have hx := congruence_of_mem_fiber x.2
    have hy := congruence_of_mem_fiber y.2
    linear_combination hx - hy
  have heqNat :
      b * (x.1.1 : ℕ) + a * (y.1.2 : ℕ) ≡
        b * (y.1.1 : ℕ) + a * (x.1.2 : ℕ) [MOD g * a * b] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [Nat.cast_add, Nat.cast_mul] using heq
  have hdecompX1 : (x.1.1 : ℕ) = (x.1.1 : ℕ) % a +
      a * (firstBlock ha c x : ℕ) := by
    simpa [firstBlock] using (Nat.mod_add_div (x.1.1 : ℕ) a).symm
  have hdecompY1 : (y.1.1 : ℕ) = (y.1.1 : ℕ) % a +
      a * (firstBlock ha c y : ℕ) := by
    simpa [firstBlock] using (Nat.mod_add_div (y.1.1 : ℕ) a).symm
  have hdecompX2 : (x.1.2 : ℕ) = (x.1.2 : ℕ) % b +
      b * (secondBlock hb c x : ℕ) := by
    simpa [secondBlock] using (Nat.mod_add_div (x.1.2 : ℕ) b).symm
  have hdecompY2 : (y.1.2 : ℕ) = (y.1.2 : ℕ) % b +
      b * (secondBlock hb c y : ℕ) := by
    simpa [secondBlock] using (Nat.mod_add_div (y.1.2 : ℕ) b).symm
  rw [hdecompX1, hdecompY1, hdecompX2, hdecompY2, hfirst, hsecond] at heqNat
  have hnormalized :
      (b * ((y.1.1 : ℕ) % a) + a * ((y.1.2 : ℕ) % b)) +
          a * b * ((firstBlock ha c x : ℕ) + (secondBlock hb c y : ℕ)) ≡
        (b * ((y.1.1 : ℕ) % a) + a * ((y.1.2 : ℕ) % b)) +
          a * b * ((firstBlock ha c y : ℕ) + (secondBlock hb c x : ℕ))
            [MOD a * b * g] := by
    simpa [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heqNat
  have hscaled :
      a * b * ((firstBlock ha c x : ℕ) + (secondBlock hb c y : ℕ)) ≡
        a * b * ((firstBlock ha c y : ℕ) + (secondBlock hb c x : ℕ))
          [MOD a * b * g] := by
    exact hnormalized.add_left_cancel'
      (b * ((y.1.1 : ℕ) % a) + a * ((y.1.2 : ℕ) % b))
  exact hscaled.mul_left_cancel' (Nat.mul_pos ha hb).ne'

private lemma first_affine_eq {g a b p : ℕ} (ha : 0 < a)
    (hab : a.Coprime b) {c : ℤ}
    (x y : ↑(congruenceFiber g a b c)) :
    ((x.1.1 : ℕ) : ZMod p) + a * (firstBlock ha c y : ℕ) =
      ((y.1.1 : ℕ) : ZMod p) + a * (firstBlock ha c x : ℕ) := by
  have hmod := first_modEq_of_mem_congruenceFiber hab x.2 y.2
  rw [Nat.ModEq] at hmod
  have hx := Nat.mod_add_div (x.1.1 : ℕ) a
  have hy := Nat.mod_add_div (y.1.1 : ℕ) a
  have hnat : (x.1.1 : ℕ) + a * (firstBlock ha c y : ℕ) =
      (y.1.1 : ℕ) + a * (firstBlock ha c x : ℕ) := by
    simp only [firstBlock]
    omega
  simpa only [Nat.cast_add, Nat.cast_mul] using
    congrArg (fun n : ℕ ↦ (n : ZMod p)) hnat

private lemma second_affine_eq {g a b p : ℕ} (hb : 0 < b)
    (hab : a.Coprime b) {c : ℤ}
    (x y : ↑(congruenceFiber g a b c)) :
    ((x.1.2 : ℕ) : ZMod p) + b * (secondBlock hb c y : ℕ) =
      ((y.1.2 : ℕ) : ZMod p) + b * (secondBlock hb c x : ℕ) := by
  have hmod := second_modEq_of_mem_congruenceFiber hab x.2 y.2
  rw [Nat.ModEq] at hmod
  have hx := Nat.mod_add_div (x.1.2 : ℕ) b
  have hy := Nat.mod_add_div (y.1.2 : ℕ) b
  have hnat : (x.1.2 : ℕ) + b * (secondBlock hb c y : ℕ) =
      (y.1.2 : ℕ) + b * (secondBlock hb c x : ℕ) := by
    simp only [secondBlock]
    omega
  simpa only [Nat.cast_add, Nat.cast_mul] using
    congrArg (fun n : ℕ ↦ (n : ZMod p)) hnat

private lemma block_sum_cast_eq {g a b p : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hpg : p ∣ g) {c : ℤ}
    (x y : ↑(congruenceFiber g a b c)) :
    ((firstBlock ha c x : ℕ) : ZMod p) + (secondBlock hb c y : ℕ) =
      (firstBlock ha c y : ℕ) + (secondBlock hb c x : ℕ) := by
  have hmod := (block_sum_modEq ha hb hab x y).of_dvd hpg
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  simpa [Nat.cast_add] using hmod

private noncomputable def congruenceFiberPrimeImage {g a b : ℕ}
    (ha : 0 < a) (c : ℤ) (p : g.primeFactors) : Finset (ZMod (p : ℕ)) :=
  (congruenceFiber g a b c).attach.image fun z ↦
    ((firstBlock ha c z : ℕ) : ZMod (p : ℕ))

private noncomputable def congruenceFiberPrimePowerImage {g a b : ℕ}
    (ha : 0 < a) (c : ℤ) (p : g.primeFactors) :
    Finset (ZMod ((p : ℕ) ^ g.factorization p)) :=
  (congruenceFiber g a b c).attach.image fun z ↦
    ((firstBlock ha c z : ℕ) : ZMod ((p : ℕ) ^ g.factorization p))

private lemma congruenceFiberPrimeImage_card_le {g a b : ℕ}
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (c : ℤ) (p : g.primeFactors) :
    (congruenceFiberPrimeImage (b := b) ha c p).card ≤
      if (p : ℕ) ∣ a * b then (p : ℕ) - 1
      else if (p : ℕ) ∣ c.natAbs then (p : ℕ) - 1 else (p : ℕ) - 2 := by
  classical
  let hp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨hp⟩
  have hpg : (p : ℕ) ∣ g := Nat.dvd_of_mem_primeFactors p.2
  by_cases hne : (congruenceFiber g a b c).Nonempty
  · let z₀ : ↑(congruenceFiber g a b c) := ⟨hne.choose, hne.choose_spec⟩
    let t₀ : ZMod (p : ℕ) := ((firstBlock ha c z₀ : ℕ) : ZMod (p : ℕ))
    let A₀ : ZMod (p : ℕ) := ((z₀.1.1 : ℕ) : ZMod (p : ℕ))
    let B₀ : ZMod (p : ℕ) := ((z₀.1.2 : ℕ) : ZMod (p : ℕ))
    let rootA : ZMod (p : ℕ) := t₀ - A₀ / (a : ZMod (p : ℕ))
    let rootB : ZMod (p : ℕ) := t₀ - B₀ / (b : ZMod (p : ℕ))
    have rootA_not_mem (hpna : ¬(p : ℕ) ∣ a) :
        rootA ∉ congruenceFiberPrimeImage (b := b) ha c p := by
      intro hmem
      obtain ⟨z, -, htz⟩ := Finset.mem_image.mp hmem
      have ha0 : (a : ZMod (p : ℕ)) ≠ 0 := by
        exact fun h ↦ hpna ((ZMod.natCast_eq_zero_iff a (p : ℕ)).mp h)
      have hrel := first_affine_eq (p := (p : ℕ)) ha hab z z₀
      have hAzero : ((z.1.1 : ℕ) : ZMod (p : ℕ)) = 0 := by
        change ((z.1.1 : ℕ) : ZMod (p : ℕ)) = 0
        change ((firstBlock ha c z : ℕ) : ZMod (p : ℕ)) = rootA at htz
        rw [htz] at hrel
        change ((z.1.1 : ℕ) : ZMod (p : ℕ)) + a * t₀ =
          A₀ + a * rootA at hrel
        change ((z.1.1 : ℕ) : ZMod (p : ℕ)) = 0
        dsimp only [rootA] at hrel
        field_simp [ha0] at hrel
        linear_combination hrel
      have hpA : (p : ℕ) ∣ (z.1.1 : ℕ) :=
        (ZMod.natCast_eq_zero_iff _ _).mp hAzero
      have hcopA := (mem_congruenceFiber_iff.mp z.2).1
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
        (dvd_mul_of_dvd_left hpg a) hpA) hcopA
    have rootB_not_mem (hpnb : ¬(p : ℕ) ∣ b) :
        rootB ∉ congruenceFiberPrimeImage (b := b) ha c p := by
      intro hmem
      obtain ⟨z, -, htz⟩ := Finset.mem_image.mp hmem
      have hb0 : (b : ZMod (p : ℕ)) ≠ 0 := by
        exact fun h ↦ hpnb ((ZMod.natCast_eq_zero_iff b (p : ℕ)).mp h)
      have hrelB := second_affine_eq (p := (p : ℕ)) hb hab z z₀
      have hrelBlock := block_sum_cast_eq ha hb hab hpg z z₀
      have hBzero : ((z.1.2 : ℕ) : ZMod (p : ℕ)) = 0 := by
        change ((firstBlock ha c z : ℕ) : ZMod (p : ℕ)) = rootB at htz
        rw [htz] at hrelBlock
        change ((z.1.2 : ℕ) : ZMod (p : ℕ)) + b * (secondBlock hb c z₀ : ℕ) =
          B₀ + b * (secondBlock hb c z : ℕ) at hrelB
        change rootB + (secondBlock hb c z₀ : ℕ) =
          t₀ + (secondBlock hb c z : ℕ) at hrelBlock
        change ((z.1.2 : ℕ) : ZMod (p : ℕ)) = 0
        dsimp only [rootB] at hrelBlock
        field_simp [hb0] at hrelBlock
        linear_combination hrelB - hrelBlock
      have hpB : (p : ℕ) ∣ (z.1.2 : ℕ) :=
        (ZMod.natCast_eq_zero_iff _ _).mp hBzero
      have hcopB := (mem_congruenceFiber_iff.mp z.2).2.1
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
        (dvd_mul_of_dvd_left hpg b) hpB) hcopB
    have one_forbidden (r : ZMod (p : ℕ))
        (hr : r ∉ congruenceFiberPrimeImage (b := b) ha c p) :
        (congruenceFiberPrimeImage (b := b) ha c p).card ≤ (p : ℕ) - 1 := by
      calc
        (congruenceFiberPrimeImage (b := b) ha c p).card ≤
            ((Finset.univ : Finset (ZMod (p : ℕ))).erase r).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact fun hxr ↦ hr (hxr ▸ hx)
        _ = (p : ℕ) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, ZMod.card]
    by_cases hpab : (p : ℕ) ∣ a * b
    · simp only [hpab, if_pos]
      rcases hp.dvd_mul.mp hpab with hpa | hpb
      · have hpnb : ¬(p : ℕ) ∣ b := fun hpb ↦
          (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb) hab
        exact one_forbidden rootB (rootB_not_mem hpnb)
      · have hpna : ¬(p : ℕ) ∣ a := fun hpa ↦
          (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb) hab
        exact one_forbidden rootA (rootA_not_mem hpna)
    · have hpna : ¬(p : ℕ) ∣ a := fun hpa ↦ hpab (dvd_mul_of_dvd_left hpa b)
      have hpnb : ¬(p : ℕ) ∣ b := fun hpb ↦ hpab (dvd_mul_of_dvd_right hpb a)
      simp only [hpab, if_false]
      by_cases hpc : (p : ℕ) ∣ c.natAbs
      · simp only [hpc, if_pos]
        exact one_forbidden rootA (rootA_not_mem hpna)
      · simp only [hpc, if_false]
        have hroots : rootA ≠ rootB := by
          intro heq
          have ha0 : (a : ZMod (p : ℕ)) ≠ 0 := by
            exact fun h ↦ hpna ((ZMod.natCast_eq_zero_iff a (p : ℕ)).mp h)
          have hb0 : (b : ZMod (p : ℕ)) ≠ 0 := by
            exact fun h ↦ hpnb ((ZMod.natCast_eq_zero_iff b (p : ℕ)).mp h)
          have hcross : (b : ZMod (p : ℕ)) * A₀ =
              (a : ZMod (p : ℕ)) * B₀ := by
            dsimp only [rootA, rootB] at heq
            have hdiv : A₀ / (a : ZMod (p : ℕ)) =
                B₀ / (b : ZMod (p : ℕ)) := by
              exact sub_right_inj.mp heq
            field_simp [ha0, hb0] at hdiv
            simpa [mul_comm] using hdiv
          have hpmod : (p : ℕ) ∣ g * a * b := by
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpg a) b
          have hlin := (linear_modEq_of_mem_fiber z₀.2).of_dvd
            (Int.natCast_dvd_natCast.2 hpmod)
          have hcast :
              (b : ZMod (p : ℕ)) * A₀ =
                (a : ZMod (p : ℕ)) * B₀ + (c : ZMod (p : ℕ)) := by
            simpa [A₀, B₀, Nat.cast_mul] using
              (ZMod.intCast_eq_intCast_iff _ _ _).mpr hlin
          have hc0 : (c : ZMod (p : ℕ)) = 0 := by
            rw [hcross] at hcast
            apply add_left_cancel (a := (a : ZMod (p : ℕ)) * B₀)
            simpa using hcast.symm
          have hpcZ : ((p : ℤ) ∣ c) :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd c (p : ℕ)).mp hc0
          apply hpc
          apply Int.natCast_dvd_natCast.1
          exact Int.dvd_natAbs.2 hpcZ
        calc
          (congruenceFiberPrimeImage (b := b) ha c p).card ≤
              (((Finset.univ : Finset (ZMod (p : ℕ))).erase rootA).erase rootB).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            exact ⟨fun h ↦ rootB_not_mem hpnb (h ▸ hx),
              fun h ↦ rootA_not_mem hpna (h ▸ hx)⟩
          _ = (p : ℕ) - 2 := by
            rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem,
              Finset.card_univ, ZMod.card]
            · omega
            · simp
            · simp [hroots.symm]
  · have himage : congruenceFiberPrimeImage (b := b) ha c p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro x hx
      obtain ⟨z, -, -⟩ := Finset.mem_image.mp hx
      exact hne ⟨z.1, z.2⟩
    rw [himage]
    simp

private lemma congruenceFiberPrimePowerImage_card_le {g a b : ℕ}
    (hg : 0 < g) (ha : 0 < a) (c : ℤ) (p : g.primeFactors) :
    (congruenceFiberPrimePowerImage (b := b) ha c p).card ≤
      (p : ℕ) ^ (g.factorization p - 1) *
        (congruenceFiberPrimeImage (b := b) ha c p).card := by
  classical
  let hp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
  have hpg : (p : ℕ) ∣ g := Nat.dvd_of_mem_primeFactors p.2
  have he : 0 < g.factorization p := hp.factorization_pos_of_dvd hg.ne' hpg
  have hp0 : 0 < (p : ℕ) := hp.pos
  have hpow0 : (p : ℕ) ^ g.factorization p ≠ 0 := pow_ne_zero _ hp.ne_zero
  letI : NeZero ((p : ℕ) ^ g.factorization p) := ⟨hpow0⟩
  have hpPow : (p : ℕ) ∣ (p : ℕ) ^ g.factorization p := dvd_pow_self _ he.ne'
  let project :
      ↑(congruenceFiberPrimePowerImage (b := b) ha c p) →
        Fin ((p : ℕ) ^ (g.factorization p - 1)) ×
          ↑(congruenceFiberPrimeImage (b := b) ha c p) := fun x ↦
    (⟨x.1.val / (p : ℕ), by
        apply (Nat.div_lt_iff_lt_mul hp0).2
        rw [← pow_succ, show g.factorization p - 1 + 1 = g.factorization p by omega]
        exact x.1.val_lt⟩,
      ⟨ZMod.castHom hpPow (ZMod (p : ℕ)) x.1, by
        obtain ⟨z, -, hx⟩ := Finset.mem_image.mp x.2
        apply Finset.mem_image.2
        refine ⟨z, by simp, ?_⟩
        rw [← hx]
        simp⟩)
  have hinj : Function.Injective project := by
    intro x y hxy
    apply Subtype.ext
    apply ZMod.val_injective ((p : ℕ) ^ g.factorization p)
    have hdiv : x.1.val / (p : ℕ) = y.1.val / (p : ℕ) := by
      exact Fin.ext_iff.mp (congrArg Prod.fst hxy)
    have hproj : ZMod.castHom hpPow (ZMod (p : ℕ)) x.1 =
        ZMod.castHom hpPow (ZMod (p : ℕ)) y.1 := by
      exact congrArg Subtype.val (congrArg Prod.snd hxy)
    have hmod : x.1.val % (p : ℕ) = y.1.val % (p : ℕ) := by
      have hproj' := hproj
      rw [← ZMod.natCast_zmod_val x.1, ← ZMod.natCast_zmod_val y.1] at hproj'
      have hcast : (x.1.val : ZMod (p : ℕ)) = (y.1.val : ZMod (p : ℕ)) := by
        simpa only [map_natCast] using hproj'
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    exact Nat.mod_add_div x.1.val (p : ℕ) ▸
      Nat.mod_add_div y.1.val (p : ℕ) ▸
        congrArg₂ (fun u v ↦ u + (p : ℕ) * v) hmod hdiv
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective project hinj

private lemma firstBlock_injective {g a b : ℕ} (ha : 0 < a)
    (hab : a.Coprime b) (c : ℤ) :
    Function.Injective (firstBlock (g := g) (b := b) ha c) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    have hmod := first_modEq_of_mem_congruenceFiber hab x.2 y.2
    have hdiv : (x.1.1 : ℕ) / a = (y.1.1 : ℕ) / a := by
      exact Fin.ext_iff.mp hxy
    rw [Nat.ModEq] at hmod
    exact Nat.mod_add_div (x.1.1 : ℕ) a ▸
      Nat.mod_add_div (y.1.1 : ℕ) a ▸ congrArg₂ (fun u v ↦ u + a * v) hmod hdiv
  · have hx := congruence_of_mem_fiber x.2
    have hy := congruence_of_mem_fiber y.2
    have hfirst : x.1.1 = y.1.1 := by
      apply Fin.ext
      have hmod := first_modEq_of_mem_congruenceFiber hab x.2 y.2
      have hdiv : (x.1.1 : ℕ) / a = (y.1.1 : ℕ) / a := by
        exact Fin.ext_iff.mp hxy
      rw [Nat.ModEq] at hmod
      exact Nat.mod_add_div (x.1.1 : ℕ) a ▸
        Nat.mod_add_div (y.1.1 : ℕ) a ▸ congrArg₂ (fun u v ↦ u + a * v) hmod hdiv
    rw [hfirst] at hx
    have hmul :
        (a : ZMod (g * a * b)) * (x.1.2 : ℕ) =
          (a : ZMod (g * a * b)) * (y.1.2 : ℕ) := by
      linear_combination hy - hx
    have hmodNat :
        a * (x.1.2 : ℕ) ≡ a * (y.1.2 : ℕ) [MOD g * a * b] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa [Nat.cast_mul] using hmul
    have hcancel : (x.1.2 : ℕ) ≡ (y.1.2 : ℕ) [MOD g * b] := by
      have hmodNat' :
          a * (x.1.2 : ℕ) ≡ a * (y.1.2 : ℕ) [MOD a * (g * b)] := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmodNat
      exact hmodNat'.mul_left_cancel' ha.ne'
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hcancel x.1.2.isLt y.1.2.isLt)

private lemma congruenceFiberCount_le_prod_primePowerImage {g a b : ℕ}
    (hg : 0 < g) (ha : 0 < a) (hab : a.Coprime b) (c : ℤ) :
    congruenceFiberCount g a b c ≤
      ∏ p : g.primeFactors,
        (congruenceFiberPrimePowerImage (b := b) ha c p).card := by
  classical
  let embed : ↑(congruenceFiber g a b c) →
      ((p : g.primeFactors) →
        ↑(congruenceFiberPrimePowerImage (b := b) ha c p)) := fun z p ↦
    ⟨((firstBlock ha c z : ℕ) : ZMod ((p : ℕ) ^ g.factorization p)), by
      apply Finset.mem_image.2
      exact ⟨z, by simp, rfl⟩⟩
  have hinj : Function.Injective embed := by
    intro x y hxy
    apply firstBlock_injective ha hab c
    apply Fin.ext
    have hcoords :
        (fun p : g.primeFactors ↦
          ZMod.equivPi (n := g) hg.ne'
            ((firstBlock ha c x : ℕ) : ZMod g) p) =
        (fun p : g.primeFactors ↦
          ZMod.equivPi (n := g) hg.ne'
            ((firstBlock ha c y : ℕ) : ZMod g) p) := by
      funext p
      have hpEq := congrArg Subtype.val (congrFun hxy p)
      change ((firstBlock ha c x : ℕ) :
          ZMod ((p : ℕ) ^ g.factorization p)) =
        ((firstBlock ha c y : ℕ) :
          ZMod ((p : ℕ) ^ g.factorization p)) at hpEq
      simpa using hpEq
    have hcast :
        ((firstBlock ha c x : ℕ) : ZMod g) =
          ((firstBlock ha c y : ℕ) : ZMod g) :=
      (ZMod.equivPi (n := g) hg.ne').injective hcoords
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ g).mp hcast
    exact Nat.ModEq.eq_of_lt_of_lt hmod
      (firstBlock ha c x).isLt (firstBlock ha c y).isLt
  rw [congruenceFiberCount, ← Fintype.card_coe]
  calc
    Fintype.card ↑(congruenceFiber g a b c) ≤
        Fintype.card ((p : g.primeFactors) →
          ↑(congruenceFiberPrimePowerImage (b := b) ha c p)) :=
      Fintype.card_le_of_injective embed hinj
    _ = ∏ p : g.primeFactors,
          (congruenceFiberPrimePowerImage (b := b) ha c p).card := by
      rw [Fintype.card_pi]
      simp only [Fintype.card_coe]

/-- The exact prime-product upper bound for a reduced congruence fibre.
At a prime of `g` which divides `a*b`, the local factor is
`p^(v_p(g)-1) * (p-1)`.  At every other prime of `g`, it is
`p^(v_p(g)-1) * (p-1)` when `p ∣ c`, and
`p^(v_p(g)-1) * (p-2)` otherwise. -/
theorem congruenceFiberCount_le_localProduct {g a b : ℕ}
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (c : ℤ) :
    congruenceFiberCount g a b c ≤ congruenceFiberLocalProduct g a b c := by
  classical
  by_cases hcop : (a * b).Coprime c.natAbs
  · rw [congruenceFiberLocalProduct, if_pos hcop]
    calc
      congruenceFiberCount g a b c ≤
          ∏ p : g.primeFactors,
            (congruenceFiberPrimePowerImage (b := b) ha c p).card :=
        congruenceFiberCount_le_prod_primePowerImage hg ha hab c
      _ ≤ ∏ p : g.primeFactors,
          (p : ℕ) ^ (g.factorization p - 1) *
            (congruenceFiberPrimeImage (b := b) ha c p).card := by
        apply Finset.prod_le_prod
        · intro p _
          exact Nat.zero_le _
        · intro p _
          exact congruenceFiberPrimePowerImage_card_le hg ha c p
      _ ≤ ∏ p : g.primeFactors,
          (p : ℕ) ^ (g.factorization p - 1) *
            (if (p : ℕ) ∣ a * b then (p : ℕ) - 1
              else if (p : ℕ) ∣ c.natAbs then (p : ℕ) - 1 else (p : ℕ) - 2) := by
        apply Finset.prod_le_prod
        · intro p _
          exact Nat.zero_le _
        · intro p _
          exact Nat.mul_le_mul_left _
            (congruenceFiberPrimeImage_card_le hg ha hb hab c p)
      _ = ∏ p ∈ g.primeFactors,
          p ^ (g.factorization p - 1) *
            (if p ∣ a * b then p - 1
              else if p ∣ c.natAbs then p - 1 else p - 2) := by
        rw [show (Finset.univ : Finset g.primeFactors) =
          g.primeFactors.attach by ext p; simp]
        exact Finset.prod_attach g.primeFactors (fun p ↦
          p ^ (g.factorization p - 1) *
            (if p ∣ a * b then p - 1
              else if p ∣ c.natAbs then p - 1 else p - 2))
  · rw [congruenceFiberLocalProduct, if_neg hcop]
    obtain ⟨p, hp, hpab, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    rw [congruenceFiberCount_eq_zero_of_prime_dvd_unequal hab hp hpab]
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.2 hpc)

/-- A congruence fibre has at most `g` elements before any local coprimality
density is used. -/
theorem congruenceFiberCount_le_g {g a b : ℕ} (hg : 0 < g) (ha : 0 < a)
    (hab : a.Coprime b) (c : ℤ) :
    congruenceFiberCount g a b c ≤ g := by
  classical
  rw [congruenceFiberCount, ← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective (firstBlock ha c)
    (firstBlock_injective ha hab c)

end Erdos999

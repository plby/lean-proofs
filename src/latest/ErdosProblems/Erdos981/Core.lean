/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.CharacterLargeSieve
import ErdosProblems.Erdos981.External.Erdos439.Main
import ErdosProblems.Erdos888.SquarePart
import ErdosProblems.Erdos981.External.Erdos822.FiniteEnergy
import ErdosProblems.Erdos387.AnalyticInputs
import ErdosProblems.Erdos981.External.Erdos980.Assembly
import ErdosProblems.Erdos981.External.Erdos980.ElliottTail.Burgess
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Erdős Problem 981: core definitions and finite character estimates

For an odd prime `p`, let `F ε p` be the least positive integer `m` after
which every quadratic character partial sum is strictly below `ε * N`.
This file proves Elliott's asymptotic mean theorem for `F ε p`.

The detailed mathematical proof and Leanization map are in `tex/981.tex`.
-/

open scoped BigOperators NumberTheorySymbols
open Filter Finset

namespace Erdos981

/-! ## Quadratic characters with a natural modulus

The medium-range moment argument sums `J(d | m)` with `m` varying.  The
following small wrapper packages the elementary periodicity and
multiplicativity properties needed to regard that function as an ordinary
complex Dirichlet character.  Keeping the wrapper here makes the precise
normalization (`0` off the reduced residue classes) explicit.
-/

/-- An integer-valued quadratic character modulo `m`, in the exact form used
below before passage to Mathlib's complex `DirichletCharacter`. -/
structure QuadraticCharacterMod (m : ℕ) where
  toFun : ℕ → ℤ
  periodic : ∀ {a b : ℕ}, Nat.ModEq m a b → toFun a = toFun b
  map_non_coprime : ∀ {a : ℕ}, ¬ Nat.Coprime a m → toFun a = 0
  map_coprime : ∀ {a : ℕ}, Nat.Coprime a m → toFun a = 1 ∨ toFun a = -1
  map_mul : ∀ {a b : ℕ}, Nat.Coprime a m → Nat.Coprime b m →
    toFun (a * b) = toFun a * toFun b

instance {m : ℕ} : CoeFun (QuadraticCharacterMod m) (fun _ ↦ ℕ → ℤ) :=
  ⟨QuadraticCharacterMod.toFun⟩

lemma QuadraticCharacterMod.map_one {m : ℕ} (χ : QuadraticCharacterMod m) :
    χ 1 = 1 := by
  have hcop : Nat.Coprime 1 m := by simp
  rcases χ.map_coprime hcop with h | h
  · exact h
  · have hmul := χ.map_mul (a := 1) (b := 1) hcop hcop
    rw [h] at hmul
    norm_num at hmul

lemma natCoprime_val_of_isUnit_zmod {m : ℕ} [NeZero m]
    {a : ZMod m} (ha : IsUnit a) : Nat.Coprime a.val m := by
  rw [← ha.unit_spec]
  exact ZMod.val_coe_unit_coprime ha.unit

lemma not_natCoprime_val_of_not_isUnit_zmod {m : ℕ} [NeZero m]
    {a : ZMod m} (ha : ¬ IsUnit a) : ¬ Nat.Coprime a.val m := by
  intro hcop
  apply ha
  simpa [ZMod.natCast_zmod_val a] using
    (ZMod.isUnit_iff_coprime a.val m).2 hcop

/-- The complex Dirichlet character associated to an integer-valued
quadratic character. -/
def QuadraticCharacterMod.toDirichletCharacterComplex {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) : DirichletCharacter ℂ m where
  toFun a := (χ a.val : ℂ)
  map_one' := by
    have hperiodic : χ ((1 : ZMod m).val) = χ 1 := by
      apply χ.periodic
      rw [← ZMod.natCast_eq_natCast_iff]
      simp
    rw [hperiodic]
    simpa using congrArg (fun z : ℤ ↦ (z : ℂ)) χ.map_one
  map_mul' := by
    intro a b
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · have hcopa := natCoprime_val_of_isUnit_zmod ha
        have hcopb := natCoprime_val_of_isUnit_zmod hb
        have hperiodic : χ ((a * b).val) = χ (a.val * b.val) := by
          apply χ.periodic
          rw [← ZMod.natCast_eq_natCast_iff]
          simp
        rw [show (χ ((a * b).val) : ℂ) = (χ (a.val * b.val) : ℂ) by
          exact_mod_cast hperiodic]
        exact_mod_cast χ.map_mul hcopa hcopb
      · have hnon : ¬ IsUnit (a * b) := fun hab ↦
          hb (isUnit_of_mul_isUnit_right hab)
        rw [χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon),
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hb)]
        simp
    · have hnon : ¬ IsUnit (a * b) := fun hab ↦
        ha (isUnit_of_mul_isUnit_left hab)
      rw [χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon),
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)]
      simp
  map_nonunit' := by
    intro a ha
    rw [χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)]
    simp

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) := by
  change ((χ ((n : ZMod m).val) : ℂ) = (χ n : ℂ))
  simpa [ZMod.val_natCast] using congrArg (fun z : ℤ ↦ (z : ℂ))
    (χ.periodic (Nat.mod_modEq n m))

private lemma d_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : d ∣ m :=
  dvd_trans (dvd_mul_left d 4) hdvd

private lemma two_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : 2 ∣ m :=
  dvd_trans (by exact ⟨2 * d, by omega⟩) hdvd

/-- The real quadratic character `J(d|·)`, regarded modulo any multiple of
`4d`. -/
def attachedQuadraticCharacter (d m : ℕ) (hdvd : 4 * d ∣ m) :
    QuadraticCharacterMod m where
  toFun n := if Nat.Coprime n m then jacobiSym (d : ℤ) n else 0
  periodic := by
    intro a b hmod
    have hcop : Nat.Coprime a m ↔ Nat.Coprime b m := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
    by_cases ha : Nat.Coprime a m
    · have hb := hcop.mp ha
      have hmod' : Nat.ModEq (4 * d) a b := hmod.of_dvd hdvd
      have haOdd : Odd a := (Nat.coprime_two_right).1
        (ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd))
      have hbOdd : Odd b := (Nat.coprime_two_right).1
        (hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd))
      rw [if_pos ha, if_pos hb]
      calc
        jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) (a % (4 * d)) := by
          simpa using jacobiSym.mod_right (d : ℤ) haOdd
        _ = jacobiSym (d : ℤ) (b % (4 * d)) := by rw [hmod']
        _ = jacobiSym (d : ℤ) b := by
          simpa using (jacobiSym.mod_right (d : ℤ) hbOdd).symm
    · have hb : ¬ Nat.Coprime b m := mt hcop.mpr ha
      rw [if_neg ha, if_neg hb]
  map_non_coprime := by
    intro a ha
    rw [if_neg ha]
  map_coprime := by
    intro a ha
    have had : Nat.Coprime a d :=
      ha.coprime_dvd_right (d_dvd_of_four_d_dvd hdvd)
    have hgcd : Int.gcd (d : ℤ) a = 1 := by
      simpa [Int.gcd_eq_natAbs, Nat.gcd_comm] using had.gcd_eq_one
    rw [if_pos ha]
    exact jacobiSym.eq_one_or_neg_one hgcd
  map_mul := by
    intro a b ha hb
    have haOdd : Odd a := (Nat.coprime_two_right).1
      (ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd))
    have hbOdd : Odd b := (Nat.coprime_two_right).1
      (hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd))
    have ha0 : a ≠ 0 := fun h ↦ by subst a; simp at haOdd
    have hb0 : b ≠ 0 := fun h ↦ by subst b; simp at hbOdd
    split_ifs at * with hab
    · exact jacobiSym.mul_right' (d : ℤ) ha0 hb0
    · exact (hab (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩)).elim

@[simp] lemma attachedQuadraticCharacter_apply_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = jacobiSym (d : ℤ) n := by
  simp [attachedQuadraticCharacter, hn]

/-- A nontrivial squarefree numerator has a reduced residue on which its
Jacobi character is `-1`.  This is the elementary CRT input behind the
nonprincipality of the attached character. -/
lemma exists_coprime_jacobiSym_eq_neg_one_of_squarefree
    {d : ℕ} (hd : Squarefree d) (hd1 : 1 < d) :
    ∃ a : ℕ, Nat.Coprime a (4 * d) ∧ Odd a ∧ jacobiSym (d : ℤ) a = -1 := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd1.ne'
  let e := d / q
  have hdecomp : q * e = d := Nat.mul_div_cancel' hqd
  have hqecop : Nat.Coprime q e := by
    apply Nat.coprime_of_squarefree_mul
    simpa [hdecomp] using hd
  by_cases hq2 : q = 2
  · subst q
    have heOdd : Odd e := by
      rw [← Nat.coprime_two_left]
      exact hqecop
    have h8e : Nat.Coprime 8 e := by
      exact (Nat.Coprime.pow_left 3 hqecop)
    let a : ℕ := (Nat.chineseRemainder h8e 5 1).1
    have ha8 : Nat.ModEq 8 a 5 := by
      simpa [a] using (Nat.chineseRemainder h8e 5 1).prop.1
    have hae : Nat.ModEq e a 1 := by
      simpa [a] using (Nat.chineseRemainder h8e 5 1).prop.2
    have ha8cop : Nat.Coprime a 8 := by
      rw [Nat.coprime_iff_gcd_eq_one, ha8.gcd_eq]
      decide
    have haecop : Nat.Coprime a e := by
      rw [Nat.coprime_iff_gcd_eq_one, hae.gcd_eq]
      simp
    have ha4mod : Nat.ModEq 4 a 1 :=
      (ha8.of_dvd (by omega : 4 ∣ 8)).trans (by decide)
    have ha4 : a % 4 = 1 := by
      exact Nat.mod_eq_of_modEq ha4mod (by norm_num)
    have haOdd : Odd a := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one ha4)
    have hepos : 0 < e := by
      by_contra h
      have he0 : e = 0 := Nat.eq_zero_of_not_pos h
      rw [he0, Nat.mul_zero] at hdecomp
      omega
    have ha4eEq : a % (4 * e) = 1 := by
      have hmod : Nat.ModEq (4 * e) a 1 :=
        (Nat.modEq_and_modEq_iff_modEq_mul
          (Nat.Coprime.pow_left 2 hqecop)).mp ⟨ha4mod, hae⟩
      exact Nat.mod_eq_of_modEq hmod (by omega)
    have haje : jacobiSym (e : ℤ) a = 1 := by
      calc
        jacobiSym (e : ℤ) a = jacobiSym (e : ℤ) (a % (4 * e)) :=
          jacobiSym.mod_right' e haOdd
        _ = jacobiSym (e : ℤ) 1 := by rw [ha4eEq]
        _ = 1 := jacobiSym.one_right _
    have haj2 : jacobiSym (2 : ℤ) a = -1 := by
      rw [jacobiSym.at_two haOdd, ZMod.χ₈_nat_eq_if_mod_eight]
      have ha8' : a % 8 = 5 := by
        exact Nat.mod_eq_of_modEq ha8 (by norm_num)
      simp [ha8', Nat.odd_iff.mp haOdd]
    refine ⟨a, ?_, haOdd, ?_⟩
    · rw [← hdecomp]
      convert Nat.Coprime.mul_right ha8cop haecop using 1 <;> omega
    · have haj2' : jacobiSym ((2 : ℕ) : ℤ) a = -1 := by
        norm_num
        exact haj2
      rw [← hdecomp, Nat.cast_mul, jacobiSym.mul_left, haj2', haje]
      norm_num
  · have hqOdd : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2)
    have hq4 : Nat.Coprime q 4 := by
      simpa using hqOdd.coprime_two_right.pow_right 2
    have hq4e : Nat.Coprime q (4 * e) := Nat.Coprime.mul_right hq4 hqecop
    letI : Fact q.Prime := ⟨hq⟩
    have hchar : ringChar (ZMod q) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hq2
    obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one' (F := ZMod q) hchar
    let b : ℕ := u.val.val
    let a : ℕ := (Nat.chineseRemainder hq4e b 1).1
    have haq : Nat.ModEq q a b := by
      simpa [a] using (Nat.chineseRemainder hq4e b 1).prop.1
    have ha4e : Nat.ModEq (4 * e) a 1 := by
      simpa [a] using (Nat.chineseRemainder hq4e b 1).prop.2
    have hacopq : Nat.Coprime a q := by
      rw [Nat.coprime_iff_gcd_eq_one, haq.gcd_eq]
      exact ZMod.val_coe_unit_coprime u
    have hacop4e : Nat.Coprime a (4 * e) := by
      rw [Nat.coprime_iff_gcd_eq_one, ha4e.gcd_eq]
      simp
    have ha4mod : Nat.ModEq 4 a 1 := ha4e.of_dvd (dvd_mul_right 4 e)
    have ha4 : a % 4 = 1 := by
      exact Nat.mod_eq_of_modEq ha4mod (by norm_num)
    have haOdd : Odd a := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one ha4)
    have hepos : 0 < e := by
      by_contra h
      have he0 : e = 0 := Nat.eq_zero_of_not_pos h
      rw [he0, Nat.mul_zero] at hdecomp
      omega
    have haje : jacobiSym (e : ℤ) a = 1 := by
      calc
        jacobiSym (e : ℤ) a = jacobiSym (e : ℤ) (a % (4 * e)) :=
          jacobiSym.mod_right' e haOdd
        _ = 1 := by
          have h : a % (4 * e) = 1 :=
            Nat.mod_eq_of_modEq ha4e (by omega)
          rw [h]
          simp
    have hajq : jacobiSym (q : ℤ) a = -1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hqOdd ha4]
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      have hcast : (b : ZMod q) = u.val := by
        simp [b]
      have habcast : (a : ZMod q) = (b : ZMod q) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact haq
      have habcast' : ((a : ℤ) : ZMod q) = u.val := by
        simpa only [Int.cast_natCast] using habcast.trans hcast
      rw [legendreSym]
      rw [habcast']
      exact hu
    refine ⟨a, ?_, haOdd, ?_⟩
    · rw [← hdecomp]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Nat.Coprime.mul_right hacopq hacop4e)
    · rw [← hdecomp, Nat.cast_mul, jacobiSym.mul_left, hajq, haje]
      norm_num

/-- Every positive nonsquare numerator has a prime test value, coprime to the
full period `4k`, on which its Jacobi character is negative. -/
lemma exists_coprime_jacobiSym_eq_neg_one_of_not_isSquare
    {k : ℕ} (hk : 0 < k) (hksq : ¬ IsSquare k) :
    ∃ a : ℕ, Nat.Coprime a (4 * k) ∧ Odd a ∧ jacobiSym (k : ℤ) a = -1 := by
  let d := Erdos888.squarefreePart k
  let s := Erdos888.squarePartRoot k
  have hdpos : 0 < d := Erdos888.squarefreePart_pos hk
  have hdne : d ≠ 1 := by
    intro hd1
    apply hksq
    refine ⟨s, ?_⟩
    change k = s * s
    simpa [d, s, hd1, pow_two] using
      (Erdos888.squarePart_decomposition k).symm
  have hd1 : 1 < d := by omega
  obtain ⟨b, hb4d, hbOdd, hjb⟩ :=
    exists_coprime_jacobiSym_eq_neg_one_of_squarefree
      (Erdos888.squarefreePart_squarefree k) hd1
  have h4d : 4 * d ≠ 0 := by positivity
  obtain ⟨a, hka, haPrime, hab⟩ :=
    Nat.forall_exists_prime_gt_and_modEq k h4d hb4d
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  have ha2 : 2 < a := hk2.trans_lt hka
  have haOdd : Odd a :=
    Nat.odd_iff.mpr (haPrime.eq_two_or_odd.resolve_left (by omega))
  have hacop4 : Nat.Coprime a 4 := by
    simpa using haOdd.coprime_two_right.pow_right 2
  have hacopk : Nat.Coprime a k :=
    haPrime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk hka)
  have hacop4k : Nat.Coprime a (4 * k) :=
    Nat.Coprime.mul_right hacop4 hacopk
  have hjd : jacobiSym (d : ℤ) a = -1 := by
    calc
      jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) (a % (4 * d)) :=
        jacobiSym.mod_right' d haOdd
      _ = jacobiSym (d : ℤ) (b % (4 * d)) := by rw [hab]
      _ = jacobiSym (d : ℤ) b :=
        (jacobiSym.mod_right' d hbOdd).symm
      _ = -1 := by simpa [d] using hjb
  have hjd' : jacobiSym (d : ℤ) a = -1 := by
    simpa [d] using hjd
  have hscop : Nat.Coprime s a := by
    apply Nat.Coprime.symm
    apply hacopk.coprime_dvd_right
    rw [← Erdos888.squarePart_decomposition k]
    refine ⟨s * d, ?_⟩
    simp [s, d, pow_two, Nat.mul_assoc]
  have hsgcd : Int.gcd (s : ℤ) a = 1 := by
    simpa [Int.gcd_eq_natAbs] using hscop.gcd_eq_one
  refine ⟨a, hacop4k, haOdd, ?_⟩
  rw [← Erdos888.squarePart_decomposition k, Nat.cast_mul,
    Nat.cast_pow, jacobiSym.mul_left, jacobiSym.sq_one' hsgcd, hjd',
    one_mul]

/-- The complex Dirichlet character associated to `J(k|·)` at its natural
period `4k`. -/
noncomputable def attachedQuadraticDirichletCharacter (k : ℕ) (hk : 0 < k) :
    DirichletCharacter ℂ (4 * k) :=
  @QuadraticCharacterMod.toDirichletCharacterComplex (4 * k)
    ⟨by positivity⟩
    (attachedQuadraticCharacter k (4 * k) (dvd_refl (4 * k)))

/-- The complex Dirichlet character attached to a positive nonsquare is
nonprincipal. -/
lemma attachedQuadraticDirichletCharacter_ne_one {k : ℕ} (hk : 0 < k)
    (hksq : ¬ IsSquare k) : attachedQuadraticDirichletCharacter k hk ≠ 1 := by
  letI : NeZero (4 * k) := ⟨by positivity⟩
  obtain ⟨a, hacop, _haOdd, hja⟩ :=
    exists_coprime_jacobiSym_eq_neg_one_of_not_isSquare hk hksq
  intro hprincipal
  have happ := congrArg (fun χ : DirichletCharacter ℂ (4 * k) ↦
    χ (a : ZMod (4 * k))) hprincipal
  rw [attachedQuadraticDirichletCharacter,
    QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat,
    attachedQuadraticCharacter_apply_coprime (dvd_refl (4 * k)) hacop,
    hja] at happ
  have haunit : IsUnit (a : ZMod (4 * k)) :=
    (ZMod.isUnit_iff_coprime a (4 * k)).2 hacop
  rw [MulChar.one_apply haunit] at happ
  norm_num at happ

/-- Extend `J(k|m)` by zero on the even denominators.  For positive `k`
this is exactly the integer-valued attached character of period `4k`. -/
def quadraticDenominatorTerm (k m : ℕ) : ℤ :=
  if Odd m then jacobiSym (k : ℤ) m else 0

lemma quadraticDenominatorTerm_eq_attached {k m : ℕ} (hk : 0 < k) :
    quadraticDenominatorTerm k m =
      attachedQuadraticCharacter k (4 * k) (dvd_refl (4 * k)) m := by
  by_cases hmOdd : Odd m
  · by_cases hcop : Nat.Coprime m (4 * k)
    · simp [quadraticDenominatorTerm, attachedQuadraticCharacter, hmOdd, hcop]
    · have hcop4 : Nat.Coprime m 4 := by
        simpa using hmOdd.coprime_two_right.pow_right 2
      have hnotk : ¬ Nat.Coprime m k := by
        intro hmk
        exact hcop (Nat.Coprime.mul_right hcop4 hmk)
      have hmgcd : Int.gcd (k : ℤ) m ≠ 1 := by
        simpa [Int.gcd_eq_natAbs, Nat.gcd_comm,
          Nat.coprime_iff_gcd_eq_one] using hnotk
      have hm0 : m ≠ 0 := by
        rintro rfl
        simpa using hmOdd
      have hjzero : jacobiSym (k : ℤ) m = 0 :=
        jacobiSym.eq_zero_iff.mpr ⟨hm0, hmgcd⟩
      simp [quadraticDenominatorTerm, attachedQuadraticCharacter,
        hmOdd, hcop, hjzero]
  · have hnotcop : ¬ Nat.Coprime m (4 * k) := by
      intro hcop
      have hm4 := hcop.coprime_dvd_right (dvd_mul_right 4 k)
      have hm2 := hm4.coprime_dvd_right (by omega : 2 ∣ 4)
      exact hmOdd ((Nat.coprime_two_right).mp hm2)
    simp [quadraticDenominatorTerm, attachedQuadraticCharacter, hmOdd, hnotcop]

private lemma sum_range_dirichletCharacter (M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) :
    (∑ n ∈ Finset.range M, χ (n : ZMod M)) = ∑ a : ZMod M, χ a := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv M).toEquiv
  intro n
  have hn : (n.val : ZMod M) = (ZMod.finEquiv M).toEquiv n := by
    cases M with
    | zero => exact Fin.elim0 n
    | succ M =>
        simp only [ZMod.finEquiv, RingEquiv.toEquiv_eq_coe]
        apply Fin.ext
        change n.val % (M + 1) = n.val
        exact Nat.mod_eq_of_lt n.isLt
  exact congrArg χ hn

/-- A nonsquare quadratic denominator character has zero sum over its exact
period. -/
lemma sum_quadraticDenominatorTerm_period_eq_zero {k : ℕ} (hk : 0 < k)
    (hksq : ¬ IsSquare k) :
    ∑ m ∈ Finset.range (4 * k), quadraticDenominatorTerm k m = 0 := by
  letI : NeZero (4 * k) := ⟨by positivity⟩
  apply Int.cast_injective (α := ℂ)
  push_cast
  calc
    (∑ m ∈ Finset.range (4 * k),
        (quadraticDenominatorTerm k m : ℂ)) =
        ∑ m ∈ Finset.range (4 * k),
          attachedQuadraticDirichletCharacter k hk (m : ZMod (4 * k)) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [attachedQuadraticDirichletCharacter,
        QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat]
      exact_mod_cast quadraticDenominatorTerm_eq_attached hk
    _ = ∑ a : ZMod (4 * k), attachedQuadraticDirichletCharacter k hk a :=
      sum_range_dirichletCharacter (4 * k) _
    _ = 0 := MulChar.sum_eq_zero_of_ne_one
      (attachedQuadraticDirichletCharacter_ne_one hk hksq)

lemma quadraticDenominatorTerm_add_period (k t n : ℕ) (hk : 0 < k) :
    quadraticDenominatorTerm k (t * (4 * k) + n) =
      quadraticDenominatorTerm k n := by
  rw [quadraticDenominatorTerm_eq_attached hk,
    quadraticDenominatorTerm_eq_attached hk]
  apply (attachedQuadraticCharacter k (4 * k) (dvd_refl (4 * k))).periodic
  simp [Nat.ModEq]

lemma sum_quadraticDenominatorTerm_mul_period (k t : ℕ) (hk : 0 < k) :
    (∑ m ∈ Finset.range (t * (4 * k)), quadraticDenominatorTerm k m) =
      t • ∑ m ∈ Finset.range (4 * k), quadraticDenominatorTerm k m := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, add_nsmul, one_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      exact quadraticDenominatorTerm_add_period k t n hk

lemma quadraticDenominatorTerm_le_one (k m : ℕ) :
    quadraticDenominatorTerm k m ≤ 1 := by
  by_cases hm : Odd m
  · simp only [quadraticDenominatorTerm, if_pos hm]
    rcases jacobiSym.trichotomy (a := (k : ℤ)) (b := m) with h | h | h <;>
      omega
  · simp [quadraticDenominatorTerm, hm]

/-- The incomplete odd-denominator character sum is bounded by one period.
This deliberately elementary `4k` bound is sufficient in Elliott's medium
range because `k` is a bounded tuple product. -/
lemma sum_quadraticDenominatorTerm_lt_period {k : ℕ} (hk : 0 < k)
    (hksq : ¬ IsSquare k) (x : ℕ) :
    (∑ m ∈ Finset.range x, quadraticDenominatorTerm k m : ℤ) < 4 * k := by
  nth_rewrite 1 [show x = (x / (4 * k)) * (4 * k) + x % (4 * k) by
    rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]]
  rw [Finset.sum_range_add]
  have hblock :
      (∑ m ∈ Finset.range (x / (4 * k) * (4 * k)),
          quadraticDenominatorTerm k m) = 0 := by
    rw [sum_quadraticDenominatorTerm_mul_period k _ hk,
      sum_quadraticDenominatorTerm_period_eq_zero hk hksq, nsmul_zero]
  rw [hblock, zero_add]
  calc
    (∑ m ∈ Finset.range (x % (4 * k)),
        quadraticDenominatorTerm k (x / (4 * k) * (4 * k) + m)) =
        ∑ m ∈ Finset.range (x % (4 * k)), quadraticDenominatorTerm k m := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact quadraticDenominatorTerm_add_period k (x / (4 * k)) m hk
    _ ≤ ∑ _m ∈ Finset.range (x % (4 * k)), (1 : ℤ) := by
      exact Finset.sum_le_sum fun m _hm ↦ quadraticDenominatorTerm_le_one k m
    _ < 4 * k := by
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.mod_lt x (by positivity : 0 < 4 * k)

/-- The partial sum `∑_{1 ≤ n ≤ N} (n / p)`, using the Jacobi symbol so that
the modulus can remain an ordinary natural-number variable.  On prime moduli
this is the Legendre symbol by `legendreSym.to_jacobiSym`. -/
def legendrePartialSum (p N : ℕ) : ℤ :=
  ∑ n ∈ range N, jacobiSym (n + 1 : ℤ) p

/-- The defining property of an admissible eventual-time threshold. -/
def IsEventualThreshold (ε : ℝ) (p m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ N : ℕ, m ≤ N → (legendrePartialSum p N : ℝ) < ε * (N : ℝ)

/-- The bounded version of the threshold property, used to approximate the
eventual threshold by data from the first `M` character sums. -/
def IsTruncatedThreshold (ε : ℝ) (p M m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ N : ℕ, m ≤ N → N ≤ M →
    (legendrePartialSum p N : ℝ) < ε * (N : ℝ)

lemma exists_isTruncatedThreshold (ε : ℝ) (p M : ℕ) :
    ∃ m : ℕ, IsTruncatedThreshold ε p M m := by
  refine ⟨M + 1, by omega, ?_⟩
  omega

/-- The least eventual-time threshold, with value `0` only in the irrelevant
case in which the defining set is empty. -/
noncomputable def eventualThreshold (ε : ℝ) (p : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ m : ℕ, IsEventualThreshold ε p m then Nat.find h else 0

/-- The least threshold which works through time `M`.  The witness `M + 1`
always works, so unlike `eventualThreshold` this definition has no fallback
case. -/
noncomputable def truncatedThreshold (ε : ℝ) (p M : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_isTruncatedThreshold ε p M)

/-- The odd primes strictly below `x`. -/
def oddPrimesBelow (x : ℕ) : Finset ℕ :=
  (range x).filter fun p => p.Prime ∧ Odd p

/-- The sum in Erdős Problem 981, interpreted as a real-valued function. -/
noncomputable def thresholdPrimeSum (ε : ℝ) (x : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesBelow x, (eventualThreshold ε p : ℝ)

/-! ## The finite random completely multiplicative model -/

/-- The primes which can divide a positive integer at most `M`. -/
def modelPrimes (M : ℕ) : Finset ℕ :=
  (range (M + 1)).filter Nat.Prime

/-- A choice of one random bit for every prime at most `M`. -/
def SignPattern (M : ℕ) :=
  {q // q ∈ modelPrimes M} → Bool

instance (M : ℕ) : Fintype (SignPattern M) := by
  dsimp [SignPattern]
  infer_instance

instance (M : ℕ) : DecidableEq (SignPattern M) := by
  dsimp [SignPattern]
  infer_instance

/-- Interpret a bit as one of the two integer signs. -/
def boolSign (b : Bool) : ℤ :=
  if b then -1 else 1

/-- The completely multiplicative sign associated with a finite pattern.
For `n ≤ M`, every prime occurring in `n` is represented among the factors. -/
def randomMul (M : ℕ) (ω : SignPattern M) (n : ℕ) : ℤ :=
  ∏ q : {q // q ∈ modelPrimes M}, boolSign (ω q) ^ n.factorization q.1

/-- The corresponding random partial sum through `N`. -/
def randomPartialSum (M : ℕ) (ω : SignPattern M) (N : ℕ) : ℤ :=
  ∑ n ∈ range N, randomMul M ω (n + 1)

/-- The bounded threshold property in the random model. -/
def IsRandomTruncatedThreshold (ε : ℝ) (M : ℕ) (ω : SignPattern M) (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ N : ℕ, m ≤ N → N ≤ M →
    (randomPartialSum M ω N : ℝ) < ε * (N : ℝ)

lemma exists_isRandomTruncatedThreshold (ε : ℝ) (M : ℕ) (ω : SignPattern M) :
    ∃ m : ℕ, IsRandomTruncatedThreshold ε M ω m := by
  refine ⟨M + 1, by omega, ?_⟩
  omega

/-- The least bounded threshold in one realization of the random model. -/
noncomputable def randomTruncatedThreshold
    (ε : ℝ) (M : ℕ) (ω : SignPattern M) : ℕ := by
  classical
  exact Nat.find (exists_isRandomTruncatedThreshold ε M ω)

/-- The finite-model mean of the truncated threshold. -/
noncomputable def finiteModelConstant (ε : ℝ) (M : ℕ) : ℝ :=
  (∑ ω : SignPattern M, (randomTruncatedThreshold ε M ω : ℝ)) /
    Fintype.card (SignPattern M)

@[simp] lemma boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by
  cases b <;> simp [boolSign]

@[simp] lemma randomMul_one (M : ℕ) (ω : SignPattern M) :
    randomMul M ω 1 = 1 := by
  simp [randomMul]

lemma randomMul_mul (M : ℕ) (ω : SignPattern M) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    randomMul M ω (a * b) = randomMul M ω a * randomMul M ω b := by
  simp only [randomMul, Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add,
    Finset.prod_mul_distrib]

lemma sum_boolSign_pow_of_even {e : ℕ} (he : Even e) :
    ∑ b : Bool, boolSign b ^ e = 2 := by
  simp [boolSign, he.neg_one_pow]

lemma sum_boolSign_pow_of_odd {e : ℕ} (he : Odd e) :
    ∑ b : Bool, boolSign b ^ e = 0 := by
  simp [boolSign, he.neg_one_pow]

lemma sum_boolSign_pow (e : ℕ) :
    ∑ b : Bool, boolSign b ^ e = if Even e then 2 else 0 := by
  rcases e.even_or_odd with he | he
  · rw [if_pos he, sum_boolSign_pow_of_even he]
  · rw [if_neg (Nat.not_even_iff_odd.mpr he), sum_boolSign_pow_of_odd he]

lemma sum_randomMul (M k : ℕ) :
    ∑ ω : SignPattern M, randomMul M ω k =
      if (∀ q : {q // q ∈ modelPrimes M}, Even (k.factorization q.1))
      then (2 : ℤ) ^ (modelPrimes M).card else 0 := by
  classical
  change (∑ ω : ({q // q ∈ modelPrimes M} → Bool),
      ∏ q : {q // q ∈ modelPrimes M}, boolSign (ω q) ^ k.factorization q.1) = _
  calc
    (∑ ω : ({q // q ∈ modelPrimes M} → Bool),
        ∏ q : {q // q ∈ modelPrimes M}, boolSign (ω q) ^ k.factorization q.1) =
        ∏ q : {q // q ∈ modelPrimes M},
          ∑ b : Bool, boolSign b ^ k.factorization q.1 :=
      (Fintype.prod_sum
        (fun q : {q // q ∈ modelPrimes M} =>
          fun b : Bool => boolSign b ^ k.factorization q.1)).symm
    _ = _ := by
      simp only [sum_boolSign_pow]
      by_cases h : ∀ q : {q // q ∈ modelPrimes M}, Even (k.factorization q.1)
      · simp [h]
      · simp only [not_forall] at h
        obtain ⟨q, hq⟩ := h
        have hsubtype : ¬∀ a : {q // q ∈ modelPrimes M},
            Even (k.factorization a.1) := by
          intro hall
          exact hq (hall q)
        rw [if_neg hsubtype]
        exact Finset.prod_eq_zero (s := Finset.univ) (i := q)
          (by simp) (by simp [hq])

@[simp] lemma card_signPattern (M : ℕ) :
    Fintype.card (SignPattern M) = 2 ^ (modelPrimes M).card := by
  simp [SignPattern]

lemma mem_modelPrimes {M q : ℕ} :
    q ∈ modelPrimes M ↔ q.Prime ∧ q ≤ M := by
  simp [modelPrimes, and_comm]

lemma isSquare_iff_even_factorization (k : ℕ) :
    IsSquare k ↔ ∀ q : ℕ, q.Prime → Even (k.factorization q) := by
  constructor
  · rintro ⟨a, rfl⟩ q hq
    by_cases ha : a = 0
    · subst a
      simp
    rw [Nat.factorization_mul ha ha, Finsupp.add_apply]
    exact Even.add_self _
  · intro h
    by_cases hk : k = 0
    · subst k
      exact ⟨0, by simp⟩
    let f : ℕ →₀ ℕ :=
      Finsupp.mapRange (fun e : ℕ => e / 2) (by simp) k.factorization
    have hf : ∀ q ∈ f.support, q.Prime := by
      intro q hq
      exact Nat.prime_of_mem_primeFactors
        (Finsupp.support_mapRange hq)
    let aPos : ℕ+ := Nat.factorizationEquiv.symm ⟨f, hf⟩
    let a : ℕ := aPos.1
    have ha : a ≠ 0 := aPos.2.ne'
    have hfactor : a.factorization = f := by
      have happly := Nat.factorizationEquiv.apply_symm_apply ⟨f, hf⟩
      exact congrArg Subtype.val happly
    refine ⟨a, ?_⟩
    symm
    apply Nat.factorization_inj (mul_ne_zero ha ha) hk
    rw [Nat.factorization_mul ha ha, hfactor]
    ext q
    simp only [Finsupp.add_apply, f, Finsupp.mapRange_apply]
    by_cases hq : q.Prime
    · simpa [two_mul] using Nat.two_mul_div_two_of_even (h q hq)
    · simp [Nat.factorization_eq_zero_of_not_prime k hq]

/-- Every prime divisor of `k` is represented in the model at level `M`. -/
def PrimeFactorsBounded (k M : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ k → q ≤ M

lemma model_even_iff_isSquare {M k : ℕ} (hbound : PrimeFactorsBounded k M) :
    (∀ q : {q // q ∈ modelPrimes M}, Even (k.factorization q.1)) ↔ IsSquare k := by
  rw [isSquare_iff_even_factorization]
  constructor
  · intro h q hq
    by_cases hqk : q ∣ k
    · exact h ⟨q, mem_modelPrimes.mpr ⟨hq, hbound q hq hqk⟩⟩
    · rw [Nat.factorization_eq_zero_of_not_dvd hqk]
      simp
  · intro h q
    exact h q.1 (mem_modelPrimes.mp q.2).1

lemma sum_randomMul_eq_indicator_square {M k : ℕ}
    (hbound : PrimeFactorsBounded k M) :
    ∑ ω : SignPattern M, randomMul M ω k =
      if IsSquare k then (Fintype.card (SignPattern M) : ℤ) else 0 := by
  rw [sum_randomMul]
  by_cases hsquare : IsSquare k
  · have heven := (model_even_iff_isSquare hbound).mpr hsquare
    rw [if_pos hsquare, if_pos heven]
    simp
  · have hnotEven : ¬∀ q : {q // q ∈ modelPrimes M},
        Even (k.factorization q.1) := by
      exact fun h => hsquare ((model_even_iff_isSquare hbound).mp h)
    rw [if_neg hsquare, if_neg hnotEven]

lemma primeFactorsBounded_finset_prod {ι : Type*} [DecidableEq ι]
    {M : ℕ} {s : Finset ι} {g : ι → ℕ}
    (hgpos : ∀ i ∈ s, 0 < g i) (hgle : ∀ i ∈ s, g i ≤ M) :
    PrimeFactorsBounded (∏ i ∈ s, g i) M := by
  intro q hq hqdvd
  obtain ⟨i, hi, hqidvd⟩ := (_root_.Prime.dvd_finsetProd_iff hq.prime g).mp hqdvd
  exact (Nat.le_of_dvd (hgpos i hi) hqidvd).trans (hgle i hi)

lemma randomMul_finset_prod {ι : Type*} [DecidableEq ι]
    (M : ℕ) (ω : SignPattern M) (s : Finset ι) (g : ι → ℕ)
    (hg : ∀ i ∈ s, g i ≠ 0) :
    randomMul M ω (∏ i ∈ s, g i) = ∏ i ∈ s, randomMul M ω (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self _ _)
      have hgs : ∀ i ∈ s, g i ≠ 0 := fun i hi =>
        hg i (Finset.mem_insert_of_mem hi)
      have hprod : ∏ i ∈ s, g i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr hgs
      rw [Finset.prod_insert ha, randomMul_mul M ω hga hprod,
        ih hgs, Finset.prod_insert ha]

lemma sum_randomMul_finset_product {ι : Type*} [DecidableEq ι]
    {M : ℕ} {s : Finset ι} {g : ι → ℕ}
    (hgpos : ∀ i ∈ s, 0 < g i) (hgle : ∀ i ∈ s, g i ≤ M) :
    ∑ ω : SignPattern M, ∏ i ∈ s, randomMul M ω (g i) =
      if IsSquare (∏ i ∈ s, g i)
      then (Fintype.card (SignPattern M) : ℤ) else 0 := by
  calc
    (∑ ω : SignPattern M, ∏ i ∈ s, randomMul M ω (g i)) =
        ∑ ω : SignPattern M, randomMul M ω (∏ i ∈ s, g i) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      symm
      apply randomMul_finset_prod
      exact fun i hi => (hgpos i hi).ne'
    _ = _ := sum_randomMul_eq_indicator_square
      (primeFactorsBounded_finset_prod hgpos hgle)

/-! ## Square-product tuples -/

open Erdos888

/-- Two positive integers have square product exactly when their canonical
squarefree parts agree. -/
lemma isSquare_mul_iff_squarefreePart_eq {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    IsSquare (u * v) ↔ squarefreePart u = squarefreePart v := by
  have hru : squarePartRoot u ≠ 0 := (squarePartRoot_pos hu).ne'
  have hrv : squarePartRoot v ≠ 0 := (squarePartRoot_pos hv).ne'
  have hsu : squarefreePart u ≠ 0 := (squarefreePart_pos hu).ne'
  have hsv : squarefreePart v ≠ 0 := (squarefreePart_pos hv).ne'
  constructor
  · intro hsquare
    apply Nat.eq_of_factorization_eq hsu hsv
    intro q
    have hufac : u.factorization q =
        2 * (squarePartRoot u).factorization q +
          (squarefreePart u).factorization q := by
      calc
        u.factorization q =
            (squarePartRoot u ^ 2 * squarefreePart u).factorization q := by
          rw [squarePart_decomposition u]
        _ = _ := by
          rw [Nat.factorization_mul (pow_ne_zero 2 hru) hsu,
            Nat.factorization_pow]
          simp [Finsupp.add_apply]
    have hvfac : v.factorization q =
        2 * (squarePartRoot v).factorization q +
          (squarefreePart v).factorization q := by
      calc
        v.factorization q =
            (squarePartRoot v ^ 2 * squarefreePart v).factorization q := by
          rw [squarePart_decomposition v]
        _ = _ := by
          rw [Nat.factorization_mul (pow_ne_zero 2 hrv) hsv,
            Nat.factorization_pow]
          simp [Finsupp.add_apply]
    by_cases hq : q.Prime
    · have hevenUV : Even ((u * v).factorization q) :=
        (isSquare_iff_even_factorization (u * v)).mp hsquare q hq
      have heven : Even
          ((squarefreePart u).factorization q +
            (squarefreePart v).factorization q) := by
        rw [Nat.factorization_mul hu.ne' hv.ne', Finsupp.add_apply,
          hufac, hvfac] at hevenUV
        rcases hevenUV with ⟨e, he⟩
        refine ⟨e - (squarePartRoot u).factorization q -
          (squarePartRoot v).factorization q, ?_⟩
        omega
      have hule : (squarefreePart u).factorization q ≤ 1 :=
        (squarefreePart_squarefree u).natFactorization_le_one q
      have hvle : (squarefreePart v).factorization q ≤ 1 :=
        (squarefreePart_squarefree v).natFactorization_le_one q
      rcases heven with ⟨e, he⟩
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime (squarefreePart u) hq,
        Nat.factorization_eq_zero_of_not_prime (squarefreePart v) hq]
  · intro heq
    refine ⟨squarePartRoot u * squarePartRoot v * squarefreePart u, ?_⟩
    calc
      u * v =
          (squarePartRoot u ^ 2 * squarefreePart u) *
            (squarePartRoot v ^ 2 * squarefreePart v) := by
        rw [squarePart_decomposition u, squarePart_decomposition v]
      _ = (squarePartRoot u * squarePartRoot v * squarefreePart u) *
          (squarePartRoot u * squarePartRoot v * squarefreePart u) := by
        rw [← heq]
        ring

/-- The three-dimensional positive box used to expand a sixth moment into
two triples. -/
def tripleBox (N : ℕ) : Finset (Fin 3 → ℕ) :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc 1 N

/-- Product of the three entries of a point in `tripleBox`. -/
def tripleProduct (a : Fin 3 → ℕ) : ℕ :=
  ∏ i, a i

/-- The fiber of the triple-product map over `u`. -/
def tripleProductFiber (N u : ℕ) : Finset (Fin 3 → ℕ) :=
  (tripleBox N).filter fun a => tripleProduct a = u

@[simp] lemma mem_tripleBox {N : ℕ} {a : Fin 3 → ℕ} :
    a ∈ tripleBox N ↔ ∀ i, 1 ≤ a i ∧ a i ≤ N := by
  simp [tripleBox, Fintype.mem_piFinset]

@[simp] lemma mem_tripleProductFiber {N u : ℕ} {a : Fin 3 → ℕ} :
    a ∈ tripleProductFiber N u ↔
      (∀ i, 1 ≤ a i ∧ a i ≤ N) ∧ tripleProduct a = u := by
  simp [tripleProductFiber]

lemma tripleProduct_eq (a : Fin 3 → ℕ) :
    tripleProduct a = a 0 * a 1 * a 2 := by
  simp [tripleProduct, Fin.prod_univ_succ, mul_assoc]

lemma tripleProduct_pos {N : ℕ} {a : Fin 3 → ℕ} (ha : a ∈ tripleBox N) :
    0 < tripleProduct a := by
  rw [tripleProduct_eq]
  exact mul_pos (mul_pos (mem_tripleBox.mp ha 0).1
    (mem_tripleBox.mp ha 1).1) (mem_tripleBox.mp ha 2).1

lemma tripleProduct_le_cube {N : ℕ} {a : Fin 3 → ℕ} (ha : a ∈ tripleBox N) :
    tripleProduct a ≤ N ^ 3 := by
  rw [tripleProduct_eq, pow_succ, pow_two]
  exact Nat.mul_le_mul (Nat.mul_le_mul (mem_tripleBox.mp ha 0).2
    (mem_tripleBox.mp ha 1).2) (mem_tripleBox.mp ha 2).2

lemma tripleProductFiber_card_le_divisors_sq {N u : ℕ} (hu : 0 < u) :
    (tripleProductFiber N u).card ≤ u.divisors.card ^ 2 := by
  classical
  let f : (Fin 3 → ℕ) → ℕ × ℕ := fun a => (a 0, a 1)
  have hmap : Set.MapsTo f (tripleProductFiber N u)
      (u.divisors.product u.divisors) := by
    intro a ha
    have hprod := (mem_tripleProductFiber.mp ha).2
    have ha0 : a 0 ∣ u := by
      rw [← hprod, tripleProduct_eq]
      exact ⟨a 1 * a 2, by simp [mul_assoc]⟩
    have ha1 : a 1 ∣ u := by
      rw [← hprod, tripleProduct_eq]
      exact ⟨a 0 * a 2, by ac_rfl⟩
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨ha0, hu.ne'⟩,
        Nat.mem_divisors.mpr ⟨ha1, hu.ne'⟩⟩
  have hinj : Set.InjOn f (tripleProductFiber N u) := by
    intro a ha b hb hab
    have h0 : a 0 = b 0 := congrArg Prod.fst hab
    have h1 : a 1 = b 1 := congrArg Prod.snd hab
    have hpa := (mem_tripleProductFiber.mp ha).2
    have hpb := (mem_tripleProductFiber.mp hb).2
    have h2 : a 2 = b 2 := by
      have hb0 : 0 < b 0 := ((mem_tripleProductFiber.mp hb).1 0).1
      have hb1 : 0 < b 1 := ((mem_tripleProductFiber.mp hb).1 1).1
      have hpos : 0 < b 0 * b 1 := mul_pos hb0 hb1
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc
        b 0 * b 1 * a 2 = a 0 * a 1 * a 2 := by rw [h0, h1]
        _ = u := by simpa [tripleProduct_eq] using hpa
        _ = b 0 * b 1 * b 2 := by simpa [tripleProduct_eq] using hpb.symm
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  calc
    (tripleProductFiber N u).card ≤
        (u.divisors.product u.divisors).card :=
      Finset.card_le_card_of_injOn f hmap hinj
    _ = u.divisors.card ^ 2 := by simp [pow_two]

/-- In a bounded positive interval, a fixed squarefree part occurs at most
`sqrt X` times: its canonical square root determines the integer. -/
lemma card_squarefreePartFiber_Icc_le_sqrt (X s : ℕ) :
    (squarefreePartFiber (Finset.Icc 1 X) s).card ≤ Nat.sqrt X := by
  classical
  have hmap : Set.MapsTo squarePartRoot
      (squarefreePartFiber (Finset.Icc 1 X) s)
      (Finset.Icc 1 (Nat.sqrt X)) := by
    intro n hn
    have hnIcc := (mem_squarefreePartFiber.mp hn).1
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnIcc).1
    have hnX : n ≤ X := (Finset.mem_Icc.mp hnIcc).2
    exact Finset.mem_Icc.mpr
      ⟨squarePartRoot_pos hnpos,
        Nat.le_sqrt'.mpr ((squarePart_sq_le hnpos).trans hnX)⟩
  calc
    (squarefreePartFiber (Finset.Icc 1 X) s).card ≤
        (Finset.Icc 1 (Nat.sqrt X)).card :=
      Finset.card_le_card_of_injOn squarePartRoot hmap
        (squarePartRoot_injOn_squarefreePartFiber _ _)
    _ ≤ Nat.sqrt X := by simp

/-- There are at most `X * sqrt X` ordered positive pairs up to `X` whose
product is a square.  This deliberately coarse bound is already summable
after the sixth-moment normalization. -/
lemma squareProductPairs_Icc_card_le (X : ℕ) :
    ((Erdos822.collisionPairs (Finset.Icc 1 X) squarefreePart).card : ℕ) ≤
      X * Nat.sqrt X := by
  classical
  rw [Erdos822.collisionPairs_card_eq_collisionEnergy,
    Erdos822.collisionEnergy]
  calc
    (∑ s ∈ (Finset.Icc 1 X).image squarefreePart,
        Erdos822.fiberCount (Finset.Icc 1 X) squarefreePart s ^ 2) ≤
        ∑ s ∈ (Finset.Icc 1 X).image squarefreePart,
          Nat.sqrt X * Erdos822.fiberCount
            (Finset.Icc 1 X) squarefreePart s := by
      apply Finset.sum_le_sum
      intro s hs
      have hfiber : Erdos822.fiberCount (Finset.Icc 1 X) squarefreePart s ≤
          Nat.sqrt X := by
        simpa [Erdos822.fiberCount, squarefreePartFiber] using
          card_squarefreePartFiber_Icc_le_sqrt X s
      simpa [pow_two, mul_comm] using
        Nat.mul_le_mul_right
          (Erdos822.fiberCount (Finset.Icc 1 X) squarefreePart s) hfiber
    _ = Nat.sqrt X * (Finset.Icc 1 X).card := by
      rw [← Finset.mul_sum,
        ← Erdos822.card_eq_sum_fiberCount (Finset.Icc 1 X) squarefreePart]
    _ ≤ X * Nat.sqrt X := by
      simp [mul_comm]

/-- Ordered pairs of triples whose six entries have square product. -/
noncomputable def squareTriplePairs (N : ℕ) :
    Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) :=
  Erdos822.collisionPairs (tripleBox N) (squarefreePart ∘ tripleProduct)

@[simp] lemma mem_squareTriplePairs {N : ℕ}
    {ab : (Fin 3 → ℕ) × (Fin 3 → ℕ)} :
    ab ∈ squareTriplePairs N ↔
      ab.1 ∈ tripleBox N ∧ ab.2 ∈ tripleBox N ∧
        IsSquare (tripleProduct ab.1 * tripleProduct ab.2) := by
  simp only [squareTriplePairs, Erdos822.collisionPairs, Finset.mem_filter,
    Finset.mem_product, Function.comp_apply]
  constructor
  · rintro ⟨⟨ha, hb⟩, heq⟩
    exact ⟨ha, hb,
      (isSquare_mul_iff_squarefreePart_eq (tripleProduct_pos ha)
        (tripleProduct_pos hb)).mpr heq⟩
  · rintro ⟨ha, hb, hsquare⟩
    exact ⟨⟨ha, hb⟩,
      (isSquare_mul_iff_squarefreePart_eq (tripleProduct_pos ha)
        (tripleProduct_pos hb)).mp hsquare⟩

/-! The same construction in arbitrary dimension is used below for the
twelfth and higher moments.  We retain the explicit three-dimensional
version above because it is the literal sixth-moment identity in Elliott's
paper. -/

abbrev tupleBox (r N : ℕ) : Finset (Fin r → ℕ) :=
  Erdos444.orderedTuples (Finset.Icc 1 N) r

abbrev tupleProduct {r : ℕ} (a : Fin r → ℕ) : ℕ :=
  Erdos444.tupleProduct a

def tupleProductFiber (r N u : ℕ) : Finset (Fin r → ℕ) :=
  (tupleBox r N).filter fun a => tupleProduct a = u

lemma tupleProduct_pos_of_mem {r N : ℕ} {a : Fin r → ℕ}
    (ha : a ∈ tupleBox r N) : 0 < tupleProduct a :=
  Erdos444.tupleProduct_pos ha fun m hm => (Finset.mem_Icc.mp hm).1

lemma tupleProduct_le_pow_of_mem {r N : ℕ} {a : Fin r → ℕ}
    (ha : a ∈ tupleBox r N) : tupleProduct a ≤ N ^ r :=
  Erdos444.tupleProduct_le_pow ha fun m hm => (Finset.mem_Icc.mp hm).2

lemma tupleProductFiber_card_le_divisors_pow
    (r N u : ℕ) (hu : 0 < u) :
    (tupleProductFiber r N u).card ≤ u.divisors.card ^ r := by
  classical
  calc
    (tupleProductFiber r N u).card ≤
        Erdos444.representationCount (Finset.Icc 1 N) r u := by
      apply Finset.card_le_card
      intro a ha
      rw [tupleProductFiber, Finset.mem_filter] at ha
      change a ∈ (Erdos444.orderedTuples (Finset.Icc 1 N) r).filter
        (fun a => Erdos444.tupleProduct a ∣ u)
      rw [Finset.mem_filter]
      exact ⟨ha.1, ha.2.symm ▸ dvd_rfl⟩
    _ ≤ Erdos444.divisorCount (Set.univ : Set ℕ) u ^ r :=
      Erdos444.representationCount_le_divisorCount_pow
        (fun _m _hm => Set.mem_univ _) hu.ne'
    _ ≤ u.divisors.card ^ r :=
      Nat.pow_le_pow_left
        (Erdos444.divisorCount_le_card_divisors Set.univ u) r

noncomputable def squareTuplePairs (r N : ℕ) :
    Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  Erdos822.collisionPairs (tupleBox r N) (squarefreePart ∘ tupleProduct)

@[simp] lemma mem_squareTuplePairs {r N : ℕ}
    {ab : (Fin r → ℕ) × (Fin r → ℕ)} :
    ab ∈ squareTuplePairs r N ↔
      ab.1 ∈ tupleBox r N ∧ ab.2 ∈ tupleBox r N ∧
        IsSquare (tupleProduct ab.1 * tupleProduct ab.2) := by
  simp only [squareTuplePairs, Erdos822.collisionPairs, Finset.mem_filter,
    Finset.mem_product, Function.comp_apply]
  constructor
  · rintro ⟨⟨ha, hb⟩, heq⟩
    exact ⟨ha, hb,
      (isSquare_mul_iff_squarefreePart_eq (tupleProduct_pos_of_mem ha)
        (tupleProduct_pos_of_mem hb)).mpr heq⟩
  · rintro ⟨ha, hb, hsquare⟩
    exact ⟨⟨ha, hb⟩,
      (isSquare_mul_iff_squarefreePart_eq (tupleProduct_pos_of_mem ha)
        (tupleProduct_pos_of_mem hb)).mp hsquare⟩

def tuplePairProduct {r : ℕ}
    (ab : (Fin r → ℕ) × (Fin r → ℕ)) : ℕ × ℕ :=
  (tupleProduct ab.1, tupleProduct ab.2)

noncomputable def tuplePairProductFiber (r N u v : ℕ) :
    Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  (squareTuplePairs r N).filter fun ab => tuplePairProduct ab = (u, v)

lemma tuplePairProductFiber_card_le (r N u v : ℕ) :
    (tuplePairProductFiber r N u v).card ≤
      (tupleProductFiber r N u).card * (tupleProductFiber r N v).card := by
  classical
  calc
    (tuplePairProductFiber r N u v).card ≤
        ((tupleProductFiber r N u).product
          (tupleProductFiber r N v)).card := by
      apply Finset.card_le_card
      intro ab hab
      rw [tuplePairProductFiber, Finset.mem_filter] at hab
      have huv : tupleProduct ab.1 = u ∧ tupleProduct ab.2 = v := by
        simpa [tuplePairProduct, Prod.ext_iff] using hab.2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr
            ⟨(mem_squareTuplePairs.mp hab.1).1, huv.1⟩,
          Finset.mem_filter.mpr
            ⟨(mem_squareTuplePairs.mp hab.1).2.1, huv.2⟩⟩
    _ = (tupleProductFiber r N u).card *
        (tupleProductFiber r N v).card := Finset.card_product _ _

lemma tuplePairProduct_mapsTo (r N : ℕ) :
    Set.MapsTo (tuplePairProduct (r := r)) (↑(squareTuplePairs r N) :
      Set ((Fin r → ℕ) × (Fin r → ℕ)))
      (↑(Erdos822.collisionPairs (Finset.Icc 1 (N ^ r)) squarefreePart) :
        Set (ℕ × ℕ)) := by
  intro ab hab
  have h := mem_squareTuplePairs.mp hab
  change tuplePairProduct ab ∈
    Erdos822.collisionPairs (Finset.Icc 1 (N ^ r)) squarefreePart
  rw [Erdos822.collisionPairs, Finset.mem_filter, Finset.mem_product]
  have hapos := tupleProduct_pos_of_mem h.1
  have hbpos := tupleProduct_pos_of_mem h.2.1
  exact ⟨⟨Finset.mem_Icc.mpr
      ⟨hapos, tupleProduct_le_pow_of_mem h.1⟩,
    Finset.mem_Icc.mpr
      ⟨hbpos, tupleProduct_le_pow_of_mem h.2.1⟩⟩,
    (isSquare_mul_iff_squarefreePart_eq hapos hbpos).mp h.2.2⟩

lemma squareTuplePairs_card_eq_sum_fibers (r N : ℕ) :
    (squareTuplePairs r N).card =
      ∑ uv ∈ Erdos822.collisionPairs (Finset.Icc 1 (N ^ r)) squarefreePart,
        (tuplePairProductFiber r N uv.1 uv.2).card := by
  classical
  simpa [tuplePairProductFiber, tuplePairProduct, Prod.ext_iff] using
    (Finset.card_eq_sum_card_fiberwise
      (s := squareTuplePairs r N)
      (t := Erdos822.collisionPairs (Finset.Icc 1 (N ^ r)) squarefreePart)
      (f := tuplePairProduct (r := r)) (tuplePairProduct_mapsTo r N))

/-- Uniform subpower multiplicity bound for square-product tuple pairs.
The exponent `1/4` is intentionally generous: each of the two product
fibers costs one copy of the `N^(1/8)` divisor envelope. -/
lemma exists_squareTuplePairs_card_le (r : ℕ) (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((squareTuplePairs r N).card : ℝ) ≤
        Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 *
          ((N ^ r : ℕ) * Nat.sqrt (N ^ r) : ℕ) := by
  obtain ⟨N₀, hN₀⟩ :=
    Erdos439.PowerDecay.exists_uniform_divisor_power_le_subpower r hr
  refine ⟨max 1 N₀, ?_⟩
  intro N hN
  have hN0 : N₀ ≤ N := (le_max_right 1 N₀).trans hN
  rw [squareTuplePairs_card_eq_sum_fibers]
  calc
    (↑(∑ uv ∈ Erdos822.collisionPairs (Finset.Icc 1 (N ^ r)) squarefreePart,
        (tuplePairProductFiber r N uv.1 uv.2).card) : ℝ) =
        ∑ uv ∈ Erdos822.collisionPairs (Finset.Icc 1 (N ^ r)) squarefreePart,
          ((tuplePairProductFiber r N uv.1 uv.2).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ _uv ∈ Erdos822.collisionPairs
          (Finset.Icc 1 (N ^ r)) squarefreePart,
          Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 := by
      apply Finset.sum_le_sum
      intro uv huv
      have huIcc := (Finset.mem_product.mp
        (Finset.mem_filter.mp huv).1).1
      have hvIcc := (Finset.mem_product.mp
        (Finset.mem_filter.mp huv).1).2
      have hufiber := tupleProductFiber_card_le_divisors_pow r N uv.1
        (Finset.mem_Icc.mp huIcc).1
      have hvfiber := tupleProductFiber_card_le_divisors_pow r N uv.2
        (Finset.mem_Icc.mp hvIcc).1
      have huenv := hN₀ N hN0 uv.1 huIcc
      have hvenv := hN₀ N hN0 uv.2 hvIcc
      calc
        ((tuplePairProductFiber r N uv.1 uv.2).card : ℝ) ≤
            ((tupleProductFiber r N uv.1).card : ℝ) *
              ((tupleProductFiber r N uv.2).card : ℝ) := by
          exact_mod_cast tuplePairProductFiber_card_le r N uv.1 uv.2
        _ ≤ ((uv.1.divisors.card : ℝ) ^ r) *
              ((uv.2.divisors.card : ℝ) ^ r) := by
          gcongr <;> exact_mod_cast ‹_›
        _ ≤ Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 := by
          rw [pow_two]
          exact mul_le_mul huenv hvenv (by positivity)
            (by simp [Erdos439.PowerDecay.divisorSubpowerEnvelope]; positivity)
    _ = ((Erdos822.collisionPairs
          (Finset.Icc 1 (N ^ r)) squarefreePart).card : ℝ) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 := by
      simp [mul_comm]
    _ ≤ ((N ^ r : ℕ) * Nat.sqrt (N ^ r) : ℕ) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 := by
      gcongr
      exact_mod_cast squareProductPairs_Icc_card_le (N ^ r)
    _ = Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 *
          ((N ^ r : ℕ) * Nat.sqrt (N ^ r) : ℕ) := by ring

/-! ## The exact even-moment expansion

The following lemmas turn the `2r`-th moment of the one-sided character
sum into a finite sum over pairs of `r`-tuples.  Summing over odd
denominators then exposes the attached character from the preceding
section.  Square tuple-products form the diagonal; every nonsquare product
has a complete period of length `4k` and hence contributes only its final
incomplete period.
-/

lemma legendrePartialSum_eq_sum_Icc (p N : ℕ) :
    legendrePartialSum p N =
      ∑ n ∈ Finset.Icc 1 N, jacobiSym (n : ℤ) p := by
  rw [legendrePartialSum]
  apply Finset.sum_bij (fun n _hn => n + 1)
  · intro n hn
    rw [Finset.mem_Icc]
    exact ⟨by omega, by simpa using Finset.mem_range.mp hn⟩
  · intro n₁ hn₁ n₂ hn₂ h
    omega
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
    refine ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    rfl

lemma jacobiSym_tupleProduct {r m : ℕ} (a : Fin r → ℕ) :
    (∏ i, jacobiSym (a i : ℤ) m) =
      jacobiSym (tupleProduct a : ℤ) m := by
  have h := jacobiSym.list_prod_left
    (l := List.ofFn fun i : Fin r => (a i : ℤ)) (n := m)
  rw [show (tupleProduct a : ℤ) = ∏ i, (a i : ℤ) by
    change ((∏ i, a i : ℕ) : ℤ) = ∏ i, (a i : ℤ)
    push_cast
    rfl]
  simpa [List.prod_ofFn] using h.symm

lemma legendrePartialSum_pow_eq_tupleSum (m r N : ℕ) :
    legendrePartialSum m N ^ r =
      ∑ a ∈ tupleBox r N, jacobiSym (tupleProduct a : ℤ) m := by
  rw [legendrePartialSum_eq_sum_Icc, Finset.sum_pow']
  apply Finset.sum_congr
  · rfl
  intro a ha
  exact jacobiSym_tupleProduct a

lemma legendrePartialSum_evenMoment_eq (m r N : ℕ) :
    legendrePartialSum m N ^ (2 * r) =
      ∑ ab ∈ (tupleBox r N).product (tupleBox r N),
        jacobiSym (tupleProduct ab.1 * tupleProduct ab.2 : ℤ) m := by
  rw [show 2 * r = r + r by omega, pow_add,
    legendrePartialSum_pow_eq_tupleSum,
    Finset.sum_mul_sum]
  rw [← Finset.sum_product (tupleBox r N) (tupleBox r N)
    (fun ab => jacobiSym (tupleProduct ab.1 : ℤ) m *
      jacobiSym (tupleProduct ab.2 : ℤ) m)]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [show (tupleProduct ab.1 * tupleProduct ab.2 : ℤ) =
      (tupleProduct ab.1 : ℤ) * (tupleProduct ab.2 : ℤ) by
    push_cast
    rfl]
  rw [jacobiSym.mul_left]

lemma sum_odd_legendrePartialSum_evenMoment_eq (r N x : ℕ) :
    (∑ m ∈ Finset.range x,
        if Odd m then legendrePartialSum m N ^ (2 * r) else 0) =
      ∑ ab ∈ (tupleBox r N).product (tupleBox r N),
        ∑ m ∈ Finset.range x,
          quadraticDenominatorTerm
            (tupleProduct ab.1 * tupleProduct ab.2) m := by
  calc
    (∑ m ∈ Finset.range x,
        if Odd m then legendrePartialSum m N ^ (2 * r) else 0) =
        ∑ m ∈ Finset.range x,
          ∑ ab ∈ (tupleBox r N).product (tupleBox r N),
            quadraticDenominatorTerm
              (tupleProduct ab.1 * tupleProduct ab.2) m := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hodd : Odd m
      · simp only [if_pos hodd, legendrePartialSum_evenMoment_eq]
        apply Finset.sum_congr rfl
        intro ab hab
        simp [quadraticDenominatorTerm, hodd]
      · simp [quadraticDenominatorTerm, hodd]
    _ = _ := by rw [Finset.sum_comm]

lemma squareTuplePairs_eq_filter (r N : ℕ) :
    squareTuplePairs r N =
      ((tupleBox r N).product (tupleBox r N)).filter fun ab =>
        IsSquare (tupleProduct ab.1 * tupleProduct ab.2) := by
  classical
  ext ab
  rw [mem_squareTuplePairs, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hb, hsquare⟩
    exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hsquare⟩
  · rintro ⟨hab, hsquare⟩
    exact ⟨(Finset.mem_product.mp hab).1,
      (Finset.mem_product.mp hab).2, hsquare⟩

lemma tupleBox_card (r N : ℕ) :
    (tupleBox r N).card = N ^ r := by
  classical
  simp [tupleBox, Erdos444.orderedTuples, Fintype.card_piFinset]

lemma sum_quadraticDenominatorTerm_le_range (k x : ℕ) :
    (∑ m ∈ Finset.range x, quadraticDenominatorTerm k m : ℤ) ≤ x := by
  calc
    (∑ m ∈ Finset.range x, quadraticDenominatorTerm k m : ℤ) ≤
        ∑ _m ∈ Finset.range x, (1 : ℤ) := by
      exact Finset.sum_le_sum fun m _hm => quadraticDenominatorTerm_le_one k m
    _ = x := by simp

lemma tuplePairProduct_le_pow {r N : ℕ}
    {ab : (Fin r → ℕ) × (Fin r → ℕ)}
    (hab : ab ∈ (tupleBox r N).product (tupleBox r N)) :
    tupleProduct ab.1 * tupleProduct ab.2 ≤ N ^ (2 * r) := by
  rw [show 2 * r = r + r by omega, pow_add]
  exact Nat.mul_le_mul
    (tupleProduct_le_pow_of_mem (Finset.mem_product.mp hab).1)
    (tupleProduct_le_pow_of_mem (Finset.mem_product.mp hab).2)

/-- Elliott's medium-range moment estimate in its finite exact form.  The
first term is the square-product diagonal.  The second term bounds every
nonsquare tuple pair by one incomplete character period. -/
lemma sum_odd_legendrePartialSum_evenMoment_le (r N x : ℕ) :
    (∑ m ∈ Finset.range x,
        if Odd m then legendrePartialSum m N ^ (2 * r) else 0) ≤
      (x : ℤ) * (squareTuplePairs r N).card +
        (4 * N ^ (2 * r) : ℕ) *
          ((tupleBox r N).product (tupleBox r N)).card := by
  classical
  rw [sum_odd_legendrePartialSum_evenMoment_eq]
  let S := (tupleBox r N).product (tupleBox r N)
  let B : ℤ := (4 * N ^ (2 * r) : ℕ)
  let P : ((Fin r → ℕ) × (Fin r → ℕ)) → Prop := fun ab =>
    IsSquare (tupleProduct ab.1 * tupleProduct ab.2)
  have hpoint : ∀ ab ∈ S,
      (∑ m ∈ Finset.range x,
          quadraticDenominatorTerm
            (tupleProduct ab.1 * tupleProduct ab.2) m : ℤ) ≤
        if P ab then (x : ℤ) else B := by
    intro ab hab
    by_cases hsquare : P ab
    · simpa [P, hsquare] using
        sum_quadraticDenominatorTerm_le_range
          (tupleProduct ab.1 * tupleProduct ab.2) x
    · simp only [P, hsquare, if_false]
      have hapos := tupleProduct_pos_of_mem (Finset.mem_product.mp hab).1
      have hbpos := tupleProduct_pos_of_mem (Finset.mem_product.mp hab).2
      have hkpos : 0 < tupleProduct ab.1 * tupleProduct ab.2 :=
        Nat.mul_pos hapos hbpos
      have hperiod := sum_quadraticDenominatorTerm_lt_period
        hkpos hsquare x
      have hprod := tuplePairProduct_le_pow hab
      change (∑ m ∈ Finset.range x,
          quadraticDenominatorTerm
            (tupleProduct ab.1 * tupleProduct ab.2) m : ℤ) ≤
        ((4 * N ^ (2 * r) : ℕ) : ℤ)
      calc
        _ ≤ ((4 * (tupleProduct ab.1 * tupleProduct ab.2) : ℕ) : ℤ) :=
          hperiod.le
        _ ≤ ((4 * N ^ (2 * r) : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_left 4 hprod
  calc
    (∑ ab ∈ S,
        ∑ m ∈ Finset.range x,
          quadraticDenominatorTerm
            (tupleProduct ab.1 * tupleProduct ab.2) m : ℤ) ≤
        ∑ ab ∈ S, if P ab then (x : ℤ) else B :=
      Finset.sum_le_sum hpoint
    _ = ((S.filter P).card : ℤ) * x +
        ((S.filter fun ab => ¬ P ab).card : ℤ) * B := by
      rw [Finset.sum_ite]
      simp
    _ ≤ ((S.filter P).card : ℤ) * x + (S.card : ℤ) * B := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right (by
          exact_mod_cast Finset.card_filter_le S (fun ab => ¬ P ab)) (by
            simp [B])) _
    _ = (x : ℤ) * (squareTuplePairs r N).card +
        (4 * N ^ (2 * r) : ℕ) * S.card := by
      rw [show S.filter P = squareTuplePairs r N by
        simpa [S, P] using (squareTuplePairs_eq_filter r N).symm]
      simp [B]
      ring

/-! ### The concrete twentieth-moment medium-range bound -/

/-- In dimension ten the diagonal has size at most `N^17`.  The deliberately
generous estimate `N^(1/8) ≤ N` avoids fractional-power bookkeeping while
retaining the two powers of decay needed after Markov's inequality. -/
lemma exists_squareTuplePairs_ten_card_le :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((squareTuplePairs 10 N).card : ℝ) ≤ (N : ℝ) ^ 17 := by
  obtain ⟨N₀, hN₀⟩ := exists_squareTuplePairs_card_le 10 (by omega)
  refine ⟨max 1 N₀, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left 1 N₀).trans hN
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have henv : Erdos439.PowerDecay.divisorSubpowerEnvelope N ≤ (N : ℝ) := by
    exact Real.rpow_le_self_of_one_le hbase (by norm_num)
  calc
    ((squareTuplePairs 10 N).card : ℝ) ≤
        Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 *
          ((N ^ 10 : ℕ) * Nat.sqrt (N ^ 10) : ℕ) :=
      hN₀ N ((le_max_right 1 N₀).trans hN)
    _ = Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 *
          ((N : ℝ) ^ 10 * (N : ℝ) ^ 5) := by
      rw [show Nat.sqrt (N ^ 10) = N ^ 5 by
        rw [show N ^ 10 = (N ^ 5) ^ 2 by ring]
        simp]
      push_cast
      rfl
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 10 * (N : ℝ) ^ 5) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by
        show 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ)
        exact Real.rpow_nonneg (by positivity) _) henv 2) (by
          positivity)
    _ = (N : ℝ) ^ 17 := by ring

lemma sum_odd_legendrePartialSum_twentiethMoment_le (N x : ℕ) :
    (∑ m ∈ Finset.range x,
        if Odd m then legendrePartialSum m N ^ 20 else 0) ≤
      (x : ℤ) * (squareTuplePairs 10 N).card + 4 * (N : ℤ) ^ 40 := by
  have h := sum_odd_legendrePartialSum_evenMoment_le 10 N x
  norm_num at h ⊢
  rw [tupleBox_card] at h
  norm_num at h
  convert h using 1 <;> ring

/-- Odd moduli below `x` at which the one-sided character sum at time `N`
violates the desired strict inequality.  This superset of the bad primes is
what the moment argument counts. -/
noncomputable def oddBadModuli (ε : ℝ) (N x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun m =>
    Odd m ∧ ε * (N : ℝ) ≤ (legendrePartialSum m N : ℝ)

lemma oddBadModuli_card_mul_le_moment {ε : ℝ} (hε : 0 ≤ ε) (N x : ℕ) :
    ((oddBadModuli ε N x).card : ℝ) * (ε * (N : ℝ)) ^ 20 ≤
      ((∑ m ∈ Finset.range x,
        if Odd m then legendrePartialSum m N ^ 20 else 0 : ℤ) : ℝ) := by
  classical
  calc
    ((oddBadModuli ε N x).card : ℝ) * (ε * (N : ℝ)) ^ 20 =
        ∑ _m ∈ oddBadModuli ε N x, (ε * (N : ℝ)) ^ 20 := by
      simp [mul_comm]
    _ ≤ ∑ m ∈ oddBadModuli ε N x,
        ((legendrePartialSum m N : ℝ) ^ 20) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmge := (Finset.mem_filter.mp hm).2.2
      exact pow_le_pow_left₀ (mul_nonneg hε (by positivity)) hmge 20
    _ ≤ ∑ m ∈ Finset.range x,
        if Odd m then ((legendrePartialSum m N : ℝ) ^ 20) else 0 := by
      rw [show (∑ m ∈ oddBadModuli ε N x,
          ((legendrePartialSum m N : ℝ) ^ 20)) =
          ∑ m ∈ oddBadModuli ε N x,
            if Odd m then ((legendrePartialSum m N : ℝ) ^ 20) else 0 by
        apply Finset.sum_congr rfl
        intro m hm
        rw [if_pos (Finset.mem_filter.mp hm).2.1]]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro m hmrange hmbad
        split_ifs <;> positivity
    _ = ((∑ m ∈ Finset.range x,
        if Odd m then legendrePartialSum m N ^ 20 else 0 : ℤ) : ℝ) := by
      push_cast
      rfl

/-- Markov's inequality combined with the twentieth-moment estimate. -/
lemma exists_oddBadModuli_card_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℕ,
      ((oddBadModuli ε N x).card : ℝ) ≤
        ((x : ℝ) * (N : ℝ) ^ 17 + 4 * (N : ℝ) ^ 40) /
          (ε * (N : ℝ)) ^ 20 := by
  obtain ⟨N₀, hN₀⟩ := exists_squareTuplePairs_ten_card_le
  refine ⟨max 1 N₀, ?_⟩
  intro N hN x
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_left 1 N₀).trans hN)
  rw [le_div_iff₀ (pow_pos (mul_pos hε (by exact_mod_cast hNpos)) 20)]
  refine (oddBadModuli_card_mul_le_moment hε.le N x).trans ?_
  have hmoment := sum_odd_legendrePartialSum_twentiethMoment_le N x
  have hcast :
      (((∑ m ∈ Finset.range x,
          if Odd m then legendrePartialSum m N ^ 20 else 0 : ℤ) : ℤ) : ℝ) ≤
        ((x : ℝ) * ((squareTuplePairs 10 N).card : ℝ) +
          4 * (N : ℝ) ^ 40) := by
    exact_mod_cast hmoment
  exact hcast.trans (by
    gcongr
    exact hN₀ N ((le_max_right 1 N₀).trans hN))

/-- The medium-range estimate in the summable form used by the tail
argument: `x/N^3` is summable after the threshold-time weight `N` is
inserted, while the finite-period error is `N^20`. -/
lemma exists_oddBadModuli_card_bound_simplified {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℕ,
      ((oddBadModuli ε N x).card : ℝ) ≤
        (ε ^ 20)⁻¹ *
          ((x : ℝ) / (N : ℝ) ^ 3 + 4 * (N : ℝ) ^ 20) := by
  obtain ⟨N₀, hN₀⟩ := exists_oddBadModuli_card_bound hε
  refine ⟨max 1 N₀, ?_⟩
  intro N hN x
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one
      ((le_max_left 1 N₀).trans hN)
  refine (hN₀ N ((le_max_right 1 N₀).trans hN) x).trans_eq ?_
  rw [mul_pow]
  field_simp [hε.ne', hNpos.ne']

lemma jacobiSym_le_one (a : ℤ) (p : ℕ) : jacobiSym a p ≤ 1 := by
  rcases jacobiSym.trichotomy (a := a) (b := p) with h | h | h <;> omega

lemma sum_jacobiSym_range_eq_zero {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    ∑ n ∈ range p, jacobiSym (n : ℤ) p = 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpne2 : p ≠ 2 := hpodd.ne_two_of_dvd_nat (dvd_refl p)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hpne2
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ n : Fin p, jacobiSym (n : ℤ) p =
        ∑ a : ZMod p, quadraticChar (ZMod p) a := by
      apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
      intro n
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      rw [legendreSym]
      have hn : (n.val : ZMod p) = (ZMod.finEquiv p).toEquiv n := by
        cases p with
        | zero => exact Fin.elim0 n
        | succ p =>
            simp only [ZMod.finEquiv, RingEquiv.toEquiv_eq_coe, RingEquiv.refl_apply]
            apply Fin.ext
            change n.val % (p + 1) = n.val
            exact Nat.mod_eq_of_lt n.isLt
      simpa using congrArg (quadraticChar (ZMod p)) hn
    _ = 0 := quadraticChar_sum_zero hchar

lemma sum_jacobiSym_one_to_prime_eq_zero {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    ∑ n ∈ range p, jacobiSym (n + 1 : ℤ) p = 0 := by
  have hzero : jacobiSym 0 p = 0 := jacobiSym.zero_left hp.one_lt
  have hpzero : jacobiSym (p : ℤ) p = 0 := by
    rw [jacobiSym.mod_left]
    simpa using hzero
  calc
    ∑ n ∈ range p, jacobiSym (n + 1 : ℤ) p =
        (∑ n ∈ range p, jacobiSym (n + 1 : ℤ) p) + jacobiSym 0 p := by
      rw [hzero, add_zero]
    _ = ∑ n ∈ range (p + 1), jacobiSym (n : ℤ) p := by
      simpa using (Finset.sum_range_succ' (fun n : ℕ => jacobiSym (n : ℤ) p) p).symm
    _ = (∑ n ∈ range p, jacobiSym (n : ℤ) p) + jacobiSym (p : ℤ) p := by
      rw [Finset.sum_range_succ]
    _ = 0 := by rw [sum_jacobiSym_range_eq_zero hp hpodd, hpzero, add_zero]

lemma jacobiSym_add_mul_period (p t n : ℕ) :
    jacobiSym (t * p + n + 1 : ℤ) p = jacobiSym (n + 1 : ℤ) p := by
  apply jacobiSym.mod_left'
  push_cast
  simp [Int.add_emod, add_assoc]

lemma legendrePartialSum_mul_period (p t : ℕ) :
    legendrePartialSum p (t * p) = t • legendrePartialSum p p := by
  induction t with
  | zero => simp [legendrePartialSum]
  | succ t ih =>
      rw [Nat.succ_mul, legendrePartialSum, Finset.sum_range_add]
      rw [legendrePartialSum] at ih
      rw [ih, add_nsmul, one_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      exact jacobiSym_add_mul_period p t n

lemma legendrePartialSum_eq_mod {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (N : ℕ) :
    legendrePartialSum p N = legendrePartialSum p (N % p) := by
  nth_rewrite 1 [show N = (N / p) * p + N % p by
    rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]]
  rw [legendrePartialSum, Finset.sum_range_add, legendrePartialSum]
  have hblock : ∑ n ∈ range (N / p * p), jacobiSym (n + 1 : ℤ) p = 0 := by
    change legendrePartialSum p (N / p * p) = 0
    rw [legendrePartialSum_mul_period, legendrePartialSum,
      sum_jacobiSym_one_to_prime_eq_zero hp hpodd, nsmul_zero]
  rw [hblock, zero_add]
  apply Finset.sum_congr rfl
  intro n _hn
  exact jacobiSym_add_mul_period p (N / p) n

lemma legendrePartialSum_le (p N : ℕ) : legendrePartialSum p N ≤ N := by
  rw [legendrePartialSum]
  calc
    ∑ n ∈ range N, jacobiSym (n + 1 : ℤ) p ≤ ∑ _n ∈ range N, (1 : ℤ) := by
      exact sum_le_sum fun n _hn => jacobiSym_le_one (n + 1 : ℤ) p
    _ = N := by simp

lemma legendrePartialSum_lt_prime {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (N : ℕ) :
    legendrePartialSum p N < p := by
  rw [legendrePartialSum_eq_mod hp hpodd]
  exact (legendrePartialSum_le p (N % p)).trans_lt (by
    exact_mod_cast Nat.mod_lt N hp.pos)

lemma exists_eventualThreshold {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) :
    ∃ m : ℕ, IsEventualThreshold ε p m := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (max (1 : ℝ) ((p : ℝ) / ε))
  have hm1real : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm1 : 1 ≤ m := by exact_mod_cast hm1real.le
  have hratio : (p : ℝ) / ε < m := (le_max_right _ _).trans_lt hm
  have hp_lt : (p : ℝ) < ε * m := by
    calc
      (p : ℝ) = ε * ((p : ℝ) / ε) := by field_simp
      _ < ε * m := mul_lt_mul_of_pos_left hratio hε
  refine ⟨m, hm1, ?_⟩
  intro N hmN
  have hsum : (legendrePartialSum p N : ℝ) < p := by
    exact_mod_cast legendrePartialSum_lt_prime hp hpodd N
  have hmono : ε * (m : ℝ) ≤ ε * (N : ℝ) := by
    gcongr
  exact hsum.trans (hp_lt.trans_le hmono)

lemma isEventualThreshold_one_of_one_lt {ε : ℝ} (hε : 1 < ε) (p : ℕ) :
    IsEventualThreshold ε p 1 := by
  refine ⟨le_rfl, ?_⟩
  intro N hN
  have hsum : (legendrePartialSum p N : ℝ) ≤ N := by
    exact_mod_cast legendrePartialSum_le p N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  exact hsum.trans_lt (by nlinarith)

lemma eventualThreshold_spec {ε : ℝ} {p : ℕ}
    (h : ∃ m : ℕ, IsEventualThreshold ε p m) :
    IsEventualThreshold ε p (eventualThreshold ε p) := by
  classical
  rw [eventualThreshold, dif_pos h]
  exact Nat.find_spec h

lemma eventualThreshold_minimal {ε : ℝ} {p m : ℕ}
    (hm : IsEventualThreshold ε p m) : eventualThreshold ε p ≤ m := by
  classical
  have h : ∃ k : ℕ, IsEventualThreshold ε p k := ⟨m, hm⟩
  rw [eventualThreshold, dif_pos h]
  exact Nat.find_min' h hm

lemma truncatedThreshold_spec (ε : ℝ) (p M : ℕ) :
    IsTruncatedThreshold ε p M (truncatedThreshold ε p M) := by
  classical
  rw [truncatedThreshold]
  exact Nat.find_spec (exists_isTruncatedThreshold ε p M)

lemma truncatedThreshold_minimal {ε : ℝ} {p M m : ℕ}
    (hm : IsTruncatedThreshold ε p M m) : truncatedThreshold ε p M ≤ m := by
  classical
  rw [truncatedThreshold]
  exact Nat.find_min' (exists_isTruncatedThreshold ε p M) hm

lemma one_le_truncatedThreshold (ε : ℝ) (p M : ℕ) :
    1 ≤ truncatedThreshold ε p M :=
  (truncatedThreshold_spec ε p M).1

lemma truncatedThreshold_le_succ (ε : ℝ) (p M : ℕ) :
    truncatedThreshold ε p M ≤ M + 1 := by
  apply truncatedThreshold_minimal
  refine ⟨by omega, ?_⟩
  omega

lemma truncatedThreshold_le_eventualThreshold {ε : ℝ} {p M : ℕ}
    (h : ∃ m : ℕ, IsEventualThreshold ε p m) :
    truncatedThreshold ε p M ≤ eventualThreshold ε p := by
  apply truncatedThreshold_minimal
  exact ⟨(eventualThreshold_spec h).1, fun N hm _hM =>
    (eventualThreshold_spec h).2 N hm⟩

lemma eventualThreshold_spec_of_pos {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) :
    IsEventualThreshold ε p (eventualThreshold ε p) :=
  eventualThreshold_spec (exists_eventualThreshold hε hp hpodd)

lemma one_le_eventualThreshold_of_pos {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) :
    1 ≤ eventualThreshold ε p :=
  (eventualThreshold_spec_of_pos hε hp hpodd).1

lemma eventualThreshold_eq_one_of_one_lt {ε : ℝ} (hε : 1 < ε) (p : ℕ) :
    eventualThreshold ε p = 1 := by
  have h := isEventualThreshold_one_of_one_lt hε p
  apply Nat.le_antisymm (eventualThreshold_minimal h)
  exact (eventualThreshold_spec ⟨1, h⟩).1

lemma thresholdPrimeSum_eq_card_of_one_lt {ε : ℝ} (hε : 1 < ε) (x : ℕ) :
    thresholdPrimeSum ε x = (oddPrimesBelow x).card := by
  simp [thresholdPrimeSum, eventualThreshold_eq_one_of_one_lt hε]

end Erdos981

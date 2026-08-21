/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 937

Bajpai, Bennett, and Chan proved that there are infinitely many four-term arithmetic
progressions of pairwise coprime powerful numbers.  The mathematical reconstruction and the
formalization map are in `tex/937.tex`.
-/

syntax (name := answerSyntax937) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Nat

/-- A natural number is `k`-full when every prime factor occurs to exponent at least `k`.
This is the definition used by `FormalConjecturesUtil`. -/
def Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- Powerful (squarefull) natural numbers are the `2`-full numbers. -/
abbrev Powerful : ℕ → Prop := Full 2

end Nat

namespace Erdos937

open Nat Set

/-- The four numbers `a, a+d, a+2d, a+3d` form a nonconstant progression of pairwise
coprime powerful numbers.  This is the exact upstream specification. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  a.Powerful ∧ (a + d).Powerful ∧ (a + 2 * d).Powerful ∧ (a + 3 * d).Powerful ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧
  (a + 2 * d).Coprime (a + 3 * d)

/-! ## The three-square parametrization -/

/-- The first square root in the parametrization of three squares in arithmetic progression. -/
def apX (a b : ℤ) : ℤ := a ^ 2 - b ^ 2 + 2 * a * b

/-- The middle square root in the parametrization. -/
def apY (a b : ℤ) : ℤ := a ^ 2 + b ^ 2

/-- The third square root in the parametrization. -/
def apZ (a b : ℤ) : ℤ := a ^ 2 - b ^ 2 - 2 * a * b

/-- One quarter of the common difference. -/
def apDelta (a b : ℤ) : ℤ := a * b * (b ^ 2 - a ^ 2)

/-- The fourth member of the progression after the first three members have been squared. -/
def quartic (a b : ℤ) : ℤ :=
  a ^ 4 - 8 * a ^ 3 * b + 2 * a ^ 2 * b ^ 2 + 8 * a * b ^ 3 + b ^ 4

lemma apY_sq_sub_apX_sq (a b : ℤ) :
    apY a b ^ 2 - apX a b ^ 2 = 4 * apDelta a b := by
  simp only [apX, apY, apDelta]
  ring

lemma apZ_sq_sub_apY_sq (a b : ℤ) :
    apZ a b ^ 2 - apY a b ^ 2 = 4 * apDelta a b := by
  simp only [apZ, apY, apDelta]
  ring

lemma quartic_sub_apZ_sq (a b : ℤ) :
    quartic a b - apZ a b ^ 2 = 4 * apDelta a b := by
  simp only [quartic, apZ, apDelta]
  ring

lemma quartic_parity_transform (a b : ℤ) (hs : 2 ∣ a + b) (hd : 2 ∣ a - b) :
    4 * quartic ((a + b) / 2) ((a - b) / 2) = quartic a b := by
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv⟩ := hd
  have ha : a = u + v := by omega
  have hb : b = u - v := by omega
  subst a
  subst b
  have hsum : (u + v + (u - v)) / 2 = u := by omega
  have hdiff : (u + v - (u - v)) / 2 = v := by omega
  rw [hsum, hdiff]
  simp only [quartic]
  ring

/-! ## A fixed multiplication-by-five orbit

For the infinitude argument it is enough to iterate one fixed rational map.  We use the integral
short Weierstrass model obtained from the BBC curve.
-/

abbrev shortA : ℚ := -478842624
abbrev shortB : ℚ := 3011551764480

private def shortCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, shortA, shortB⟩

def ShortOnCurve (P : ℚ × ℚ) : Prop :=
  P.2 ^ 2 = P.1 ^ 3 + shortA * P.1 + shortB

/-- Affine doubling on the short model.  Our orbit never meets a point with `y = 0`. -/
def shortDouble (P : ℚ × ℚ) : ℚ × ℚ :=
  let m := (3 * P.1 ^ 2 + shortA) / (2 * P.2)
  let x := m ^ 2 - 2 * P.1
  (x, m * (P.1 - x) - P.2)

/-- Affine addition when the two x-coordinates are distinct. -/
def shortAdd (P Q : ℚ × ℚ) : ℚ × ℚ :=
  let m := (Q.2 - P.2) / (Q.1 - P.1)
  let x := m ^ 2 - P.1 - Q.1
  (x, m * (P.1 - x) - P.2)

/-- Multiplication by five, implemented as `P + 2(2P)`. -/
def shortMulFive (P : ℚ × ℚ) : ℚ × ℚ :=
  shortAdd P (shortDouble (shortDouble P))

lemma shortCurve_equation_iff (P : ℚ × ℚ) :
    shortCurve.toAffine.Equation P.1 P.2 ↔ ShortOnCurve P := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortCurve, ShortOnCurve, shortA, shortB, WeierstrassCurve.toAffine]

lemma shortDouble_onCurve {P : ℚ × ℚ} (hP : ShortOnCurve P) (hy : P.2 ≠ 0) :
    ShortOnCurve (shortDouble P) := by
  have he : shortCurve.toAffine.Equation P.1 P.2 :=
    (shortCurve_equation_iff P).2 hP
  have hneg : P.2 ≠ shortCurve.toAffine.negY P.1 P.2 := by
    simp only [shortCurve, WeierstrassCurve.toAffine, WeierstrassCurve.Affine.negY]
    intro h
    apply hy
    linarith
  have hadd := shortCurve.toAffine.equation_add he he
    (fun h => hneg h.2)
  rw [shortCurve.toAffine.slope_of_Y_ne rfl hneg] at hadd
  have hm : P.2 + P.2 = 2 * P.2 := by ring
  apply (shortCurve_equation_iff (shortDouble P)).1
  convert hadd using 1
  case e'_2 => rfl
  case e'_4 =>
    simp [shortDouble, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
    ring
  case e'_5 =>
    simp [shortDouble, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
    ring

lemma shortAdd_onCurve {P Q : ℚ × ℚ} (hP : ShortOnCurve P) (hQ : ShortOnCurve Q)
    (hx : P.1 ≠ Q.1) : ShortOnCurve (shortAdd P Q) := by
  have heP : shortCurve.toAffine.Equation P.1 P.2 :=
    (shortCurve_equation_iff P).2 hP
  have heQ : shortCurve.toAffine.Equation Q.1 Q.2 :=
    (shortCurve_equation_iff Q).2 hQ
  have hadd := shortCurve.toAffine.equation_add heP heQ (fun h => hx h.1)
  rw [shortCurve.toAffine.slope_of_X_ne hx] at hadd
  have hm : (Q.2 - P.2) / (Q.1 - P.1) = (P.2 - Q.2) / (P.1 - Q.1) := by
    field_simp [sub_ne_zero.mpr hx, sub_ne_zero.mpr (Ne.symm hx)]
    ring
  apply (shortCurve_equation_iff (shortAdd P Q)).1
  convert hadd using 1
  case e'_2 => rfl
  case e'_4 =>
    simp [shortAdd, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
  case e'_5 =>
    simp [shortAdd, shortCurve, shortA, shortB, WeierstrassCurve.toAffine,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    rw [hm]
    ring

lemma shortMulFive_onCurve {P : ℚ × ℚ} (hP : ShortOnCurve P) (hy : P.2 ≠ 0)
    (hy2 : (shortDouble P).2 ≠ 0)
    (hx : P.1 ≠ (shortDouble (shortDouble P)).1) :
    ShortOnCurve (shortMulFive P) := by
  have h2 := shortDouble_onCurve hP hy
  have h4 := shortDouble_onCurve h2 hy2
  exact shortAdd_onCurve hP h4 hx

/-! ## The local calculation at five -/

private instance primeFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The subring of rationals integral at the prime `p`, expressed using `padicValRat`. -/
private def padicIntegral (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | 0 ≤ padicValRat p q}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro q r hq hr
    by_cases hqr : q + r = 0
    · simp [hqr]
    · exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hqr)
  neg_mem' := by
    intro q hq
    simpa using hq
  mul_mem' := by
    intro q r hq hr
    change 0 ≤ padicValRat p q at hq
    change 0 ≤ padicValRat p r at hr
    change 0 ≤ padicValRat p (q * r)
    by_cases hq0 : q = 0
    · simp [hq0]
    by_cases hr0 : r = 0
    · simp [hr0]
    rw [padicValRat.mul hq0 hr0]
    omega

private lemma int_padicIntegral (p : ℕ) [Fact p.Prime] (z : ℤ) :
    0 ≤ padicValRat p (z : ℚ) := by
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le (padicValInt p z)

private lemma integral_add {q r : ℚ} (hq : 0 ≤ padicValRat 5 q)
    (hr : 0 ≤ padicValRat 5 r) : 0 ≤ padicValRat 5 (q + r) := by
  change q ∈ padicIntegral 5 at hq
  change r ∈ padicIntegral 5 at hr
  change q + r ∈ padicIntegral 5
  exact (padicIntegral 5).add_mem hq hr

private lemma integral_sub {q r : ℚ} (hq : 0 ≤ padicValRat 5 q)
    (hr : 0 ≤ padicValRat 5 r) : 0 ≤ padicValRat 5 (q - r) := by
  change q ∈ padicIntegral 5 at hq
  change r ∈ padicIntegral 5 at hr
  change q - r ∈ padicIntegral 5
  exact (padicIntegral 5).sub_mem hq hr

private lemma integral_mul {q r : ℚ} (hq : 0 ≤ padicValRat 5 q)
    (hr : 0 ≤ padicValRat 5 r) : 0 ≤ padicValRat 5 (q * r) := by
  change q ∈ padicIntegral 5 at hq
  change r ∈ padicIntegral 5 at hr
  change q * r ∈ padicIntegral 5
  exact (padicIntegral 5).mul_mem hq hr

private lemma integral_pow {q : ℚ} (hq : 0 ≤ padicValRat 5 q) (n : ℕ) :
    0 ≤ padicValRat 5 (q ^ n) := by
  change q ∈ padicIntegral 5 at hq
  change q ^ n ∈ padicIntegral 5
  exact (padicIntegral 5).pow_mem hq n

private lemma padicValRat_one_add_sq_mul {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    padicValRat 5 (1 + z ^ 2 * t) = 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  have hsum : (1 : ℚ) + z ^ 2 * t ≠ 0 := by
    intro h
    have heq : z ^ 2 * t = -1 := by linarith
    rw [heq] at hp_pos
    simp at hp_pos
  simpa using padicValRat.add_eq_of_lt (p := 5) hsum one_ne_zero hp0
    (by simpa using hp_pos)

private lemma padicValRat_five_add_sq_mul {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    padicValRat 5 (5 + z ^ 2 * t) = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  by_cases ht0 : t = 0
  · subst t
    simpa using padicValRat.self (p := 5) (by norm_num)
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_gt : 1 < padicValRat 5 (z ^ 2 * t) := by omega
  have hsum : (5 : ℚ) + z ^ 2 * t ≠ 0 := by
    intro h
    have heq : z ^ 2 * t = -5 := by linarith
    rw [heq] at hp_gt
    rw [padicValRat.neg] at hp_gt
    have h5 : padicValRat 5 (5 : ℚ) = 1 := padicValRat.self (by norm_num)
    omega
  have h5 : padicValRat 5 (5 : ℚ) = 1 := padicValRat.self (by norm_num)
  simpa [h5] using padicValRat.add_eq_of_lt (p := 5) hsum (by norm_num) hp0 (by omega)

private lemma one_add_sq_mul_ne_zero {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    (1 : ℚ) + z ^ 2 * t ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  intro h
  have heq : z ^ 2 * t = -1 := by linarith
  rw [heq] at hp_pos
  simp at hp_pos

private lemma five_add_sq_mul_ne_zero {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    (5 : ℚ) + z ^ 2 * t ≠ 0 := by
  intro h
  have hv := padicValRat_five_add_sq_mul hz ht
  rw [h] at hv
  simp at hv

private lemma padicValRat_three_add_sq_mul {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    padicValRat 5 (3 + z ^ 2 * t) = 0 := by
  have h3 : padicValRat 5 (3 : ℚ) = 0 := by
    change padicValRat 5 ((3 : ℤ) : ℚ) = 0
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd (p := 5) (z := (3 : ℤ)) (by norm_num)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0, h3]
  have hp0 : z ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) ht0
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  have hsum : (3 : ℚ) + z ^ 2 * t ≠ 0 := by
    intro h
    have heq : z ^ 2 * t = -3 := by linarith
    rw [heq, padicValRat.neg, h3] at hp_pos
    omega
  simpa [h3] using padicValRat.add_eq_of_lt (p := 5) hsum (by norm_num) hp0 (by omega)

private lemma three_add_sq_mul_ne_zero {z t : ℚ}
    (hz : 0 < padicValRat 5 z) (ht : 0 ≤ padicValRat 5 t) :
    (3 : ℚ) + z ^ 2 * t ≠ 0 := by
  have h3 : padicValRat 5 (3 : ℚ) = 0 := by
    change padicValRat 5 ((3 : ℤ) : ℚ) = 0
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd (p := 5) (z := (3 : ℤ)) (by norm_num)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp : padicValRat 5 (z ^ 2 * t) =
      (2 : ℤ) * padicValRat 5 z + padicValRat 5 t := by
    rw [padicValRat.mul (pow_ne_zero _ hz0) ht0, padicValRat.pow]
    norm_num
  have hp_pos : 0 < padicValRat 5 (z ^ 2 * t) := by omega
  intro h
  have heq : z ^ 2 * t = -3 := by linarith
  rw [heq, padicValRat.neg, h3] at hp_pos
  omega

private def curveTail {R : Type*} [CommRing R] (A B z : R) : R := A + B * z

private def threeTail {R : Type*} [CommRing R] (A B z : R) : R :=
  6 * A + 12 * B * z - A ^ 2 * z ^ 2

private def fourTail {R : Type*} [CommRing R] (A B z : R) : R :=
  5 * A + 20 * B * z - 5 * A ^ 2 * z ^ 2 - 4 * A * B * z ^ 3 -
    (8 * B ^ 2 + A ^ 3) * z ^ 4

private def fiveTail {R : Type*} [CommRing R] (A B z : R) : R :=
  62 * A + 380 * B * z - 105 * A ^ 2 * z ^ 2 + 240 * A * B * z ^ 3 -
    (300 * A ^ 3 + 240 * B ^ 2) * z ^ 4 - 696 * A ^ 2 * B * z ^ 5 -
    (125 * A ^ 4 + 1920 * A * B ^ 2) * z ^ 6 -
    (80 * A ^ 3 * B + 1600 * B ^ 3) * z ^ 7 -
    (50 * A ^ 5 + 240 * A ^ 2 * B ^ 2) * z ^ 8 -
    (100 * A ^ 4 * B + 640 * A * B ^ 3) * z ^ 9 +
    (A ^ 6 - 32 * A ^ 3 * B ^ 2 - 256 * B ^ 4) * z ^ 10

private noncomputable def tailPolynomial (which : ℕ) : Polynomial ℤ :=
  let A := Polynomial.C (-478842624 : ℤ)
  let B := Polynomial.C (3011551764480 : ℤ)
  let z := Polynomial.X
  match which with
  | 0 => curveTail A B z
  | 1 => threeTail A B z
  | 2 => fourTail A B z
  | _ => fiveTail A B z

private lemma integral_eval_int (P : Polynomial ℤ) {z : ℚ}
    (hz : 0 ≤ padicValRat 5 z) :
    0 ≤ padicValRat 5 (P.eval₂ (Int.castRingHom ℚ) z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa using integral_add hP hQ
  | monomial n a =>
      simp only [Polynomial.eval₂_monomial]
      exact integral_mul (int_padicIntegral 5 a) (integral_pow hz n)

private lemma tailPolynomial_eval (which : ℕ) (z : ℚ) :
    (tailPolynomial which).eval₂ (Int.castRingHom ℚ) z =
      (match which with
       | 0 => curveTail shortA shortB z
       | 1 => threeTail shortA shortB z
       | 2 => fourTail shortA shortB z
       | _ => fiveTail shortA shortB z) := by
  rcases which with _ | which
  · simp [tailPolynomial, curveTail, shortA, shortB, Polynomial.eval₂_pow]
  rcases which with _ | which
  · simp [tailPolynomial, threeTail, shortA, shortB, Polynomial.eval₂_pow]
  rcases which with _ | which
  · simp [tailPolynomial, fourTail, shortA, shortB, Polynomial.eval₂_pow]
  · simp [tailPolynomial, fiveTail, shortA, shortB, Polynomial.eval₂_pow]

private lemma integral_tail (which : ℕ) {z : ℚ} (hz : 0 ≤ padicValRat 5 z) :
    let A := shortA
    let B := shortB
    0 ≤ padicValRat 5
      (match which with
       | 0 => curveTail A B z
       | 1 => threeTail A B z
       | 2 => fourTail A B z
       | _ => fiveTail A B z) := by
  dsimp
  rw [← tailPolynomial_eval]
  exact integral_eval_int _ hz

def curvePoly (x : ℚ) : ℚ := x ^ 3 + shortA * x + shortB

def threePoly (x : ℚ) : ℚ :=
  3 * x ^ 4 + 6 * shortA * x ^ 2 + 12 * shortB * x - shortA ^ 2

def fourPoly (x : ℚ) : ℚ :=
  x ^ 6 + 5 * shortA * x ^ 4 + 20 * shortB * x ^ 3 - 5 * shortA ^ 2 * x ^ 2 -
    4 * shortA * shortB * x - 8 * shortB ^ 2 - shortA ^ 3

def fivePoly (x : ℚ) : ℚ :=
  32 * curvePoly x ^ 2 * fourPoly x - threePoly x ^ 3

def fivePhi (x : ℚ) : ℚ :=
  x * fivePoly x ^ 2 -
    8 * curvePoly x * threePoly x * fourPoly x * (fivePoly x - 4 * fourPoly x ^ 2)

def sevenPoly (x : ℚ) : ℚ :=
  fivePoly x * threePoly x ^ 3 - 128 * curvePoly x ^ 2 * fourPoly x ^ 3

def fiveYPoly (x : ℚ) : ℚ :=
  4 * fourPoly x ^ 2 * sevenPoly x -
    threePoly x ^ 3 * (fivePoly x - 4 * fourPoly x ^ 2) ^ 2

/-- Multiplication by five written only with the univariate division polynomials. -/
def fiveMap (P : ℚ × ℚ) : ℚ × ℚ :=
  (fivePhi P.1 / fivePoly P.1 ^ 2,
    P.2 * fiveYPoly P.1 / fivePoly P.1 ^ 3)

private lemma curvePoly_reverse {x : ℚ} (hx : x ≠ 0) :
    curvePoly x = x ^ 3 * (1 + x⁻¹ ^ 2 * curveTail shortA shortB x⁻¹) := by
  simp only [curvePoly, curveTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma threePoly_reverse {x : ℚ} (hx : x ≠ 0) :
    threePoly x = x ^ 4 * (3 + x⁻¹ ^ 2 * threeTail shortA shortB x⁻¹) := by
  simp only [threePoly, threeTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma fourPoly_reverse {x : ℚ} (hx : x ≠ 0) :
    fourPoly x = x ^ 6 * (1 + x⁻¹ ^ 2 * fourTail shortA shortB x⁻¹) := by
  simp only [fourPoly, fourTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma fivePoly_reverse {x : ℚ} (hx : x ≠ 0) :
    fivePoly x = x ^ 12 * (5 + x⁻¹ ^ 2 * fiveTail shortA shortB x⁻¹) := by
  simp only [fivePoly, curvePoly, threePoly, fourPoly, fiveTail]
  simp only [inv_eq_one_div]
  field_simp [hx]
  ring

private lemma curvePoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (curvePoly x) = 3 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (curveTail shortA shortB x⁻¹) := by
    simpa using integral_tail 0 (le_of_lt hz)
  have hr := padicValRat_one_add_sq_mul hz ht
  have hr0 := one_add_sq_mul_ne_zero hz ht
  rw [curvePoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma threePoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (threePoly x) = 4 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (threeTail shortA shortB x⁻¹) := by
    simpa using integral_tail 1 (le_of_lt hz)
  have hr := padicValRat_three_add_sq_mul hz ht
  have hr0 := three_add_sq_mul_ne_zero hz ht
  rw [threePoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma fourPoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fourPoly x) = 6 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (fourTail shortA shortB x⁻¹) := by
    simpa using integral_tail 2 (le_of_lt hz)
  have hr := padicValRat_one_add_sq_mul hz ht
  have hr0 := one_add_sq_mul_ne_zero hz ht
  rw [fourPoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma fivePoly_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fivePoly x) = 12 * padicValRat 5 x + 1 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by simp [hv]
  have ht : 0 ≤ padicValRat 5 (fiveTail shortA shortB x⁻¹) := by
    simpa using integral_tail 3 (le_of_lt hz)
  have hr := padicValRat_five_add_sq_mul hz ht
  have hr0 := five_add_sq_mul_ne_zero hz ht
  rw [fivePoly_reverse hx, padicValRat.mul (pow_ne_zero _ hx) hr0,
    padicValRat.pow, hr]
  norm_num

private lemma curvePoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : curvePoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [curvePoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (one_add_sq_mul_ne_zero hz (by simpa using integral_tail 0 (le_of_lt hz)))

private lemma threePoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : threePoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [threePoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (three_add_sq_mul_ne_zero hz (by simpa using integral_tail 1 (le_of_lt hz)))

private lemma fourPoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : fourPoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [fourPoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (one_add_sq_mul_ne_zero hz (by simpa using integral_tail 2 (le_of_lt hz)))

private lemma fivePoly_ne_zero {x : ℚ} (hv : padicValRat 5 x < 0) : fivePoly x ≠ 0 := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hz : 0 < padicValRat 5 x⁻¹ := by rw [padicValRat.inv]; omega
  rw [fivePoly_reverse hx]
  exact mul_ne_zero (pow_ne_zero _ hx)
    (five_add_sq_mul_ne_zero hz (by simpa using integral_tail 3 (le_of_lt hz)))

private lemma intUnit_padicVal {z : ℤ} (hz : ¬(5 : ℤ) ∣ z) :
    padicValRat 5 (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd hz

private lemma fiveMinusFourSq_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fivePoly x - 4 * fourPoly x ^ 2) = 12 * padicValRat 5 x := by
  have h5v := fivePoly_padicVal hv
  have h4v := fourPoly_padicVal hv
  have h50 := fivePoly_ne_zero hv
  have h40 := fourPoly_ne_zero hv
  have hc4 : padicValRat 5 (4 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  have hs0 : (4 : ℚ) * fourPoly x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ h40)
  have hsv : padicValRat 5 ((4 : ℚ) * fourPoly x ^ 2) =
      12 * padicValRat 5 x := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero _ h40), hc4, padicValRat.pow, h4v]
    ring
  have hlt : padicValRat 5 (-((4 : ℚ) * fourPoly x ^ 2)) <
      padicValRat 5 (fivePoly x) := by simp only [padicValRat.neg, hsv, h5v]; omega
  have hsum : -((4 : ℚ) * fourPoly x ^ 2) + fivePoly x ≠ 0 := by
    intro h
    have heq : fivePoly x = (4 : ℚ) * fourPoly x ^ 2 := by linarith
    have := congrArg (padicValRat 5) heq
    rw [h5v, hsv] at this
    omega
  have := padicValRat.add_eq_of_lt (p := 5) hsum (neg_ne_zero.mpr hs0) h50 hlt
  rw [padicValRat.neg, hsv] at this
  simpa [sub_eq_add_neg, add_comm] using this

private lemma fivePhi_padicVal {x : ℚ} (hv : padicValRat 5 x < 0) :
    padicValRat 5 (fivePhi x) = 25 * padicValRat 5 x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hv
  have hC0 := curvePoly_ne_zero hv
  have h30 := threePoly_ne_zero hv
  have h40 := fourPoly_ne_zero hv
  have h50 := fivePoly_ne_zero hv
  have hd0 : fivePoly x - 4 * fourPoly x ^ 2 ≠ 0 := by
    intro h
    have hv0 := fiveMinusFourSq_padicVal hv
    rw [h] at hv0
    simp at hv0
    omega
  have hCv := curvePoly_padicVal hv
  have h3v := threePoly_padicVal hv
  have h4v := fourPoly_padicVal hv
  have h5v := fivePoly_padicVal hv
  have hdv := fiveMinusFourSq_padicVal hv
  have h8v : padicValRat 5 (8 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  let U := x * fivePoly x ^ 2
  let V := 8 * curvePoly x * threePoly x * fourPoly x *
    (fivePoly x - 4 * fourPoly x ^ 2)
  have hU0 : U ≠ 0 := mul_ne_zero hx (pow_ne_zero _ h50)
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hC0) h30) h40) hd0
  have hUv : padicValRat 5 U = 25 * padicValRat 5 x + 2 := by
    dsimp [U]
    rw [padicValRat.mul hx (pow_ne_zero _ h50), padicValRat.pow, h5v]
    ring
  have hVv : padicValRat 5 V = 25 * padicValRat 5 x := by
    dsimp [V]
    rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hC0) h30) h40) hd0,
      padicValRat.mul (mul_ne_zero (mul_ne_zero (by norm_num) hC0) h30) h40,
      padicValRat.mul (mul_ne_zero (by norm_num) hC0) h30,
      padicValRat.mul (by norm_num) hC0, h8v, hCv, h3v, h4v, hdv]
    ring
  have hsum : -V + U ≠ 0 := by
    intro h
    have heq : U = V := by linarith
    have := congrArg (padicValRat 5) heq
    rw [hUv, hVv] at this
    omega
  have hval := padicValRat.add_eq_of_lt (p := 5) hsum (neg_ne_zero.mpr hV0) hU0 (by
    simp only [padicValRat.neg, hUv, hVv]
    omega)
  rw [padicValRat.neg, hVv] at hval
  simpa [fivePhi, U, V, sub_eq_add_neg, add_comm] using hval

private lemma fiveMap_fst_padicVal {P : ℚ × ℚ} (hv : padicValRat 5 P.1 < 0) :
    padicValRat 5 (fiveMap P).1 = padicValRat 5 P.1 - 2 := by
  have hphi0 : fivePhi P.1 ≠ 0 := by
    intro h
    have hv0 := fivePhi_padicVal hv
    rw [h] at hv0
    simp at hv0
    omega
  have h50 := fivePoly_ne_zero hv
  simp only [fiveMap, Prod.fst]
  rw [padicValRat.div hphi0 (pow_ne_zero _ h50), fivePhi_padicVal hv,
    padicValRat.pow, fivePoly_padicVal hv]
  ring

private lemma five_curve_polynomial_identity (x : ℚ) :
    curvePoly x * fiveYPoly x ^ 2 =
      fivePhi x ^ 3 + shortA * fivePhi x * fivePoly x ^ 4 + shortB * fivePoly x ^ 6 := by
  simp only [curvePoly, threePoly, fourPoly, fivePoly, fivePhi, sevenPoly, fiveYPoly,
    shortA, shortB]
  ring

lemma fiveMap_onCurve {P : ℚ × ℚ} (hP : ShortOnCurve P)
    (hv : padicValRat 5 P.1 < 0) : ShortOnCurve (fiveMap P) := by
  have h50 := fivePoly_ne_zero hv
  have hc : P.2 ^ 2 = curvePoly P.1 := by
    simpa [ShortOnCurve, curvePoly] using hP
  simp only [ShortOnCurve, fiveMap, Prod.fst, Prod.snd]
  field_simp [h50]
  rw [hc, five_curve_polynomial_identity]
  ring

/-- The point `2P₁` on the short model. -/
def shortStart : ℚ × ℚ :=
  (Rat.divInt 21443383536 511225,
    Rat.divInt (-2752977651830784) 365525875)

lemma shortStart_onCurve : ShortOnCurve shortStart := by
  norm_num [ShortOnCurve, shortStart, shortA, shortB, Rat.divInt_eq_div]

lemma shortStart_fst_padicVal : padicValRat 5 shortStart.1 = -2 := by
  simp only [shortStart, Prod.fst, padicValRat_def]
  rw [Rat.divInt_eq_div]
  rw [Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)]
  have hdenrat : (((21443383536 : ℤ) : ℚ) / ((511225 : ℤ) : ℚ)).den = 511225 := by
    exact_mod_cast Rat.den_div_eq_of_coprime (a := 21443383536) (b := 511225)
      (by norm_num) (by norm_num)
  rw [hdenrat]
  have hn : padicValInt 5 21443383536 = 0 :=
    padicValInt.eq_zero_of_not_dvd (by norm_num)
  have hd : padicValNat 5 511225 = 2 := by
    apply le_antisymm
    · by_contra h
      have h3 : 3 ≤ padicValNat 5 511225 := by omega
      have := (pow_dvd_iff_le_padicValNat (p := 5) (k := 3) (n := 511225)
        (by norm_num) (by norm_num)).2 h3
      norm_num at this
    · exact (pow_dvd_iff_le_padicValNat (p := 5) (k := 2) (n := 511225)
        (by norm_num) (by norm_num)).1 (by norm_num)
  omega

lemma shortStart_snd_padicVal : padicValRat 5 shortStart.2 = -3 := by
  simp only [shortStart, Prod.snd, padicValRat_def]
  rw [Rat.divInt_eq_div]
  rw [Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)]
  have hdenrat : (((-2752977651830784 : ℤ) : ℚ) /
      ((365525875 : ℤ) : ℚ)).den = 365525875 := by
    exact_mod_cast Rat.den_div_eq_of_coprime (a := -2752977651830784) (b := 365525875)
      (by norm_num) (by norm_num)
  rw [hdenrat]
  have hn : padicValInt 5 (-2752977651830784) = 0 :=
    padicValInt.eq_zero_of_not_dvd (by norm_num)
  have hd : padicValNat 5 365525875 = 3 := by
    apply le_antisymm
    · by_contra h
      have h4 : 4 ≤ padicValNat 5 365525875 := by omega
      have := (pow_dvd_iff_le_padicValNat (p := 5) (k := 4) (n := 365525875)
        (by norm_num) (by norm_num)).2 h4
      norm_num at this
    · exact (pow_dvd_iff_le_padicValNat (p := 5) (k := 3) (n := 365525875)
        (by norm_num) (by norm_num)).1 (by norm_num)
  omega

/-! ## The infinite rational orbit and the quartic -/

def orbit (n : ℕ) : ℚ × ℚ := (fiveMap^[n]) shortStart

lemma orbit_fst_padicVal (n : ℕ) : padicValRat 5 (orbit n).1 = -2 - 2 * n := by
  induction n with
  | zero => simpa [orbit] using shortStart_fst_padicVal
  | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      rw [fiveMap_fst_padicVal]
      · simp only [orbit] at ih
        omega
      · simp only [orbit] at ih
        omega

lemma orbit_onCurve (n : ℕ) : ShortOnCurve (orbit n) := by
  induction n with
  | zero => simpa [orbit] using shortStart_onCurve
  | succ n ih =>
      rw [orbit, Function.iterate_succ_apply']
      apply fiveMap_onCurve
      · simpa [orbit] using ih
      · have hv := orbit_fst_padicVal n
        simp only [orbit] at hv ⊢
        omega

private lemma short_snd_padicVal {P : ℚ × ℚ} (hP : ShortOnCurve P)
    (hv : padicValRat 5 P.1 < 0) :
    padicValRat 5 P.2 = 3 * padicValRat 5 P.1 / 2 := by
  have hc : P.2 ^ 2 = curvePoly P.1 := by
    simpa [ShortOnCurve, curvePoly] using hP
  have hC0 := curvePoly_ne_zero hv
  have hy0 : P.2 ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
    exact hC0 hc.symm
  have hval := congrArg (padicValRat 5) hc
  rw [padicValRat.pow, curvePoly_padicVal hv] at hval
  norm_num at hval
  omega

lemma orbit_snd_padicVal (n : ℕ) : padicValRat 5 (orbit n).2 = -3 - 3 * n := by
  have hx := orbit_fst_padicVal n
  have hy := short_snd_padicVal (orbit_onCurve n) (by omega : padicValRat 5 (orbit n).1 < 0)
  omega

/-- The old BBC `x`-coordinate recovered from the integral short model. -/
def bbcX (P : ℚ × ℚ) : ℚ :=
  (P.1 - ((17808 : ℤ) : ℚ)) / ((36 : ℤ) : ℚ)

/-- The old BBC `y`-coordinate recovered from the integral short model. -/
def bbcY (P : ℚ × ℚ) : ℚ :=
  (P.2 / ((108 : ℤ) : ℚ) + ((128 : ℤ) : ℚ) * bbcX P +
    ((3360 : ℤ) : ℚ)) / ((2 : ℤ) : ℚ)

def BBCOnCurve (P : ℚ × ℚ) : Prop :=
  P.2 ^ 2 - 128 * P.1 * P.2 - 3360 * P.2 =
    P.1 ^ 3 - 2612 * P.1 ^ 2 + 149568 * P.1

lemma short_to_BBC {P : ℚ × ℚ} (hP : ShortOnCurve P) :
    BBCOnCurve (bbcX P, bbcY P) := by
  simp only [ShortOnCurve, bbcX, bbcY, BBCOnCurve, Prod.fst, Prod.snd] at hP ⊢
  norm_num [shortA, shortB] at hP
  field_simp
  ring_nf at hP ⊢
  linarith

/-- The quartic parameter associated to a short-model point. -/
def quarticX (P : ℚ × ℚ) : ℚ := 146 * bbcX P / bbcY P - 2

def quarticY (P : ℚ × ℚ) : ℚ :=
  (bbcX P ^ 3 - 149568 * bbcX P - 3360 * bbcY P) / bbcY P ^ 2

lemma BBC_to_quartic {P : ℚ × ℚ} (hP : ShortOnCurve P) (hy : bbcY P ≠ 0) :
    quarticX P ^ 4 - 8 * quarticX P ^ 3 + 2 * quarticX P ^ 2 +
      8 * quarticX P + 1 = 73 * quarticY P ^ 2 := by
  have he := short_to_BBC hP
  simp only [BBCOnCurve, Prod.fst, Prod.snd] at he
  have he0 :
      bbcY P ^ 2 - 128 * bbcX P * bbcY P - 3360 * bbcY P -
        (bbcX P ^ 3 - 2612 * bbcX P ^ 2 + 149568 * bbcX P) = 0 :=
    sub_eq_zero.mpr he
  simp only [quarticX, quarticY]
  field_simp [hy]
  linear_combination (norm := ring)
    73 * (bbcX P ^ 3 + 2612 * bbcX P ^ 2 - 128 * bbcX P * bbcY P +
      149568 * bbcX P + bbcY P ^ 2 + 3360 * bbcY P) * he0

private lemma padicVal_sub_int {q : ℚ} (z : ℤ) (hq : padicValRat 5 q < 0) :
    padicValRat 5 (q - z) = padicValRat 5 q := by
  by_cases hz0 : z = 0
  · simp [hz0]
  have hz := int_padicIntegral 5 z
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hnegz : -(z : ℚ) ≠ 0 := by
    exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr hz0)
  have hsum : q + -(z : ℚ) ≠ 0 := by
    intro h
    have heq : q = (z : ℚ) := by linarith
    have := congrArg (padicValRat 5) heq
    rw [this] at hq
    omega
  have h := padicValRat.add_eq_of_lt (p := 5) hsum hq0 hnegz
    (by simpa using lt_of_lt_of_le hq hz)
  simpa [sub_eq_add_neg] using h

lemma orbit_bbcX_padicVal (n : ℕ) :
    padicValRat 5 (bbcX (orbit n)) = -2 - 2 * n := by
  have hx := orbit_fst_padicVal n
  have hnum := padicVal_sub_int (17808 : ℤ) (by omega : padicValRat 5 (orbit n).1 < 0)
  have hnum0 : (orbit n).1 - ((17808 : ℤ) : ℚ) ≠ 0 := by
    intro h
    rw [h] at hnum
    simp at hnum
    omega
  have h36 : padicValRat 5 (((36 : ℤ) : ℚ)) = 0 :=
    intUnit_padicVal (by norm_num)
  simp only [bbcX]
  rw [padicValRat.div hnum0 (by norm_num), hnum, h36, hx]
  omega

lemma orbit_bbcY_padicVal (n : ℕ) :
    padicValRat 5 (bbcY (orbit n)) = -3 - 3 * n := by
  let yterm : ℚ := (orbit n).2 / 108
  let xterm : ℚ := 128 * bbcX (orbit n)
  have hy := orbit_snd_padicVal n
  have hx := orbit_bbcX_padicVal n
  have hy0 : (orbit n).2 ≠ 0 := by intro h; simp [h] at hy; omega
  have h108 : padicValRat 5 (108 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  have h128 : padicValRat 5 (128 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  have hx0 : bbcX (orbit n) ≠ 0 := by intro h; simp [h] at hx; omega
  have hyv : padicValRat 5 yterm = -3 - 3 * n := by
    dsimp [yterm]
    rw [padicValRat.div hy0 (by norm_num), hy, h108]
    omega
  have hxv : padicValRat 5 xterm = -2 - 2 * n := by
    dsimp [xterm]
    rw [padicValRat.mul (by norm_num) hx0, h128, hx]
    omega
  have hyterm0 : yterm ≠ 0 := by intro h; rw [h] at hyv; simp at hyv; omega
  have hxterm0 : xterm ≠ 0 := by intro h; rw [h] at hxv; simp at hxv; omega
  have hxy0 : yterm + xterm ≠ 0 := by
    intro h
    have heq : yterm = -xterm := by linarith
    have := congrArg (padicValRat 5) heq
    rw [hyv, padicValRat.neg, hxv] at this
    omega
  have hxyv : padicValRat 5 (yterm + xterm) = -3 - 3 * n := by
    rw [padicValRat.add_eq_of_lt (p := 5) hxy0 hyterm0 hxterm0 (by omega), hyv]
  have h3360 : 0 ≤ padicValRat 5 (((3360 : ℤ) : ℚ)) :=
    int_padicIntegral 5 (3360 : ℤ)
  have hsum0 : yterm + xterm + ((3360 : ℤ) : ℚ) ≠ 0 := by
    intro h
    have heq : yterm + xterm = -(((3360 : ℤ) : ℚ)) := by linarith
    have := congrArg (padicValRat 5) heq
    rw [hxyv, padicValRat.neg] at this
    omega
  have hlt :
      padicValRat 5 (yterm + xterm) < padicValRat 5 (((3360 : ℤ) : ℚ)) := by
    rw [hxyv]
    exact lt_of_lt_of_le (by omega) h3360
  have hsumv :
      padicValRat 5 (yterm + xterm + ((3360 : ℤ) : ℚ)) = -3 - 3 * n := by
    rw [padicValRat.add_eq_of_lt (p := 5) hsum0 (by
      intro h; rw [h] at hxyv; simp at hxyv; omega) (by norm_num) hlt, hxyv]
  have h2 : padicValRat 5 (2 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  simp only [bbcY]
  change padicValRat 5 ((yterm + xterm + ((3360 : ℤ) : ℚ)) / 2) = _
  rw [padicValRat.div hsum0 (by norm_num), hsumv, h2]
  omega

lemma orbit_bbcY_ne_zero (n : ℕ) : bbcY (orbit n) ≠ 0 := by
  intro h
  have hv := orbit_bbcY_padicVal n
  rw [h] at hv
  simp at hv
  omega

lemma orbit_quarticX_add_two_padicVal (n : ℕ) :
    padicValRat 5 (quarticX (orbit n) + 2) = 1 + n := by
  have hx := orbit_bbcX_padicVal n
  have hy := orbit_bbcY_padicVal n
  have hx0 : bbcX (orbit n) ≠ 0 := by intro h; simp [h] at hx; omega
  have hy0 := orbit_bbcY_ne_zero n
  have h146 : padicValRat 5 (146 : ℚ) = 0 := intUnit_padicVal (by norm_num)
  simp only [quarticX]
  rw [sub_add_cancel]
  rw [padicValRat.div (mul_ne_zero (by norm_num) hx0) hy0,
    padicValRat.mul (by norm_num) hx0, h146, hx, hy]
  omega

lemma quarticX_orbit_injective : Function.Injective (fun n : ℕ => quarticX (orbit n)) := by
  intro m n h
  have h' := congrArg (fun q : ℚ => padicValRat 5 (q + 2)) h
  rw [orbit_quarticX_add_two_padicVal, orbit_quarticX_add_two_padicVal] at h'
  omega

end Erdos937

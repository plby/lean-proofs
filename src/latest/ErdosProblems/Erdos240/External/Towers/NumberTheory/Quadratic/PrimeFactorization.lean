import ErdosProblems.Erdos240.External.Towers.NumberTheory.Quadratic.PrimeDecomposition
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Milne, Algebraic Number Theory, Example 3.44

This file records the splitting, inert, and ramified cases for rational primes in the
quadratic-order models of quadratic rings of integers.  For odd primes not dividing the
radicand, the Legendre symbol distinguishes the split and inert cases.  We also record the
two possibilities for the prime `2` in the half-integral model.
-/

namespace Towers.NumberTheory.Milne

open Ideal
open Towers.NumberTheory

noncomputable section

/-- The coordinate embedding of the half-integral quadratic order with basis
`1, (1 + sqrt (4 * A + 1)) / 2` into its quadratic algebra over `ℚ`. -/
def halfIntegralEmbedding (A : ℤ) :
    QOrd A 1 →+* QFModel (4 * A + 1) where
  toFun z := ⟨(z.re : ℚ) + (z.im : ℚ) / 2, (z.im : ℚ) / 2⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> norm_num
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;>
      push_cast <;> ring
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      push_cast
      ring
    · simp only [QuadraticAlgebra.im_mul]
      push_cast
      ring

theorem quadratic_half_embedding (A : ℤ) :
    Function.Injective (halfIntegralEmbedding A) := by
  intro x y hxy
  have him := congrArg QuadraticAlgebra.im hxy
  change (x.im : ℚ) / 2 = (y.im : ℚ) / 2 at him
  have him' : (x.im : ℚ) = (y.im : ℚ) := by linarith
  have hre := congrArg QuadraticAlgebra.re hxy
  change (x.re : ℚ) + (x.im : ℚ) / 2 =
    (y.re : ℚ) + (y.im : ℚ) / 2 at hre
  have hre' : (x.re : ℚ) = (y.re : ℚ) := by linarith
  apply QuadraticAlgebra.ext
  · exact Rat.intCast_injective hre'
  · exact Rat.intCast_injective him'

instance quadraticHalfAlgebra (A : ℤ) :
    Algebra (QOrd A 1) (QFModel (4 * A + 1)) :=
  (halfIntegralEmbedding A).toAlgebra

instance quadraticHalfTower (A : ℤ) :
    IsScalarTower ℤ (QOrd A 1) (QFModel (4 * A + 1)) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext z <;> norm_num [halfIntegralEmbedding])

/-- For square-free `4 * A + 1`, the half-integral quadratic order is the full ring of
integers of `ℚ[sqrt (4 * A + 1)]`.  Thus the factorization theorems below really take place
in the maximal order, including when the radicand is `1` modulo `4`. -/
theorem quadratic_half_closure (A : ℤ)
    (hm : Squarefree (4 * A + 1)) :
    IsIntegralClosure (QOrd A 1) ℤ
      (QFModel (4 * A + 1)) where
  algebraMap_injective := quadratic_half_embedding A
  isIntegral_iff {x} := by
    rw [QFModel.integral_half_coordinates
      (4 * A + 1) hm (by omega)]
    constructor
    · rintro ⟨a, b, ha, hb⟩
      refine ⟨(⟨a, b⟩ : QOrd A 1), ?_⟩
      apply QuadraticAlgebra.ext
      · exact ha.symm
      · exact hb.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.re, y.im, rfl, rfl⟩

private theorem splits_simple_mod
    (A B : ℤ) (p : ℕ) [Fact p.Prime] (r : ZMod p)
    (hroot : r ^ 2 = (A : ZMod p) + (B : ZMod p) * r)
    (hsimple : 2 * r ≠ (B : ZMod p)) :
    ∃ a : ℤ,
      (QOrd.rootIdeal A B p a).IsPrime ∧
      (QOrd.rootIdeal A B p (B - a)).IsPrime ∧
      QOrd.rootIdeal A B p a ≠ QOrd.rootIdeal A B p (B - a) ∧
      QOrd.rootIdeal A B p a * QOrd.rootIdeal A B p (B - a) =
        span {(p : QOrd A B)} := by
  obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) r
  have hroot' : (a : ZMod p) ^ 2 =
      (A : ZMod p) + (B : ZMod p) * (a : ZMod p) := by
    simpa using hroot
  have hdiv : (p : ℤ) ∣ a ^ 2 - B * a - A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr (by linear_combination hroot')
  have hnot : ¬(p : ℤ) ∣ 2 * a - B := by
    intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * a - B) p).mpr h
    apply hsimple
    exact sub_eq_zero.mp (by simpa using hz)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hcop : IsCoprime (p : ℤ) (2 * a - B) :=
    hpZ.irreducible.coprime_iff_not_dvd.mpr hnot
  change ∃ u v : ℤ, u * (p : ℤ) + v * (2 * a - B) = 1 at hcop
  obtain ⟨q, hq⟩ := hdiv
  exact ⟨a, QOrd.splits_at_root A B p a ⟨q, hq⟩ (by simpa using hcop)⟩

/-- An integer is a square modulo `p` exactly when an integral square differs from it by a
multiple of `p`. -/
theorem square_zmod_sq (m : ℤ) (p : ℕ) :
    IsSquare (m : ZMod p) ↔ ∃ a : ℤ, (p : ℤ) ∣ a ^ 2 - m := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (Int.castRingHom (ZMod p)) r
    refine ⟨a, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simpa [pow_two] using sub_eq_zero.mpr hr.symm
  · rintro ⟨a, ha⟩
    refine ⟨(a : ZMod p), ?_⟩
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 - m) p).mpr ha
    have haeq : (a : ZMod p) ^ 2 = (m : ZMod p) := by
      exact sub_eq_zero.mp (by simpa [Int.cast_sub, Int.cast_pow] using hz)
    simpa [pow_two] using haeq.symm

/-- Example 3.44(ii), split case: if `m` is a nonzero square modulo the odd prime `p`, then
`(p)` is the product of two distinct prime ideals in the integral-coordinate quadratic order. -/
theorem odd_splits_square
    (m : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : ¬(p : ℤ) ∣ m) (hm : IsSquare (m : ZMod p)) :
    ∃ a : ℤ,
      (QOrd.rootIdeal m 0 p a).IsPrime ∧
      (QOrd.rootIdeal m 0 p (-a)).IsPrime ∧
      QOrd.rootIdeal m 0 p a ≠ QOrd.rootIdeal m 0 p (-a) ∧
      QOrd.rootIdeal m 0 p a * QOrd.rootIdeal m 0 p (-a) =
        span {(p : QOrd m 0)} := by
  obtain ⟨a, ha⟩ := (square_zmod_sq m p).mp hm
  exact ⟨a, QOrd.odd_splits_order m a p hp2 hpm ha⟩

/-- Example 3.44(ii), inert case: if `m` is not a square modulo `p`, then `(p)` remains
prime in the integral-coordinate quadratic order. -/
theorem odd_inert_square
    (m : ℤ) (p : ℕ) [Fact p.Prime] (hm : ¬IsSquare (m : ZMod p)) :
    (span {(p : QOrd m 0)}).IsPrime := by
  apply QOrd.odd_inert_order m p
  intro a ha
  apply hm
  exact (square_zmod_sq m p).mpr ⟨a, ha⟩

/-- The Legendre-symbol form of the split criterion in Example 3.44(ii). -/
theorem splits_legendre_sym
    (m : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : ¬(p : ℤ) ∣ m) (hleg : legendreSym p m = 1) :
    ∃ a : ℤ,
      (QOrd.rootIdeal m 0 p a).IsPrime ∧
      (QOrd.rootIdeal m 0 p (-a)).IsPrime ∧
      QOrd.rootIdeal m 0 p a ≠ QOrd.rootIdeal m 0 p (-a) ∧
      QOrd.rootIdeal m 0 p a * QOrd.rootIdeal m 0 p (-a) =
        span {(p : QOrd m 0)} := by
  apply odd_splits_square m p hp2 hpm
  apply (legendreSym.eq_one_iff p ?_).mp hleg
  intro hm0
  exact hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hm0)

/-- The Legendre-symbol form of the inert criterion in Example 3.44(ii). -/
theorem odd_inert_legendre
    (m : ℤ) (p : ℕ) [Fact p.Prime] (hleg : legendreSym p m = -1) :
    (span {(p : QOrd m 0)}).IsPrime := by
  apply odd_inert_square m p
  exact (legendreSym.eq_neg_one_iff p).mp hleg

/-- Example 3.44(i), in the integral-coordinate model: a prime dividing the square-free
radicand ramifies. -/
theorem ramifies_quadratic_radical
    (m : ℤ) (hm : Squarefree m) (p : ℕ) [Fact p.Prime]
    (hpm : (p : ℤ) ∣ m) :
    (QOrd.rootIdeal m 0 p 0).IsPrime ∧
      QOrd.rootIdeal m 0 p 0 * QOrd.rootIdeal m 0 p 0 =
        span {(p : QOrd m 0)} :=
  QOrd.odd_ramifies_order m hm p hpm

/-- The three factorization types listed in Example 3.44 for an odd rational prime and a
square-free radicand: ramified when `p ∣ m`, and otherwise split or inert according to the
Legendre symbol. -/
theorem odd_factorization_trichotomy
    (m : ℤ) (hm : Squarefree m) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((p : ℤ) ∣ m ∧
      (QOrd.rootIdeal m 0 p 0).IsPrime ∧
      QOrd.rootIdeal m 0 p 0 * QOrd.rootIdeal m 0 p 0 =
        span {(p : QOrd m 0)}) ∨
    (¬(p : ℤ) ∣ m ∧
      ∃ a : ℤ,
        (QOrd.rootIdeal m 0 p a).IsPrime ∧
        (QOrd.rootIdeal m 0 p (-a)).IsPrime ∧
        QOrd.rootIdeal m 0 p a ≠ QOrd.rootIdeal m 0 p (-a) ∧
        QOrd.rootIdeal m 0 p a * QOrd.rootIdeal m 0 p (-a) =
          span {(p : QOrd m 0)}) ∨
    (¬(p : ℤ) ∣ m ∧ (span {(p : QOrd m 0)}).IsPrime) := by
  by_cases hpm : (p : ℤ) ∣ m
  · exact Or.inl ⟨hpm, ramifies_quadratic_radical m hm p hpm⟩
  · have hm0 : (m : ZMod p) ≠ 0 := by
      intro hz
      exact hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hz)
    rcases legendreSym.eq_one_or_neg_one p hm0 with hleg | hleg
    · exact Or.inr <| Or.inl
        ⟨hpm, splits_legendre_sym m p hp2 hpm hleg⟩
    · exact Or.inr <| Or.inr
        ⟨hpm, odd_inert_legendre m p hleg⟩

/-- Example 3.44(ii), split case in the full half-integral order.  Here
`QOrd A 1` has discriminant `4 * A + 1` and basis element
`(1 + sqrt (4 * A + 1)) / 2`. -/
theorem odd_half_square
    (A : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : ¬(p : ℤ) ∣ 4 * A + 1)
    (hm : IsSquare ((4 * A + 1 : ℤ) : ZMod p)) :
    ∃ r : ℤ,
      (QOrd.rootIdeal A 1 p r).IsPrime ∧
      (QOrd.rootIdeal A 1 p (1 - r)).IsPrime ∧
      QOrd.rootIdeal A 1 p r ≠ QOrd.rootIdeal A 1 p (1 - r) ∧
      QOrd.rootIdeal A 1 p r * QOrd.rootIdeal A 1 p (1 - r) =
        span {(p : QOrd A 1)} := by
  obtain ⟨s, hs⟩ := hm
  have hsquare : s ^ 2 = ((4 * A + 1 : ℤ) : ZMod p) := by
    simpa [pow_two] using hs.symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hpd with hp1 | hp2'
    · exact (Fact.out : Nat.Prime p).ne_one hp1
    · exact hp2 hp2'
  let r : ZMod p := (s + 1) / 2
  have hr : r ^ 2 = (A : ZMod p) + ((1 : ℤ) : ZMod p) * r := by
    dsimp [r]
    field_simp [htwo]
    have hsquare' : s ^ 2 = 4 * (A : ZMod p) + 1 := by
      simpa using hsquare
    linear_combination hsquare'
  have hm0 : ((4 * A + 1 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hpm
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * A + 1) p).mp hz
  have hs0 : s ≠ 0 := by
    intro hszero
    apply hm0
    rw [← hsquare, hszero]
    simp
  have hsimple : 2 * r ≠ ((1 : ℤ) : ZMod p) := by
    intro h
    apply hs0
    calc
      s = 2 * r - 1 := by
        dsimp [r]
        field_simp [htwo]
        ring
      _ = 0 := sub_eq_zero.mpr (by simpa using h)
  exact splits_simple_mod A 1 p r hr hsimple

/-- Example 3.44(ii), inert case in the full half-integral order. -/
theorem odd_inert_half
    (A : ℤ) (p : ℕ) [Fact p.Prime]
    (hm : ¬IsSquare ((4 * A + 1 : ℤ) : ZMod p)) :
    (span {(p : QOrd A 1)}).IsPrime := by
  apply QOrd.inert_no_root A 1 p
  intro r hr
  apply hm
  refine ⟨2 * r - 1, ?_⟩
  have hr' : (A : ZMod p) = r ^ 2 - r := by
    apply eq_sub_of_add_eq
    simpa using hr.symm
  calc
    ((4 * A + 1 : ℤ) : ZMod p) = 4 * (A : ZMod p) + 1 := by push_cast; ring
    _ = 4 * (r ^ 2 - r) + 1 := by rw [hr']
    _ = (2 * r - 1) * (2 * r - 1) := by ring

/-- The Legendre-symbol form of splitting in the full half-integral order. -/
theorem odd_legendre_sym
    (A : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpm : ¬(p : ℤ) ∣ 4 * A + 1)
    (hleg : legendreSym p (4 * A + 1) = 1) :
    ∃ r : ℤ,
      (QOrd.rootIdeal A 1 p r).IsPrime ∧
      (QOrd.rootIdeal A 1 p (1 - r)).IsPrime ∧
      QOrd.rootIdeal A 1 p r ≠ QOrd.rootIdeal A 1 p (1 - r) ∧
      QOrd.rootIdeal A 1 p r * QOrd.rootIdeal A 1 p (1 - r) =
        span {(p : QOrd A 1)} := by
  apply odd_half_square A p hp2 hpm
  apply (legendreSym.eq_one_iff p ?_).mp hleg
  intro hm0
  exact hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd (4 * A + 1) p).mp hm0)

/-- The Legendre-symbol form of inertia in the full half-integral order. -/
theorem inert_legendre_sym
    (A : ℤ) (p : ℕ) [Fact p.Prime]
    (hleg : legendreSym p (4 * A + 1) = -1) :
    (span {(p : QOrd A 1)}).IsPrime := by
  apply odd_inert_half A p
  exact (legendreSym.eq_neg_one_iff p).mp hleg

/-- Example 3.44(i), ramification in the full half-integral order.  A prime dividing the
square-free discriminant `4 * A + 1` has one prime divisor whose square is `(p)`. -/
theorem odd_ramifies_discriminant
    (A : ℤ) (hm : Squarefree (4 * A + 1)) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpm : (p : ℤ) ∣ 4 * A + 1) :
    ∃ r : ℤ,
      (QOrd.rootIdeal A 1 p r).IsPrime ∧
      QOrd.rootIdeal A 1 p r * QOrd.rootIdeal A 1 p r =
        span {(p : QOrd A 1)} := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hnot2 : ¬(p : ℤ) ∣ 2 := by
    intro hpd
    have hpdNat : p ∣ 2 := Int.natCast_dvd_natCast.mp (by simpa using hpd)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hpdNat with hp1 | hp2'
    · exact (Fact.out : Nat.Prime p).ne_one hp1
    · exact hp2 hp2'
  have hcop2 : IsCoprime (p : ℤ) 2 :=
    hpZ.irreducible.coprime_iff_not_dvd.mpr hnot2
  obtain ⟨u, v, huv⟩ := hcop2
  let r : ℤ := v
  have ht : 1 - 2 * r = (p : ℤ) * u := by
    dsimp [r]
    nlinarith [huv]
  have hsqdiv : (p : ℤ) ∣ (1 - 2 * r) ^ 2 := by
    obtain ⟨t, ht'⟩ := show (p : ℤ) ∣ 1 - 2 * r from ⟨u, ht⟩
    refine ⟨(p : ℤ) * t ^ 2, ?_⟩
    rw [ht']
    ring
  have hfourN : (p : ℤ) ∣ 4 * (A + r * (1 - r)) := by
    have hd := dvd_sub hpm hsqdiv
    convert hd using 1
    rfl
    ring
  have hnot4 : ¬(p : ℤ) ∣ 4 := by
    intro hp4
    have hp22 : (p : ℤ) ∣ 2 * 2 := by simpa using hp4
    rcases hpZ.dvd_mul.mp hp22 with hp2' | hp2'
    · exact hnot2 hp2'
    · exact hnot2 hp2'
  have hNdiv : (p : ℤ) ∣ A + r * (1 - r) :=
    (hpZ.dvd_mul.mp hfourN).resolve_left hnot4
  obtain ⟨q, hq⟩ := hNdiv
  have hqnot : ¬(p : ℤ) ∣ q := by
    intro hpq
    obtain ⟨s, hs⟩ := hpq
    have hpSq : (p : ℤ) ^ 2 ∣ 4 * A + 1 := by
      refine ⟨u ^ 2 + 4 * s, ?_⟩
      calc
        4 * A + 1 = (1 - 2 * r) ^ 2 + 4 * (A + r * (1 - r)) := by ring
        _ = ((p : ℤ) * u) ^ 2 + 4 * ((p : ℤ) * q) := by rw [ht, hq]
        _ = ((p : ℤ) * u) ^ 2 + 4 * ((p : ℤ) * ((p : ℤ) * s)) := by rw [hs]
        _ = (p : ℤ) ^ 2 * (u ^ 2 + 4 * s) := by ring
    exact hpZ.not_unit (hm (p : ℤ) (by simpa [pow_two] using hpSq))
  have hcopq : IsCoprime (p : ℤ) q :=
    hpZ.irreducible.coprime_iff_not_dvd.mpr hqnot
  change ∃ u v : ℤ, u * (p : ℤ) + v * q = 1 at hcopq
  refine ⟨r, QOrd.ramifies_at_root A 1 p r ⟨q, hq⟩ ⟨u, ht⟩ ?_⟩
  intro q' hq'
  have hqq : q' = q := by
    apply mul_left_cancel₀ hp0
    exact hq'.symm.trans hq
  simpa [hqq] using hcopq

/-- Example 3.44(i)-(ii) in the maximal half-integral order.  For a square-free
`m = 4 * A + 1`, every odd prime ramifies when it divides `m`, and otherwise splits or
stays prime according to the Legendre symbol of `m`. -/
theorem odd_half_trichotomy
    (A : ℤ) (hm : Squarefree (4 * A + 1))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((p : ℤ) ∣ 4 * A + 1 ∧
      ∃ r : ℤ,
        (QOrd.rootIdeal A 1 p r).IsPrime ∧
        QOrd.rootIdeal A 1 p r * QOrd.rootIdeal A 1 p r =
          span {(p : QOrd A 1)}) ∨
    (¬(p : ℤ) ∣ 4 * A + 1 ∧
      ∃ r : ℤ,
        (QOrd.rootIdeal A 1 p r).IsPrime ∧
        (QOrd.rootIdeal A 1 p (1 - r)).IsPrime ∧
        QOrd.rootIdeal A 1 p r ≠ QOrd.rootIdeal A 1 p (1 - r) ∧
        QOrd.rootIdeal A 1 p r * QOrd.rootIdeal A 1 p (1 - r) =
          span {(p : QOrd A 1)}) ∨
    (¬(p : ℤ) ∣ 4 * A + 1 ∧
      (span {(p : QOrd A 1)}).IsPrime) := by
  by_cases hpm : (p : ℤ) ∣ 4 * A + 1
  · exact Or.inl ⟨hpm,
      odd_ramifies_discriminant A hm p hp2 hpm⟩
  · have hm0 : (((4 * A + 1 : ℤ) : ZMod p)) ≠ 0 := by
      intro hz
      exact hpm ((ZMod.intCast_zmod_eq_zero_iff_dvd (4 * A + 1) p).mp hz)
    rcases legendreSym.eq_one_or_neg_one p hm0 with hleg | hleg
    · exact Or.inr <| Or.inl
        ⟨hpm, odd_legendre_sym
          A p hp2 hpm hleg⟩
    · exact Or.inr <| Or.inr
        ⟨hpm, inert_legendre_sym A p hleg⟩

/-- Example 3.44(iii), split case for `m = 8k + 1`. -/
theorem splits_quadratic_eight (k : ℤ) :
    (QOrd.rootIdeal (2 * k) 1 2 0).IsPrime ∧
      (QOrd.rootIdeal (2 * k) 1 2 1).IsPrime ∧
      QOrd.rootIdeal (2 * k) 1 2 0 ≠
        QOrd.rootIdeal (2 * k) 1 2 1 ∧
      QOrd.rootIdeal (2 * k) 1 2 0 *
          QOrd.rootIdeal (2 * k) 1 2 1 =
        span {(2 : QOrd (2 * k) 1)} :=
  QOrd.two_splits_eight k

/-- Example 3.44(iii), inert case for `m = 8k + 5`. -/
theorem inert_eight_five (k : ℤ) :
    (span {(2 : QOrd (2 * k + 1) 1)}).IsPrime :=
  QOrd.two_inert_eight k

/-- Example 3.44(i) at `2`, for a square-free radicand congruent to `2` modulo `4`. -/
theorem ramifies_quadratic_add (k : ℤ) :
    (QOrd.rootIdeal (4 * k + 2) 0 2 0).IsPrime ∧
      QOrd.rootIdeal (4 * k + 2) 0 2 0 *
          QOrd.rootIdeal (4 * k + 2) 0 2 0 =
        span {(2 : QOrd (4 * k + 2) 0)} :=
  QOrd.ramifies_four_add k

/-- Example 3.44(i) at `2`, for a square-free radicand congruent to `3` modulo `4`. -/
theorem ramifies_quadratic_four (k : ℤ) :
    (QOrd.rootIdeal (4 * k + 3) 0 2 (-1)).IsPrime ∧
      QOrd.rootIdeal (4 * k + 3) 0 2 (-1) *
          QOrd.rootIdeal (4 * k + 3) 0 2 (-1) =
        span {(2 : QOrd (4 * k + 3) 0)} :=
  QOrd.ramifies_four_three k

end

end Towers.NumberTheory.Milne

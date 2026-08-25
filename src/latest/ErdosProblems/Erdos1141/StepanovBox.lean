import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

/-!
# Nonvanishing for the quadratic Stepanov construction

A polynomial whose nonzero exponents have residues below `A` modulo the
characteristic has the same property after translation.  Lucas's theorem
therefore bounds every root multiplicity modulo the characteristic.
Two such polynomials cannot cancel after one is multiplied by a half-power
of a polynomial with a simple root.  This is the nonvanishing argument for
the auxiliary polynomial used to estimate quadratic character sums.
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {p A : ℕ}

/-- All nonzero coefficients occur at exponents with small residue modulo `p`. -/
def LowResidueSupport (p A : ℕ) (P : K[X]) : Prop :=
  ∀ n : ℕ, P.coeff n ≠ 0 → n % p < A

theorem choose_cast_eq_zero_of_residue_lt [Fact p.Prime] [CharP K p]
    {n k : ℕ} (h : n % p < k % p) :
    (n.choose k : K) = 0 := by
  have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at hmod
  exact (CharP.cast_eq_zero_iff K p _).mpr (Nat.modEq_zero_iff_dvd.mp hmod)

theorem LowResidueSupport.taylor [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : LowResidueSupport p A P) (x : K) :
    LowResidueSupport p A (taylor x P) := by
  intro k hk
  by_contra hkle
  have hkA : A ≤ k % p := Nat.le_of_not_gt hkle
  apply hk
  rw [taylor_coeff, hasseDeriv_apply, Polynomial.sum_def, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnA := hP n (Polynomial.mem_support_iff.mp hn)
  have hchoose : (n.choose k : K) = 0 := choose_cast_eq_zero_of_residue_lt (hnA.trans_le hkA)
  simp [hchoose]

theorem LowResidueSupport.rootMultiplicity_mod_lt [Fact p.Prime] [CharP K p] {P : K[X]}
    (hP : LowResidueSupport p A P) (hP0 : P ≠ 0) (x : K) :
    P.rootMultiplicity x % p < A := by
  have hT : Polynomial.taylor x P ≠ 0 := (Polynomial.taylor_eq_zero x P).not.mpr hP0
  have hcoeff : (Polynomial.taylor x P).coeff (Polynomial.taylor x P).natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hres := hP.taylor x _ hcoeff
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact hres

theorem rootMultiplicity_neg_eq (P : K[X]) (x : K) :
    (-P).rootMultiplicity x = P.rootMultiplicity x := by
  simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree, neg_comp,
    Polynomial.natTrailingDegree_neg]

theorem rootMultiplicity_pow_eq {f : K[X]} (hf : f ≠ 0) (x : K) (t : ℕ) :
    (f ^ t).rootMultiplicity x = t * f.rootMultiplicity x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf), ih]
    ring

/-- The two halves of the quadratic auxiliary polynomial are independent.
The degree of `f` is unrestricted; only one simple root is needed. -/
theorem add_pow_mul_ne_zero [Fact p.Prime] [CharP K p] {P Q f : K[X]} {x : K} {t : ℕ}
    (hP : LowResidueSupport p A P) (hQ : LowResidueSupport p A Q)
    (hne : P ≠ 0 ∨ Q ≠ 0) (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    P + f ^ t * Q ≠ 0 := by
  intro hzero
  have hQ0 : Q ≠ 0 := by
    intro hQzero
    have hPzero : P = 0 := by simpa [hQzero] using hzero
    exact hne.elim (fun h => h hPzero) (fun h => h hQzero)
  have hP0 : P ≠ 0 := by
    intro hPzero
    have hprod : f ^ t * Q = 0 := by simpa [hPzero] using hzero
    exact mul_ne_zero (pow_ne_zero _ hf) hQ0 hprod
  have hPmod := hP.rootMultiplicity_mod_lt hP0 x
  have hQmod := hQ.rootMultiplicity_mod_lt hQ0 x
  have hmult : P.rootMultiplicity x = t + Q.rootMultiplicity x := by
    rw [eq_neg_of_add_eq_zero_left hzero, rootMultiplicity_neg_eq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hQ0),
      rootMultiplicity_pow_eq hf x t, hx, mul_one]
  have htlt : t < p := by omega
  have hsumlt : t + Q.rootMultiplicity x % p < p := by omega
  have hmod : P.rootMultiplicity x % p = t + Q.rootMultiplicity x % p := by
    rw [hmult, Nat.add_mod, Nat.mod_eq_of_lt htlt, Nat.mod_eq_of_lt hsumlt]
  omega

/-- The exponent of one monomial in the Frobenius coefficient box. -/
def boxExponent (p : ℕ) {A B : ℕ} (i : Fin A × Fin B) : ℕ := i.1 + p * i.2

theorem boxExponent_mod {A B : ℕ} (hA : A ≤ p) (i : Fin A × Fin B) :
    boxExponent p i % p = i.1 := by
  simp [boxExponent, Nat.add_mod, Nat.mod_eq_of_lt (i.1.isLt.trans_le hA)]

theorem boxExponent_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxExponent p : Fin A × Fin B → ℕ) := by
  intro i j hij
  have ha : (i.1 : ℕ) = j.1 := by
    simpa only [boxExponent_mod hA] using congrArg (fun n => n % p) hij
  have hp0 : 0 < p := (Nat.zero_le _).trans_lt (i.1.isLt.trans_le hA)
  have hmul : p * (i.2 : ℕ) = p * (j.2 : ℕ) := by
    simpa only [boxExponent, ha, Nat.add_left_cancel_iff] using hij
  exact Prod.ext (Fin.ext ha) (Fin.ext (Nat.eq_of_mul_eq_mul_left hp0 hmul))

/-- A polynomial with coefficients in a rectangular Frobenius box. -/
noncomputable def boxPolynomial {A B : ℕ} (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B, monomial (boxExponent p i) (a i)

theorem boxPolynomial_coeff {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) (i : Fin A × Fin B) :
    (boxPolynomial (p := p) a).coeff (boxExponent p i) = a i := by
  classical
  rw [boxPolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne := (boxExponent_injective hA).ne hji
    simp [coeff_monomial, hne]
  · simp

theorem boxPolynomial_injective {A B : ℕ} (hA : A ≤ p) :
    Function.Injective (boxPolynomial (K := K) (p := p) (A := A) (B := B)) := by
  intro a b hab
  funext i
  simpa only [boxPolynomial_coeff hA] using
    congrArg (fun P : K[X] => P.coeff (boxExponent p i)) hab

theorem boxPolynomial_lowResidueSupport {A B : ℕ} (hA : A ≤ p)
    (a : Fin A × Fin B → K) : LowResidueSupport p A (boxPolynomial (p := p) a) := by
  classical
  intro n hn
  by_contra hnot
  apply hn
  rw [boxPolynomial, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hne : boxExponent p i ≠ n := by
    intro h
    have : n % p = i.1 := h ▸ boxExponent_mod hA i
    exact hnot (this ▸ i.1.isLt)
  simp [coeff_monomial, hne]

theorem boxPolynomial_ne_zero {A B : ℕ} (hA : A ≤ p)
    {a : Fin A × Fin B → K} (ha : a ≠ 0) : boxPolynomial (p := p) a ≠ 0 := by
  intro h
  apply ha
  apply boxPolynomial_injective (K := K) hA
  simpa [boxPolynomial] using h

theorem box_auxiliary_ne_zero [Fact p.Prime] [CharP K p]
    {A B t : ℕ} {a b : Fin A × Fin B → K}
    (hab : a ≠ 0 ∨ b ≠ 0) {f : K[X]} {x : K}
    (hf : f ≠ 0) (hx : f.rootMultiplicity x = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) :
    boxPolynomial (p := p) a + f ^ t * boxPolynomial (p := p) b ≠ 0 := by
  have hAp : A ≤ p := by omega
  exact add_pow_mul_ne_zero (boxPolynomial_lowResidueSupport hAp a)
    (boxPolynomial_lowResidueSupport hAp b)
    (hab.imp (boxPolynomial_ne_zero hAp) (boxPolynomial_ne_zero hAp))
    hf hx hAt htA

end Pollack17.Stepanov

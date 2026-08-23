import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The polynomial used in Tijdeman's auxiliary-function argument

This scratch development isolates the elementary algebraic and arithmetic facts about

`Delta_h(X) = ((X + 1) ... (X + h)) / h!`.

The normalized derivatives are Hasse derivatives.  Thus they agree, over `ℚ`, with the
ordinary `m`-fold derivative divided by `m!`, but are already defined integrally over `ℤ`.
-/

noncomputable section

open scoped Polynomial

namespace Erdos240Delta

open Finset Polynomial

/-- The integral numerator `(X + 1) ... (X + h)`. -/
def deltaNumeratorInt (h : ℕ) : ℤ[X] :=
  (ascPochhammer ℤ h).comp (X + 1)

/-- The numerator, regarded as a rational polynomial. -/
def deltaNumerator (h : ℕ) : ℚ[X] :=
  (deltaNumeratorInt h).map (Int.castRingHom ℚ)

/-- Tijdeman's polynomial `Delta(X; h) = prod_{1 ≤ i ≤ h} (X+i) / h!`. -/
def delta (h : ℕ) : ℚ[X] :=
  C ((h.factorial : ℚ)⁻¹) * deltaNumerator h

/-- The normalized `m`th derivative of the integral numerator. -/
def deltaHasseNumeratorInt (h m : ℕ) : ℤ[X] :=
  hasseDeriv m (deltaNumeratorInt h)

/-- The normalized `m`th derivative of `Delta(X; h)`. -/
def deltaHasse (h m : ℕ) : ℚ[X] :=
  hasseDeriv m (delta h)

@[simp]
theorem deltaNumeratorInt_zero : deltaNumeratorInt 0 = 1 := by
  simp [deltaNumeratorInt]

theorem natDegree_deltaNumeratorInt (h : ℕ) :
    (deltaNumeratorInt h).natDegree = h := by
  rw [deltaNumeratorInt, Polynomial.natDegree_comp, ascPochhammer_natDegree]
  change h * (X + C (1 : ℤ)).natDegree = h
  rw [Polynomial.natDegree_X_add_C, Nat.mul_one]

theorem deltaNumeratorInt_succ (h : ℕ) :
    deltaNumeratorInt (h + 1) =
      deltaNumeratorInt h * (X + C (h + 1 : ℤ)) := by
  simp only [deltaNumeratorInt, ascPochhammer_succ_right, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.X_comp, Polynomial.natCast_comp]
  congr 1
  ext n
  simp
  ring

theorem map_deltaHasseNumeratorInt (h m : ℕ) :
    (deltaHasseNumeratorInt h m).map (Int.castRingHom ℚ) =
      hasseDeriv m (deltaNumerator h) := by
  ext n
  simp [deltaHasseNumeratorInt, deltaNumerator, hasseDeriv_coeff]

theorem deltaHasse_eq (h m : ℕ) :
    deltaHasse h m =
      C ((h.factorial : ℚ)⁻¹) *
        (deltaHasseNumeratorInt h m).map (Int.castRingHom ℚ) := by
  ext n
  simp [deltaHasse, delta, deltaHasseNumeratorInt, deltaNumerator,
    hasseDeriv_coeff]
  ring

/-- Multiplication by `h!` clears every coefficient denominator of every
normalized derivative. -/
theorem factorial_mul_deltaHasse_eq_map (h m : ℕ) :
    C (h.factorial : ℚ) * deltaHasse h m =
      (deltaHasseNumeratorInt h m).map (Int.castRingHom ℚ) := by
  rw [deltaHasse_eq]
  ext n
  simp
  field_simp

/-- Hasse differentiation is ordinary repeated differentiation divided by `m!`.
The scalar action here is the natural-number scalar action on `ℚ[X]`. -/
theorem factorial_smul_deltaHasse (h m : ℕ) :
    m.factorial • deltaHasse h m =
      (derivative^[m]) (delta h) := by
  simpa [deltaHasse] using
    congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℚ) m) (delta h)

theorem factorial_mul_eval_deltaHasse (h m : ℕ) (x : ℚ) :
    (m.factorial : ℚ) * (deltaHasse h m).eval x =
      ((derivative^[m]) (delta h)).eval x := by
  have he := congrArg (fun p : ℚ[X] ↦ p.eval x) (factorial_smul_deltaHasse h m)
  simpa [nsmul_eq_mul] using he

theorem natDegree_deltaHasseNumeratorInt_le (h m : ℕ) :
    (deltaHasseNumeratorInt h m).natDegree ≤ h - m := by
  calc
    (deltaHasseNumeratorInt h m).natDegree ≤ (deltaNumeratorInt h).natDegree - m :=
      Polynomial.natDegree_hasseDeriv_le _ _
    _ = h - m := by rw [natDegree_deltaNumeratorInt]

theorem natDegree_map_deltaHasseNumeratorInt_le (h m : ℕ) :
    ((deltaHasseNumeratorInt h m).map (Int.castRingHom ℚ)).natDegree ≤ h - m :=
  Polynomial.natDegree_map_le.trans (natDegree_deltaHasseNumeratorInt_le h m)

theorem deltaNumerator_eq (h : ℕ) :
    deltaNumerator h = (ascPochhammer ℚ h).comp (X + 1) := by
  simp [deltaNumerator, deltaNumeratorInt, Polynomial.map_comp]

theorem deltaNumerator_succ (h : ℕ) :
    deltaNumerator (h + 1) =
      deltaNumerator h * (X + C (h + 1 : ℚ)) := by
  simp [deltaNumerator, deltaNumeratorInt_succ]

theorem eval_deltaNumerator_eq_prod (h : ℕ) (x : ℚ) :
    (deltaNumerator h).eval x =
      ∏ i ∈ Finset.range h, (x + (i + 1 : ℕ)) := by
  induction h with
  | zero => simp [deltaNumerator]
  | succ h ih =>
      rw [deltaNumerator_succ, Polynomial.eval_mul, Finset.prod_range_succ, ih]
      simp [Nat.cast_add, Nat.cast_one]

theorem eval_delta_eq_prod (h : ℕ) (x : ℚ) :
    (delta h).eval x =
      (h.factorial : ℚ)⁻¹ * ∏ i ∈ Finset.range h, (x + (i + 1 : ℕ)) := by
  simp [delta, eval_deltaNumerator_eq_prod]

theorem eval_delta (h : ℕ) (x : ℚ) :
    (delta h).eval x =
      (h.factorial : ℚ)⁻¹ * (ascPochhammer ℚ h).eval (x + 1) := by
  simp [delta, deltaNumerator_eq, Polynomial.eval_comp]

/-- At nonnegative integral arguments, `Delta_h` is a binomial coefficient. -/
theorem eval_delta_nat (h n : ℕ) :
    (delta h).eval (n : ℚ) = ((n + h).choose h : ℚ) := by
  rw [eval_delta, show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num,
    ascPochhammer_nat_eq_natCast_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  simp only [Nat.cast_mul]
  field_simp

theorem eval_delta_nat_nonneg (h n : ℕ) :
    0 ≤ (delta h).eval (n : ℚ) := by
  rw [eval_delta_nat]
  positivity

/-- A simple size bound which is already a little sharper than
`Delta_h(n) ≤ (n+h)^h`. -/
theorem eval_delta_nat_le_pow (h n : ℕ) :
    (delta h).eval (n : ℚ) ≤ (n + 1 : ℚ) ^ h := by
  rw [eval_delta_nat]
  exact_mod_cast Nat.choose_add_le_add_one_pow n h

/-- Homogenization gives the general denominator-clearing fact for integral
polynomials.  If `deg p ≤ d`, then `q^d p(z/q)` is an integer. -/
theorem exists_int_pow_mul_eval_map (p : ℤ[X]) (d q : ℕ) (z : ℤ)
    (hp : p.natDegree ≤ d) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ d * (p.map (Int.castRingHom ℚ)).eval ((z : ℚ) / q) = (w : ℚ) := by
  let w : ℤ := MvPolynomial.eval ![z, (q : ℤ)] (p.homogenize d)
  refine ⟨w, ?_⟩
  have hp' : (p.map (Int.castRingHom ℚ)).natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hp
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have he := Polynomial.eval_homogenize (K := ℚ) hp'
    ![(z : ℚ), (q : ℚ)] (by simpa using hq')
  rw [Polynomial.homogenize_map] at he
  have hw : (w : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) ![(z : ℚ), (q : ℚ)] (p.homogenize d) := by
    dsimp [w]
    have hc := MvPolynomial.eval₂_comp (Int.castRingHom ℚ)
      ![z, (q : ℤ)] (p.homogenize d)
    have hv : (⇑(Int.castRingHom ℚ) ∘ ![z, (q : ℤ)]) =
        ![(z : ℚ), (q : ℚ)] := by
      funext i
      fin_cases i <;> simp
    rw [hv] at hc
    exact hc
  have he' :
      (q : ℚ) ^ d * (p.map (Int.castRingHom ℚ)).eval ((z : ℚ) / q) =
        MvPolynomial.eval₂ (Int.castRingHom ℚ)
          ![(z : ℚ), (q : ℚ)] (p.homogenize d) := by
    simpa [mul_comm] using he.symm
  exact he'.trans hw.symm

/-- The sharp elementary denominator bound for the normalized derivatives:
if `x = z/q`, then `q^(h-m) h! Delta_h^[m](x)` is an integer. -/
theorem exists_int_cleared_deltaHasse (h m q : ℕ) (z : ℤ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (h - m) * (h.factorial : ℚ) *
          (deltaHasse h m).eval ((z : ℚ) / q) = (w : ℚ) := by
  obtain ⟨w, hw⟩ := exists_int_pow_mul_eval_map
    (deltaHasseNumeratorInt h m) (h - m) q z
    (natDegree_deltaHasseNumeratorInt_le h m) hq
  refine ⟨w, ?_⟩
  rw [deltaHasse_eq, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    (q : ℚ) ^ (h - m) * (h.factorial : ℚ) *
          ((h.factorial : ℚ)⁻¹ *
            ((deltaHasseNumeratorInt h m).map (Int.castRingHom ℚ)).eval
              ((z : ℚ) / q)) =
        (q : ℚ) ^ (h - m) *
          ((deltaHasseNumeratorInt h m).map (Int.castRingHom ℚ)).eval
            ((z : ℚ) / q) := by
      field_simp
    _ = (w : ℚ) := hw

/-- A version phrased without choosing a presentation for `x`: it suffices
that `q*x` is an integer. -/
theorem exists_int_cleared_deltaHasse_of_mul_eq_int
    (h m q : ℕ) (x : ℚ) (z : ℤ) (hq : q ≠ 0)
    (hx : (q : ℚ) * x = (z : ℚ)) :
    ∃ w : ℤ,
      (q : ℚ) ^ (h - m) * (h.factorial : ℚ) *
          (deltaHasse h m).eval x = (w : ℚ) := by
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hx' : x = (z : ℚ) / q := by
    apply (eq_div_iff hq').2
    simpa [mul_comm] using hx
  rw [hx']
  exact exists_int_cleared_deltaHasse h m q z hq

/-- In particular, `q^h h! Delta_h(z/q)` is integral. -/
theorem exists_int_cleared_delta (h q : ℕ) (z : ℤ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ h * (h.factorial : ℚ) *
          (delta h).eval ((z : ℚ) / q) = (w : ℚ) := by
  simpa [deltaHasse] using exists_int_cleared_deltaHasse h 0 q z hq

end Erdos240Delta

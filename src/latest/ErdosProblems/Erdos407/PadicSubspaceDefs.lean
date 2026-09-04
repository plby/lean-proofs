/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.PadicProduct
import ErdosProblems.Erdos407.GeneralPosition

/-!
# Elementary definitions for the rational `{infinity, 2, 3}` Subspace Theorem

This file develops the exact rational specialization of Schlickewei's
Subspace Theorem which is used for Erdős Problem 407.  Norms are rational
valued, so all local products remain in `ℚ`; no coercion to real numbers is
needed in the arithmetic application.

The elementary material in the first part is also useful independently of
the deep finite-cover argument: positivity and multiplicativity of the three
local norms, the Archimedean box height, rational hyperplanes, and the
absorption of every bounded-height exceptional set into finitely many proper
hyperplanes in dimension at least two.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators

/-- The three places of `ℚ` which may be nontrivial on a `{2,3}`-unit. -/
abbrev Place23 := Fin 3

namespace Place23

/-- The ordinary Archimedean place. -/
def infinite : Place23 := 0

/-- The `2`-adic place. -/
def two : Place23 := 1

/-- The `3`-adic place. -/
def three : Place23 := 2

end Place23

/-- The normalized absolute value at one of `infinity`, `2`, and `3`. -/
def placeNorm : Place23 → ℚ → ℚ
  | 0 => fun q => |q|
  | 1 => padicNorm 2
  | 2 => padicNorm 3

@[simp] theorem placeNorm_infinite (q : ℚ) : placeNorm .infinite q = |q| := rfl
@[simp] theorem placeNorm_two (q : ℚ) : placeNorm .two q = padicNorm 2 q := rfl
@[simp] theorem placeNorm_three (q : ℚ) : placeNorm .three q = padicNorm 3 q := rfl

@[simp] theorem placeNorm_zero (v : Place23) : placeNorm v 0 = 0 := by
  rcases v with ⟨v, hv⟩
  interval_cases v <;> simp [placeNorm]

@[simp] theorem placeNorm_one (v : Place23) : placeNorm v 1 = 1 := by
  rcases v with ⟨v, hv⟩
  interval_cases v <;> simp [placeNorm]

theorem placeNorm_nonneg (v : Place23) (q : ℚ) : 0 ≤ placeNorm v q := by
  fin_cases v
  · exact abs_nonneg q
  · exact padicNorm.nonneg q
  · exact padicNorm.nonneg q

@[simp] theorem placeNorm_eq_zero_iff (v : Place23) (q : ℚ) :
    placeNorm v q = 0 ↔ q = 0 := by
  fin_cases v
  · simp [placeNorm]
  · change padicNorm 2 q = 0 ↔ q = 0
    exact ⟨padicNorm.zero_of_padicNorm_eq_zero, fun h => by simp [h]⟩
  · change padicNorm 3 q = 0 ↔ q = 0
    exact ⟨padicNorm.zero_of_padicNorm_eq_zero, fun h => by simp [h]⟩

theorem placeNorm_pos_iff (v : Place23) (q : ℚ) :
    0 < placeNorm v q ↔ q ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_eq, eq_comm, placeNorm_eq_zero_iff]
  simp [placeNorm_nonneg]

theorem placeNorm_mul (v : Place23) (q r : ℚ) :
    placeNorm v (q * r) = placeNorm v q * placeNorm v r := by
  fin_cases v
  · exact abs_mul q r
  · exact padicNorm.mul q r
  · exact padicNorm.mul q r

theorem placeNorm_neg (v : Place23) (q : ℚ) : placeNorm v (-q) = placeNorm v q := by
  rcases v with ⟨v, hv⟩
  interval_cases v <;> simp [placeNorm]

/-- The product over our three named places is the usual restricted
three-place norm product. -/
theorem prod_placeNorm_eq_threePlaceProduct (q : ℚ) :
    (∏ v : Place23, placeNorm v q) = PadicProduct.normProduct23 q := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [placeNorm, PadicProduct.normProduct23, PadicProduct.archNorm]
  ring

/-- A nonzero integer has restricted norm product at least one.  Equivalently,
the local factors at all primes other than `2` and `3`, which are omitted from
`normProduct23`, can only decrease the full product formula. -/
theorem one_le_threePlaceProduct_int {z : ℤ} (hz : z ≠ 0) :
    1 ≤ PadicProduct.normProduct23 (z : ℚ) := by
  let n : ℕ := z.natAbs
  let a : ℕ := padicValNat 2 n
  let b : ℕ := padicValNat 3 n
  have hn : n ≠ 0 := by simpa [n] using hz
  have h2 : 2 ^ a ∣ n := by
    simpa [a] using (pow_padicValNat_dvd (p := 2) (n := n))
  have h3 : 3 ^ b ∣ n := by
    simpa [b] using (pow_padicValNat_dvd (p := 3) (n := n))
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) :=
    (by norm_num : Nat.Coprime 2 3).pow a b
  have hdvd : 2 ^ a * 3 ^ b ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd h2 h3
  have hleN : 2 ^ a * 3 ^ b ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hleQ : ((2 ^ a * 3 ^ b : ℕ) : ℚ) ≤ n := by
    exact_mod_cast hleN
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [PadicProduct.normProduct23, PadicProduct.archNorm,
    padicNorm.eq_zpow_of_nonzero hzQ, padicNorm.eq_zpow_of_nonzero hzQ,
    padicValRat.of_int, padicValRat.of_int]
  change 1 ≤ |(z : ℚ)| * (2 : ℚ) ^ (-(a : ℤ)) * (3 : ℚ) ^ (-(b : ℤ))
  rw [show |(z : ℚ)| = (n : ℚ) by simp [n], zpow_neg, zpow_neg,
    zpow_natCast, zpow_natCast]
  have hden : (0 : ℚ) < (2 ^ a * 3 ^ b : ℕ) := by positivity
  rw [inv_eq_one_div, inv_eq_one_div]
  calc
    1 ≤ (n : ℚ) / ((2 ^ a * 3 ^ b : ℕ) : ℚ) :=
      (one_le_div hden).2 hleQ
    _ = (n : ℚ) * (1 / (2 : ℚ) ^ a) * (1 / (3 : ℚ) ^ b) := by
      push_cast
      field_simp

/-- Clearing the canonical denominator of a nonzero rational number gives
an integral value, so its restricted norm product is bounded below by the
reciprocal denominator contribution.  This is the product-formula estimate
used to bound local logarithmic exponents for a fixed rational linear form. -/
theorem one_le_normProduct23_mul_den {q : ℚ} (hq : q ≠ 0) :
    1 ≤ PadicProduct.normProduct23 q *
      PadicProduct.normProduct23 (q.den : ℚ) := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hnum : q.num ≠ 0 := by
    intro hzero
    apply hq
    rw [← q.num_div_den, hzero]
    simp
  rw [← PadicProduct.normProduct23_mul, Rat.mul_den_eq_num]
  exact one_le_threePlaceProduct_int hnum

/-- On a nonnegative integer, the restricted norm product is no larger than
the Archimedean factor. -/
theorem normProduct23_natCast_le (d : ℕ) :
    PadicProduct.normProduct23 (d : ℚ) ≤ d := by
  have h2 : padicNorm 2 (d : ℚ) ≤ 1 := by
    simpa only [Int.cast_natCast] using
      (padicNorm.of_int (p := 2) (d : ℤ))
  have h3 : padicNorm 3 (d : ℚ) ≤ 1 := by
    simpa only [Int.cast_natCast] using
      (padicNorm.of_int (p := 3) (d : ℤ))
  have h2nonneg : 0 ≤ padicNorm 2 (d : ℚ) := padicNorm.nonneg _
  have h3nonneg : 0 ≤ padicNorm 3 (d : ℚ) := padicNorm.nonneg _
  rw [PadicProduct.normProduct23, PadicProduct.archNorm,
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ d)]
  calc
    (d : ℚ) * padicNorm 2 (d : ℚ) * padicNorm 3 (d : ℚ) ≤
        (d : ℚ) * 1 * padicNorm 3 (d : ℚ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h2 (by positivity)) h3nonneg
    _ ≤ (d : ℚ) * 1 * 1 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (d : ℚ) := by ring

/-- A rational linear form in `n` variables. -/
abbrev RatLinearForm (n : ℕ) := (Fin n → ℚ) →ₗ[ℚ] ℚ

/-- Evaluate all local bases of forms on a rational point and multiply all
`3n` resulting local norms. -/
def localFormProduct {n : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → ℚ) : ℚ :=
  ∏ v, ∏ i, placeNorm v (L v i x)

theorem localFormProduct_nonneg {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (x : Fin n → ℚ) :
    0 ≤ localFormProduct L x := by
  exact Finset.prod_nonneg fun v _ => Finset.prod_nonneg fun i _ =>
    placeNorm_nonneg v (L v i x)

/-- The Archimedean box height of an integral vector.  The empty-dimensional
value is set to zero; all applications have positive dimension. -/
def boxHeight {n : ℕ} (x : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun i => (x i).natAbs

@[simp] theorem boxHeight_zero {n : ℕ} : boxHeight (0 : Fin n → ℤ) = 0 := by
  simp [boxHeight]

theorem natAbs_le_boxHeight {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    (x i).natAbs ≤ boxHeight x := by
  exact Finset.le_sup (s := Finset.univ) (f := fun j => (x j).natAbs)
    (Finset.mem_univ i)

theorem boxHeight_pos {n : ℕ} {x : Fin n → ℤ} (hx : x ≠ 0) :
    0 < boxHeight x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have habs : 0 < (x i).natAbs := Int.natAbs_pos.mpr hi
  exact habs.trans_le (natAbs_le_boxHeight x i)

theorem eq_zero_of_boxHeight_eq_zero {n : ℕ} {x : Fin n → ℤ}
    (hx : boxHeight x = 0) : x = 0 := by
  by_contra hne
  have := boxHeight_pos hne
  omega

/-- Coordinatewise coercion from an integral vector. -/
def intCastVec {n : ℕ} (x : Fin n → ℤ) : Fin n → ℚ := fun i => x i

@[simp] theorem intCastVec_apply {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    intCastVec x i = (x i : ℚ) := rfl

theorem intCastVec_injective {n : ℕ} :
    Function.Injective (intCastVec : (Fin n → ℤ) → Fin n → ℚ) := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- The strong, fixed-exponent inequality arising from a projectively
normalized `{2,3}`-unit equation.  It is written without division so it also
has a useful literal meaning at the zero vector. -/
def SatisfiesStrongInequality {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (x : Fin n → ℤ) : Prop :=
  localFormProduct L (intCastVec x) * boxHeight x ≤ 1

/-- A rational hyperplane presented by a nonzero coefficient vector. -/
def OnHyperplane {n : ℕ} (b : Fin n → ℚ) (x : Fin n → ℤ) : Prop :=
  ∑ i, b i * (x i : ℚ) = 0

/-- A finite family of proper rational hyperplanes covers a set of integral
points. -/
def HasFiniteHyperplaneCover {n : ℕ} (X : Set (Fin n → ℤ)) : Prop :=
  ∃ B : Finset (Fin n → ℚ),
    (∀ b ∈ B, b ≠ 0) ∧ ∀ x ∈ X, ∃ b ∈ B, OnHyperplane b x

/-- The local form bases are nonsingular at every one of the three places. -/
def IsNonsingularFamily {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : Prop :=
  ∀ v, LinearIndependent ℚ (L v)

/-- Primitive nonzero integral solutions of the strong Subspace-Theorem
inequality. -/
def primitiveStrongSolutions {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : Set (Fin n → ℤ) :=
  {x | PadicProduct.IsPrimitive x ∧ x ≠ 0 ∧ SatisfiesStrongInequality L x}

/-- Coefficients of a linear form in the standard coordinate basis. -/
def coefficientVector {n : ℕ} (f : RatLinearForm n) : Fin n → ℚ :=
  fun i => f (Pi.single i 1)

/-- A fixed common denominator for the coefficients of a rational linear
form.  The product is used instead of the lcm because it makes divisibility
through finite sums immediate. -/
def linearFormDenominator {n : ℕ} (f : RatLinearForm n) : ℕ :=
  ∏ i, (coefficientVector f i).den

/-- The `ℓ¹` coefficient size of a rational form at one of the three places. -/
def linearFormPlaceConstant {n : ℕ} (v : Place23)
    (f : RatLinearForm n) : ℚ :=
  ∑ i, placeNorm v (coefficientVector f i)

theorem linearFormPlaceConstant_nonneg {n : ℕ} (v : Place23)
    (f : RatLinearForm n) : 0 ≤ linearFormPlaceConstant v f := by
  exact Finset.sum_nonneg fun i _ => placeNorm_nonneg v _

theorem linearFormDenominator_pos {n : ℕ} (f : RatLinearForm n) :
    0 < linearFormDenominator f := by
  unfold linearFormDenominator
  exact Finset.prod_pos fun i _ => (coefficientVector f i).den_pos

private theorem den_sum_dvd_prod_den {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → ℚ) :
    (∑ i ∈ s, q i).den ∣ ∏ i ∈ s, (q i).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

private theorem prod_dvd_prod_of_pointwise {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ s, a i ∣ b i) :
    (∏ i ∈ s, a i) ∣ ∏ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact Nat.mul_dvd_mul (h i (by simp))
        (ih fun j hj => h j (by simp [hj]))

/-- Evaluation of a linear form is the dot product with its coefficient
vector. -/
theorem linearForm_eq_dotProduct {n : ℕ} (f : RatLinearForm n)
    (x : Fin n → ℚ) :
    f x = ∑ i, coefficientVector f i * x i := by
  classical
  have hx : x = ∑ i, x i • Pi.single i (1 : ℚ) := by
    funext j
    simp [Pi.single_apply]
  calc
    f x = f (∑ i, x i • Pi.single i (1 : ℚ)) := congrArg f hx
    _ = ∑ i, f (x i • Pi.single i (1 : ℚ)) := by rw [map_sum]
    _ = ∑ i, coefficientVector f i * x i := by
      simp [map_smul, coefficientVector, mul_comm]

/-- At every retained place, evaluation of a fixed rational form at a
nonzero integral vector is bounded by its fixed coefficient size times the
Archimedean box height.  At the finite places the stronger height-free bound
is used internally; the displayed uniform form is convenient for logarithmic
boxing. -/
theorem placeNorm_linearForm_le_constant_mul_boxHeight {n : ℕ}
    (v : Place23) (f : RatLinearForm n) (x : Fin n → ℤ) (hx : x ≠ 0) :
    placeNorm v (f (intCastVec x)) ≤
      linearFormPlaceConstant v f * boxHeight x := by
  classical
  have hHnat : 1 ≤ boxHeight x := boxHeight_pos hx
  have hH : (1 : ℚ) ≤ boxHeight x := by exact_mod_cast hHnat
  fin_cases v
  · change |f (intCastVec x)| ≤
      (∑ i, |coefficientVector f i|) * boxHeight x
    rw [linearForm_eq_dotProduct]
    calc
      |∑ i, coefficientVector f i * (x i : ℚ)| ≤
          ∑ i, |coefficientVector f i * (x i : ℚ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |coefficientVector f i| * (x i).natAbs := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      _ ≤ ∑ i, |coefficientVector f i| * boxHeight x := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left
            (by exact_mod_cast natAbs_le_boxHeight x i) (abs_nonneg _)
      _ = (∑ i, |coefficientVector f i|) * boxHeight x := by
        rw [← Finset.sum_mul]
  · change padicNorm 2 (f (intCastVec x)) ≤
      (∑ i, padicNorm 2 (coefficientVector f i)) * boxHeight x
    rw [linearForm_eq_dotProduct]
    have hcoeff (i : Fin n) : padicNorm 2 (coefficientVector f i) ≤
        ∑ j, padicNorm 2 (coefficientVector f j) :=
      Finset.single_le_sum (fun j _ => padicNorm.nonneg _) (Finset.mem_univ i)
    have hsum : padicNorm 2 (∑ i, coefficientVector f i * (x i : ℚ)) ≤
        ∑ i, padicNorm 2 (coefficientVector f i) := by
      apply padicNorm.sum_le'
      · intro i _
        rw [padicNorm.mul]
        calc
          padicNorm 2 (coefficientVector f i) * padicNorm 2 (x i : ℚ) ≤
              padicNorm 2 (coefficientVector f i) * 1 :=
            mul_le_mul_of_nonneg_left
              (by simpa only [Int.cast_natCast] using
                (padicNorm.of_int (p := 2) (x i)))
              (padicNorm.nonneg _)
          _ ≤ ∑ j, padicNorm 2 (coefficientVector f j) := by
            simpa using hcoeff i
      · exact Finset.sum_nonneg fun i _ => padicNorm.nonneg _
    exact hsum.trans (le_mul_of_one_le_right
      (Finset.sum_nonneg fun i _ => padicNorm.nonneg _) hH)
  · change padicNorm 3 (f (intCastVec x)) ≤
      (∑ i, padicNorm 3 (coefficientVector f i)) * boxHeight x
    rw [linearForm_eq_dotProduct]
    have hcoeff (i : Fin n) : padicNorm 3 (coefficientVector f i) ≤
        ∑ j, padicNorm 3 (coefficientVector f j) :=
      Finset.single_le_sum (fun j _ => padicNorm.nonneg _) (Finset.mem_univ i)
    have hsum : padicNorm 3 (∑ i, coefficientVector f i * (x i : ℚ)) ≤
        ∑ i, padicNorm 3 (coefficientVector f i) := by
      apply padicNorm.sum_le'
      · intro i _
        rw [padicNorm.mul]
        calc
          padicNorm 3 (coefficientVector f i) * padicNorm 3 (x i : ℚ) ≤
              padicNorm 3 (coefficientVector f i) * 1 :=
            mul_le_mul_of_nonneg_left
              (by simpa only [Int.cast_natCast] using
                (padicNorm.of_int (p := 3) (x i)))
              (padicNorm.nonneg _)
          _ ≤ ∑ j, padicNorm 3 (coefficientVector f j) := by
            simpa using hcoeff i
      · exact Finset.sum_nonneg fun i _ => padicNorm.nonneg _
    exact hsum.trans (le_mul_of_one_le_right
      (Finset.sum_nonneg fun i _ => padicNorm.nonneg _) hH)

/-- Evaluating a fixed rational linear form on an integral vector introduces
no denominator beyond the fixed product of its coefficient denominators. -/
theorem linearForm_value_den_dvd {n : ℕ} (f : RatLinearForm n)
    (x : Fin n → ℤ) :
    (f (intCastVec x)).den ∣ linearFormDenominator f := by
  rw [linearForm_eq_dotProduct]
  have hsum := den_sum_dvd_prod_den Finset.univ
    (fun i => coefficientVector f i * (x i : ℚ))
  refine hsum.trans ?_
  unfold linearFormDenominator
  apply prod_dvd_prod_of_pointwise
  intro i _
  exact (Rat.mul_den_dvd _ _).trans (by simp)

/-- Product-formula lower bound for a nonzero value of a fixed rational
linear form.  Crucially, the right factor is independent of the integral
point; this is what gives a uniform lower endpoint for logarithmic boxes. -/
theorem one_le_normProduct23_linearForm_mul_denominator {n : ℕ}
    (f : RatLinearForm n) (x : Fin n → ℤ)
    (hfx : f (intCastVec x) ≠ 0) :
    1 ≤ PadicProduct.normProduct23 (f (intCastVec x)) *
      linearFormDenominator f := by
  let q : ℚ := f (intCastVec x)
  have hbase := one_le_normProduct23_mul_den (q := q) hfx
  have hdenD : q.den ≤ linearFormDenominator f :=
    Nat.le_of_dvd (linearFormDenominator_pos f)
      (linearForm_value_den_dvd f x)
  have hnormDen : PadicProduct.normProduct23 (q.den : ℚ) ≤
      linearFormDenominator f :=
    (normProduct23_natCast_le q.den).trans (by exact_mod_cast hdenD)
  have hqnonneg : 0 ≤ PadicProduct.normProduct23 q := by
    unfold PadicProduct.normProduct23 PadicProduct.archNorm
    exact mul_nonneg
      (mul_nonneg (abs_nonneg q) (padicNorm.nonneg q))
      (padicNorm.nonneg q)
  exact hbase.trans (mul_le_mul_of_nonneg_left hnormDen hqnonneg)

theorem coefficientVector_ne_zero {n : ℕ} {f : RatLinearForm n}
    (hf : f ≠ 0) : coefficientVector f ≠ 0 := by
  intro hcoeff
  apply hf
  apply LinearMap.ext
  intro x
  rw [linearForm_eq_dotProduct]
  simp [hcoeff]

theorem linearFormPlaceConstant_pos {n : ℕ} (v : Place23)
    {f : RatLinearForm n} (hf : f ≠ 0) :
    0 < linearFormPlaceConstant v f := by
  have hcoeff : coefficientVector f ≠ 0 := coefficientVector_ne_zero hf
  obtain ⟨i, hi⟩ : ∃ i, coefficientVector f i ≠ 0 := by
    by_contra h
    push Not at h
    exact hcoeff (funext h)
  have hterm : 0 < placeNorm v (coefficientVector f i) :=
    (placeNorm_pos_iff v _).2 hi
  exact hterm.trans_le (by
    unfold linearFormPlaceConstant
    exact Finset.single_le_sum
      (fun j _ => placeNorm_nonneg v (coefficientVector f j))
      (Finset.mem_univ i))

/-- The points on which at least one form vanishes are already covered by
the finitely many kernels of the given forms. -/
theorem zeroLocalForm_hasFiniteHyperplaneCover {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : ∀ v i, L v i ≠ 0) :
    HasFiniteHyperplaneCover
      {x : Fin n → ℤ | ∃ v i, L v i (intCastVec x) = 0} := by
  classical
  let B : Finset (Fin n → ℚ) :=
    Finset.univ.biUnion fun v => Finset.univ.image fun i => coefficientVector (L v i)
  refine ⟨B, ?_, ?_⟩
  · intro b hb
    simp only [B, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hb
    obtain ⟨v, i, _hi, rfl⟩ := hb
    exact coefficientVector_ne_zero (hL v i)
  · intro x hx
    obtain ⟨v, i, hzero⟩ := hx
    refine ⟨coefficientVector (L v i), ?_, ?_⟩
    · simp [B]
    · rw [OnHyperplane, ← linearForm_eq_dotProduct]
      exact hzero

/-! ## Elementary finite-height and hyperplane lemmas -/

/-- Integral vectors of bounded box height form a finite set. -/
theorem finite_boxHeight_le {n H : ℕ} :
    {x : Fin n → ℤ | boxHeight x ≤ H}.Finite := by
  let I : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  have hsub : {x : Fin n → ℤ | boxHeight x ≤ H} ⊆
      Set.univ.pi (fun _ : Fin n => (I : Set ℤ)) := by
    intro x hx i _hiUniv
    have hi : (x i).natAbs ≤ H := (natAbs_le_boxHeight x i).trans hx
    have hiZ : ((x i).natAbs : ℤ) ≤ H := by exact_mod_cast hi
    have hupper : x i ≤ (x i).natAbs := Int.le_natAbs
    have hlower' : -(x i) ≤ (x i).natAbs := by
      simpa using (Int.le_natAbs (a := -(x i)))
    have hlower : -(H : ℤ) ≤ x i := by omega
    exact (Finset.mem_Icc.mpr ⟨hlower, hupper.trans hiZ⟩)
  exact (Set.Finite.pi fun _ => I.finite_toSet).subset hsub

/-- In dimension at least two, every nonzero rational point lies on a proper
rational hyperplane. -/
theorem exists_nonzero_form_vanishes {n : ℕ} (hn : 2 ≤ n)
    {x : Fin n → ℚ} (hx : x ≠ 0) :
    ∃ b : Fin n → ℚ, b ≠ 0 ∧ (∑ i, b i * x i) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have hn' : 1 < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hn' i
  let b : Fin n → ℚ := fun k =>
    if k = i then x j else if k = j then -x i else 0
  have hbj : b j = -x i := by simp [b, hji]
  have hb : b ≠ 0 := by
    intro hb0
    have := congrFun hb0 j
    simp [hbj, hi] at this
  refine ⟨b, hb, ?_⟩
  classical
  have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin n)) := by simp [hji]
  let f : Fin n → ℚ := fun k => b k * x k
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≠ i := by
      exact fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1 h
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [f, b, hki, hkj]
  have hiSum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hjSum := Finset.sum_erase_add (Finset.univ.erase i) f hjmem
  change ∑ k, f k = 0
  rw [← hiSum, ← hjSum, hrest]
  simp [f, b, hji]
  ring

/-- Any finite set of nonzero integral points in dimension at least two is
contained in a finite union of proper rational hyperplanes. -/
theorem finite_hasFiniteHyperplaneCover {n : ℕ} (hn : 2 ≤ n)
    {X : Set (Fin n → ℤ)} (hX : X.Finite) (hzero : (0 : Fin n → ℤ) ∉ X) :
    HasFiniteHyperplaneCover X := by
  classical
  choose b hb hvan using fun x : X =>
    exists_nonzero_form_vanishes hn
      (x := intCastVec x.1) (fun h => by
        have hx0 : x.1 = 0 := by
          apply intCastVec_injective
          funext i
          simpa [intCastVec] using congrFun h i
        apply hzero
        simpa [hx0] using x.2)
  let : Fintype X := hX.fintype
  let SX : Finset X := Finset.univ
  let B : Finset (Fin n → ℚ) := SX.image b
  refine ⟨B, ?_, ?_⟩
  · intro c hc
    simp only [B, Finset.mem_image] at hc
    obtain ⟨x, _hx, rfl⟩ := hc
    exact hb x
  · intro x hx
    let sx : X := ⟨x, hx⟩
    refine ⟨b sx, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨sx, by simp [SX], rfl⟩
    · exact hvan sx

/-- Consequently, every bounded-height set of nonzero integral points is
absorbed by finitely many proper hyperplanes. -/
theorem bounded_hasFiniteHyperplaneCover {n H : ℕ} (hn : 2 ≤ n) :
    HasFiniteHyperplaneCover
      {x : Fin n → ℤ | x ≠ 0 ∧ boxHeight x ≤ H} := by
  apply finite_hasFiniteHyperplaneCover hn
  · exact finite_boxHeight_le.subset fun _ hx => hx.2
  · simp

/-- Hyperplane covers are preserved when the covered set is made smaller. -/
theorem HasFiniteHyperplaneCover.mono {n : ℕ} {X Y : Set (Fin n → ℤ)}
    (hY : HasFiniteHyperplaneCover Y) (hXY : X ⊆ Y) :
    HasFiniteHyperplaneCover X := by
  obtain ⟨B, hB, hcover⟩ := hY
  exact ⟨B, hB, fun x hx => hcover x (hXY hx)⟩

/-- The union of two finitely hyperplane-covered sets is finitely
hyperplane-covered. -/
theorem HasFiniteHyperplaneCover.union {n : ℕ} {X Y : Set (Fin n → ℤ)}
    (hX : HasFiniteHyperplaneCover X) (hY : HasFiniteHyperplaneCover Y) :
    HasFiniteHyperplaneCover (X ∪ Y) := by
  classical
  obtain ⟨B, hB, hBX⟩ := hX
  obtain ⟨C, hC, hCY⟩ := hY
  refine ⟨B ∪ C, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_union.mp hb with hbB | hbC
    · exact hB b hbB
    · exact hC b hbC
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨b, hb, hbx⟩ := hBX x hx
      exact ⟨b, Finset.mem_union_left C hb, hbx⟩
    · obtain ⟨b, hb, hbx⟩ := hCY x hx
      exact ⟨b, Finset.mem_union_right B hb, hbx⟩

/-- It is enough to prove the analytic Subspace-Theorem conclusion above one
fixed height: the finitely many smaller nonzero integral points can be added
to the exceptional hyperplanes. -/
theorem hasFiniteHyperplaneCover_of_above {n H : ℕ} (hn : 2 ≤ n)
    {X : Set (Fin n → ℤ)} (hzero : (0 : Fin n → ℤ) ∉ X)
    (habove : HasFiniteHyperplaneCover {x | x ∈ X ∧ H < boxHeight x}) :
    HasFiniteHyperplaneCover X := by
  let Xsmall : Set (Fin n → ℤ) := {x | x ∈ X ∧ boxHeight x ≤ H}
  let Xlarge : Set (Fin n → ℤ) := {x | x ∈ X ∧ H < boxHeight x}
  have hsmall : HasFiniteHyperplaneCover Xsmall :=
    (bounded_hasFiniteHyperplaneCover (H := H) hn).mono fun x hx =>
      ⟨fun hx0 => hzero (hx0 ▸ hx.1), hx.2⟩
  have hlarge : HasFiniteHyperplaneCover Xlarge := habove
  apply (hsmall.union hlarge).mono
  intro x hx
  by_cases hle : boxHeight x ≤ H
  · exact Or.inl ⟨hx, hle⟩
  · exact Or.inr ⟨hx, lt_of_not_ge hle⟩

/-- The precise large-height statement which remains after all bounded
exceptions have been discharged. -/
def HasLargeHeightSubspaceConclusion {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : Prop :=
  ∃ H : ℕ, HasFiniteHyperplaneCover
    {x | x ∈ primitiveStrongSolutions L ∧ H < boxHeight x}

/-- A large-height form of the theorem immediately gives the full form. -/
theorem finiteCover_of_largeHeightConclusion {n : ℕ} (hn : 2 ≤ n)
    {L : Place23 → Fin n → RatLinearForm n}
    (hlarge : HasLargeHeightSubspaceConclusion L) :
    HasFiniteHyperplaneCover (primitiveStrongSolutions L) := by
  obtain ⟨H, hH⟩ := hlarge
  exact hasFiniteHyperplaneCover_of_above hn
    (by simp [primitiveStrongSolutions]) hH

/-!
The remaining theorem is the specialized rational p-adic Subspace Theorem.
Its proof proceeds through approximation domains, adelic successive minima,
the auxiliary polynomial constructed using Siegel's lemma, and the
generalized Roth index estimate.  Those components are kept in separate
files so that their exact algebraic and analytic invariants can be checked
independently.
-/

end Erdos407.PadicSubspace

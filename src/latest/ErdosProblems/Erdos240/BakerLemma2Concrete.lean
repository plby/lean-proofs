/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerAdmissibleParameters
import ErdosProblems.Erdos240.BakerAuxiliary
import ErdosProblems.Erdos240.BakerSourceState
import ErdosProblems.Erdos240.IntegerValuedPolynomial

/-!
# Concrete initialization of the van der Poorten--Loxton auxiliary system

This file instantiates the source-shaped matrix of `BakerAuxiliary` at level
zero.  In particular, its columns have the literal side lengths

`L₋₁, L₀, (Lᵢ)ᵢ<n, Lₙ`,

and its rows are the pairs consisting of an integer point
`1 ≤ l ≤ R(0)` and a multi-index of total weight at most `S(0)`.

The integrality proof below uses the sharp normalization
`lcmUpto(h) ^ (m₀ + ... + m_{n-1})`.  No exponent proportional to the
degree of a powered Delta polynomial is introduced.
-/

noncomputable section

open scoped BigOperators Polynomial

namespace Erdos240.BakerLemma2Concrete

open Finset
open Erdos240
open Erdos240.BakerAuxiliary
open Erdos240.DeltaPower
open Erdos240.IntegerValuedPolynomial

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The literal level-zero coefficient box, definitionally identified with
the canonical source state propagated by Lemmas 3--6. -/
abbrev initialBoxShape {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : BoxShape oldRank :=
  Erdos240.BakerSourceState.levelBoxShape P 0

/-- The exact initial integral radius `R(0)`. -/
def initialRadius {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ := P.R 0

/-- The exact initial total derivative budget `S(0)`. -/
def initialBudget {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ := P.Slevel 0

@[simp] theorem initialBoxShape_shiftMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (initialBoxShape P).shiftMax = P.LminusOne := rfl

@[simp] theorem initialBoxShape_deltaMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (initialBoxShape P).deltaMax = P.Lzero := rfl

@[simp] theorem initialBoxShape_oldMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (initialBoxShape P).oldMax = P.LiZero := by
  funext i
  simp [initialBoxShape, Erdos240.BakerSourceState.levelBoxShape]

@[simp] theorem initialBoxShape_lastMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (initialBoxShape P).lastMax = P.LlastZero := by
  simp [initialBoxShape, Erdos240.BakerSourceState.levelBoxShape]

@[simp] theorem initialRadius_eq {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : initialRadius P = P.R 0 := rfl

@[simp] theorem initialBudget_eq {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : initialBudget P = P.Slevel 0 := rfl

/-- A signed-integer version of the elementary powered-Delta size bound.
Unlike the deliberately coarse fixed-base estimate in `DeltaPower`, this
retains polynomial dependence on the argument, which is essential when the
argument contains a source coefficient bounded by `Bsrc`. -/
theorem abs_poweredDeltaHasse_eval_int_le_pow
    (h lambda m : ℕ) (z : ℤ) :
    |(poweredDeltaHasse h lambda m).eval (z : ℚ)| ≤
      ((z.natAbs + 1 + h : ℕ) : ℚ) ^ (h * lambda) := by
  let p : ℚ[X] := poweredDeltaHasse h lambda m
  have hp : CoeffNonneg p := by
    exact (coeffNonneg_poweredDelta h lambda).hasseDeriv m
  have habsEval : |p.eval (z : ℚ)| ≤ p.eval (z.natAbs : ℚ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
    calc
      |∑ i ∈ p.support, p.coeff i * (z : ℚ) ^ i| ≤
          ∑ i ∈ p.support, |p.coeff i * (z : ℚ) ^ i| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ p.support, p.coeff i * (z.natAbs : ℚ) ^ i := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [abs_mul, abs_pow, abs_of_nonneg (hp i)]
            norm_num
  have hnext : p.eval (z.natAbs : ℚ) ≤
      (poweredDelta h lambda).eval ((z.natAbs + 1 : ℕ) : ℚ) := by
    exact poweredDeltaHasse_eval_nat_le_next h lambda m z.natAbs
  have hchoose :
      (poweredDelta h lambda).eval ((z.natAbs + 1 : ℕ) : ℚ) =
        (((z.natAbs + 1 + h).choose h : ℕ) : ℚ) ^ lambda := by
    simp only [poweredDelta, Polynomial.eval_pow, Erdos240Delta.eval_delta_nat]
  calc
    |(poweredDeltaHasse h lambda m).eval (z : ℚ)| = |p.eval (z : ℚ)| := rfl
    _ ≤ p.eval (z.natAbs : ℚ) := habsEval
    _ ≤ (poweredDelta h lambda).eval ((z.natAbs + 1 : ℕ) : ℚ) := hnext
    _ = (((z.natAbs + 1 + h).choose h : ℕ) : ℚ) ^ lambda := hchoose
    _ ≤ (((z.natAbs + 1 + h) ^ h : ℕ) : ℚ) ^ lambda := by
      gcongr
      exact_mod_cast Nat.choose_le_pow (z.natAbs + 1 + h) h
    _ = ((z.natAbs + 1 + h : ℕ) : ℚ) ^ (h * lambda) := by
      norm_num [pow_mul]

/-- The literal sharp integral matrix for the initial source equations. -/
def initialIntegralConstraintModel {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ) :
    IntegralConstraintModel
      (radius := initialRadius P) (budget := initialBudget P)
      (L := initialBoxShape P) P.h b bLast alpha alphaLast :=
  IntegralConstraintModel.ofSourceData P.h b bLast alpha alphaLast

/-- Every initial row point lies in the literal interval `1, ..., R(0)`. -/
theorem initial_row_point_le_radius {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P)) :
    row.point ≤ initialRadius P := by
  exact Nat.succ_le_iff.mpr row.pointIndex.isLt

/-- Coordinate bounds read directly from the complete initial box. -/
theorem initial_lambda_shift_lt_h {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (lambda : LambdaBox (initialBoxShape P)) :
    lambda.shift < P.h := by
  simpa only [LambdaBox.shift, initialBoxShape_shiftMax,
    P.LminusOne_add_one_eq_h] using lambda.shiftIndex.isLt

theorem initial_lambda_deltaIndex_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (lambda : LambdaBox (initialBoxShape P)) :
    lambda.deltaIndex ≤ P.Lzero := by
  exact Nat.le_of_lt_succ lambda.deltaIndexFin.isLt

theorem initial_lambda_oldExponent_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (lambda : LambdaBox (initialBoxShape P)) (r : Fin oldRank) :
    lambda.oldExponent r ≤ P.LiZero r := by
  change (lambda.oldExponentFin r : ℕ) ≤ P.LiZero r
  simpa only [initialBoxShape_oldMax] using
    Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt

theorem initial_lambda_lastExponent_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (lambda : LambdaBox (initialBoxShape P)) :
    lambda.lastExponent ≤ P.LlastZero := by
  change (lambda.lastExponentFin : ℕ) ≤ P.LlastZero
  simpa only [initialBoxShape_lastMax] using
    Nat.le_of_lt_succ lambda.lastExponentFin.isLt

/-- The signed constant argument in an old Delta factor is controlled by
the source coefficient cutoff and the two visible exponent sides. -/
theorem natAbs_old_delta_argument_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LambdaBox (initialBoxShape P)) (r : Fin oldRank) :
    (bLast * lambda.oldExponent r -
        b r * lambda.lastExponent).natAbs ≤
      P.Bsrc * (P.LiZero r + P.LlastZero) := by
  calc
    (bLast * lambda.oldExponent r -
          b r * lambda.lastExponent).natAbs ≤
        (bLast * lambda.oldExponent r).natAbs +
          (b r * lambda.lastExponent).natAbs :=
      Int.natAbs_sub_le _ _
    _ = bLast.natAbs * lambda.oldExponent r +
          (b r).natAbs * lambda.lastExponent := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ P.Bsrc * P.LiZero r + P.Bsrc * P.LlastZero := by
      exact Nat.add_le_add
        (Nat.mul_le_mul hbLast (initial_lambda_oldExponent_le P lambda r))
        (Nat.mul_le_mul (hb r) (initial_lambda_lastExponent_le P lambda))
    _ = P.Bsrc * (P.LiZero r + P.LlastZero) := by
      rw [Nat.mul_add]

/-- A common base for all of the source's two-argument old-coordinate
Delta factors.  Their degrees are the row orders, whose *sum* is bounded by
`initialBudget`; no fixed old side length occurs as a polynomial degree. -/
def initialOldDeltaBaseNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  P.Bsrc * ((∑ r : Fin oldRank, P.LiZero r) + P.LlastZero) +
    initialBudget P + 1

/-- A literal integral majorant for the Delta-polynomial portion of every
initial matrix entry.  It deliberately retains all source parameters; the
later logarithmic estimate may simplify it without obscuring the exact
entrywise argument.  The old-coordinate contribution has exponent only the
total derivative budget, exactly as in the source estimate
`(2B)^(m₁+⋯+mₙ₋₁)`. -/
def initialDeltaMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  (18 * P.h) ^ (P.h * (P.Lzero + 1)) *
    (initialOldDeltaBaseNat P) ^ initialBudget P

/-- The exponential monomial portion of an initial row is largest at the
upper endpoint of every exponent side and at the endpoint `R(0)`. -/
def initialMonomialMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  (∏ r : Fin oldRank,
      P.old r ^ (P.LiZero r * initialRadius P)) *
    P.newPrime ^ (P.LlastZero * initialRadius P)

def initialRationalEntryMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  initialDeltaMajorantNat P * initialMonomialMajorantNat P

def initialMatrixMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  Nat.lcmUpto P.h ^ initialBudget P * initialRationalEntryMajorantNat P

/-- The source-faithful cleared-head majorant.  The lcm normalization is
combined with the head derivative before estimating, avoiding the spurious
`log h` loss of a coefficientwise polynomial bound. -/
def initialClearedHeadMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  4 ^ (P.h * initialBudget P +
    (P.Lzero + 1) * (18 * P.h))

/-- Majorant for the product of ordinary old-coordinate Delta factors.
The factorial in each two-argument Delta is retained.  The elementary bound
`choose (L + m) m ≤ 2 ^ (L + m)` separates the total row order from the
sum of the old exponent sides. -/
def initialOldDeltaSharpMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  (2 * P.Bsrc) ^ initialBudget P *
    2 ^ (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero))

/-- Complete source-faithful majorant for the already integral initial
matrix. -/
def initialSourceMatrixMajorantNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  (max (4 ^ P.h) (2 * P.Bsrc)) ^ initialBudget P *
    4 ^ ((P.Lzero + 1) * (18 * P.h)) *
      2 ^ (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) *
        initialMonomialMajorantNat P

/-- Uniform bound for the first (moving integral-point) Delta factor. -/
theorem abs_initial_head_delta_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    |(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
        (row.order none)).eval
          (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)| ≤
      ((18 * P.h : ℕ) : ℚ) ^ (P.h * (P.Lzero + 1)) := by
  have hraw := abs_poweredDeltaHasse_eval_int_le_pow
    P.h (lambda.deltaIndex + 1) (row.order none)
      ((row.point : ℤ) + lambda.shift)
  have hz :
      ((row.point : ℤ) + lambda.shift).natAbs =
        row.point + lambda.shift := by
    have hcast : (row.point : ℤ) + (lambda.shift : ℤ) =
        ((row.point + lambda.shift : ℕ) : ℤ) := by norm_num
    rw [hcast]
    exact Int.natAbs_ofNat' _
  have hpoint := initial_row_point_le_radius P row
  have hshift := initial_lambda_shift_lt_h P lambda
  have hpoint' : row.point ≤ 16 * P.h := by
    simpa only [initialRadius, VDPLParameters.R, pow_zero, Nat.mul_one] using
      hpoint
  have hsum : row.point + (lambda.shift + 1 + P.h) ≤
      16 * P.h + (P.h + P.h) :=
    Nat.add_le_add hpoint'
      (Nat.add_le_add (Nat.succ_le_of_lt hshift) le_rfl)
  have hbase :
      ((row.point : ℤ) + lambda.shift).natAbs + 1 + P.h ≤ 18 * P.h := by
    rw [hz]
    calc
      row.point + lambda.shift + 1 + P.h =
          row.point + (lambda.shift + 1 + P.h) := by omega
      _ ≤ 16 * P.h + (P.h + P.h) := hsum
      _ = 18 * P.h := by omega
  have hexp : P.h * (lambda.deltaIndex + 1) ≤
      P.h * (P.Lzero + 1) :=
    Nat.mul_le_mul_left P.h (Nat.add_le_add_right
      (initial_lambda_deltaIndex_le P lambda) 1)
  have hbaseOne : 1 ≤ 18 * P.h := by
    have := P.h_pos
    omega
  have hpowNat :
      (((row.point : ℤ) + lambda.shift).natAbs + 1 + P.h) ^
          (P.h * (lambda.deltaIndex + 1)) ≤
        (18 * P.h) ^ (P.h * (P.Lzero + 1)) := by
    calc
      (((row.point : ℤ) + lambda.shift).natAbs + 1 + P.h) ^
            (P.h * (lambda.deltaIndex + 1)) ≤
          (18 * P.h) ^ (P.h * (lambda.deltaIndex + 1)) :=
        Nat.pow_le_pow_left hbase _
      _ ≤ (18 * P.h) ^ (P.h * (P.Lzero + 1)) :=
        Nat.pow_le_pow_right hbaseOne hexp
  exact hraw.trans (by exact_mod_cast hpowNat)

/-- Uniform bound for the source's ordinary two-argument Delta polynomial at
a signed integer.  Its degree is `m`, not `h * L`. -/
theorem abs_delta_eval_int_le_pow (m : ℕ) (z : ℤ) :
    |(Erdos240Delta.delta m).eval (z : ℚ)| ≤
      (((z.natAbs + m + 1 : ℕ) : ℚ) ^ m) := by
  rw [Erdos240Delta.eval_delta_eq_prod, abs_mul, abs_prod]
  have hfactorial : |((m.factorial : ℚ)⁻¹)| ≤ 1 := by
    rw [abs_inv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ m.factorial)]
    exact (inv_le_one₀ (by positivity)).2 (by exact_mod_cast m.factorial_pos)
  have hprod :
      ∏ i ∈ Finset.range m, |(z : ℚ) + (i + 1 : ℕ)| ≤
        (((z.natAbs + m + 1 : ℕ) : ℚ) ^ m) := by
    calc
      ∏ i ∈ Finset.range m, |(z : ℚ) + (i + 1 : ℕ)| ≤
          ∏ _i ∈ Finset.range m,
            ((z.natAbs + m + 1 : ℕ) : ℚ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          have him : i + 1 ≤ m := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
          calc
            |(z : ℚ) + (i + 1 : ℕ)| ≤
                |(z : ℚ)| + |((i + 1 : ℕ) : ℚ)| := abs_add_le _ _
            _ = ((z.natAbs + (i + 1) : ℕ) : ℚ) := by
              rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ (i + 1 : ℕ))]
              norm_num
            _ ≤ ((z.natAbs + m + 1 : ℕ) : ℚ) := by
              exact_mod_cast Nat.add_le_add_left (him.trans (Nat.le_succ m)) z.natAbs
      _ = (((z.natAbs + m + 1 : ℕ) : ℚ) ^ m) := by simp
  calc
    |((m.factorial : ℚ)⁻¹)| *
          ∏ i ∈ Finset.range m, |(z : ℚ) + (i + 1 : ℕ)| ≤
        1 * (((z.natAbs + m + 1 : ℕ) : ℚ) ^ m) :=
      mul_le_mul hfactorial hprod (by positivity) (by norm_num)
    _ = (((z.natAbs + m + 1 : ℕ) : ℚ) ^ m) := one_mul _

/-- Factorial-sensitive form of the preceding estimate.  If `|z| ≤ B L`,
then the source's two-argument Delta is bounded by
`B^m * choose (L+m) m`. -/
theorem abs_delta_eval_int_le_pow_mul_choose
    (m B L : ℕ) (z : ℤ) (hB : 1 ≤ B) (hz : z.natAbs ≤ B * L) :
    |(Erdos240Delta.delta m).eval (z : ℚ)| ≤
      (B : ℚ) ^ m * ((L + m).choose m : ℚ) := by
  rw [Erdos240Delta.eval_delta_eq_prod, abs_mul, abs_inv,
    abs_of_nonneg (by positivity : (0 : ℚ) ≤ m.factorial), abs_prod]
  have hprod :
      ∏ i ∈ Finset.range m, |(z : ℚ) + (i + 1 : ℕ)| ≤
        ((B ^ m * (L + 1).ascFactorial m : ℕ) : ℚ) := by
    calc
      ∏ i ∈ Finset.range m, |(z : ℚ) + (i + 1 : ℕ)| ≤
          ∏ i ∈ Finset.range m, ((B * (L + (i + 1)) : ℕ) : ℚ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          have hiB : i + 1 ≤ B * (i + 1) := by
            simpa only [one_mul] using Nat.mul_le_mul_right (i + 1) hB
          have hnat : z.natAbs + (i + 1) ≤ B * (L + (i + 1)) := by
            calc
              z.natAbs + (i + 1) ≤ B * L + B * (i + 1) :=
                Nat.add_le_add hz hiB
              _ = B * (L + (i + 1)) := by ring
          calc
            |(z : ℚ) + (i + 1 : ℕ)| ≤
                |(z : ℚ)| + |((i + 1 : ℕ) : ℚ)| := abs_add_le _ _
            _ = ((z.natAbs + (i + 1) : ℕ) : ℚ) := by
              rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ (i + 1 : ℕ))]
              norm_num
            _ ≤ ((B * (L + (i + 1)) : ℕ) : ℚ) := by exact_mod_cast hnat
      _ = ((B ^ m * (L + 1).ascFactorial m : ℕ) : ℚ) := by
        norm_cast
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_range]
        congr 1
        rw [Nat.ascFactorial_eq_prod_range]
        apply Finset.prod_congr rfl
        intro i hi
        omega
  calc
    (m.factorial : ℚ)⁻¹ *
          ∏ i ∈ Finset.range m, |(z : ℚ) + (i + 1 : ℕ)| ≤
        (m.factorial : ℚ)⁻¹ *
          ((B ^ m * (L + 1).ascFactorial m : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (B : ℚ) ^ m * ((L + m).choose m : ℚ) := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose]
      push_cast
      field_simp

/-- Binary-binomial consequence in the form used for the product over old
coordinates.  This is the estimate appearing in the source: the row order
contributes to the common base `2B`, while the side length contributes only
a power of `2`. -/
theorem abs_delta_eval_int_le_pow_mul_budgetSide
    (m B L : ℕ) (z : ℤ) (hB : 1 ≤ B) (hz : z.natAbs ≤ B * L) :
    |(Erdos240Delta.delta m).eval (z : ℚ)| ≤
      ((2 * B : ℕ) : ℚ) ^ m * (2 : ℚ) ^ L := by
  refine (abs_delta_eval_int_le_pow_mul_choose m B L z hB hz).trans ?_
  have hchoose : (L + m).choose m ≤ 2 ^ (L + m) :=
    Nat.choose_le_two_pow _ _
  calc
    (B : ℚ) ^ m * ((L + m).choose m : ℚ) ≤
        (B : ℚ) ^ m * ((2 ^ (L + m) : ℕ) : ℚ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hchoose) (by positivity)
    _ = ((2 * B : ℕ) : ℚ) ^ m * (2 : ℚ) ^ L := by
      push_cast
      rw [pow_add]
      ring

/-- Uniform bound for one old-coordinate two-argument Delta factor. -/
theorem abs_initial_old_delta_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) (r : Fin oldRank) :
    |(Erdos240Delta.delta (row.order (some r))).eval
          ((bLast * lambda.oldExponent r -
            b r * lambda.lastExponent : ℤ) : ℚ)| ≤
      ((initialOldDeltaBaseNat P : ℕ) : ℚ) ^ (row.order (some r)) := by
  let z : ℤ := bLast * lambda.oldExponent r -
    b r * lambda.lastExponent
  have hraw := abs_delta_eval_int_le_pow (row.order (some r)) z
  have hLiSum : P.LiZero r ≤ ∑ i : Fin oldRank, P.LiZero i :=
    Finset.single_le_sum (fun i _ ↦ Nat.zero_le (P.LiZero i))
      (Finset.mem_univ r)
  have horder : row.order (some r) ≤ initialBudget P :=
    (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (row.order i))
      (Finset.mem_univ (some r))).trans row.weight_le
  have hbase : z.natAbs + row.order (some r) + 1 ≤
      initialOldDeltaBaseNat P := by
    unfold initialOldDeltaBaseNat
    dsimp only [z]
    have hz := natAbs_old_delta_argument_le P b bLast hb hbLast lambda r
    have hside :
        P.Bsrc * (P.LiZero r + P.LlastZero) ≤
          P.Bsrc * ((∑ i : Fin oldRank, P.LiZero i) + P.LlastZero) :=
      Nat.mul_le_mul_left P.Bsrc (Nat.add_le_add_right hLiSum P.LlastZero)
    omega
  have hpowNat :
      (z.natAbs + row.order (some r) + 1) ^ (row.order (some r)) ≤
        initialOldDeltaBaseNat P ^ (row.order (some r)) :=
    Nat.pow_le_pow_left hbase _
  exact hraw.trans (by exact_mod_cast hpowNat)

/-- The head denominator and head powered derivative, estimated together in
the sharp source normalization. -/
theorem initial_cleared_head_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    sourceRowDenominator P.h row *
        |(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
          (row.order none)).eval
            (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)| ≤
      (initialClearedHeadMajorantNat P : ℚ) := by
  have hraw :=
    lcmUpto_pow_mul_abs_poweredDeltaHasse_eval_nat_le_four_pow
      P.h (lambda.deltaIndex + 1) (row.order none)
        (row.point + lambda.shift) P.h_pos
  have harg :
      (((row.point : ℤ) + lambda.shift : ℤ) : ℚ) =
        ((row.point + lambda.shift : ℕ) : ℚ) := by norm_num
  have hheadOrder : row.order none ≤ initialBudget P :=
    (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (row.order i))
      (Finset.mem_univ none)).trans row.weight_le
  have hpoint := initial_row_point_le_radius P row
  have hshift := initial_lambda_shift_lt_h P lambda
  have hpoint' : row.point ≤ 16 * P.h := by
    simpa only [initialRadius, VDPLParameters.R, pow_zero, Nat.mul_one] using
      hpoint
  have hargBound : row.point + lambda.shift + P.h ≤ 18 * P.h := by
    omega
  have hlambda : lambda.deltaIndex + 1 ≤ P.Lzero + 1 :=
    Nat.add_le_add_right (initial_lambda_deltaIndex_le P lambda) 1
  have hexp :
      P.h * row.order none +
          (lambda.deltaIndex + 1) * (row.point + lambda.shift + P.h) ≤
        P.h * initialBudget P + (P.Lzero + 1) * (18 * P.h) := by
    exact Nat.add_le_add
      (Nat.mul_le_mul_left P.h hheadOrder)
      (Nat.mul_le_mul hlambda hargBound)
  unfold sourceRowDenominator initialClearedHeadMajorantNat
  rw [harg]
  exact hraw.trans (by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 4) hexp)

/-- The same cleared-head estimate with the actual head row order retained.
This is the form needed to combine it with the old-coordinate orders before
using the total-budget bound. -/
theorem initial_cleared_head_le_split {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    sourceRowDenominator P.h row *
        |(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
          (row.order none)).eval
            (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)| ≤
      ((4 ^ P.h : ℕ) : ℚ) ^ row.order none *
        (4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h)) := by
  have hraw :=
    lcmUpto_pow_mul_abs_poweredDeltaHasse_eval_nat_le_four_pow
      P.h (lambda.deltaIndex + 1) (row.order none)
        (row.point + lambda.shift) P.h_pos
  have harg :
      (((row.point : ℤ) + lambda.shift : ℤ) : ℚ) =
        ((row.point + lambda.shift : ℕ) : ℚ) := by norm_num
  have hpoint := initial_row_point_le_radius P row
  have hshift := initial_lambda_shift_lt_h P lambda
  have hpoint' : row.point ≤ 16 * P.h := by
    simpa only [initialRadius, VDPLParameters.R, pow_zero, Nat.mul_one] using
      hpoint
  have hargBound : row.point + lambda.shift + P.h ≤ 18 * P.h := by
    omega
  have hlambda : lambda.deltaIndex + 1 ≤ P.Lzero + 1 :=
    Nat.add_le_add_right (initial_lambda_deltaIndex_le P lambda) 1
  have hside :
      (lambda.deltaIndex + 1) * (row.point + lambda.shift + P.h) ≤
        (P.Lzero + 1) * (18 * P.h) :=
    Nat.mul_le_mul hlambda hargBound
  unfold sourceRowDenominator
  rw [harg]
  refine hraw.trans ?_
  rw [pow_add, pow_mul]
  have hsideQ :
      (4 : ℚ) ^ ((lambda.deltaIndex + 1) *
          (row.point + lambda.shift + P.h)) ≤
        (4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 4) hside
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  exact mul_le_mul le_rfl hsideQ (by positivity) (by positivity)

/-- Row-specific source estimate for the product of ordinary old-coordinate
Delta factors.  Both the actual sum of old row orders and the exact sum of
old exponent sides are retained. -/
theorem abs_initial_old_delta_product_le_rowSharp {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    |∏ r : Fin oldRank,
        (Erdos240Delta.delta (row.order (some r))).eval
          ((bLast * lambda.oldExponent r -
            b r * lambda.lastExponent : ℤ) : ℚ)| ≤
      (((2 * P.Bsrc : ℕ) : ℚ) ^
          (∑ r : Fin oldRank, row.order (some r))) *
        (2 : ℚ) ^
          (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) := by
  have hB : 1 ≤ P.Bsrc := by
    have hBreal : (1 : ℝ) ≤ P.Bsrc :=
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
    exact_mod_cast hBreal
  have hfactor (r : Fin oldRank) :
      |(Erdos240Delta.delta (row.order (some r))).eval
          ((bLast * lambda.oldExponent r -
            b r * lambda.lastExponent : ℤ) : ℚ)| ≤
        (((2 * P.Bsrc : ℕ) : ℚ) ^ row.order (some r)) *
          (2 : ℚ) ^ (P.LiZero r + P.LlastZero) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      abs_delta_eval_int_le_pow_mul_budgetSide
        (row.order (some r)) P.Bsrc (P.LiZero r + P.LlastZero)
        (bLast * lambda.oldExponent r - b r * lambda.lastExponent)
        hB (natAbs_old_delta_argument_le P b bLast hb hbLast lambda r)
  rw [abs_prod]
  calc
    ∏ r : Fin oldRank,
        |(Erdos240Delta.delta (row.order (some r))).eval
          ((bLast * lambda.oldExponent r -
            b r * lambda.lastExponent : ℤ) : ℚ)| ≤
      ∏ r : Fin oldRank,
        ((((2 * P.Bsrc : ℕ) : ℚ) ^ row.order (some r)) *
          (2 : ℚ) ^ (P.LiZero r + P.LlastZero)) :=
      Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun r _ ↦ hfactor r)
    _ = (((2 * P.Bsrc : ℕ) : ℚ) ^
          (∑ r : Fin oldRank, row.order (some r))) *
        (2 : ℚ) ^
          (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Finset.prod_pow_eq_pow_sum]

/-- Product estimate for all ordinary old-coordinate Delta factors, retaining
their factorial denominators. -/
theorem abs_initial_old_delta_product_le_sharp {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    |∏ r : Fin oldRank,
        (Erdos240Delta.delta (row.order (some r))).eval
          ((bLast * lambda.oldExponent r -
            b r * lambda.lastExponent : ℤ) : ℚ)| ≤
      (initialOldDeltaSharpMajorantNat P : ℚ) := by
  have hsumOrder :
      (∑ r : Fin oldRank, row.order (some r)) ≤ initialBudget P := by
    calc
      (∑ r : Fin oldRank, row.order (some r)) ≤
          row.order none + ∑ r : Fin oldRank, row.order (some r) :=
        Nat.le_add_left _ _
      _ = row.weight := row.weight_eq_head_add_sum.symm
      _ ≤ initialBudget P := row.weight_le
  refine (abs_initial_old_delta_product_le_rowSharp
    P b bLast hb hbLast row lambda).trans ?_
  unfold initialOldDeltaSharpMajorantNat
  push_cast
  have hB : 1 ≤ P.Bsrc := by
    have hBreal : (1 : ℝ) ≤ P.Bsrc :=
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
    exact_mod_cast hBreal
  have hbase : (1 : ℚ) ≤ 2 * (P.Bsrc : ℚ) := by
    exact_mod_cast (show 1 ≤ 2 * P.Bsrc by omega)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hbase hsumOrder)
    (by positivity)

/-- Product form of the two preceding Delta estimates. -/
theorem abs_initial_sourceDeltaFactor_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    |sourceDeltaFactor P.h b bLast row lambda| ≤
      (initialDeltaMajorantNat P : ℚ) := by
  have hhead := abs_initial_head_delta_le P row lambda
  have hsumOrder :
      (∑ r : Fin oldRank, row.order (some r)) ≤ initialBudget P := by
    calc
      (∑ r : Fin oldRank, row.order (some r)) ≤
          row.order none + ∑ r : Fin oldRank, row.order (some r) :=
        Nat.le_add_left _ _
      _ = row.weight := row.weight_eq_head_add_sum.symm
      _ ≤ initialBudget P := row.weight_le
  have hbaseOne : 1 ≤ initialOldDeltaBaseNat P := by
    unfold initialOldDeltaBaseNat
    omega
  have hold :
      |∏ r : Fin oldRank,
          (Erdos240Delta.delta (row.order (some r))).eval
              ((bLast * lambda.oldExponent r -
                b r * lambda.lastExponent : ℤ) : ℚ)| ≤
        ((initialOldDeltaBaseNat P : ℕ) : ℚ) ^ initialBudget P := by
    rw [abs_prod]
    calc
      ∏ r : Fin oldRank,
          |(Erdos240Delta.delta (row.order (some r))).eval
              ((bLast * lambda.oldExponent r -
                b r * lambda.lastExponent : ℤ) : ℚ)| ≤
          ∏ r : Fin oldRank,
            (((initialOldDeltaBaseNat P : ℕ) : ℚ) ^
              (row.order (some r))) := by
        exact Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _)
          (fun r _ ↦ abs_initial_old_delta_le P b bLast hb hbLast row lambda r)
      _ = ((initialOldDeltaBaseNat P : ℕ) : ℚ) ^
          (∑ r : Fin oldRank, row.order (some r)) := by
        rw [← Finset.prod_pow_eq_pow_sum]
      _ ≤ ((initialOldDeltaBaseNat P : ℕ) : ℚ) ^ initialBudget P := by
        exact pow_le_pow_right₀ (by exact_mod_cast hbaseOne) hsumOrder
  unfold sourceDeltaFactor initialDeltaMajorantNat
  rw [abs_mul]
  have hmul := mul_le_mul hhead hold (abs_nonneg _) (by positivity)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hmul

/-- Uniform bound for the positive integral exponential monomial in a row. -/
theorem abs_initial_monomial_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    |((∏ r : Fin oldRank,
        (P.old r : ℤ) ^ (lambda.oldExponent r * row.point)) *
          (P.newPrime : ℤ) ^ (lambda.lastExponent * row.point) : ℚ)| ≤
      (initialMonomialMajorantNat P : ℚ) := by
  have hpoint := initial_row_point_le_radius P row
  have holdExp : ∀ r : Fin oldRank,
      lambda.oldExponent r * row.point ≤
        P.LiZero r * initialRadius P := by
    intro r
    exact Nat.mul_le_mul (initial_lambda_oldExponent_le P lambda r) hpoint
  have hlastExp : lambda.lastExponent * row.point ≤
      P.LlastZero * initialRadius P :=
    Nat.mul_le_mul (initial_lambda_lastExponent_le P lambda) hpoint
  have holdNat :
      (∏ r : Fin oldRank,
          P.old r ^ (lambda.oldExponent r * row.point)) ≤
        ∏ r : Fin oldRank,
          P.old r ^ (P.LiZero r * initialRadius P) := by
    exact Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun r _ ↦
      Nat.pow_le_pow_right (P.old_prime r).one_le (holdExp r))
  have hlastNat :
      P.newPrime ^ (lambda.lastExponent * row.point) ≤
        P.newPrime ^ (P.LlastZero * initialRadius P) :=
    Nat.pow_le_pow_right P.new_prime.one_le hlastExp
  have hnat := Nat.mul_le_mul holdNat hlastNat
  unfold initialMonomialMajorantNat
  norm_num [abs_mul, abs_pow, Finset.abs_prod]
  exact_mod_cast hnat

/-- Every literal rational coefficient is bounded by the exact integral
majorant assembled above. -/
theorem abs_initial_rationalConstraintEntry_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (row : ConstraintRow oldRank (initialRadius P) (initialBudget P))
    (lambda : LambdaBox (initialBoxShape P)) :
    |rationalConstraintEntry P.h b bLast
        (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda| ≤
      (initialRationalEntryMajorantNat P : ℚ) := by
  unfold rationalConstraintEntry initialRationalEntryMajorantNat
  rw [abs_mul]
  have hmul := mul_le_mul
    (abs_initial_sourceDeltaFactor_le P b bLast hb hbLast row lambda)
    (abs_initial_monomial_le P row lambda)
    (abs_nonneg _) (by positivity)
  simpa only [Nat.cast_mul] using hmul

/-- The unconditional sharp integral realization is bounded by the same
rational-entry majorant, multiplied only by the exact maximal row
denominator. -/
theorem norm_initialIntegralConstraintModel_le_majorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc) :
    ‖(initialIntegralConstraintModel P b bLast
        (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
      (initialMatrixMajorantNat P : ℝ) := by
  let model := initialIntegralConstraintModel P b bLast
    (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)
  apply norm_matrix_le_of_entrywise model (initialMatrixMajorantNat P)
    (by positivity)
  intro row lambda
  have hden : sourceRowDenominator P.h row ≤
      ((Nat.lcmUpto P.h ^ initialBudget P : ℕ) : ℚ) := by
    unfold sourceRowDenominator
    norm_cast
    exact Nat.pow_le_pow_right (Nat.lcmUpto_pos P.h)
      ((Finset.single_le_sum (fun i _ ↦ Nat.zero_le (row.order i))
        (Finset.mem_univ none)).trans row.weight_le)
  have hentry :=
    abs_initial_rationalConstraintEntry_le P b bLast hb hbLast row lambda
  have hdenNonneg : 0 ≤ sourceRowDenominator P.h row := by
    unfold sourceRowDenominator
    positivity
  have hq : |(model.matrix row lambda : ℚ)| ≤
      (initialMatrixMajorantNat P : ℚ) := by
    rw [model.matrix_cast_eq, abs_mul, abs_of_nonneg hdenNonneg]
    unfold initialMatrixMajorantNat
    have hmul := mul_le_mul hden hentry (abs_nonneg _) (by positivity)
    simpa only [Nat.cast_mul, Nat.cast_pow] using hmul
  dsimp only [model] at hq ⊢
  rw [Int.norm_eq_abs]
  exact_mod_cast hq

/-- Source-faithful entrywise bound for the integral matrix.  Here the head
denominator is combined with the head derivative, and the old Delta
factorials are retained. -/
theorem norm_initialIntegralConstraintModel_le_sourceMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc) :
    ‖(initialIntegralConstraintModel P b bLast
        (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
      (initialSourceMatrixMajorantNat P : ℝ) := by
  let model := initialIntegralConstraintModel P b bLast
    (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)
  apply norm_matrix_le_of_entrywise model (initialSourceMatrixMajorantNat P)
    (by positivity)
  intro row lambda
  have hhead := initial_cleared_head_le_split P row lambda
  have hold := abs_initial_old_delta_product_le_rowSharp
    P b bLast hb hbLast row lambda
  have hmono := abs_initial_monomial_le P row lambda
  have hweight :
      row.order none + ∑ r : Fin oldRank, row.order (some r) ≤
        initialBudget P := by
    rw [← row.weight_eq_head_add_sum]
    exact row.weight_le
  have hcommonOne :
      (1 : ℚ) ≤ (max (4 ^ P.h) (2 * P.Bsrc) : ℕ) := by
    exact_mod_cast (le_trans (Nat.pow_pos (by norm_num : 0 < 4))
      (Nat.le_max_left _ _))
  have hderivative :
      (((4 ^ P.h : ℕ) : ℚ) ^ row.order none) *
          (((2 * P.Bsrc : ℕ) : ℚ) ^
            (∑ r : Fin oldRank, row.order (some r))) ≤
        ((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
          initialBudget P := by
    calc
      (((4 ^ P.h : ℕ) : ℚ) ^ row.order none) *
          (((2 * P.Bsrc : ℕ) : ℚ) ^
            (∑ r : Fin oldRank, row.order (some r))) ≤
        (((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^ row.order none) *
          (((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
            (∑ r : Fin oldRank, row.order (some r))) := by
        exact mul_le_mul
          (pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.le_max_left (4 ^ P.h) (2 * P.Bsrc)) _)
          (pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.le_max_right (4 ^ P.h) (2 * P.Bsrc)) _)
          (by positivity) (by positivity)
      _ = ((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
          (row.order none + ∑ r : Fin oldRank, row.order (some r)) := by
        rw [pow_add]
      _ ≤ ((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
          initialBudget P := pow_le_pow_right₀ hcommonOne hweight
  have hdelta :
      (sourceRowDenominator P.h row *
          |(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
            (row.order none)).eval
              (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)|) *
        |∏ r,
          (Erdos240Delta.delta (row.order (some r))).eval
            ((bLast * lambda.oldExponent r -
              b r * lambda.lastExponent : ℤ) : ℚ)| ≤
      (((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
          initialBudget P) *
        (4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h)) *
          (2 : ℚ) ^
            (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) := by
    calc
      (sourceRowDenominator P.h row *
          |(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
            (row.order none)).eval
              (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)|) *
        |∏ r,
          (Erdos240Delta.delta (row.order (some r))).eval
            ((bLast * lambda.oldExponent r -
              b r * lambda.lastExponent : ℤ) : ℚ)| ≤
        ((((4 ^ P.h : ℕ) : ℚ) ^ row.order none) *
            (4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h))) *
          ((((2 * P.Bsrc : ℕ) : ℚ) ^
              (∑ r : Fin oldRank, row.order (some r))) *
            (2 : ℚ) ^
              (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero))) :=
          mul_le_mul hhead hold (abs_nonneg _) (by positivity)
      _ = ((((4 ^ P.h : ℕ) : ℚ) ^ row.order none) *
            (((2 * P.Bsrc : ℕ) : ℚ) ^
              (∑ r : Fin oldRank, row.order (some r)))) *
          ((4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h)) *
            (2 : ℚ) ^
              (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero))) := by ring
      _ ≤ (((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
            initialBudget P) *
          ((4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h)) *
            (2 : ℚ) ^
              (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero))) :=
        mul_le_mul_of_nonneg_right hderivative (by positivity)
      _ = (((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℚ) ^
          initialBudget P) *
        (4 : ℚ) ^ ((P.Lzero + 1) * (18 * P.h)) *
          (2 : ℚ) ^
            (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) := by
        ring
  have hdenNonneg : 0 ≤ sourceRowDenominator P.h row := by
    unfold sourceRowDenominator
    positivity
  have hq : |(model.matrix row lambda : ℚ)| ≤
      (initialSourceMatrixMajorantNat P : ℚ) := by
    rw [model.matrix_cast_eq]
    unfold rationalConstraintEntry sourceDeltaFactor
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hdenNonneg]
    rw [show sourceRowDenominator P.h row *
        (|(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
            (row.order none)).eval
              (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)| *
          |∏ r,
            (Erdos240Delta.delta (row.order (some r))).eval
              ((bLast * lambda.oldExponent r -
                b r * lambda.lastExponent : ℤ) : ℚ)| *
          |((∏ r, (P.old r : ℤ) ^
              (lambda.oldExponent r * row.point)) *
            (P.newPrime : ℤ) ^
              (lambda.lastExponent * row.point) : ℚ)|) =
        ((sourceRowDenominator P.h row *
          |(poweredDeltaHasse P.h (lambda.deltaIndex + 1)
            (row.order none)).eval
              (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)|) *
          |∏ r,
            (Erdos240Delta.delta (row.order (some r))).eval
              ((bLast * lambda.oldExponent r -
                b r * lambda.lastExponent : ℤ) : ℚ)|) *
          |((∏ r, (P.old r : ℤ) ^
              (lambda.oldExponent r * row.point)) *
            (P.newPrime : ℤ) ^
              (lambda.lastExponent * row.point) : ℚ)| by ring]
    refine (mul_le_mul hdelta hmono (abs_nonneg _) (by positivity)).trans_eq ?_
    unfold initialSourceMatrixMajorantNat
    push_cast
    ring
  dsimp only [model] at hq ⊢
  rw [Int.norm_eq_abs]
  exact_mod_cast hq

/-- A compact name for the exact level-zero equation/unknown inequality. -/
def InitialDimensionCondition {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : Prop :=
  initialRadius P * (initialBudget P + 1) ^ (oldRank + 1) <
    unknownCount (initialBoxShape P)

@[simp] theorem unknownCount_initialBoxShape {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    unknownCount (initialBoxShape P) =
      P.h * P.LzeroPlusOne *
        ((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1)) := by
  simp only [unknownCount, initialBoxShape_shiftMax,
    initialBoxShape_deltaMax, initialBoxShape_oldMax,
    initialBoxShape_lastMax, P.LminusOne_add_one_eq_h,
    P.Lzero_add_one_eq_LzeroPlusOne]

/-- The real side lengths are strictly smaller than the corresponding
numbers of integral choices. -/
theorem real_side_product_lt_choice_product {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (∏ i, P.LiZeroScale i) * P.LlastZeroScale <
      (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) := by
  have hold : (∏ i, P.LiZeroScale i) <
      ∏ i, ((P.LiZero i + 1 : ℕ) : ℝ) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _hi
      exact P.LiZeroScale_pos i
    · intro i _hi
      simpa only [Nat.cast_add, Nat.cast_one] using
        P.LiZeroScale_lt_add_one i
    · exact Finset.univ_nonempty
  have hlast : P.LlastZeroScale < ((P.LlastZero + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      P.LlastZeroScale_lt_add_one
  have hold_nonneg : 0 ≤ ∏ i, P.LiZeroScale i :=
    Finset.prod_nonneg fun i _hi ↦ (P.LiZeroScale_pos i).le
  have hchoices_pos : 0 < ∏ i, ((P.LiZero i + 1 : ℕ) : ℝ) := by positivity
  calc
    (∏ i, P.LiZeroScale i) * P.LlastZeroScale <
        (∏ i, ((P.LiZero i + 1 : ℕ) : ℝ)) *
          ((P.LlastZero + 1 : ℕ) : ℝ) :=
      mul_lt_mul hold hlast.le P.LlastZeroScale_pos hchoices_pos.le
    _ = (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) := by
      push_cast
      rfl

/-- If the zeroth side has reached scale two, its floor retains at least
half of its real size. -/
theorem half_LzeroScale_le_cast_LzeroPlusOne {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (hscale : 2 ≤ P.LzeroScale) :
    P.LzeroScale / 2 ≤ (P.LzeroPlusOne : ℝ) := by
  have hfloor := P.LzeroScale_lt_add_one
  linarith

/-- Common numerator of the `n` logarithmic side lengths. -/
def commonSideScale {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld

theorem LiZeroScale_eq_common_div {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin oldRank) :
    P.LiZeroScale i = commonSideScale P / Real.log (P.oldHeight i) := by
  rfl

theorem LlastZeroScale_eq_common_div {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    P.LlastZeroScale = commonSideScale P / Real.log P.newHeight := by
  rfl

/-- Multiplying the logarithmic side scales cancels precisely one copy of
the full height product `Omega`. -/
theorem real_side_product_eq {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (∏ i, P.LiZeroScale i) * P.LlastZeroScale =
      (commonSideScale P) ^ P.rank / P.Omega := by
  simp only [LiZeroScale_eq_common_div, LlastZeroScale_eq_common_div,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [show P.rank = oldRank + 1 by simp [VDPLParameters.rank], pow_succ]
  unfold VDPLParameters.Omega VDPLParameters.OmegaOld
  have hold : (∏ i : Fin oldRank, Real.log (P.oldHeight i)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _hi ↦ P.log_oldHeight_pos i)
  have hlast : Real.log P.newHeight ≠ 0 := ne_of_gt P.log_newHeight_pos
  field_simp

/-- Rank-only lower bound inserted in the finite source requirement ledger
for the Lemma 2 dimension count. -/
def initialDimensionConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  2048 * (16 * P.rank : ℝ) ^ P.rank

def initialDimensionRequirement {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  initialDimensionConstant P ^ (3 : ℕ)

/-- A second fixed rank-only ledger entry used to absorb the polynomial
number of level-zero coefficients into the exponential Siegel scale. -/
def initialUnknownRequirement {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  144 * (P.rank + 2 : ℝ) ^ (2 : ℕ)

theorem initialDimensionConstant_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    0 < initialDimensionConstant P := by
  unfold initialDimensionConstant
  have hrank : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
  positivity

theorem initialUnknownRequirement_lt_k {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements) :
    initialUnknownRequirement P < P.k :=
  P.requirement_lt_k hreq

/-- Membership in the finite admissibility ledger gives exactly the cube
root inequality used in the dimension count. -/
theorem initialDimensionConstant_lt_cuberoot_k {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    initialDimensionConstant P < P.k ^ (1 / 3 : ℝ) := by
  have hraw : initialDimensionRequirement P < P.k :=
    P.requirement_lt_k hreq
  have hc : 0 ≤ initialDimensionRequirement P := by
    unfold initialDimensionRequirement
    exact pow_nonneg (initialDimensionConstant_pos P).le _
  have hrpow := Real.rpow_lt_rpow hc hraw (by norm_num : (0 : ℝ) < 1 / 3)
  have hid : initialDimensionRequirement P ^ (1 / 3 : ℝ) =
      initialDimensionConstant P := by
    unfold initialDimensionRequirement
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (initialDimensionConstant_pos P).le]
    norm_num
  rwa [hid] at hrpow

/-- The parameter identity responsible for the surviving cube root of `k`:
`(k^(1-sigma))^(rank+1) = k^(1/3) * k^rank`. -/
theorem initial_source_power_identity {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (P.k ^ (1 - P.sigma)) ^ (P.rank + 1) =
      P.k ^ (1 / 3 : ℝ) * P.k ^ P.rank := by
  calc
    (P.k ^ (1 - P.sigma)) ^ (P.rank + 1) =
        (P.k ^ (1 - P.sigma)) ^ ((P.rank + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = P.k ^ ((1 - P.sigma) * (P.rank + 1 : ℝ)) := by
      push_cast
      rw [Real.rpow_mul P.k_pos.le]
    _ = P.k ^ ((1 / 3 : ℝ) + P.rank) := by
      congr 1
      rw [P.sigma_eq]
      have hrank : (0 : ℝ) < P.rank + 1 := by positivity
      field_simp
      ring
    _ = P.k ^ (1 / 3 : ℝ) * P.k ^ (P.rank : ℝ) := by
      exact Real.rpow_add P.k_pos _ _
    _ = P.k ^ (1 / 3 : ℝ) * P.k ^ P.rank := by
      rw [Real.rpow_natCast]

@[simp] theorem initialRadius_formula {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    initialRadius P = 16 * P.h := by
  simp [initialRadius, VDPLParameters.R]

theorem initial_levelScale_formula {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    P.levelScale 0 = P.k * P.Omega * Real.log P.OmegaOld := by
  simp [VDPLParameters.levelScale, VDPLParameters.qInvPow]

theorem one_le_initial_levelScale {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    1 ≤ P.levelScale 0 := by
  have heps : P.epsilon ≤ 1 := by
    linarith [P.epsilon_pos, P.sigma_pos, P.sigma_add_epsilon_lt_one]
  have hk13 : (13 : ℝ) ≤ P.k := by
    calc
      (13 : ℝ) = P.q := by simp [VDPLParameters.q]
      _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
      _ ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k heps
      _ = P.k := Real.rpow_one _
  have hkOmega : (13 : ℝ) ≤ P.k * P.Omega :=
    hk13.trans (le_mul_of_one_le_right P.k_pos.le P.one_le_Omega)
  have hlog : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
    have htwo := Real.log_two_gt_d9
    nlinarith [htwo, P.log_two_le_log_OmegaOld]
  have hfirst : (13 : ℝ) * (1 / 2 : ℝ) <
      13 * Real.log P.OmegaOld :=
    mul_lt_mul_of_pos_left hlog (by norm_num)
  have hsecond : (13 : ℝ) * Real.log P.OmegaOld ≤
      (P.k * P.Omega) * Real.log P.OmegaOld :=
    mul_le_mul_of_nonneg_right hkOmega P.log_OmegaOld_pos.le
  rw [initial_levelScale_formula]
  nlinarith [hfirst.trans_le hsecond]

/-- The initial scale is already larger than six.  This small numerical
margin turns the visible factor `h` in the column count into a factor of the
exponential height scale. -/
theorem six_lt_initial_levelScale {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    6 < P.levelScale 0 := by
  have heps : P.epsilon ≤ 1 := by
    linarith [P.epsilon_pos, P.sigma_pos, P.sigma_add_epsilon_lt_one]
  have hk13 : (13 : ℝ) ≤ P.k := by
    calc
      (13 : ℝ) = P.q := by simp [VDPLParameters.q]
      _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
      _ ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k heps
      _ = P.k := Real.rpow_one _
  have hkOmega : (13 : ℝ) ≤ P.k * P.Omega :=
    hk13.trans (le_mul_of_one_le_right P.k_pos.le P.one_le_Omega)
  have hlog : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
    have htwo := Real.log_two_gt_d9
    nlinarith [htwo, P.log_two_le_log_OmegaOld]
  have hmul : (13 : ℝ) * (1 / 2 : ℝ) <
      (P.k * P.Omega) * Real.log P.OmegaOld := by
    calc
      (13 : ℝ) * (1 / 2 : ℝ) ≤
          (P.k * P.Omega) * (1 / 2 : ℝ) := by gcongr
      _ < (P.k * P.Omega) * Real.log P.OmegaOld := by
        exact mul_lt_mul_of_pos_left hlog (mul_pos P.k_pos P.Omega_pos)
  rw [initial_levelScale_formula]
  nlinarith

theorem initialBudget_add_one_cast_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    ((initialBudget P + 1 : ℕ) : ℝ) ≤
      2 * (P.k * P.Omega * Real.log P.OmegaOld) := by
  have hfloor := P.Slevel_cast_le 0
  have hone := one_le_initial_levelScale P
  rw [initial_levelScale_formula] at hfloor hone
  simp only [initialBudget, Nat.cast_add, Nat.cast_one]
  linarith

theorem two_le_LzeroScale_of_requirement {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    2 ≤ P.LzeroScale := by
  have hroot := initialDimensionConstant_lt_cuberoot_k P hreq
  have hbase : (1 : ℝ) ≤ 16 * P.rank := by
    have hrank : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
    nlinarith
  have hpow : (1 : ℝ) ≤ (16 * P.rank : ℝ) ^ P.rank :=
    one_le_pow₀ hbase
  have hconst : (16 : ℝ) < initialDimensionConstant P := by
    unfold initialDimensionConstant
    nlinarith
  have hexponent : (1 / 3 : ℝ) ≤ 1 - P.sigma := by
    rw [P.sigma_eq]
    have hrank : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
    field_simp
    nlinarith
  have hX : P.k ^ (1 / 3 : ℝ) ≤ P.k ^ (1 - P.sigma) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hexponent
  unfold VDPLParameters.LzeroScale
  have hOmega := P.one_le_Omega
  have : (16 : ℝ) < P.k ^ (1 - P.sigma) := hconst.trans hroot |>.trans_le hX
  have hmul : P.k ^ (1 - P.sigma) ≤
      P.k ^ (1 - P.sigma) * P.Omega :=
    le_mul_of_one_le_right (Real.rpow_pos_of_pos P.k_pos _).le hOmega
  nlinarith

/-- The rank-only requirement supplies the real scale inequality for eight
times the crude row count.  This is the source margin which later gives the
raw Siegel exponent `M/(N-M) ≤ 1/7`. -/
theorem eight_initial_row_scale_lt {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    (((8 * initialRadius P *
      (initialBudget P + 1) ^ (oldRank + 1) : ℕ) : ℝ)) <
      (P.h : ℝ) * (P.LzeroScale / 2) *
        ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) := by
  have hrank : P.rank = oldRank + 1 := by simp [VDPLParameters.rank]
  have hbudget := initialBudget_add_one_cast_le P
  have hbudgetpow :
      (((initialBudget P + 1 : ℕ) : ℝ) ^ P.rank) ≤
        (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank :=
    pow_le_pow_left₀ (by positivity) hbudget _
  have hleft :
      (((8 * initialRadius P *
        (initialBudget P + 1) ^ (oldRank + 1) : ℕ) : ℝ)) ≤
        128 * (P.h : ℝ) *
          (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank := by
    rw [initialRadius_formula, ← hrank]
    push_cast
    push_cast at hbudgetpow
    have hm := mul_le_mul_of_nonneg_left hbudgetpow
      (show 0 ≤ 128 * (P.h : ℝ) by positivity)
    calc
      8 * (16 * (P.h : ℝ)) *
          ((initialBudget P : ℝ) + 1) ^ P.rank =
          128 * (P.h : ℝ) *
            ((initialBudget P : ℝ) + 1) ^ P.rank := by ring
      _ ≤ 128 * (P.h : ℝ) *
          (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank := hm
  have hroot := initialDimensionConstant_lt_cuberoot_k P hreq
  have hkpowpos : 0 < P.k ^ P.rank := pow_pos P.k_pos _
  have hpower :
      initialDimensionConstant P * P.k ^ P.rank <
        (P.k ^ (1 - P.sigma)) ^ (P.rank + 1) := by
    rw [initial_source_power_identity]
    exact mul_lt_mul_of_pos_right hroot hkpowpos
  calc
    (((8 * initialRadius P *
      (initialBudget P + 1) ^ (oldRank + 1) : ℕ) : ℝ)) ≤
        128 * (P.h : ℝ) *
          (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank := hleft
    _ < (P.h : ℝ) * (P.LzeroScale / 2) *
          ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) := by
      rw [real_side_product_eq]
      unfold VDPLParameters.LzeroScale commonSideScale
      unfold initialDimensionConstant at hpower
      have hOmega0 : P.Omega ≠ 0 := P.Omega_pos.ne'
      have hrankpos : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
      have hrank0 : (8 * (P.rank : ℝ)) ≠ 0 := by positivity
      change
        128 * (P.h : ℝ) *
            (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank <
          (P.h : ℝ) *
              (((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega) / 2) *
            ((((8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
              P.Omega * Real.log P.OmegaOld) ^ P.rank) / P.Omega)
      let factor : ℝ :=
        (1 / 16 : ℝ) * (P.h : ℝ) * P.Omega ^ P.rank *
          (Real.log P.OmegaOld) ^ P.rank *
            (8 * (P.rank : ℝ))⁻¹ ^ P.rank
      have hfactor : 0 < factor := by
        dsimp only [factor]
        have hh : (0 : ℝ) < P.h := by exact_mod_cast P.h_pos
        have hinv : 0 < (8 * (P.rank : ℝ))⁻¹ := by positivity
        exact mul_pos
          (mul_pos
            (mul_pos
              (mul_pos (by positivity) hh)
                (pow_pos P.Omega_pos _))
              (pow_pos P.log_OmegaOld_pos _))
            (pow_pos hinv _)
      have hmul := mul_lt_mul_of_pos_right hpower hfactor
      have hratio :
          (16 * (P.rank : ℝ)) ^ P.rank *
              (8 * (P.rank : ℝ))⁻¹ ^ P.rank =
            2 ^ P.rank := by
        rw [← mul_pow]
        have hbase :
            (16 * (P.rank : ℝ)) * (8 * (P.rank : ℝ))⁻¹ = 2 := by
          field_simp [hrank0]
          ring
        rw [hbase]
      have hleftEq :
          128 * (P.h : ℝ) *
              (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank =
            2048 * (16 * (P.rank : ℝ)) ^ P.rank * P.k ^ P.rank * factor := by
        dsimp only [factor]
        have hproduct :
            (2 * (P.k * P.Omega * Real.log P.OmegaOld)) ^ P.rank =
              2 ^ P.rank * P.k ^ P.rank * P.Omega ^ P.rank *
                Real.log P.OmegaOld ^ P.rank := by
          simp only [mul_pow]
          ring
        rw [hproduct]
        calc
          128 * (P.h : ℝ) *
                (2 ^ P.rank * P.k ^ P.rank * P.Omega ^ P.rank *
                  Real.log P.OmegaOld ^ P.rank) =
              128 * (P.h : ℝ) * P.k ^ P.rank *
                P.Omega ^ P.rank * Real.log P.OmegaOld ^ P.rank *
                  ((16 * (P.rank : ℝ)) ^ P.rank *
                    (8 * (P.rank : ℝ))⁻¹ ^ P.rank) := by
              rw [hratio]
              ring
          _ = 2048 * (16 * (P.rank : ℝ)) ^ P.rank * P.k ^ P.rank *
                ((1 / 16 : ℝ) * (P.h : ℝ) * P.Omega ^ P.rank *
                  Real.log P.OmegaOld ^ P.rank *
                    (8 * (P.rank : ℝ))⁻¹ ^ P.rank) := by
              ring
      have hrightEq :
          (P.h : ℝ) *
              (((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega) / 2) *
            ((((8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
              P.Omega * Real.log P.OmegaOld) ^ P.rank) / P.Omega) =
            (P.k ^ (1 - P.sigma)) ^ P.rank * P.k ^ (1 - P.sigma) *
              factor := by
        dsimp only [factor]
        simp only [mul_pow, inv_pow]
        field_simp [hOmega0, hrank0]
        ring
      rw [hleftEq, hrightEq]
      rw [pow_succ] at hmul
      exact hmul

/-- The older factor-two form follows immediately from the source-faithful
factor-eight margin. -/
theorem twice_initial_row_scale_lt {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    (((2 * initialRadius P *
      (initialBudget P + 1) ^ (oldRank + 1) : ℕ) : ℝ)) <
      (P.h : ℝ) * (P.LzeroScale / 2) *
        ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) := by
  have height := eight_initial_row_scale_lt P hreq
  apply lt_of_le_of_lt (b :=
    (((8 * initialRadius P *
      (initialBudget P + 1) ^ (oldRank + 1) : ℕ) : ℝ))) ?_ height
  push_cast
  have hr : (0 : ℝ) ≤ initialRadius P := by positivity
  have hb : (0 : ℝ) ≤
      ((initialBudget P : ℝ) + 1) ^ (oldRank + 1) := by positivity
  nlinarith

/-- Convert any natural upper bound lying below the real initial box scale
into a strict bound by the exact number of level-zero coefficients.  This
packages all floor and off-by-one bookkeeping in one reusable statement. -/
theorem nat_lt_initial_unknownCount_of_real_scale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (hLzero : 2 ≤ P.LzeroScale)
    (hscale :
      (N : ℝ) <
        (P.h : ℝ) * (P.LzeroScale / 2) *
          ((∏ i, P.LiZeroScale i) * P.LlastZeroScale)) :
    N < unknownCount (initialBoxShape P) := by
  have hside := real_side_product_lt_choice_product P
  have hL0 := half_LzeroScale_le_cast_LzeroPlusOne P hLzero
  have hh : (0 : ℝ) < P.h := by exact_mod_cast P.h_pos
  have hsidepos : 0 < (∏ i, P.LiZeroScale i) * P.LlastZeroScale :=
    mul_pos (Finset.prod_pos fun i _hi ↦ P.LiZeroScale_pos i)
      P.LlastZeroScale_pos
  have hmiddle :
      (P.h : ℝ) * (P.LzeroScale / 2) *
          ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) <
        (P.h : ℝ) * (P.LzeroPlusOne : ℝ) *
          (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) := by
    have hhalfpos : 0 < P.LzeroScale / 2 := by linarith
    have hchoiceSidePos :
        0 < (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) := by
      positivity
    have hfirst :
        (P.LzeroScale / 2) *
            ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) <
          (P.LzeroPlusOne : ℝ) *
            (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) :=
      calc
        (P.LzeroScale / 2) *
              ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) <
            (P.LzeroScale / 2) *
              (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_left hside hhalfpos
        _ ≤ (P.LzeroPlusOne : ℝ) *
              (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hL0 hchoiceSidePos.le
    simpa only [mul_assoc] using mul_lt_mul_of_pos_left hfirst hh
  have hcast :
      (N : ℝ) <
        (unknownCount (initialBoxShape P) : ℝ) := by
    calc
      (N : ℝ) <
          (P.h : ℝ) * (P.LzeroScale / 2) *
            ((∏ i, P.LiZeroScale i) * P.LlastZeroScale) := hscale
      _ < (P.h : ℝ) * (P.LzeroPlusOne : ℝ) *
            (((∏ i, (P.LiZero i + 1)) * (P.LlastZero + 1) : ℕ) : ℝ) :=
        hmiddle
      _ = (unknownCount (initialBoxShape P) : ℝ) := by
        rw [unknownCount_initialBoxShape]
        push_cast
        ring
  exact_mod_cast hcast

/-- All floor and off-by-one bookkeeping for the initial dimension count.
Only the displayed real scale inequality remains to be supplied by the
rank-only lower-bound requirement on `k`. -/
theorem initialDimensionCondition_of_real_scale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hLzero : 2 ≤ P.LzeroScale)
    (hscale :
      (((initialRadius P * (initialBudget P + 1) ^ (oldRank + 1) : ℕ) : ℝ)) <
        (P.h : ℝ) * (P.LzeroScale / 2) *
          ((∏ i, P.LiZeroScale i) * P.LlastZeroScale)) :
    InitialDimensionCondition P :=
  nat_lt_initial_unknownCount_of_real_scale P
    (initialRadius P * (initialBudget P + 1) ^ (oldRank + 1)) hLzero hscale

/-- The admissible rank-only requirement makes even twice the crude row
bound smaller than the exact level-zero number of coefficients. -/
theorem twice_initialDimensionCondition_of_requirement
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    2 * (initialRadius P * (initialBudget P + 1) ^ (oldRank + 1)) <
      unknownCount (initialBoxShape P) := by
  apply nat_lt_initial_unknownCount_of_real_scale P
  · exact two_le_LzeroScale_of_requirement P hreq
  · convert twice_initial_row_scale_lt P hreq using 1 <;>
      push_cast <;> ring

/-- Exact Siegel-lemma slack at level zero, deduced from the displayed
source requirement rather than assumed as a separate matrix hypothesis. -/
theorem initial_cardinality_slack_of_requirement
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    2 * Fintype.card
        (ConstraintRow oldRank (initialRadius P) (initialBudget P)) ≤
      Fintype.card (LambdaBox (initialBoxShape P)) := by
  rw [card_lambdaBox]
  have hrows := card_constraintRow_le oldRank (initialRadius P) (initialBudget P)
  have hdim := twice_initialDimensionCondition_of_requirement P hreq
  omega

/-- Source-faithful factor-eight form of the exact row/column margin. -/
theorem eight_initialDimensionCondition_of_requirement
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    8 * (initialRadius P * (initialBudget P + 1) ^ (oldRank + 1)) <
      unknownCount (initialBoxShape P) := by
  apply nat_lt_initial_unknownCount_of_real_scale P
  · exact two_le_LzeroScale_of_requirement P hreq
  · convert eight_initial_row_scale_lt P hreq using 1 <;>
      push_cast <;> ring

theorem initial_eight_cardinality_slack_of_requirement
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialDimensionRequirement P ∈ P.kRequirements) :
    8 * Fintype.card
        (ConstraintRow oldRank (initialRadius P) (initialBudget P)) ≤
      Fintype.card (LambdaBox (initialBoxShape P)) := by
  rw [card_lambdaBox]
  have hrows := card_constraintRow_le oldRank (initialRadius P) (initialBudget P)
  have hdim := eight_initialDimensionCondition_of_requirement P hreq
  omega

/-- The exact level-zero column count is absorbed by one sixth of the
source coefficient-height exponent.  Only the displayed rank-only ledger
entry is used; in particular this estimate is uniform in the varying prime
and in the coefficient cutoff. -/
theorem initial_unknownCount_le_exp_heightScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements) :
    (Fintype.card (LambdaBox (initialBoxShape P)) : ℝ) ≤
      Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
        Real.log P.OmegaOld) := by
  let T : ℝ := P.k * P.Omega * Real.log P.OmegaOld
  let scale : ℝ := (1 / 6 : ℝ) * P.h * T
  have hT : 6 < T := by
    simpa only [T, initial_levelScale_formula] using
      six_lt_initial_levelScale P
  have hTpos : 0 < T := by linarith
  have hXpos : 0 < scale := by
    dsimp only [scale]
    have hh : (0 : ℝ) < P.h := by exact_mod_cast P.h_pos
    positivity
  have hkpow : P.k ^ (1 - P.sigma) ≤ P.k := by
    calc
      P.k ^ (1 - P.sigma) ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k (by
          linarith [P.sigma_pos])
      _ = P.k := Real.rpow_one _
  have hLzero : (P.LzeroPlusOne : ℝ) ≤ T := by
    calc
      (P.LzeroPlusOne : ℝ) ≤ P.LzeroScale := P.LzeroPlusOne_cast_le
      _ ≤ T := by
        unfold VDPLParameters.LzeroScale
        dsimp only [T]
        have hmul :
            P.k ^ (1 - P.sigma) * P.Omega ≤ P.k * P.Omega :=
          mul_le_mul_of_nonneg_right hkpow P.Omega_pos.le
        have hlog : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
          have htwo := Real.log_two_gt_d9
          nlinarith [htwo, P.log_two_le_log_OmegaOld]
        have hright :
            (1 / 8 : ℝ) * (P.k * P.Omega) ≤
              (P.k * P.Omega) * Real.log P.OmegaOld := by
          have hkO : 0 ≤ P.k * P.Omega :=
            mul_nonneg P.k_pos.le P.Omega_pos.le
          nlinarith
        calc
          (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega =
              (1 / 8 : ℝ) *
                (P.k ^ (1 - P.sigma) * P.Omega) := by ring
          _ ≤ (1 / 8 : ℝ) * (P.k * P.Omega) := by gcongr
          _ ≤ (P.k * P.Omega) * Real.log P.OmegaOld := hright
  have hLi : ∀ i : Fin oldRank, ((P.LiZero i + 1 : ℕ) : ℝ) ≤ 2 * T := by
    intro i
    have hscale : P.LiZeroScale i ≤ T := by
      unfold VDPLParameters.LiZeroScale
      dsimp only [T]
      have hrank : (1 : ℝ) ≤ 8 * P.rank := by
        have : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
        nlinarith
      have hinv : (8 * (P.rank : ℝ))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ hrank
      have hlogden : (1 : ℝ) ≤ Real.log (P.oldHeight i) :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (P.two_le_log_oldHeight i)
      have hk0 : 0 ≤ P.k := P.k_pos.le
      have hkpow0 : 0 ≤ P.k ^ (1 - P.sigma) :=
        (Real.rpow_pos_of_pos P.k_pos _).le
      have hOmega0 : 0 ≤ P.Omega := P.Omega_pos.le
      have hlog0 : 0 ≤ Real.log P.OmegaOld := P.log_OmegaOld_pos.le
      calc
        (8 * (P.rank : ℝ))⁻¹ * P.k ^ (1 - P.sigma) *
              P.Omega * Real.log P.OmegaOld /
              Real.log (P.oldHeight i) ≤
            1 * P.k * P.Omega * Real.log P.OmegaOld / 1 := by
          gcongr
        _ = P.k * P.Omega * Real.log P.OmegaOld := by ring
    have hfloor := P.LiZero_cast_le i
    push_cast
    nlinarith
  have hLlast : ((P.LlastZero + 1 : ℕ) : ℝ) ≤ 2 * T := by
    have hscale : P.LlastZeroScale ≤ T := by
      unfold VDPLParameters.LlastZeroScale
      dsimp only [T]
      have hrank : (1 : ℝ) ≤ 8 * P.rank := by
        have : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
        nlinarith
      have hinv : (8 * (P.rank : ℝ))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ hrank
      have hlogden : (1 : ℝ) ≤ Real.log P.newHeight :=
        P.one_le_log_newHeight
      have hk0 : 0 ≤ P.k := P.k_pos.le
      have hkpow0 : 0 ≤ P.k ^ (1 - P.sigma) :=
        (Real.rpow_pos_of_pos P.k_pos _).le
      have hOmega0 : 0 ≤ P.Omega := P.Omega_pos.le
      have hlog0 : 0 ≤ Real.log P.OmegaOld := P.log_OmegaOld_pos.le
      calc
        (8 * (P.rank : ℝ))⁻¹ * P.k ^ (1 - P.sigma) *
              P.Omega * Real.log P.OmegaOld / Real.log P.newHeight ≤
            1 * P.k * P.Omega * Real.log P.OmegaOld / 1 := by
          gcongr
        _ = P.k * P.Omega * Real.log P.OmegaOld := by ring
    have hfloor := P.LlastZero_cast_le
    push_cast
    nlinarith
  have hLzero' : (P.LzeroPlusOne : ℝ) ≤ 2 * T := by
    nlinarith [hLzero]
  have hold :
      (∏ i : Fin oldRank, ((P.LiZero i + 1 : ℕ) : ℝ)) ≤
        (2 * T) ^ oldRank := by
    calc
      (∏ i : Fin oldRank, ((P.LiZero i + 1 : ℕ) : ℝ)) ≤
          ∏ _i : Fin oldRank, (2 * T) := by
            exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
              (fun i _ ↦ hLi i)
      _ = (2 * T) ^ oldRank := by simp
  have hold' :
      (∏ i : Fin oldRank, ((P.LiZero i : ℝ) + 1)) ≤
        (2 * T) ^ oldRank := by
    simpa only [Nat.cast_add, Nat.cast_one] using hold
  have hLlast' : (P.LlastZero : ℝ) + 1 ≤ 2 * T := by
    simpa only [Nat.cast_add, Nat.cast_one] using hLlast
  have hhX : (P.h : ℝ) ≤ scale := by
    dsimp only [scale]
    have hh : (0 : ℝ) ≤ P.h := by positivity
    nlinarith
  have hTX : 2 * T ≤ 6 * scale := by
    dsimp only [scale]
    have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
    nlinarith
  have hcount :
      (Fintype.card (LambdaBox (initialBoxShape P)) : ℝ) ≤
        (6 * scale) ^ (P.rank + 2) := by
    rw [card_lambdaBox, unknownCount_initialBoxShape]
    push_cast
    have hnonneg : 0 ≤ 6 * scale := by positivity
    have hscaleSix : scale ≤ 6 * scale := by nlinarith [hXpos]
    calc
      (P.h : ℝ) * P.LzeroPlusOne *
            ((∏ i : Fin oldRank, (P.LiZero i + 1 : ℝ)) *
              (P.LlastZero + 1 : ℝ)) ≤
          scale * (2 * T) * ((2 * T) ^ oldRank * (2 * T)) := by
            exact mul_le_mul
              (mul_le_mul hhX hLzero' (by positivity) (by positivity))
              (mul_le_mul hold' hLlast' (by positivity) (by positivity))
              (by positivity) (by positivity)
      _ = scale * (2 * T) ^ (oldRank + 2) := by ring
      _ ≤ (6 * scale) * (6 * scale) ^ (oldRank + 2) := by
            exact mul_le_mul hscaleSix
              (pow_le_pow_left₀ (by positivity) hTX (oldRank + 2))
              (by positivity) (by positivity)
      _ = (6 * scale) ^ (P.rank + 2) := by
            rw [show P.rank = oldRank + 1 by simp [VDPLParameters.rank]]
            simp only [pow_succ]
            ring
  have hreqk := initialUnknownRequirement_lt_k P hreq
  have hfactor : (1 : ℝ) < (P.h : ℝ) * P.Omega *
      Real.log P.OmegaOld := by
    have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
    have hO := P.one_le_Omega
    have hlog : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
      have htwo := Real.log_two_gt_d9
      nlinarith [htwo, P.log_two_le_log_OmegaOld]
    have hprod : (1 : ℝ) < 2 * 1 * Real.log P.OmegaOld := by nlinarith
    exact hprod.trans_le (by gcongr)
  have hkX : P.k < 6 * scale := by
    dsimp only [scale]
    have := mul_lt_mul_of_pos_left hfactor P.k_pos
    nlinarith
  have hXlarge : 24 * (P.rank + 2 : ℝ) ^ (2 : ℕ) < scale := by
    unfold initialUnknownRequirement at hreqk
    nlinarith
  have hlog : Real.log (6 * scale) ≤ 2 * (6 * scale) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (show 0 ≤ 6 * scale by positivity)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    convert this using 1 <;> norm_num [div_eq_mul_inv] <;> ring
  have hsqrt : 0 ≤ (6 * scale) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hsqrtSq : ((6 * scale) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = 6 * scale := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 6 * scale)]
    norm_num
  have hexponent :
      Real.log (6 * scale) * (P.rank + 2 : ℝ) ≤ scale := by
    have hn : (0 : ℝ) ≤ P.rank + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hlog hn
    have hrootBound :
        2 * (6 * scale) ^ (1 / 2 : ℝ) * (P.rank + 2 : ℝ) < scale := by
      nlinarith [sq_nonneg
        ((6 * scale) ^ (1 / 2 : ℝ) - 2 * (P.rank + 2 : ℝ))]
    exact hmul.trans hrootBound.le
  calc
    (Fintype.card (LambdaBox (initialBoxShape P)) : ℝ) ≤
        (6 * scale) ^ (P.rank + 2) := hcount
    _ = Real.exp (Real.log (6 * scale) * (P.rank + 2 : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      congr 1
      simp only [Nat.cast_add, Nat.cast_ofNat]
    _ ≤ Real.exp scale := Real.exp_le_exp.mpr hexponent
    _ = Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
        Real.log P.OmegaOld) := by
      congr 1
      dsimp only [scale, T]
      ring

/-! ## The literal source matrix fits the printed `exp (2H)` budget -/

private theorem real_pow_le_exp_of_mul_log_le {a A : ℝ} {n : ℕ}
    (ha : 0 < a) (h : (n : ℝ) * Real.log a ≤ A) :
    a ^ n ≤ Real.exp A := by
  calc
    a ^ n = Real.exp (Real.log a) ^ n := by rw [Real.exp_log ha]
    _ = Real.exp ((n : ℝ) * Real.log a) :=
      (Real.exp_nat_mul (Real.log a) n).symm
    _ ≤ Real.exp A := Real.exp_le_exp.mpr h

/-- The source seed makes the small power `k^sigma` uniformly enormous.
This is the numerical reserve used for all three lower-order entry factors. -/
theorem twoHundredFiftySix_le_k_rpow_sigma {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (256 : ℝ) ≤ P.k ^ P.sigma := by
  have hsigma : P.sigma = P.epsilon * 4 := by
    rw [P.sigma_eq, P.epsilon_eq]
    field_simp
    ring
  have hpow : (13 : ℝ) ^ (4 : ℕ) ≤
      (P.k ^ P.epsilon) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) P.q_le_k_rpow_epsilon 4
  calc
    (256 : ℝ) ≤ 13 ^ (4 : ℕ) := by norm_num
    _ ≤ (P.k ^ P.epsilon) ^ (4 : ℕ) := hpow
    _ = P.k ^ P.sigma := by
      rw [hsigma, ← Real.rpow_natCast,
        ← Real.rpow_mul P.k_pos.le]
      norm_num

/-- Both possible bases for a row derivative order are bounded by
`exp ((15/8)h)`. -/
theorem initial_commonDerivativeBase_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    ((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℝ) ≤
      Real.exp ((15 / 8 : ℝ) * P.h) := by
  have hlog4 : Real.log (4 : ℝ) ≤ 3 / 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hfour : ((4 ^ P.h : ℕ) : ℝ) ≤
      Real.exp ((15 / 8 : ℝ) * P.h) := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    apply real_pow_le_exp_of_mul_log_le (by norm_num : (0 : ℝ) < 4)
    have hh : (0 : ℝ) ≤ P.h := by positivity
    nlinarith
  have hBpos : (0 : ℝ) < P.Bsrc :=
    (Real.exp_pos 2).trans_le P.Bsrc_lower
  have hBexp : (P.Bsrc : ℝ) < Real.exp ((P.h : ℝ) + 1) := by
    rw [← Real.exp_log hBpos]
    exact Real.exp_lt_exp.mpr P.log_Bsrc_lt_h_add_one
  have hlog2 : Real.log (2 : ℝ) < 3 / 4 := by
    nlinarith [Real.log_two_lt_d9]
  have hexponent :
      Real.log (2 : ℝ) + ((P.h : ℝ) + 1) ≤
        (15 / 8 : ℝ) * P.h := by
    have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
    nlinarith
  have htwoB : ((2 * P.Bsrc : ℕ) : ℝ) ≤
      Real.exp ((15 / 8 : ℝ) * P.h) := by
    push_cast
    calc
      (2 : ℝ) * P.Bsrc ≤ 2 * Real.exp ((P.h : ℝ) + 1) :=
        (mul_lt_mul_of_pos_left hBexp (by norm_num)).le
      _ = Real.exp (Real.log (2 : ℝ) + ((P.h : ℝ) + 1)) := by
        calc
          (2 : ℝ) * Real.exp ((P.h : ℝ) + 1) =
              Real.exp (Real.log 2) * Real.exp ((P.h : ℝ) + 1) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = Real.exp (Real.log (2 : ℝ) + ((P.h : ℝ) + 1)) :=
            (Real.exp_add _ _).symm
      _ ≤ Real.exp ((15 / 8 : ℝ) * P.h) :=
        Real.exp_le_exp.mpr hexponent
  simpa only [Nat.cast_max] using max_le hfour htwoB

/-- The common-base contribution of the complete derivative multi-index
uses at most `15/8` of the source matrix exponent. -/
theorem initial_commonDerivativeFactor_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (((max (4 ^ P.h) (2 * P.Bsrc)) ^ initialBudget P : ℕ) : ℝ) ≤
      Real.exp ((15 / 8 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  have hbase := initial_commonDerivativeBase_le P
  have hpow := pow_le_pow_left₀ (by positivity) hbase (initialBudget P)
  calc
    (((max (4 ^ P.h) (2 * P.Bsrc)) ^ initialBudget P : ℕ) : ℝ) ≤
        (Real.exp ((15 / 8 : ℝ) * P.h)) ^ initialBudget P := by
      norm_num only [Nat.cast_pow]
      exact hpow
    _ = Real.exp (((initialBudget P : ℝ) *
          ((15 / 8 : ℝ) * P.h))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp ((15 / 8 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
      apply Real.exp_le_exp.mpr
      have hbudget := P.Slevel_cast_le 0
      rw [initial_levelScale_formula] at hbudget
      have hmul := mul_le_mul_of_nonneg_right hbudget
        (show 0 ≤ (15 / 8 : ℝ) * P.h by positivity)
      calc
        (initialBudget P : ℝ) * ((15 / 8 : ℝ) * P.h) ≤
            (P.k * P.Omega * Real.log P.OmegaOld) *
              ((15 / 8 : ℝ) * P.h) := hmul
        _ = (15 / 8 : ℝ) *
            ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by ring

theorem k_rpow_one_sub_sigma_mul_rpow_sigma {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    P.k ^ (1 - P.sigma) * P.k ^ P.sigma = P.k := by
  rw [← Real.rpow_add P.k_pos]
  convert Real.rpow_one P.k using 1 <;> ring

/-- The `lambda₀` side of the cleared head consumes at most `H/32`. -/
theorem initial_headSideFactor_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    ((4 ^ ((P.Lzero + 1) * (18 * P.h)) : ℕ) : ℝ) ≤
      Real.exp ((1 / 32 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hlogLower : (2 / 3 : ℝ) ≤ Real.log P.OmegaOld := by
    exact (by nlinarith [Real.log_two_gt_d9] :
      (2 / 3 : ℝ) ≤ Real.log 2).trans P.log_two_le_log_OmegaOld
  have hks := twoHundredFiftySix_le_k_rpow_sigma P
  have hkslog : (144 : ℝ) ≤
      P.k ^ P.sigma * Real.log P.OmegaOld := by
    calc
      (144 : ℝ) ≤ 256 * (2 / 3 : ℝ) := by norm_num
      _ ≤ P.k ^ P.sigma * Real.log P.OmegaOld :=
        mul_le_mul hks hlogLower (by norm_num)
          (Real.rpow_nonneg P.k_pos.le _)
  have hside : (((P.Lzero + 1) * (18 * P.h) : ℕ) : ℝ) ≤
      (18 / 8 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega := by
    rw [P.Lzero_add_one_eq_LzeroPlusOne]
    push_cast
    have hL0 := P.LzeroPlusOne_cast_le
    unfold VDPLParameters.LzeroScale at hL0
    nlinarith [mul_le_mul_of_nonneg_right hL0
      (show 0 ≤ 18 * (P.h : ℝ) by positivity)]
  have hexponent :
      ((((P.Lzero + 1) * (18 * P.h) : ℕ) : ℝ) *
        Real.log 4) ≤
      (1 / 32 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
    calc
      ((((P.Lzero + 1) * (18 * P.h) : ℕ) : ℝ) * Real.log 4) ≤
          (((P.Lzero + 1) * (18 * P.h) : ℕ) : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left hlog4 (by positivity)
      _ ≤ ((18 / 8 : ℝ) * (P.h : ℝ) *
          P.k ^ (1 - P.sigma) * P.Omega) * 2 :=
        mul_le_mul_of_nonneg_right hside (by norm_num)
      _ = (1 / 32 : ℝ) * (P.h : ℝ) *
          P.k ^ (1 - P.sigma) * P.Omega * 144 := by ring
      _ ≤ (1 / 32 : ℝ) * (P.h : ℝ) *
          P.k ^ (1 - P.sigma) * P.Omega *
            (P.k ^ P.sigma * Real.log P.OmegaOld) := by
        exact mul_le_mul_of_nonneg_left hkslog
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (by positivity))
              (Real.rpow_nonneg P.k_pos.le _))
            P.Omega_pos.le)
      _ = (1 / 32 : ℝ) * (P.h : ℝ) *
          (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
            Real.log P.OmegaOld := by ring
      _ = (1 / 32 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
        rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
        ring
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  exact real_pow_le_exp_of_mul_log_le (by norm_num) hexponent

/-- The sum of the box sides occurring in the ordinary old-coordinate
Delta factors is at most one quarter of the common side numerator. -/
theorem initial_oldDeltaSideSum_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    ((∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) : ℕ) : ℝ) ≤
      (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
  let U : ℝ := (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (by positivity))
          (Real.rpow_nonneg P.k_pos.le _)) P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hold (r : Fin oldRank) : (P.LiZero r : ℝ) ≤ U := by
    calc
      (P.LiZero r : ℝ) ≤ P.LiZeroScale r := P.LiZero_cast_le r
      _ = U / Real.log (P.oldHeight r) := by
        simp only [VDPLParameters.LiZeroScale]
        dsimp only [U]
      _ ≤ U := by
        apply (div_le_iff₀ (P.log_oldHeight_pos r)).2
        exact le_mul_of_one_le_right hU
          ((by norm_num : (1 : ℝ) ≤ 2).trans (P.two_le_log_oldHeight r))
  have hlast : (P.LlastZero : ℝ) ≤ U := by
    calc
      (P.LlastZero : ℝ) ≤ P.LlastZeroScale := P.LlastZero_cast_le
      _ = U / Real.log P.newHeight := by
        simp only [VDPLParameters.LlastZeroScale]
        dsimp only [U]
      _ ≤ U := by
        apply (div_le_iff₀ P.log_newHeight_pos).2
        exact le_mul_of_one_le_right hU P.one_le_log_newHeight
  have hsum :
      ∑ r : Fin oldRank, ((P.LiZero r + P.LlastZero : ℕ) : ℝ) ≤
        ∑ _r : Fin oldRank, (2 * U) := by
    exact Finset.sum_le_sum fun r _ ↦ by
      push_cast
      nlinarith [hold r, hlast]
  calc
    ((∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) : ℕ) : ℝ) =
        ∑ r : Fin oldRank, ((P.LiZero r + P.LlastZero : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ _r : Fin oldRank, (2 * U) := hsum
    _ = (oldRank : ℝ) * (2 * U) := by simp
    _ ≤ (P.rank : ℝ) * (2 * U) := by
      gcongr
      simp [VDPLParameters.rank]
    _ = (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
      dsimp only [U]
      have hrank : (P.rank : ℝ) ≠ 0 := by exact_mod_cast P.rank_pos.ne'
      field_simp
      ring

/-- The binary-binomial remnants from all ordinary Delta factors consume at
most `H/32`. -/
theorem initial_oldDeltaSideFactor_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    ((2 ^ (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) : ℕ) : ℝ) ≤
      Real.exp ((1 / 32 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  have hside := initial_oldDeltaSideSum_le P
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  have hks := twoHundredFiftySix_le_k_rpow_sigma P
  have hreserve : (8 : ℝ) ≤ (P.h : ℝ) * P.k ^ P.sigma := by
    calc
      (8 : ℝ) ≤ 2 * 256 := by norm_num
      _ ≤ (P.h : ℝ) * P.k ^ P.sigma :=
        mul_le_mul hh hks (by norm_num) (by positivity)
  have hexponent :
      (((∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) : ℕ) : ℝ) *
        Real.log 2) ≤
      (1 / 32 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
    calc
      (((∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) : ℕ) : ℝ) *
          Real.log 2) ≤
        ((∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) : ℕ) : ℝ) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld := hside
      _ = (1 / 32 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld * 8 := by ring
      _ ≤ (1 / 32 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld * ((P.h : ℝ) * P.k ^ P.sigma) := by
        exact mul_le_mul_of_nonneg_left hreserve
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
              P.Omega_pos.le) P.log_OmegaOld_pos.le)
      _ = (1 / 32 : ℝ) * (P.h : ℝ) *
          (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
            Real.log P.OmegaOld := by ring
      _ = (1 / 32 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
        rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
        ring
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  exact real_pow_le_exp_of_mul_log_le (by norm_num) hexponent

/-- Multiplication by the corresponding logarithmic height cancels each
side denominator.  Summing all old sides and the last side leaves exactly
the source factor `1/8`. -/
theorem initial_weightedSideLogSum_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (∑ r : Fin oldRank,
        (P.LiZero r : ℝ) * Real.log (P.oldHeight r)) +
        (P.LlastZero : ℝ) * Real.log P.newHeight ≤
      (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
  let U : ℝ := (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld
  have hold (r : Fin oldRank) :
      (P.LiZero r : ℝ) * Real.log (P.oldHeight r) ≤ U := by
    have hfloor := P.LiZero_cast_le r
    have hlog := P.log_oldHeight_pos r
    calc
      (P.LiZero r : ℝ) * Real.log (P.oldHeight r) ≤
          P.LiZeroScale r * Real.log (P.oldHeight r) :=
        mul_le_mul_of_nonneg_right hfloor hlog.le
      _ = U := by
        unfold VDPLParameters.LiZeroScale
        dsimp only [U]
        field_simp [hlog.ne']
  have hlast :
      (P.LlastZero : ℝ) * Real.log P.newHeight ≤ U := by
    have hfloor := P.LlastZero_cast_le
    have hlog := P.log_newHeight_pos
    calc
      (P.LlastZero : ℝ) * Real.log P.newHeight ≤
          P.LlastZeroScale * Real.log P.newHeight :=
        mul_le_mul_of_nonneg_right hfloor hlog.le
      _ = U := by
        unfold VDPLParameters.LlastZeroScale
        dsimp only [U]
        field_simp [hlog.ne']
  calc
    (∑ r : Fin oldRank,
        (P.LiZero r : ℝ) * Real.log (P.oldHeight r)) +
        (P.LlastZero : ℝ) * Real.log P.newHeight ≤
      (∑ _r : Fin oldRank, U) + U :=
        add_le_add (Finset.sum_le_sum fun r _ ↦ hold r) hlast
    _ = (P.rank : ℝ) * U := by
      simp [VDPLParameters.rank]
      ring
    _ = (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
      dsimp only [U]
      have hrank : (P.rank : ℝ) ≠ 0 := by exact_mod_cast P.rank_pos.ne'
      field_simp

/-- The prime monomial in every matrix entry consumes at most `H/32`.
This is where the factor `k^{-sigma}` in every exponent side is used. -/
theorem initial_monomialMajorant_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (initialMonomialMajorantNat P : ℝ) ≤
      Real.exp ((1 / 32 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  have holdBase (r : Fin oldRank) :
      (P.old r : ℝ) ≤ P.oldHeight r := (P.old_cast_lt_oldHeight r).le
  have hlastBase : (P.newPrime : ℝ) ≤ P.newHeight :=
    P.newPrime_cast_lt_varyingHeight.le.trans P.varyingHeight_le_newHeight
  have holdFactor (r : Fin oldRank) :
      (P.old r : ℝ) ^ (P.LiZero r * initialRadius P) ≤
        Real.exp (((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
          Real.log (P.oldHeight r)) := by
    calc
      (P.old r : ℝ) ^ (P.LiZero r * initialRadius P) ≤
          P.oldHeight r ^ (P.LiZero r * initialRadius P) :=
        pow_le_pow_left₀ (by positivity) (holdBase r) _
      _ ≤ Real.exp (((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
          Real.log (P.oldHeight r)) := by
        apply real_pow_le_exp_of_mul_log_le
          (n := P.LiZero r * initialRadius P) (P.oldHeight_pos r)
        norm_num only [Nat.cast_mul]
        exact le_rfl
  have hlastFactor :
      (P.newPrime : ℝ) ^ (P.LlastZero * initialRadius P) ≤
        Real.exp (((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
          Real.log P.newHeight) := by
    calc
      (P.newPrime : ℝ) ^ (P.LlastZero * initialRadius P) ≤
          P.newHeight ^ (P.LlastZero * initialRadius P) :=
        pow_le_pow_left₀ (by positivity) hlastBase _
      _ ≤ Real.exp (((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
          Real.log P.newHeight) := by
        apply real_pow_le_exp_of_mul_log_le
          (n := P.LlastZero * initialRadius P) P.newHeight_pos
        norm_num only [Nat.cast_mul]
        exact le_rfl
  have hraw : (initialMonomialMajorantNat P : ℝ) ≤
      Real.exp
        ((∑ r : Fin oldRank,
            ((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
              Real.log (P.oldHeight r)) +
          ((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
            Real.log P.newHeight) := by
    unfold initialMonomialMajorantNat
    push_cast
    calc
      (∏ r : Fin oldRank,
          (P.old r : ℝ) ^ (P.LiZero r * initialRadius P)) *
          (P.newPrime : ℝ) ^ (P.LlastZero * initialRadius P) ≤
        (∏ r : Fin oldRank,
          Real.exp (((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
            Real.log (P.oldHeight r))) *
          Real.exp (((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
            Real.log P.newHeight) := by
          exact mul_le_mul
            (Finset.prod_le_prod (fun _ _ ↦ by positivity)
              (fun r _ ↦ holdFactor r)) hlastFactor (by positivity) (by positivity)
      _ = Real.exp
          ((∑ r : Fin oldRank,
              ((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
                Real.log (P.oldHeight r)) +
            ((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
              Real.log P.newHeight) := by
        rw [← Real.exp_sum, ← Real.exp_add]
  refine hraw.trans (Real.exp_le_exp.mpr ?_)
  have hweighted := initial_weightedSideLogSum_le P
  have hRadius : (initialRadius P : ℝ) = 16 * P.h := by
    exact_mod_cast initialRadius_formula P
  have hfirst :
      (∑ r : Fin oldRank,
          ((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
            Real.log (P.oldHeight r)) +
        ((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
          Real.log P.newHeight ≤
      2 * (P.h : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
    push_cast
    calc
      (∑ r : Fin oldRank,
          ((P.LiZero r : ℝ) * initialRadius P) *
            Real.log (P.oldHeight r)) +
        ((P.LlastZero : ℝ) * initialRadius P) *
          Real.log P.newHeight =
        (∑ r : Fin oldRank,
            (initialRadius P : ℝ) *
              ((P.LiZero r : ℝ) * Real.log (P.oldHeight r))) +
          (initialRadius P : ℝ) *
            ((P.LlastZero : ℝ) * Real.log P.newHeight) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro r _
            ring
          · ring
      _ =
        (initialRadius P : ℝ) *
          ((∑ r : Fin oldRank,
              (P.LiZero r : ℝ) * Real.log (P.oldHeight r)) +
            (P.LlastZero : ℝ) * Real.log P.newHeight) := by
          rw [mul_add, Finset.mul_sum]
      _ ≤ (initialRadius P : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
            Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = 2 * (P.h : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld := by rw [hRadius]; ring
  have hks := twoHundredFiftySix_le_k_rpow_sigma P
  have hreserve : (64 : ℝ) ≤ P.k ^ P.sigma := by linarith
  calc
    (∑ r : Fin oldRank,
        ((P.LiZero r : ℝ) * (initialRadius P : ℝ)) *
          Real.log (P.oldHeight r)) +
      ((P.LlastZero : ℝ) * (initialRadius P : ℝ)) *
        Real.log P.newHeight ≤
      2 * (P.h : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := hfirst
    _ = (1 / 32 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld * 64 := by ring
    _ ≤ (1 / 32 : ℝ) * (P.h : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld * P.k ^ P.sigma := by
      exact mul_le_mul_of_nonneg_left hreserve
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (by positivity))
              (Real.rpow_nonneg P.k_pos.le _)) P.Omega_pos.le)
          P.log_OmegaOld_pos.le)
    _ = (1 / 32 : ℝ) * (P.h : ℝ) *
        (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
          Real.log P.OmegaOld := by ring
    _ = (1 / 32 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
      rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
      ring

/-- Source-faithful numerical endgame for the raw integral Siegel lemma.
The factor-eight dimension margin gives exponent at most `1/7`; a column
count of size `exp(H/6)` and matrix of size `exp(2H)` therefore fit strictly
inside the desired coefficient height `exp(H/3)`. -/
theorem siegel_rpow_le_exp_third {M N : ℕ} {matrixNorm H : ℝ}
    (hH : 0 ≤ H) (hMpos : 0 < M) (hslack : 8 * M ≤ N)
    (hN : (N : ℝ) ≤ Real.exp (H / 6))
    (hmatrix : matrixNorm ≤ Real.exp (2 * H)) :
    (((N : ℝ) * max 1 matrixNorm) ^
        ((M : ℝ) / ((N : ℝ) - (M : ℝ)))) ≤
      Real.exp (H / 3) := by
  have hMN : M < N := by omega
  have hdenpos : (0 : ℝ) < (N : ℝ) - (M : ℝ) :=
    sub_pos.mpr (by exact_mod_cast hMN)
  have hexponent_nonneg :
      0 ≤ (M : ℝ) / ((N : ℝ) - (M : ℝ)) := by positivity
  have hexponent_le :
      (M : ℝ) / ((N : ℝ) - (M : ℝ)) ≤ 1 / 7 := by
    rw [div_le_iff₀ hdenpos]
    have hslackR : 8 * (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hslack
    nlinarith
  have hexpTwo_nonneg : 1 ≤ Real.exp (2 * H) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hmax : max 1 matrixNorm ≤ Real.exp (2 * H) :=
    max_le hexpTwo_nonneg hmatrix
  have hbase : (N : ℝ) * max 1 matrixNorm ≤ Real.exp (13 * H / 6) := by
    calc
      (N : ℝ) * max 1 matrixNorm ≤
          Real.exp (H / 6) * Real.exp (2 * H) :=
        mul_le_mul hN hmax (le_trans (by norm_num) (le_max_left _ _))
          (Real.exp_pos _).le
      _ = Real.exp (13 * H / 6) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    (((N : ℝ) * max 1 matrixNorm) ^
          ((M : ℝ) / ((N : ℝ) - (M : ℝ)))) ≤
        (Real.exp (13 * H / 6)) ^
          ((M : ℝ) / ((N : ℝ) - (M : ℝ))) :=
      Real.rpow_le_rpow (by positivity) hbase hexponent_nonneg
    _ = Real.exp ((13 * H / 6) *
          ((M : ℝ) / ((N : ℝ) - (M : ℝ)))) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    _ ≤ Real.exp ((13 * H / 6) * (1 / 7)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hexponent_le (by positivity)
    _ ≤ Real.exp (H / 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Once the source's elementary parameter count has been established, the
literal initial matrix has fewer rows than columns. -/
theorem initial_card_row_lt_card_box {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (hdim : InitialDimensionCondition P) :
    Fintype.card
        (ConstraintRow oldRank (initialRadius P) (initialBudget P)) <
      Fintype.card (LambdaBox (initialBoxShape P)) :=
  card_row_lt_card_box_of_bound hdim

/-- Concrete source Lemma 2 up to the two elementary quantitative estimates
on the level-zero box and the already integral matrix.  The conclusion is
the exact nonzero coefficient vector and the exact level-zero equations.

The hypotheses are deliberately numerical inequalities, not an abstract
existence certificate: the remaining parameter-count file can discharge
them directly from the displayed choices of `k`, the side lengths, and the
entry estimates. -/
theorem exists_initial_auxiliary_coefficients
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ)
    (hscale : 0 ≤ (1 / 6 : ℝ) * P.h * P.k * P.Omega *
      Real.log P.OmegaOld)
    (hslack :
      2 * Fintype.card
          (ConstraintRow oldRank (initialRadius P) (initialBudget P)) ≤
        Fintype.card (LambdaBox (initialBoxShape P)))
    (hunknown :
      (Fintype.card (LambdaBox (initialBoxShape P)) : ℝ) ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld))
    (hmatrix :
      ‖(initialIntegralConstraintModel P b bLast alpha alphaLast).matrix‖ ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld)) :
    ∃ c : LambdaBox (initialBoxShape P) → ℤ, c ≠ 0 ∧
      (∀ row : ConstraintRow oldRank (initialRadius P) (initialBudget P),
        ∑ lambda, (c lambda : ℚ) *
          rationalConstraintEntry P.h b bLast alpha alphaLast row lambda = 0) ∧
      ‖c‖ ≤ P.coeffHeight := by
  let model := initialIntegralConstraintModel P b bLast alpha alphaLast
  obtain ⟨c, hc, heq, hheight⟩ :=
    exists_vdpl_auxiliary_coefficients model
      ((1 / 6 : ℝ) * P.h * P.k * P.Omega * Real.log P.OmegaOld)
      hscale (by simp [initialRadius, VDPLParameters.R, P.h_pos])
      hslack hunknown hmatrix
  refine ⟨c, hc, heq, ?_⟩
  unfold VDPLParameters.coeffHeight
  convert hheight using 1 <;> ring

/-- Source-faithful Lemma 2 coefficient construction.  This version uses
the raw Siegel bound together with the printed factor-eight dimension
margin, rather than the false intermediate demand that the matrix itself
fit inside `exp(H/6)`. -/
theorem exists_initial_auxiliary_coefficients_sourceHeight
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ)
    (hdim : initialDimensionRequirement P ∈ P.kRequirements)
    (hunknownReq : initialUnknownRequirement P ∈ P.kRequirements)
    (hmatrix :
      ‖(initialIntegralConstraintModel P b bLast alpha alphaLast).matrix‖ ≤
        Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld))) :
    ∃ c : LambdaBox (initialBoxShape P) → ℤ, c ≠ 0 ∧
      (∀ row : ConstraintRow oldRank (initialRadius P) (initialBudget P),
        ∑ lambda, (c lambda : ℚ) *
          rationalConstraintEntry P.h b bLast alpha alphaLast row lambda = 0) ∧
      ‖c‖ ≤ P.coeffHeight := by
  let model := initialIntegralConstraintModel P b bLast alpha alphaLast
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let M := Fintype.card
    (ConstraintRow oldRank (initialRadius P) (initialBudget P))
  let N := Fintype.card (LambdaBox (initialBoxShape P))
  have hMpos : 0 < M :=
    card_constraintRow_pos (by simp [initialRadius, VDPLParameters.R, P.h_pos])
  have hslack : 8 * M ≤ N :=
    initial_eight_cardinality_slack_of_requirement P hdim
  have hunder : M < N := by omega
  obtain ⟨c, hc, hequations, hheight⟩ :=
    exists_vdpl_auxiliary_coefficients_raw model
      (by simp [initialRadius, VDPLParameters.R, P.h_pos]) hunder
  refine ⟨c, hc, hequations, hheight.trans ?_⟩
  have hH : 0 ≤ H := by
    dsimp only [H]
    have hh : (0 : ℝ) ≤ P.h := by positivity
    have hk : 0 ≤ P.k := P.k_pos.le
    have hOmega : 0 ≤ P.Omega := P.Omega_pos.le
    have hlog : 0 ≤ Real.log P.OmegaOld := P.log_OmegaOld_pos.le
    positivity
  have hunknown : (N : ℝ) ≤ Real.exp (H / 6) := by
    dsimp only [N, H]
    convert initial_unknownCount_le_exp_heightScale P hunknownReq using 1 <;>
      ring
  have hfinal := siegel_rpow_le_exp_third hH hMpos hslack hunknown
    (by simpa only [model, H] using hmatrix)
  unfold VDPLParameters.coeffHeight
  have hheight_id :
      (1 / 3 : ℝ) * (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld =
        H / 3 := by
    dsimp only [H]
    ring
  rw [hheight_id]
  simpa only [M, N, model] using hfinal

/-- Canonical level-zero state obtained from the source-faithful raw Siegel
bound.  Unlike `exists_initial_levelState_vanishes` below, this endpoint uses
the printed factor-eight dimension margin and permits the integral matrix the
correct `exp(2H)` size. -/
theorem exists_initial_levelState_vanishes_sourceHeight
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hdim : initialDimensionRequirement P ∈ P.kRequirements)
    (hunknownReq : initialUnknownRequirement P ∈ P.kRequirements)
    (hmatrix :
      ‖(initialIntegralConstraintModel P b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
        Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld))) :
    ∃ state : Erdos240.BakerSourceState.LevelState P 0,
      Erdos240.VanishesOn
        (Erdos240.BakerSourceState.g state b bLast)
        1 (initialRadius P) (initialBudget P) := by
  obtain ⟨c, hc, hequations, hheight⟩ :=
    exists_initial_auxiliary_coefficients_sourceHeight P b bLast
      (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)
      hdim hunknownReq hmatrix
  have hpointwise : ∀ lambda, |(c lambda : ℝ)| ≤ P.coeffHeight := by
    intro lambda
    have hcomponent := (norm_le_pi_norm c lambda).trans hheight
    simpa only [Int.norm_eq_abs, Int.cast_abs, Int.cast_natCast] using hcomponent
  let state : Erdos240.BakerSourceState.LevelState P 0 :=
    Erdos240.BakerSourceState.LevelState.ofCoefficients c hc hpointwise
  refine ⟨state, ?_⟩
  apply Erdos240.BakerSourceState.levelZero_vanishes_of_auxiliaryEquations
    P state b bLast
  simpa only [state, Erdos240.BakerSourceState.LevelState.ofCoefficients] using
    hequations

/-- The same canonical source initialization with the matrix estimate
reduced to the explicit natural-number entry majorant established above. -/
theorem exists_initial_levelState_vanishes_of_majorant
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc) (hbLast : bLast.natAbs ≤ P.Bsrc)
    (hdim : initialDimensionRequirement P ∈ P.kRequirements)
    (hunknownReq : initialUnknownRequirement P ∈ P.kRequirements)
    (hmajorant : (initialMatrixMajorantNat P : ℝ) ≤
      Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) :
    ∃ state : Erdos240.BakerSourceState.LevelState P 0,
      Erdos240.VanishesOn
        (Erdos240.BakerSourceState.g state b bLast)
        1 (initialRadius P) (initialBudget P) := by
  apply exists_initial_levelState_vanishes_sourceHeight P b bLast
    hdim hunknownReq
  exact (norm_initialIntegralConstraintModel_le_majorant P b bLast hb hbLast).trans
    hmajorant

/-- Strong level-zero source initialization.  The rank-only admissibility
requirement supplies the full factor-two dimension slack, while the two
remaining hypotheses are precisely the column-count and matrix-entry
height estimates.  The returned canonical state carries nonzero integer
coefficients and their pointwise `coeffHeight` bound, and its algebraic
auxiliary function vanishes on the complete initial integral grid. -/
theorem exists_initial_levelState_vanishes
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hreq : initialDimensionRequirement P ∈ P.kRequirements)
    (hunknown :
      (Fintype.card (LambdaBox (initialBoxShape P)) : ℝ) ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld))
    (hmatrix :
      ‖(initialIntegralConstraintModel P b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld)) :
    ∃ state : Erdos240.BakerSourceState.LevelState P 0,
      Erdos240.VanishesOn
        (Erdos240.BakerSourceState.g state b bLast)
        1 (initialRadius P) (initialBudget P) := by
  have hh : (0 : ℝ) < P.h := by exact_mod_cast P.h_pos
  have hk : 0 < P.k := P.k_pos
  have hOmega : 0 < P.Omega := P.Omega_pos
  have hlog : 0 < Real.log P.OmegaOld := P.log_OmegaOld_pos
  have hscale :
      0 ≤ (1 / 6 : ℝ) * P.h * P.k * P.Omega *
        Real.log P.OmegaOld := by positivity
  have hslack := initial_cardinality_slack_of_requirement P hreq
  obtain ⟨c, hc, hequations, hheight⟩ :=
    exists_initial_auxiliary_coefficients P b bLast
      (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)
      hscale hslack hunknown hmatrix
  have hpointwise : ∀ lambda, |(c lambda : ℝ)| ≤ P.coeffHeight := by
    intro lambda
    have hcomponent := (norm_le_pi_norm c lambda).trans hheight
    simpa only [Int.norm_eq_abs, Int.cast_abs, Int.cast_natCast] using hcomponent
  let state : Erdos240.BakerSourceState.LevelState P 0 :=
    Erdos240.BakerSourceState.LevelState.ofCoefficients c hc hpointwise
  refine ⟨state, ?_⟩
  apply Erdos240.BakerSourceState.levelZero_vanishes_of_auxiliaryEquations
    P state b bLast
  simpa only [state, Erdos240.BakerSourceState.LevelState.ofCoefficients] using
    hequations

#print axioms Erdos240.BakerLemma2Concrete.initialIntegralConstraintModel
#print axioms Erdos240.BakerLemma2Concrete.exists_initial_levelState_vanishes_sourceHeight
#print axioms Erdos240.BakerLemma2Concrete.exists_initial_levelState_vanishes

end Erdos240.BakerLemma2Concrete

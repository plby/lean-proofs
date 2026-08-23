/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.Auxiliary
import ErdosProblems.Erdos240.DeltaPower
import ErdosProblems.Erdos240.IntegerValuedPolynomial
import ErdosProblems.Erdos240.SharpDeltaIndependent
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# The source-shaped auxiliary system in van der Poorten--Loxton Lemma 2

This file specializes the generic integral Siegel lemma from `Auxiliary.lean`
to the coefficient box and equations on pp. 40--42 of van der Poorten and
Loxton.  The last logarithm is distinguished.  Consequently a column has
coordinates

`(lambda_(-1), lambda_0, (lambda_r)_(r < oldRank), lambda_n)`,

and a row consists of an integral evaluation point together with the
multi-index `(m_0, (m_r)_(r < oldRank))` of total weight at most a prescribed
budget.

The rational matrix below is the literal matrix of the source.  The structure
`IntegralConstraintModel` records a row-wise denominator clearing, and
`IntegralConstraintModel.ofSourceData` constructs it unconditionally from the
checked sharp rational-grid and signed integer-grid theorems.  A row-wise
nonzero scaling preserves exactly the rational vanishing equations.
-/

noncomputable section

open scoped BigOperators Polynomial

namespace Erdos240.BakerAuxiliary

open Finset
open Erdos240.DeltaPower
open Erdos240.IntegerValuedPolynomial

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The four source side-length data.  Each number is the largest allowed
coordinate; hence the corresponding side has cardinality one more. -/
structure BoxShape (oldRank : ℕ) where
  shiftMax : ℕ
  deltaMax : ℕ
  oldMax : Fin oldRank → ℕ
  lastMax : ℕ

/-- The exact coefficient box
`0 ≤ lambda_(-1) ≤ L_(-1)`, `0 ≤ lambda_0 ≤ L_0`, and
`0 ≤ lambda_i ≤ L_i`.  A named structure prevents the elaborator from
repeatedly expanding the fourfold dependent product in later matrix types. -/
structure LambdaBox {oldRank : ℕ} (L : BoxShape oldRank) where
  shiftIndex : Fin (L.shiftMax + 1)
  deltaIndexFin : Fin (L.deltaMax + 1)
  oldExponentFin : ∀ r : Fin oldRank, Fin (L.oldMax r + 1)
  lastExponentFin : Fin (L.lastMax + 1)
  deriving DecidableEq, Fintype

def LambdaBox.shift {oldRank : ℕ} {L : BoxShape oldRank}
    (lambda : LambdaBox L) : ℕ := lambda.shiftIndex

def LambdaBox.deltaIndex {oldRank : ℕ} {L : BoxShape oldRank}
    (lambda : LambdaBox L) : ℕ := lambda.deltaIndexFin

def LambdaBox.oldExponent {oldRank : ℕ} {L : BoxShape oldRank}
    (lambda : LambdaBox L) (r : Fin oldRank) : ℕ := lambda.oldExponentFin r

def LambdaBox.lastExponent {oldRank : ℕ} {L : BoxShape oldRank}
    (lambda : LambdaBox L) : ℕ := lambda.lastExponentFin

/-- Exact number of unknown coefficients in the source box. -/
def unknownCount {oldRank : ℕ} (L : BoxShape oldRank) : ℕ :=
  (L.shiftMax + 1) * (L.deltaMax + 1) *
    ((∏ r, (L.oldMax r + 1)) * (L.lastMax + 1))

@[simp] theorem card_lambdaBox {oldRank : ℕ} (L : BoxShape oldRank) :
    Fintype.card (LambdaBox L) = unknownCount L := by
  let e : LambdaBox L ≃
      Fin (L.shiftMax + 1) × Fin (L.deltaMax + 1) ×
        ((∀ r : Fin oldRank, Fin (L.oldMax r + 1)) ×
          Fin (L.lastMax + 1)) :=
    { toFun := fun x ↦
        (x.shiftIndex, x.deltaIndexFin, x.oldExponentFin, x.lastExponentFin)
      invFun := fun x ↦ ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; rcases x with ⟨a, b, c, d⟩; rfl }
  rw [Fintype.card_congr e]
  simp [unknownCount, Nat.mul_assoc]

/-- The source derivative coordinates: `none` is `m_0`, while `some r` is
the derivative in the `r`-th old logarithmic direction. -/
abbrev DerivativeCoordinate (oldRank : ℕ) := Option (Fin oldRank)

/-- Multi-indices of total weight at most `budget`.  Coordinatewise bounding
by `budget` makes the type manifestly finite without changing the set. -/
structure BoundedMultiIndex (oldRank budget : ℕ) where
  coordinate : ∀ _ : DerivativeCoordinate oldRank, Fin (budget + 1)
  weight_le : ∑ i, (coordinate i : ℕ) ≤ budget
  deriving DecidableEq, Fintype

/-- A source equation is indexed by `1 ≤ ell ≤ radius` and a bounded
derivative multi-index. -/
structure ConstraintRow (oldRank radius budget : ℕ) where
  pointIndex : Fin radius
  multiIndex : BoundedMultiIndex oldRank budget
  deriving DecidableEq, Fintype

def ConstraintRow.point {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) : ℕ := row.pointIndex + 1

def ConstraintRow.order {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget)
    (i : DerivativeCoordinate oldRank) : ℕ := row.multiIndex.coordinate i

/-- Total normalized derivative order in a source equation. -/
def ConstraintRow.weight {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) : ℕ :=
  ∑ i, row.order i

theorem ConstraintRow.weight_le {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) : row.weight ≤ budget := by
  simpa only [ConstraintRow.weight, ConstraintRow.order] using
    row.multiIndex.weight_le

theorem card_boundedMultiIndex_le (oldRank budget : ℕ) :
    Fintype.card (BoundedMultiIndex oldRank budget) ≤
      (budget + 1) ^ (oldRank + 1) := by
  calc
    Fintype.card (BoundedMultiIndex oldRank budget) ≤
        Fintype.card (∀ _ : DerivativeCoordinate oldRank, Fin (budget + 1)) :=
      Fintype.card_le_of_injective (fun m ↦ m.coordinate) (by
        intro x y h
        cases x
        cases y
        congr)
    _ = (budget + 1) ^ (oldRank + 1) := by simp [DerivativeCoordinate]

/-- The source equation-count estimate
`M ≤ R (S+1)^n`, with `n = oldRank+1` logarithms. -/
theorem card_constraintRow_le (oldRank radius budget : ℕ) :
    Fintype.card (ConstraintRow oldRank radius budget) ≤
      radius * (budget + 1) ^ (oldRank + 1) := by
  calc
    Fintype.card (ConstraintRow oldRank radius budget) ≤
        Fintype.card (Fin radius × BoundedMultiIndex oldRank budget) :=
      Fintype.card_le_of_injective
        (fun row ↦ (row.pointIndex, row.multiIndex)) (by
          intro x y h
          rcases x with ⟨xp, xm⟩
          rcases y with ⟨yp, ym⟩
          rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          rfl)
    _ = radius * Fintype.card (BoundedMultiIndex oldRank budget) := by simp
    _ ≤ radius * (budget + 1) ^ (oldRank + 1) :=
      Nat.mul_le_mul_left radius (card_boundedMultiIndex_le oldRank budget)

/-- The multi-index of weight zero. -/
def zeroMultiIndex (oldRank budget : ℕ) : BoundedMultiIndex oldRank budget :=
  ⟨fun _ ↦ 0, by simp⟩

theorem card_constraintRow_pos {oldRank radius budget : ℕ}
    (hradius : 0 < radius) :
    0 < Fintype.card (ConstraintRow oldRank radius budget) := by
  classical
  exact Fintype.card_pos_iff.mpr
    ⟨⟨⟨0, hradius⟩, zeroMultiIndex oldRank budget⟩⟩

/-- The `Delta` factor denoted `A(ell;m)` in source equation (3).

The head is the four-argument powered derivative
`Delta(ell+lambda_(-1); h, lambda_0+1, m_0)`.  In contrast, every old
coordinate uses the source's two-argument polynomial
`Delta(x;m_r)=(x+1)...(x+m_r)/m_r!`.  In particular the old box side `L_r`
does not occur in this factor. -/
def sourceDeltaFactor {oldRank radius budget : ℕ}
    {L : BoxShape oldRank} (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LambdaBox L) : ℚ :=
  (poweredDeltaHasse h (lambda.deltaIndex + 1) (row.order none)).eval
      (((row.point : ℤ) + lambda.shift : ℤ) : ℚ) *
    ∏ r, (Erdos240Delta.delta (row.order (some r))).eval
        ((bLast * lambda.oldExponent r - b r * lambda.lastExponent : ℤ) : ℚ)

/-- The literal rational coefficient of `p(lambda)` in source equation (3)
for rational integral bases. -/
def rationalConstraintEntry {oldRank radius budget : ℕ}
    {L : BoxShape oldRank} (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LambdaBox L) : ℚ :=
  sourceDeltaFactor h b bLast row lambda *
    ((∏ r, alpha r ^ (lambda.oldExponent r * row.point)) *
      alphaLast ^ (lambda.lastExponent * row.point))

/-- The sharp source denominator at an integral evaluation point.

Only the four-argument head factor needs clearing, so this is `v(h)^m_0`.
The old two-argument Delta factors are already integer-valued at their signed
integer arguments. -/
def sourceRowDenominator {oldRank radius budget : ℕ}
    (h : ℕ) (row : ConstraintRow oldRank radius budget) : ℚ :=
  (Nat.lcmUpto h : ℚ) ^ row.order none

theorem sourceRowDenominator_ne_zero {oldRank radius budget : ℕ}
    (h : ℕ) (row : ConstraintRow oldRank radius budget) :
    sourceRowDenominator h row ≠ 0 := by
  simp only [sourceRowDenominator]
  exact pow_ne_zero _ (by
    exact_mod_cast (Nat.ne_of_gt (Nat.lcmUpto_pos h)))

/-- The sharp row denominator has exponential, rather than factorial,
growth.  This is where `LcmBound.lean` enters the source matrix estimate. -/
theorem sourceRowDenominator_le {oldRank radius budget : ℕ}
    (h : ℕ) (row : ConstraintRow oldRank radius budget) :
    sourceRowDenominator h row ≤ (512 : ℚ) ^ (h * budget) := by
  simp only [sourceRowDenominator]
  exact_mod_cast (show Nat.lcmUpto h ^ row.order none ≤ 512 ^ (h * budget) by
    calc
      Nat.lcmUpto h ^ row.order none ≤ (512 ^ h) ^ row.order none :=
        Nat.pow_le_pow_left (Erdos240.LcmBound.lcmUpto_le h) _
      _ = 512 ^ (h * row.order none) := by rw [pow_mul]
      _ ≤ 512 ^ (h * budget) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left h
          ((Finset.single_le_sum (fun i _ ↦ Nat.zero_le (row.order i))
            (Finset.mem_univ none)).trans row.weight_le)))

/-- The source row weight splits into the derivative order of the rational
evaluation factor and the orders of the constant integral factors. -/
theorem ConstraintRow.weight_eq_head_add_sum
    {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    row.weight = row.order none + ∑ r : Fin oldRank, row.order (some r) := by
  simp only [ConstraintRow.weight, Fintype.sum_option]

/-- Sharp denominator clearing for the literal source Delta product.

The first factor is deliberately discharged by the rational-grid theorem at
denominator `q = 1`; the remaining, possibly negative, constant arguments use
the integer-valued-polynomial theorem.  Thus this proof shares exactly the
normalization later used at `q^J`, while retaining the signed source shifts. -/
theorem exists_int_sourceRowDenominator_mul_sourceDeltaFactor
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LambdaBox L) :
    ∃ z : ℤ,
      sourceRowDenominator h row *
          sourceDeltaFactor h b bLast row lambda = (z : ℚ) := by
  classical
  obtain ⟨z0, hz0⟩ :=
    Erdos240.SharpDeltaIndependent.exists_int_cleared_poweredDeltaHasse_lcm
      h (lambda.deltaIndex + 1) (row.order none) 1
        (row.point + lambda.shift) (by norm_num)
  choose zr hzr using fun r : Fin oldRank ↦
    exists_int_lcmUpto_pow_mul_eval_deltaHasse
      (row.order (some r)) 0
        (bLast * lambda.oldExponent r - b r * lambda.lastExponent)
  have hz0' :
      (Nat.lcmUpto h : ℚ) ^ row.order none *
          ((Polynomial.hasseDeriv (row.order none))
            (Erdos240Delta.delta h ^ (lambda.deltaIndex + 1))).eval
              ((((row.point : ℤ) + lambda.shift : ℤ) : ℚ)) = (z0 : ℚ) := by
    simpa [poweredDeltaHasse, poweredDelta] using hz0
  have hzr' (r : Fin oldRank) :
      (Erdos240Delta.delta (row.order (some r))).eval
          ((bLast * lambda.oldExponent r -
            b r * lambda.lastExponent : ℤ) : ℚ) = (zr r : ℚ) := by
    simpa [Erdos240Delta.deltaHasse] using hzr r
  refine ⟨z0 * ∏ r, zr r, ?_⟩
  simp only [sourceRowDenominator, sourceDeltaFactor, poweredDeltaHasse]
  calc
    (Nat.lcmUpto h : ℚ) ^ row.order none *
        (((Polynomial.hasseDeriv (row.order none))
              (Erdos240Delta.delta h ^ (lambda.deltaIndex + 1))).eval
            (((row.point : ℤ) + lambda.shift : ℤ) : ℚ) *
          ∏ r, (Erdos240Delta.delta (row.order (some r))).eval
            ((bLast * lambda.oldExponent r -
              b r * lambda.lastExponent : ℤ) : ℚ)) =
        ((Nat.lcmUpto h : ℚ) ^ row.order none *
          ((Polynomial.hasseDeriv (row.order none))
              (Erdos240Delta.delta h ^ (lambda.deltaIndex + 1))).eval
            (((row.point : ℤ) + lambda.shift : ℤ) : ℚ)) *
          ∏ r, (Erdos240Delta.delta (row.order (some r))).eval
            ((bLast * lambda.oldExponent r -
              b r * lambda.lastExponent : ℤ) : ℚ) := by ring
    _ = (z0 : ℚ) * ∏ r, (zr r : ℚ) := by
      rw [hz0']
      apply congrArg ((z0 : ℚ) * ·)
      apply Finset.prod_congr rfl
      intro r _hr
      exact hzr' r
    _ = (z0 * ∏ r, zr r : ℤ) := by norm_cast

/-- Multiplication by the integral source monomials preserves the sharp row
integrality.  This is unconditional: callers no longer supply a clearing
certificate. -/
theorem exists_int_sourceRowDenominator_mul_rationalConstraintEntry
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LambdaBox L) :
    ∃ z : ℤ,
      sourceRowDenominator h row *
          rationalConstraintEntry h b bLast alpha alphaLast row lambda =
        (z : ℚ) := by
  obtain ⟨z, hz⟩ :=
    exists_int_sourceRowDenominator_mul_sourceDeltaFactor
      h b bLast row lambda
  refine ⟨z * ((∏ r, alpha r ^ (lambda.oldExponent r * row.point)) *
      alphaLast ^ (lambda.lastExponent * row.point)), ?_⟩
  rw [rationalConstraintEntry, ← mul_assoc, hz]
  norm_cast

/-- An integral realization of the literal rational system using exactly
the sharp normalization `v(h)^m` from Tijdeman's Lemma 1.  Existence of this
model is the single interface to the sharp denominator-clearing theorem; the
nonsharp factorial or `v(h)^(h*lambda)` estimates cannot instantiate it. -/
structure IntegralConstraintModel {oldRank radius budget : ℕ}
    {L : BoxShape oldRank} (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ) where
  matrix : Matrix (ConstraintRow oldRank radius budget) (LambdaBox L) ℤ
  matrix_cast_eq : ∀ row lambda,
    (matrix row lambda : ℚ) =
      sourceRowDenominator h row *
        rationalConstraintEntry h b bLast alpha alphaLast row lambda

/-- Construct the source integral matrix from the pointwise sharp
denominator-clearing conclusion of Tijdeman's Lemma 1. -/
noncomputable def IntegralConstraintModel.ofSharpClearing
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ)
    (hsharp : ∀ row : ConstraintRow oldRank radius budget,
      ∀ lambda : LambdaBox L, ∃ z : ℤ,
        sourceRowDenominator h row *
          rationalConstraintEntry h b bLast alpha alphaLast row lambda =
            (z : ℚ)) :
    IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast where
  matrix row lambda := Classical.choose (hsharp row lambda)
  matrix_cast_eq row lambda := (Classical.choose_spec (hsharp row lambda)).symm

/-- The unconditional sharp integral model for the literal source rows. -/
noncomputable def IntegralConstraintModel.ofSourceData
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℤ) (alphaLast : ℤ) :
    IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast :=
  IntegralConstraintModel.ofSharpClearing h b bLast alpha alphaLast
    (fun row lambda ↦
      exists_int_sourceRowDenominator_mul_rationalConstraintEntry
        h b bLast alpha alphaLast row lambda)

/-- Entrywise size after the sharp clearing.  This isolates the exact
`512^(h*S)` denominator contribution from the remaining source estimate. -/
theorem abs_matrix_cast_le_of_rational_entry
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast)
    (entryBound : ℚ) (hentryBound : 0 ≤ entryBound)
    (hentry : ∀ (row : ConstraintRow oldRank radius budget)
      (lambda : LambdaBox L),
      |rationalConstraintEntry h b bLast alpha alphaLast row lambda| ≤
        entryBound) (row : ConstraintRow oldRank radius budget)
    (lambda : LambdaBox L) :
    |(model.matrix row lambda : ℚ)| ≤
      (512 : ℚ) ^ (h * budget) * entryBound := by
  have hdennonneg : 0 ≤ sourceRowDenominator h row := by
    simp only [sourceRowDenominator]
    positivity
  rw [model.matrix_cast_eq, abs_mul, abs_of_nonneg hdennonneg]
  calc
      sourceRowDenominator h row *
            |rationalConstraintEntry h b bLast alpha alphaLast row lambda| ≤
          sourceRowDenominator h row * entryBound :=
        mul_le_mul_of_nonneg_left (hentry row lambda) hdennonneg
      _ ≤ (512 : ℚ) ^ (h * budget) * entryBound :=
        mul_le_mul_of_nonneg_right (sourceRowDenominator_le h row) hentryBound

/-- Convert a pointwise bound for an integral realization into the matrix
sup-norm bound required by Siegel's lemma. -/
theorem norm_matrix_le_of_entrywise
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast)
    (matrixBound : ℝ) (hbound : 0 ≤ matrixBound)
    (hentry : ∀ row lambda, ‖model.matrix row lambda‖ ≤ matrixBound) :
    ‖model.matrix‖ ≤ matrixBound := by
  rw [Matrix.norm_le_iff hbound]
  exact hentry

/-- The source-shaped constraint matrix associated to an integral model. -/
def vdplConstraintMatrix {oldRank radius budget : ℕ}
    {L : BoxShape oldRank} {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast) :
    Matrix (ConstraintRow oldRank radius budget) (LambdaBox L) ℤ := model.matrix

/-- The integral kernel equations imply exactly the rational source
equations. -/
theorem rational_equations_of_mulVec_eq_zero
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast)
    (c : LambdaBox L → ℤ) (hc : model.matrix.mulVec c = 0) :
    ∀ row : ConstraintRow oldRank radius budget, ∑ lambda, (c lambda : ℚ) *
      rationalConstraintEntry h b bLast alpha alphaLast row lambda = 0 := by
  classical
  intro row
  have hrow := congrFun hc row
  simp only [Matrix.mulVec, dotProduct] at hrow
  have hrowQ :
      (∑ lambda, (model.matrix row lambda : ℚ) * (c lambda : ℚ)) = 0 := by
    exact_mod_cast hrow
  have hscaled : sourceRowDenominator h row *
      (∑ lambda, (c lambda : ℚ) *
        rationalConstraintEntry h b bLast alpha alphaLast row lambda) = 0 := by
    rw [Finset.mul_sum]
    simpa only [model.matrix_cast_eq, mul_assoc, mul_left_comm, mul_comm] using hrowQ
  exact (mul_eq_zero.mp hscaled).resolve_left (by
    simp only [sourceRowDenominator]
    exact pow_ne_zero _ (by
      exact_mod_cast (Nat.ne_of_gt (Nat.lcmUpto_pos h))))

/-- A convenient sufficient dimension inequality, expressed using only the
visible source parameters. -/
theorem card_row_lt_card_box_of_bound
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (hdim : radius * (budget + 1) ^ (oldRank + 1) < unknownCount L) :
    Fintype.card (ConstraintRow oldRank radius budget) <
      Fintype.card (LambdaBox L) := by
  rw [card_lambdaBox]
  exact (card_constraintRow_le oldRank radius budget).trans_lt hdim

/-- The elementary real estimate which turns the explicit Siegel-lemma
bound into an exponential height.  It is kept independent of the source
index types so elaborating the auxiliary theorem remains inexpensive. -/
theorem siegel_rpow_le_exp_two {M N : ℕ} {matrixNorm heightScale : ℝ}
    (hscale : 0 ≤ heightScale) (hMpos : 0 < M)
    (hslack : 2 * M ≤ N)
    (hN : (N : ℝ) ≤ Real.exp heightScale)
    (hmatrix : matrixNorm ≤ Real.exp heightScale) :
    (((N : ℝ) * max 1 matrixNorm) ^
        ((M : ℝ) / ((N : ℝ) - (M : ℝ)))) ≤
      Real.exp (2 * heightScale) := by
  have hMN : M < N := by omega
  have hden : (0 : ℝ) ≤ (N : ℝ) - (M : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hMN.le)
  have he_nonneg : 0 ≤ (M : ℝ) / ((N : ℝ) - (M : ℝ)) :=
    div_nonneg (by positivity) hden
  have he_le : (M : ℝ) / ((N : ℝ) - (M : ℝ)) ≤ 1 := by
    have hdenpos : (0 : ℝ) < (N : ℝ) - (M : ℝ) :=
      sub_pos.mpr (by exact_mod_cast hMN)
    rw [div_le_iff₀ hdenpos]
    have hslackR : 2 * (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hslack
    linarith
  have hexp_one : 1 ≤ Real.exp heightScale := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hscale
  have hmax : max 1 matrixNorm ≤ Real.exp heightScale :=
    max_le hexp_one hmatrix
  have hbase_le : (N : ℝ) * max 1 matrixNorm ≤
      Real.exp (2 * heightScale) := by
    calc
      (N : ℝ) * max 1 matrixNorm ≤
          Real.exp heightScale * Real.exp heightScale :=
        mul_le_mul hN hmax (le_trans (by norm_num) (le_max_left _ _))
          (Real.exp_pos _).le
      _ = Real.exp (2 * heightScale) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    ((N : ℝ) * max 1 matrixNorm) ^
          ((M : ℝ) / ((N : ℝ) - (M : ℝ))) ≤
        (Real.exp (2 * heightScale)) ^
          ((M : ℝ) / ((N : ℝ) - (M : ℝ))) :=
      Real.rpow_le_rpow (by positivity) hbase_le he_nonneg
    _ ≤ (Real.exp (2 * heightScale)) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        positivity
      · exact he_le
    _ = Real.exp (2 * heightScale) := Real.rpow_one _

/-- The exact integral Siegel-lemma output before simplifying its height. -/
theorem exists_vdpl_auxiliary_coefficients_raw
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast)
    (hradius : 0 < radius)
    (hunder : Fintype.card (ConstraintRow oldRank radius budget) <
      Fintype.card (LambdaBox L)) :
    ∃ c : LambdaBox L → ℤ, c ≠ 0 ∧
      (∀ row : ConstraintRow oldRank radius budget,
        ∑ lambda, (c lambda : ℚ) *
        rationalConstraintEntry h b bLast alpha alphaLast row lambda = 0) ∧
      ‖c‖ ≤
        (Fintype.card (LambdaBox L) * max 1 ‖model.matrix‖) ^
          ((Fintype.card (ConstraintRow oldRank radius budget) : ℝ) /
            (Fintype.card (LambdaBox L) -
              Fintype.card (ConstraintRow oldRank radius budget))) := by
  classical
  have hrows : 0 < Fintype.card (ConstraintRow oldRank radius budget) :=
    card_constraintRow_pos hradius
  obtain ⟨c, hcne, hkernel, hc⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le model.matrix hunder hrows
  exact ⟨c, hcne, rational_equations_of_mulVec_eq_zero model c hkernel, hc⟩

/-- Quantitative Siegel lemma in the form used by Lemma 2.  If the number of
columns is at least twice the number of rows, and both the column count and
the integral matrix height are at most `exp(heightScale)`, then a nonzero
kernel vector has height at most `exp(2*heightScale)`.

In the application `heightScale` is a fixed constant times
`OmegaOld * log Anew * log B`.  Thus the varying final height remains a
visible *linear* factor, rather than being absorbed into a non-uniform
constant. -/
theorem exists_vdpl_auxiliary_coefficients
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast)
    (heightScale : ℝ) (hscale : 0 ≤ heightScale)
    (hradius : 0 < radius)
    (hslack : 2 * Fintype.card (ConstraintRow oldRank radius budget) ≤
      Fintype.card (LambdaBox L))
    (hunknown : (Fintype.card (LambdaBox L) : ℝ) ≤ Real.exp heightScale)
    (hmatrix : ‖model.matrix‖ ≤ Real.exp heightScale) :
    ∃ c : LambdaBox L → ℤ, c ≠ 0 ∧
      (∀ row : ConstraintRow oldRank radius budget,
        ∑ lambda, (c lambda : ℚ) *
        rationalConstraintEntry h b bLast alpha alphaLast row lambda = 0) ∧
      ‖c‖ ≤ Real.exp (2 * heightScale) := by
  classical
  have hrows : 0 < Fintype.card (ConstraintRow oldRank radius budget) :=
    card_constraintRow_pos hradius
  have hunder : Fintype.card (ConstraintRow oldRank radius budget) <
      Fintype.card (LambdaBox L) := by omega
  obtain ⟨c, hcne, heq, hc⟩ :=
    exists_vdpl_auxiliary_coefficients_raw model hradius hunder
  refine ⟨c, hcne, heq, hc.trans ?_⟩
  exact siegel_rpow_le_exp_two hscale hrows hslack hunknown hmatrix

/-- The preceding theorem with the desired dependence written literally.
The constants and the old-height product may be fixed, while `logAnew` and
`logB` remain visible. -/
theorem exists_vdpl_auxiliary_coefficients_height_shape
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℤ} {alphaLast : ℤ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast alpha alphaLast)
    (constant omegaOld logAnew logB : ℝ)
    (hconstant : 0 ≤ constant) (homega : 0 ≤ omegaOld)
    (hAnew : 0 ≤ logAnew) (hB : 0 ≤ logB)
    (hradius : 0 < radius)
    (hslack : 2 * Fintype.card (ConstraintRow oldRank radius budget) ≤
      Fintype.card (LambdaBox L))
    (hunknown : (Fintype.card (LambdaBox L) : ℝ) ≤
      Real.exp (constant * omegaOld * logAnew * logB))
    (hmatrix : ‖model.matrix‖ ≤
      Real.exp (constant * omegaOld * logAnew * logB)) :
    ∃ c : LambdaBox L → ℤ, c ≠ 0 ∧
      (∀ row : ConstraintRow oldRank radius budget,
        ∑ lambda, (c lambda : ℚ) *
        rationalConstraintEntry h b bLast alpha alphaLast row lambda = 0) ∧
      ‖c‖ ≤ Real.exp
        (2 * constant * omegaOld * logAnew * logB) := by
  have hscale : 0 ≤ constant * omegaOld * logAnew * logB := by positivity
  simpa only [mul_assoc] using
    exists_vdpl_auxiliary_coefficients model
      (constant * omegaOld * logAnew * logB) hscale hradius hslack
      hunknown hmatrix

#print axioms Erdos240.BakerAuxiliary.card_constraintRow_le
#print axioms
  Erdos240.BakerAuxiliary.exists_int_sourceRowDenominator_mul_rationalConstraintEntry
#print axioms Erdos240.BakerAuxiliary.IntegralConstraintModel.ofSourceData
#print axioms Erdos240.BakerAuxiliary.rational_equations_of_mulVec_eq_zero
#print axioms Erdos240.BakerAuxiliary.exists_vdpl_auxiliary_coefficients_height_shape

end Erdos240.BakerAuxiliary

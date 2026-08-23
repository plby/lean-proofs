/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerAuxiliary
import ErdosProblems.Erdos240.BakerLemma3
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Concrete coefficient states for the van der Poorten--Loxton induction

This file gives a single source of truth for the objects propagated through
Lemmas 3--6.  The old logarithms are indexed by `Fin oldRank`; the varying
prime is the distinguished last logarithm.

At level `J` the two polynomial coordinates `lambda_(-1)` and `lambda_0`
retain their original sides.  The ambient old and last exponential
coordinates have upper bound

`floor (q^(-J) * L_i(0))`.

A `LevelState P J` is an integer coefficient family padded to this box and
carries its genuine active sides.  Those sides may be smaller after a
residue selection, and every nonzero coefficient is required to lie inside
them.  They control the coefficient ranges only: the corrected old Delta
factors are the ordinary two-argument polynomials `Delta(x;m_r)`.
The definitions `A`, `fWithLogs`, and `gWithLogs` use the corrected source
normalization: only the Delta factor `A` is evaluated at `z / q^J`;
the exponential monomial is evaluated at the unscaled argument `z`.  Thus
at an integer `l`, the algebraic function contains `alpha_i^(lambda_i*l)`,
which is exactly the monomial needed for the residue-class descent.

The old rate in `f` is
`lambda_i - b_i * lambda_last / b_last`.

The final section proves two definitional interfaces needed downstream:

* the old Delta factor at `z/q` is identified with the residue-lifted factor
  `A'` at the successor scale; no direct equality with the canonical next
  `A`, `f`, or `g` is asserted, because that replacement is the source's
  separate inner polynomial induction;
* at level zero the rational equations produced by `BakerAuxiliary` are
  literally the values of `g` at the corresponding integral points.
-/

open scoped BigOperators Polynomial

noncomputable section

namespace Erdos240.BakerSourceState

open Finset
open Erdos240
open Erdos240.BakerAuxiliary
open Erdos240.BakerLemma3

/-- The level-`J` maximum associated to an initial exponential side `L`.
This is the literal natural floor of `q^(-J) L`. -/
def scaledExponentMax {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (J L : ℕ) : ℕ :=
  ⌊P.qInvPow J * (L : ℝ)⌋₊

@[simp] theorem scaledExponentMax_zero {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (L : ℕ) :
    scaledExponentMax P 0 L = L := by
  simp [scaledExponentMax, VDPLParameters.qInvPow]

/-- The real-floor formula is exactly natural division.  This bridge is
useful in the residue and final zero-count layers, which naturally phrase
the same side as `L / q^J`. -/
theorem scaledExponentMax_eq_div {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J L : ℕ) :
    scaledExponentMax P J L = L / P.q ^ J := by
  have hrewrite : P.qInvPow J * (L : ℝ) =
      (L : ℝ) / ((P.q ^ J : ℕ) : ℝ) := by
    unfold VDPLParameters.qInvPow
    rw [div_eq_mul_inv]
    ring
  unfold scaledExponentMax
  rw [hrewrite]
  exact Nat.floor_div_eq_div L (P.q ^ J)

theorem scaledExponentMax_cast_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J L : ℕ) :
    (scaledExponentMax P J L : ℝ) ≤ P.qInvPow J * (L : ℝ) := by
  exact Nat.floor_le (mul_nonneg (P.qInvPow_pos J).le (Nat.cast_nonneg L))

theorem scaledExponentMax_le_initial {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J L : ℕ) :
    scaledExponentMax P J L ≤ L := by
  have hq : P.qInvPow J ≤ 1 := by
    have h := P.qInvPow_antitone (Nat.zero_le J)
    simpa [VDPLParameters.qInvPow] using h
  exact_mod_cast (calc
    (scaledExponentMax P J L : ℝ) ≤ P.qInvPow J * (L : ℝ) :=
      scaledExponentMax_cast_le P J L
    _ ≤ 1 * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg L)
    _ = (L : ℝ) := one_mul _)

/-- The exact source box at level `J`.

* `shiftMax` is `lambda_(-1)`;
* `deltaMax` is `lambda_0`;
* `oldMax r` is the old exponential coordinate `lambda_r`;
* `lastMax` is the distinguished varying-prime coordinate.

Only the last two kinds are divided by `q^J`. -/
def levelBoxShape {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (J : ℕ) : BoxShape oldRank where
  shiftMax := P.LminusOne
  deltaMax := P.Lzero
  oldMax r := scaledExponentMax P J (P.LiZero r)
  lastMax := scaledExponentMax P J P.LlastZero

/-- The initial source box.  Defining it as level zero makes the coefficient
type in Lemma 2 and the base state judgmentally identical. -/
abbrev initialBoxShape {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) :
    BoxShape oldRank := levelBoxShape P 0

@[simp] theorem levelBoxShape_shiftMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (levelBoxShape P J).shiftMax = P.LminusOne := rfl

@[simp] theorem levelBoxShape_deltaMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (levelBoxShape P J).deltaMax = P.Lzero := rfl

@[simp] theorem levelBoxShape_oldMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (r : Fin oldRank) :
    (levelBoxShape P J).oldMax r =
      ⌊P.qInvPow J * (P.LiZero r : ℝ)⌋₊ := rfl

theorem levelBoxShape_oldMax_eq_div {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (r : Fin oldRank) :
    (levelBoxShape P J).oldMax r = P.LiZero r / P.q ^ J :=
  scaledExponentMax_eq_div P J (P.LiZero r)

@[simp] theorem levelBoxShape_lastMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (levelBoxShape P J).lastMax =
      ⌊P.qInvPow J * (P.LlastZero : ℝ)⌋₊ := rfl

theorem levelBoxShape_lastMax_eq_div {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (levelBoxShape P J).lastMax = P.LlastZero / P.q ^ J :=
  scaledExponentMax_eq_div P J P.LlastZero

theorem levelBoxShape_oldMax_le_initial {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (r : Fin oldRank) :
    (levelBoxShape P J).oldMax r ≤ P.LiZero r :=
  scaledExponentMax_le_initial P J (P.LiZero r)

theorem levelBoxShape_lastMax_le_initial {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (levelBoxShape P J).lastMax ≤ P.LlastZero :=
  scaledExponentMax_le_initial P J P.LlastZero

/-- Once the chosen terminal power of `q` strictly exceeds the real initial
last-coordinate side, the last side of the level box is zero.  This is the
exact endpoint bridge used after choosing `N` with
`LlastZeroScale < q^N ≤ levelBound`; the definition of `levelBound` itself
uses the corrected exponent `1 - (sigma - epsilon)`. -/
theorem levelBoxShape_lastMax_eq_zero_of_scale_lt_qpow {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (hterminal : P.LlastZeroScale < ((P.q ^ J : ℕ) : ℝ)) :
    (levelBoxShape P J).lastMax = 0 := by
  rw [levelBoxShape_lastMax_eq_div]
  apply Nat.div_eq_of_lt
  exact_mod_cast lt_of_le_of_lt P.LlastZero_cast_le hterminal

@[simp] theorem initialBoxShape_oldMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (r : Fin oldRank) :
    (initialBoxShape P).oldMax r = P.LiZero r := by
  simp [initialBoxShape, levelBoxShape]

@[simp] theorem initialBoxShape_lastMax {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (initialBoxShape P).lastMax = P.LlastZero := by
  simp [initialBoxShape, levelBoxShape]

/-- Coefficient indices at level `J`. -/
abbrev LevelIndex {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (J : ℕ) := LambdaBox (levelBoxShape P J)

/-- The concrete state propagated by source Lemma 6.

The ambient index type is the canonical level-`J` upper box.  The actual
sides `oldSide` and `lastSide` are allowed to be smaller: after selecting a
residue `rho`, the next side is `floor ((L-rho)/q)`, which need not equal the
canonical upper bound `floor (L(0)/q^(J+1))`.  Coefficients outside the active
box are required to vanish.  This padded presentation avoids dependent-type
transport while retaining the exact source coefficient ranges. -/
structure LevelState {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (J : ℕ) where
  coeff : LevelIndex P J → ℤ
  coeff_ne_zero : coeff ≠ 0
  coeff_height : ∀ lambda, |(coeff lambda : ℝ)| ≤ P.coeffHeight
  oldSide : Fin oldRank → ℕ
  lastSide : ℕ
  oldSide_le : ∀ r, oldSide r ≤ (levelBoxShape P J).oldMax r
  lastSide_le : lastSide ≤ (levelBoxShape P J).lastMax
  coeff_ne_zero_inside : ∀ lambda, coeff lambda ≠ 0 →
    (∀ r, lambda.oldExponent r ≤ oldSide r) ∧
      lambda.lastExponent ≤ lastSide
  initial_oldSide : J = 0 → oldSide = P.LiZero
  initial_lastSide : J = 0 → lastSide = P.LlastZero

namespace LevelState

variable {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}

/-- The genuine source shape represented by a padded state. -/
def activeShape (state : LevelState P J) : BoxShape oldRank where
  shiftMax := P.LminusOne
  deltaMax := P.Lzero
  oldMax := state.oldSide
  lastMax := state.lastSide

/-- The coefficient support is the complete finite source box. -/
def support (_state : LevelState P J) : Finset (LevelIndex P J) := univ

@[simp] theorem mem_support (state : LevelState P J) (lambda : LevelIndex P J) :
    lambda ∈ state.support := by
  simp [support]

/-- A nonzero coefficient family has an actual nonzero entry. -/
theorem exists_coeff_ne_zero (state : LevelState P J) :
    ∃ lambda, state.coeff lambda ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply state.coeff_ne_zero
  funext lambda
  exact h lambda

/-- Build a state once the coefficient construction has supplied the two
facts which Lemma 6 propagates. -/
def ofCoefficients (coeff : LevelIndex P J → ℤ) (coeff_ne_zero : coeff ≠ 0)
    (coeff_height : ∀ lambda, |(coeff lambda : ℝ)| ≤ P.coeffHeight) :
    LevelState P J where
  coeff := coeff
  coeff_ne_zero := coeff_ne_zero
  coeff_height := coeff_height
  oldSide r := (levelBoxShape P J).oldMax r
  lastSide := (levelBoxShape P J).lastMax
  oldSide_le _ := le_rfl
  lastSide_le := le_rfl
  coeff_ne_zero_inside lambda _ := by
    constructor
    · intro r
      exact Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt
    · exact Nat.le_of_lt_succ lambda.lastExponentFin.isLt
  initial_oldSide hJ := by
    subst J
    funext r
    exact initialBoxShape_oldMax P r
  initial_lastSide hJ := by
    subst J
    exact initialBoxShape_lastMax P

/-- Construct a state with the genuine active side lengths supplied by a
residue descent. -/
def ofActiveCoefficients (coeff : LevelIndex P J → ℤ)
    (coeff_ne_zero : coeff ≠ 0)
    (coeff_height : ∀ lambda, |(coeff lambda : ℝ)| ≤ P.coeffHeight)
    (oldSide : Fin oldRank → ℕ) (lastSide : ℕ)
    (oldSide_le : ∀ r, oldSide r ≤ (levelBoxShape P J).oldMax r)
    (lastSide_le : lastSide ≤ (levelBoxShape P J).lastMax)
    (coeff_ne_zero_inside : ∀ lambda, coeff lambda ≠ 0 →
      (∀ r, lambda.oldExponent r ≤ oldSide r) ∧
        lambda.lastExponent ≤ lastSide)
    (initial_oldSide : J = 0 → oldSide = P.LiZero)
    (initial_lastSide : J = 0 → lastSide = P.LlastZero) :
    LevelState P J :=
  ⟨coeff, coeff_ne_zero, coeff_height, oldSide, lastSide, oldSide_le,
    lastSide_le, coeff_ne_zero_inside, initial_oldSide, initial_lastSide⟩

/-- At a terminal level, the genuine last side is zero as well as its
canonical upper bound. -/
theorem lastSide_eq_zero_of_scale_lt_qpow [Nonempty (Fin oldRank)]
    (state : LevelState P J)
    (hterminal : P.LlastZeroScale < ((P.q ^ J : ℕ) : ℝ)) :
    state.lastSide = 0 := by
  have hmax := levelBoxShape_lastMax_eq_zero_of_scale_lt_qpow P J hterminal
  have hle := state.lastSide_le
  rw [hmax] at hle
  exact Nat.eq_zero_of_le_zero hle

end LevelState

/-- Canonical coordinate projections from the concrete level box. -/
def coordinates {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ} :
    SourceCoordinates oldRank (LevelIndex P J) where
  shift := LambdaBox.shift
  deltaIndex := LambdaBox.deltaIndex
  oldExponent := LambdaBox.oldExponent
  lastExponent := LambdaBox.lastExponent

/-- The coordinate projections associated with a state.  The active side
lengths remain state bookkeeping for the residue descent; the corrected
two-argument old Delta factors do not use them. -/
def coordinatesForState {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (_state : LevelState P J) :
    SourceCoordinates oldRank (LevelIndex P J) := coordinates

/-- The positive real logarithms of the fixed old prime bases. -/
def oldLog {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (r : Fin oldRank) : ℂ :=
  (Real.log (P.old r : ℝ) : ℂ)

/-- The positive real logarithm of the distinguished varying prime. -/
def lastLog {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) : ℂ :=
  (Real.log (P.newPrime : ℝ) : ℂ)

/-- The corrected Delta-polynomial factor `A_J(z;m;lambda)`.  The head is
the powered derivative, while each old coordinate contributes the
two-argument polynomial `Delta(x;m_r)`. -/
def A {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (lambda : LevelIndex P J)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  auxiliaryFactor (coordinatesForState state) P.h b bLast lambda
    (scaledArgument P.q J z) m

/-- The corrected analytic function `f_J`, with its logarithms explicit. -/
def fWithLogs {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) :
    ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  fun z m ↦
    ExponentialPolynomial.ordinaryDerivative state.support
      (fun lambda ↦ (state.coeff lambda : ℂ) * A state b bLast lambda z m)
      (modifiedRate coordinates b bLast logAlpha) 0 z

/-- The corrected algebraic function `g_J`, with its logarithms explicit. -/
def gWithLogs {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ) :
    ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  fun z m ↦
    ExponentialPolynomial.ordinaryDerivative state.support
      (fun lambda ↦ (state.coeff lambda : ℂ) * A state b bLast lambda z m)
      (algebraicRate coordinates logAlpha logAlphaLast) 0 z

/-- The canonical equivalence between the parameter rank and the explicit
`oldRank+1` indexing used by the corrected source formulas. -/
def rankEquiv {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) :
    Fin P.rank ≃ Fin (oldRank + 1) :=
  finCongr (by simp [VDPLParameters.rank])

/-- Reindex a parameter-rank multi-index for the corrected source formulas. -/
def toSourceMultiIndex {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (m : VDPLMultiIndex P.rank) : VDPLMultiIndex (oldRank + 1) :=
  fun i ↦ m ((rankEquiv P).symm i)

/-- Reindex a corrected-source multi-index back to the parameter rank. -/
def fromSourceMultiIndex {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (m : VDPLMultiIndex (oldRank + 1)) : VDPLMultiIndex P.rank :=
  fun i ↦ m (rankEquiv P i)

@[simp] theorem toSourceMultiIndex_fromSourceMultiIndex {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (m : VDPLMultiIndex (oldRank + 1)) :
    toSourceMultiIndex P (fromSourceMultiIndex P m) = m := by
  funext i
  exact congrArg m ((rankEquiv P).apply_symm_apply i)

@[simp] theorem fromSourceMultiIndex_toSourceMultiIndex {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (m : VDPLMultiIndex P.rank) :
    fromSourceMultiIndex P (toSourceMultiIndex P m) = m := by
  funext i
  exact congrArg m ((rankEquiv P).symm_apply_apply i)

theorem weight_toSourceMultiIndex {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (m : VDPLMultiIndex P.rank) :
    VDPLMultiIndex.weight (toSourceMultiIndex P m) =
      VDPLMultiIndex.weight m := by
  exact (rankEquiv P).symm.sum_comp m

theorem weight_fromSourceMultiIndex {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (m : VDPLMultiIndex (oldRank + 1)) :
    VDPLMultiIndex.weight (fromSourceMultiIndex P m) =
      VDPLMultiIndex.weight m := by
  exact (rankEquiv P).sum_comp m

/-- Source-indexed `f_J`, useful inside termwise identities. -/
def fSource {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) :
    ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  fWithLogs state b bLast (oldLog P)

/-- Source-indexed `g_J`, useful inside termwise identities. -/
def gSource {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) :
    ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  gWithLogs state b bLast (oldLog P) (lastLog P)

/-- `f_J` specialized to the rational-prime logarithms in `P`, indexed by
the exact rank carried by `P`. -/
def f {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) :
    ℂ → VDPLMultiIndex P.rank → ℂ :=
  fun z m ↦ fSource state b bLast z (toSourceMultiIndex P m)

/-- `g_J` specialized to the rational-prime logarithms in `P`, indexed by
the exact rank carried by `P`. -/
def g {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) :
    ℂ → VDPLMultiIndex P.rank → ℂ :=
  fun z m ↦ gSource state b bLast z (toSourceMultiIndex P m)

/-- Sum form of `f_J`. -/
theorem fWithLogs_eq_sum {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    fWithLogs state b bLast logAlpha z m =
      ∑ lambda, (state.coeff lambda : ℂ) *
        A state b bLast lambda z m *
          Complex.exp
            (modifiedRate coordinates b bLast logAlpha lambda *
              z) := by
  simp [fWithLogs, LevelState.support,
    ExponentialPolynomial.ordinaryDerivative, mul_assoc]

/-- Sum form of `g_J`. -/
theorem gWithLogs_eq_sum {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    gWithLogs state b bLast logAlpha logAlphaLast z m =
      ∑ lambda, (state.coeff lambda : ℂ) *
        A state b bLast lambda z m *
          Complex.exp
            (algebraicRate coordinates logAlpha logAlphaLast lambda *
              z) := by
  simp [gWithLogs, LevelState.support,
    ExponentialPolynomial.ordinaryDerivative, mul_assoc]

/-! ## Exact scaling identities -/

/-- The source argument has the exact recursion
`(z / q) / q^J = z / q^(J+1)`. -/
theorem scaledArgument_succ {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) :
    scaledArgument P.q (J + 1) z =
      scaledArgument P.q J (z / (P.q : ℂ)) := by
  have hq : (P.q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))
  unfold scaledArgument
  rw [pow_succ]
  field_simp [hq]

/-- Scaling identity for the corrected `A` factor, for a fixed coefficient
box.  This form is used while extracting the next residue class. -/
theorem auxiliaryFactor_scale_succ {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I) (J : ℕ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    auxiliaryFactor coord P.h b bLast lambda
        (scaledArgument P.q (J + 1) z) m =
      auxiliaryFactor coord P.h b bLast lambda
        (scaledArgument P.q J (z / (P.q : ℂ))) m := by
  rw [scaledArgument_succ]

/-! ## The intermediate residue-lifted factor

The source proof of Lemma 6 has a genuine intermediate object which must not
be confused with the next canonical state.  After a residue vector `rho` has
been selected, an old exponential coordinate has the form

`rho_i + q * mu_i`.

In the equation obtained directly from radical independence, the exponential
monomial is already indexed by the quotient `mu`, while the Delta factor still
contains the lifted coordinate `rho_i + q * mu_i`.  Van der Poorten--Loxton
call this factor `A'` on p. 51.  Their inner induction subsequently replaces
`A'` by the canonical `A` indexed by `mu`; that replacement is not a
definitional scaling identity.  The definitions below expose precisely the
intermediate factor and the identities which *are* definitional.
-/

/-- A residue choice for all exponential coordinates. -/
structure ExponentResidue {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) where
  old : Fin oldRank → Fin P.q
  last : Fin P.q

/-- Coordinates used by the source's intermediate factor `A'`: the shift and
head-power coordinate are unchanged, while each exponential coordinate is
lifted from `mu` to `rho + q*mu`. -/
def residueLiftCoordinates {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (_state : LevelState P J)
    (rho : ExponentResidue P) :
    SourceCoordinates oldRank (LevelIndex P (J + 1)) where
  shift := LambdaBox.shift
  deltaIndex := LambdaBox.deltaIndex
  oldExponent := fun mu r ↦ (rho.old r : ℕ) + P.q * mu.oldExponent r
  lastExponent := fun mu ↦ (rho.last : ℕ) + P.q * mu.lastExponent

/-- The intermediate factor `A'` in the residue descent.  Notice that its
Delta argument is already the successor argument `z/q^(J+1)`, but its head
power and constant evaluation points use the residue-lifted coordinates. -/
def residueLiftA {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (mu : LevelIndex P (J + 1)) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  auxiliaryFactor (residueLiftCoordinates state rho) P.h b bLast mu
    (scaledArgument P.q (J + 1) z) m

/-- The exact relation between an old index and a quotient index in a selected
residue fibre.  It is stated independently of the particular implementation
of the quotient map so the state layer does not depend cyclically on Lemma 6. -/
structure ResidueLiftAgreement {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (rho : ExponentResidue P)
    (lambda : LevelIndex P J) (mu : LevelIndex P (J + 1)) : Prop where
  shift : lambda.shift = mu.shift
  deltaIndex : lambda.deltaIndex = mu.deltaIndex
  oldExponent : ∀ r,
    lambda.oldExponent r = (rho.old r : ℕ) + P.q * mu.oldExponent r
  lastExponent :
    lambda.lastExponent = (rho.last : ℕ) + P.q * mu.lastExponent

/-- The old Delta factor evaluated on the `z/q` fibre is exactly the
intermediate residue-lifted `A'` factor.  This is the valid replacement for
the false fixed-family identity `g_J(z/q)=g_(J+1)(z)`. -/
theorem A_div_q_eq_residueLiftA {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : LevelIndex P J)
    (mu : LevelIndex P (J + 1))
    (h : ResidueLiftAgreement rho lambda mu) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    A state b bLast lambda (z / (P.q : ℂ)) m =
      residueLiftA state rho b bLast mu z m := by
  rw [A, residueLiftA, ← scaledArgument_succ]
  unfold auxiliaryFactor residueLiftCoordinates coordinatesForState coordinates
  simp only
  rw [h.shift, h.deltaIndex]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  rw [h.oldExponent r, h.lastExponent]

/-- The logarithmic rate contributed solely by the selected residues. -/
def residueRate {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    (rho : ExponentResidue P) (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) : ℂ :=
  ∑ r, (rho.old r : ℕ) * logAlpha r + (rho.last : ℕ) * logAlphaLast

/-- Before exponentiating, an old rate is the residue rate plus `q` times the
canonical quotient rate. -/
theorem algebraicRate_eq_residueRate_add_q_mul
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (rho : ExponentResidue P) (lambda : LevelIndex P J)
    (mu : LevelIndex P (J + 1))
    (h : ResidueLiftAgreement rho lambda mu)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast : ℂ) :
    algebraicRate coordinates logAlpha logAlphaLast lambda =
      residueRate rho logAlpha logAlphaLast +
        (P.q : ℂ) * algebraicRate coordinates logAlpha logAlphaLast mu := by
  classical
  simp only [algebraicRate, residueRate, coordinates]
  rw [h.lastExponent]
  simp_rw [h.oldExponent]
  push_cast
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- At `z/q`, the old algebraic exponential splits into a common radical
residue monomial and the canonical quotient exponential. -/
theorem exp_algebraicRate_div_q_eq_residue_mul
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (rho : ExponentResidue P) (lambda : LevelIndex P J)
    (mu : LevelIndex P (J + 1))
    (h : ResidueLiftAgreement rho lambda mu)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ) :
    Complex.exp
        (algebraicRate coordinates logAlpha logAlphaLast lambda *
          (z / (P.q : ℂ))) =
      Complex.exp
          (residueRate rho logAlpha logAlphaLast * (z / (P.q : ℂ))) *
        Complex.exp
          (algebraicRate coordinates logAlpha logAlphaLast mu * z) := by
  have hq : (P.q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))
  rw [algebraicRate_eq_residueRate_add_q_mul rho lambda mu h]
  rw [add_mul, Complex.exp_add]
  congr 2
  field_simp [hq]

/-- Equation (12)'s intermediate exponential polynomial: quotient
exponentials paired with the residue-lifted Delta factor `A'`.  The inner
induction in source Lemma 6 is exactly what converts this function to the
canonical `g` of the next state. -/
def residueLiftGWithLogs {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (oldState : LevelState P J) (state : LevelState P (J + 1))
    (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast : ℂ) : ℂ → VDPLMultiIndex (oldRank + 1) → ℂ :=
  fun z m ↦
    ExponentialPolynomial.ordinaryDerivative state.support
      (fun mu ↦ (state.coeff mu : ℂ) *
        residueLiftA oldState rho b bLast mu z m)
      (algebraicRate coordinates logAlpha logAlphaLast) 0 z

theorem residueLiftGWithLogs_eq_sum
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (state : LevelState P (J + 1))
    (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (logAlpha : Fin oldRank → ℂ)
    (logAlphaLast z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    residueLiftGWithLogs oldState state rho b bLast logAlpha logAlphaLast z m =
      ∑ mu, (state.coeff mu : ℂ) *
        residueLiftA oldState rho b bLast mu z m *
          Complex.exp
            (algebraicRate coordinates logAlpha logAlphaLast mu * z) := by
  simp [residueLiftGWithLogs, LevelState.support,
    ExponentialPolynomial.ordinaryDerivative, mul_assoc]

/-! ## Exact level-zero link with the Lemma 2 system -/

/-- The row derivative coordinates as a `Fin (oldRank+1)` multi-index. -/
def rowMultiIndex {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    VDPLMultiIndex (oldRank + 1) :=
  Fin.cases (row.order none) (fun r ↦ row.order (some r))

@[simp] theorem rowMultiIndex_zero {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    rowMultiIndex row 0 = row.order none := rfl

@[simp] theorem rowMultiIndex_succ {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) (r : Fin oldRank) :
    rowMultiIndex row r.succ = row.order (some r) := rfl

theorem rowMultiIndex_weight {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    VDPLMultiIndex.weight (rowMultiIndex row) = row.weight := by
  simp [VDPLMultiIndex.weight, ConstraintRow.weight, rowMultiIndex,
    Fin.sum_univ_succ]

private theorem eval₂_eq_cast_eval_of_eq (p : ℚ[X]) (xC : ℂ) (xQ : ℚ)
    (hx : xC = (xQ : ℂ)) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) xC p = ((p.eval xQ : ℚ) : ℂ) := by
  rw [hx]
  exact Polynomial.eval₂_at_apply _ _

/-- At level zero and an integral row point, `A` is precisely the complex
cast of the rational Delta factor in the Lemma 2 matrix. -/
theorem A_zero_at_row {oldRank radius budget : ℕ}
    (P : VDPLParameters (Fin oldRank)) (state : LevelState P 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LevelIndex P 0) :
    A state b bLast lambda (row.point : ℂ) (rowMultiIndex row) =
      (sourceDeltaFactor P.h b bLast row lambda : ℂ) := by
  simp only [A, scaledArgument, pow_zero, div_one,
    auxiliaryFactor, coordinatesForState, coordinates, rowMultiIndex_zero,
    rowMultiIndex_succ, sourceDeltaFactor, poweredDeltaHasseEval, simpleDeltaEval,
    LambdaBox.shift,
    LambdaBox.deltaIndex, LambdaBox.oldExponent, LambdaBox.lastExponent]
  push_cast
  congr 1
  · apply eval₂_eq_cast_eval_of_eq
    norm_num
  · apply Finset.prod_congr rfl
    intro r _
    apply eval₂_eq_cast_eval_of_eq
    norm_num

/-- Positive integral bases turn one algebraic exponential monomial into
the literal product of powers used in the rational constraint matrix. -/
theorem exp_algebraicRate_mul_nat_eq
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (lambda : I) (l : ℕ) :
    Complex.exp
        (algebraicRate coord
          (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
          (Real.log (alphaLast : ℝ) : ℂ) lambda * (l : ℂ)) =
      (∏ r, (alpha r : ℂ) ^ (coord.oldExponent lambda r * l)) *
        (alphaLast : ℂ) ^ (coord.lastExponent lambda * l) := by
  rw [algebraicRate, add_mul, Complex.exp_add]
  rw [Finset.sum_mul, Complex.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro r _
    have halphaR : (0 : ℝ) < alpha r := by exact_mod_cast halpha r
    calc
      Complex.exp
          (((coord.oldExponent lambda r : ℂ) *
              (Real.log (alpha r : ℝ) : ℂ)) * (l : ℂ)) =
          Complex.exp
            (((coord.oldExponent lambda r * l : ℕ) : ℂ) *
              (Real.log (alpha r : ℝ) : ℂ)) := by
            congr 1
            push_cast
            ring
      _ = Complex.exp (Real.log (alpha r : ℝ) : ℂ) ^
            (coord.oldExponent lambda r * l) := by
          rw [Complex.exp_nat_mul]
      _ = (alpha r : ℂ) ^ (coord.oldExponent lambda r * l) := by
          rw [← Complex.ofReal_exp, Real.exp_log halphaR]
          norm_num
  · have halphaLastR : (0 : ℝ) < alphaLast := by exact_mod_cast halphaLast
    calc
      Complex.exp
          (((coord.lastExponent lambda : ℂ) *
              (Real.log (alphaLast : ℝ) : ℂ)) * (l : ℂ)) =
          Complex.exp
            (((coord.lastExponent lambda * l : ℕ) : ℂ) *
              (Real.log (alphaLast : ℝ) : ℂ)) := by
            congr 1
            push_cast
            ring
      _ = Complex.exp (Real.log (alphaLast : ℝ) : ℂ) ^
            (coord.lastExponent lambda * l) := by
          rw [Complex.exp_nat_mul]
      _ = (alphaLast : ℂ) ^ (coord.lastExponent lambda * l) := by
          rw [← Complex.ofReal_exp, Real.exp_log halphaLastR]
          norm_num

/-- One summand of the level-zero `g` value is exactly the cast of the
corresponding Lemma 2 rational constraint summand. -/
theorem g_zero_summand_at_row {oldRank radius budget : ℕ}
    (P : VDPLParameters (Fin oldRank)) (state : LevelState P 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LevelIndex P 0) :
    (state.coeff lambda : ℂ) *
        A state b bLast lambda (row.point : ℂ) (rowMultiIndex row) *
          Complex.exp
            (algebraicRate coordinates (oldLog P) (lastLog P) lambda *
              (row.point : ℂ)) =
      (((state.coeff lambda : ℚ) *
        rationalConstraintEntry P.h b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda : ℚ) : ℂ) := by
  rw [A_zero_at_row P state]
  simp only [lastLog]
  rw [show oldLog P =
    (fun r ↦ (Real.log (P.old r : ℝ) : ℂ)) from rfl]
  rw [exp_algebraicRate_mul_nat_eq coordinates P.old P.newPrime
    (fun r ↦ (P.old_prime r).pos) P.new_prime.pos lambda row.point]
  simp only [rationalConstraintEntry]
  push_cast
  simp only [coordinates, Nat.mul_comm]
  ring

/-- The complete level-zero value at a Lemma 2 row is the complex cast of
the rational constraint sum. -/
theorem g_zero_at_row_eq_cast_constraintSum
    {oldRank radius budget : ℕ}
    (P : VDPLParameters (Fin oldRank)) (state : LevelState P 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (row : ConstraintRow oldRank radius budget) :
    gSource state b bLast (row.point : ℂ) (rowMultiIndex row) =
      ((∑ lambda, (state.coeff lambda : ℚ) *
        rationalConstraintEntry P.h b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda : ℚ) : ℂ) := by
  rw [gSource, gWithLogs_eq_sum]
  calc
    (∑ lambda,
        (state.coeff lambda : ℂ) *
          A state b bLast lambda (row.point : ℂ) (rowMultiIndex row) *
            Complex.exp
              (algebraicRate coordinates (oldLog P) (lastLog P) lambda *
                (row.point : ℂ))) =
        ∑ lambda,
          (((state.coeff lambda : ℚ) *
            rationalConstraintEntry P.h b bLast
              (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda : ℚ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro lambda _
      exact g_zero_summand_at_row P state b bLast row lambda
    _ = ((∑ lambda, (state.coeff lambda : ℚ) *
          rationalConstraintEntry P.h b bLast
            (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda : ℚ) : ℂ) := by
      exact (map_sum (algebraMap ℚ ℂ)
        (fun lambda ↦ (state.coeff lambda : ℚ) *
          rationalConstraintEntry P.h b bLast
            (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda) univ).symm

/-- Package an allowed derivative multi-index as a Lemma 2 row index. -/
def boundedMultiIndexOf {oldRank budget : ℕ}
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    BoundedMultiIndex oldRank budget where
  coordinate
    | none => ⟨m 0, Nat.lt_succ_of_le
        ((VDPLMultiIndex.component_le_weight m 0).trans hm)⟩
    | some r => ⟨m r.succ, Nat.lt_succ_of_le
        ((VDPLMultiIndex.component_le_weight m r.succ).trans hm)⟩
  weight_le := by
    simpa [VDPLMultiIndex.weight, Fin.sum_univ_succ] using hm

/-- The Lemma 2 row attached to an integral point and an allowed
multi-index. -/
def constraintRowOf {oldRank radius budget l : ℕ}
    (hl : 1 ≤ l) (hlR : l ≤ radius)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    ConstraintRow oldRank radius budget where
  pointIndex := ⟨l - 1, by omega⟩
  multiIndex := boundedMultiIndexOf m hm

@[simp] theorem constraintRowOf_point {oldRank radius budget l : ℕ}
    (hl : 1 ≤ l) (hlR : l ≤ radius)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    (constraintRowOf hl hlR m hm).point = l := by
  simp [constraintRowOf, ConstraintRow.point]
  omega

@[simp] theorem rowMultiIndex_constraintRowOf
    {oldRank radius budget l : ℕ}
    (hl : 1 ≤ l) (hlR : l ≤ radius)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    rowMultiIndex (constraintRowOf hl hlR m hm) = m := by
  funext i
  refine Fin.cases ?_ (fun r ↦ ?_) i <;> rfl

/-- Exact base bridge: the rational equations supplied by Lemma 2 imply
the complete level-zero integral-grid vanishing needed to start Lemma 6. -/
theorem levelZero_vanishes_of_auxiliaryEquations
    {oldRank radius budget : ℕ}
    (P : VDPLParameters (Fin oldRank)) (state : LevelState P 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hequations : ∀ row : ConstraintRow oldRank radius budget,
      ∑ lambda, (state.coeff lambda : ℚ) *
        rationalConstraintEntry P.h b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ) row lambda = 0) :
    VanishesOn (g state b bLast) 1 radius budget := by
  intro l hl hlR m hm
  let mSource : VDPLMultiIndex (oldRank + 1) := toSourceMultiIndex P m
  have hmSource : VDPLMultiIndex.weight mSource ≤ budget := by
    simpa [mSource, weight_toSourceMultiIndex] using hm
  let row : ConstraintRow oldRank radius budget :=
    constraintRowOf hl hlR mSource hmSource
  have hrow := g_zero_at_row_eq_cast_constraintSum P state b bLast row
  rw [hequations row] at hrow
  simpa [g, row, mSource, constraintRowOf_point,
    rowMultiIndex_constraintRowOf] using hrow

/-- Direct form of the base bridge: an integral kernel vector for the sharp
Lemma 2 matrix starts the level-zero vanishing state. -/
theorem levelZero_vanishes_of_mulVec_eq_zero
    {oldRank radius budget : ℕ}
    (P : VDPLParameters (Fin oldRank)) (state : LevelState P 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := levelBoxShape P 0) P.h b bLast
        (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ))
    (hkernel : model.matrix.mulVec state.coeff = 0) :
    VanishesOn (g state b bLast) 1 radius budget := by
  apply levelZero_vanishes_of_auxiliaryEquations P state b bLast
  exact rational_equations_of_mulVec_eq_zero model state.coeff hkernel

end Erdos240.BakerSourceState

#print axioms Erdos240.BakerSourceState.scaledArgument_succ
#print axioms Erdos240.BakerSourceState.levelBoxShape_lastMax_eq_zero_of_scale_lt_qpow
#print axioms Erdos240.BakerSourceState.LevelState.lastSide_eq_zero_of_scale_lt_qpow
#print axioms Erdos240.BakerSourceState.A_div_q_eq_residueLiftA
#print axioms Erdos240.BakerSourceState.exp_algebraicRate_div_q_eq_residue_mul
#print axioms Erdos240.BakerSourceState.levelZero_vanishes_of_auxiliaryEquations
#print axioms Erdos240.BakerSourceState.levelZero_vanishes_of_mulVec_eq_zero

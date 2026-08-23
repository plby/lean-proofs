/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3Concrete
import ErdosProblems.Erdos240.BakerSourceState
import ErdosProblems.Erdos240.RadicalBasis
import ErdosProblems.Erdos240.SharpDeltaIndependent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Instantiating the algebraic certificate in source Lemma 3

This file connects the source-level auxiliary function to the sharp
denominator theorem.  The polynomial factor is first lifted to `ℚ`; a single
common denominator clears it for every coefficient-box index.  Two concrete
certificate constructors are then available downstream:

* at integral targets the complete algebraic term lies in `ℚ`;
* at targets `l / 13`, the exponential monomial lies in the field generated
  by the positive thirteenth roots of the source primes.

The common denominator is

`(q^N)^(2*h*(Lzero+1)) * lcmUpto(h)^m₀`

at an integral target, and the same expression with `q^(N+1)` at `l/q`.
Only the powered head factor needs this denominator.  Every old-coordinate
factor is the ordinary integer-valued polynomial `Delta(x;mᵣ)` evaluated at
an integer.
-/

open scoped BigOperators NumberField Polynomial

noncomputable section

namespace Erdos240.BakerLemma3Instantiation

open Finset
open BakerLemma3
open BakerLemma3Concrete
open BakerSourceState
open Erdos240Delta
open DeltaPower

/-! ## Exact termwise majorants -/

/-- Every finite source sum has canonical termwise majorants: take the
corresponding finite sums of the nonnegative terms.  This constructor removes
all analytic-function hypotheses from the interface; parameter arithmetic may
later replace these exact sums by sharper closed-form upper bounds. -/
def exactSourceMajorants
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*} [DecidableEq I]
    (P : VDPLParameters ι) (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ)
    (q N : ℕ) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    (hcoeff : ∀ lambda ∈ support, ‖(p lambda : ℂ)‖ ≤ P.coeffHeight) :
    SourceMajorants P coord support p h b bLast logAlpha q N z m where
  supportMajorant := support.card
  deltaMajorant :=
    ∑ lambda ∈ support,
      ‖auxiliaryFactor coord h b bLast lambda (scaledArgument q N z) m‖
  exponentialMajorant :=
    ∑ lambda ∈ support,
      Real.exp (‖modifiedRate coord b bLast logAlpha lambda‖ * ‖z‖)
  amplificationMajorant :=
    ∑ lambda ∈ support,
      ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * ‖z‖
  supportMajorant_nonneg := by positivity
  deltaMajorant_nonneg := by positivity
  exponentialMajorant_nonneg := by positivity
  amplificationMajorant_nonneg := by positivity
  support_card_le := le_rfl
  coefficient_le := hcoeff
  delta_le := by
    intro lambda hlambda
    exact Finset.single_le_sum
      (fun i _hi ↦ norm_nonneg
        (auxiliaryFactor coord h b bLast i (scaledArgument q N z) m)) hlambda
  exponential_le := by
    intro lambda hlambda
    exact Finset.single_le_sum
      (fun i _hi ↦ (Real.exp_pos
        (‖modifiedRate coord b bLast logAlpha i‖ * ‖z‖)).le) hlambda
  amplification_le := by
    intro lambda hlambda
    exact Finset.single_le_sum
      (fun i _hi ↦ mul_nonneg
        (norm_nonneg ((coord.lastExponent i : ℂ) / (bLast : ℂ)))
        (norm_nonneg z)) hlambda

/-- Canonical exact majorants for the corrected source state. -/
def stateSourceMajorants {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    SourceMajorants P (coordinatesForState state) state.support state.coeff
      P.h b bLast (oldLog P) P.q J z m :=
  exactSourceMajorants P (coordinatesForState state) state.support state.coeff
    P.h b bLast (oldLog P) P.q J z m (by
      intro lambda _hlambda
      simpa only [Complex.norm_intCast, Real.norm_eq_abs] using
        state.coeff_height lambda)

/-! ## The fixed one-layer radical field -/

/-- The old source primes followed by the distinguished new prime. -/
def radicalPrime {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) :
    Fin (oldRank + 1) → ℕ :=
  Fin.lastCases P.newPrime P.old

@[simp] theorem radicalPrime_castSucc {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (r : Fin oldRank) :
    radicalPrime P r.castSucc = P.old r := by
  simp [radicalPrime]

@[simp] theorem radicalPrime_last {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    radicalPrime P (Fin.last oldRank) = P.newPrime := by
  simp [radicalPrime]

theorem radicalPrime_prime {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    ∀ i, (radicalPrime P i).Prime := by
  intro i
  exact Fin.lastCases (by simpa using P.new_prime)
    (fun r ↦ by simpa using P.old_prime r) i

theorem radicalPrime_injective {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : Function.Injective (radicalPrime P) := by
  intro i j
  refine Fin.lastCases ?_ (fun ri ↦ ?_) i
  · refine Fin.lastCases (fun _ ↦ rfl) (fun rj h ↦ ?_) j
    simp only [radicalPrime_last, radicalPrime_castSucc] at h
    exact (P.new_fresh rj h.symm).elim
  · refine Fin.lastCases (fun h ↦ ?_) (fun rj h ↦ ?_) j
    · simp only [radicalPrime_castSucc, radicalPrime_last] at h
      exact (P.new_fresh ri h).elim
    · simp only [radicalPrime_castSucc] at h
      exact congrArg Fin.castSucc (P.old_injective h)

/-- The positive complex thirteenth root selected by the real logarithm. -/
def positiveThirteenthRoot {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) : ℂ :=
  Complex.exp ((Real.log (radicalPrime P i : ℝ) : ℂ) / 13)

theorem positiveThirteenthRoot_pow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) :
    positiveThirteenthRoot P i ^ 13 =
      algebraMap ℚ ℂ (radicalPrime P i : ℚ) := by
  have hpR : (0 : ℝ) < radicalPrime P i := by
    exact_mod_cast (radicalPrime_prime P i).pos
  calc
    positiveThirteenthRoot P i ^ 13 =
        Complex.exp ((13 : ℂ) *
          ((Real.log (radicalPrime P i : ℝ) : ℂ) / 13)) := by
      symm
      exact Complex.exp_nat_mul _ _
    _ = Complex.exp (Real.log (radicalPrime P i : ℝ) : ℂ) := by
      congr 1
      field_simp
    _ = algebraMap ℚ ℂ (radicalPrime P i : ℚ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hpR]
      norm_num

/-- The source radical field is independent of the induction level: only
one layer of thirteenth roots is adjoined. -/
abbrev SourceRadicalField {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :=
  IntermediateField.adjoin ℚ (Set.range (positiveThirteenthRoot P))

noncomputable instance sourceRadicalField_finiteDimensional {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    FiniteDimensional ℚ (SourceRadicalField P) := by
  apply Towers.CField.KTheory.dimensional_adjoin_pow 13 (by norm_num)
    (Set.range (positiveThirteenthRoot P)) (Set.finite_range _)
  rintro _ ⟨i, rfl⟩
  rw [positiveThirteenthRoot_pow P i]
  exact (IntermediateField.mem_bot).2 ⟨(radicalPrime P i : ℚ), rfl⟩

noncomputable instance sourceRadicalField_numberField {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : NumberField (SourceRadicalField P) where
  to_charZero := inferInstance
  to_finiteDimensional := sourceRadicalField_finiteDimensional P

theorem finrank_sourceRadicalField {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    Module.finrank ℚ (SourceRadicalField P) = 13 ^ (oldRank + 1) := by
  classical
  have hli : LinearIndependent ℚ
      (Erdos240.Kummer.thirteenthRootMonomialInAdjoin
        (positiveThirteenthRoot P)) := by
    apply LinearIndependent.of_comp (SourceRadicalField P).val.toLinearMap
    change LinearIndependent ℚ
      (Erdos240.Kummer.thirteenthRootMonomial (positiveThirteenthRoot P))
    exact Erdos240.Kummer.linearIndependent_thirteenthRootMonomials
      (radicalPrime P) (radicalPrime_prime P) (radicalPrime_injective P)
      (positiveThirteenthRoot P) (positiveThirteenthRoot_pow P)
  have hlower : 13 ^ (oldRank + 1) ≤
      Module.finrank ℚ (SourceRadicalField P) := by
    simpa using hli.fintype_card_le_finrank
  let roots : Finset ℂ := Finset.univ.image (positiveThirteenthRoot P)
  have hpow : ∀ x ∈ roots,
      x ^ 13 ∈ (⊥ : IntermediateField ℚ ℂ) := by
    intro x hx
    simp only [roots, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [positiveThirteenthRoot_pow P i]
    exact (IntermediateField.mem_bot).2 ⟨(radicalPrime P i : ℚ), rfl⟩
  have hupper' := Towers.CField.KTheory.finrank_adjoin_finset
    13 (by norm_num) roots hpow
  have hroots : (roots : Set ℂ) = Set.range (positiveThirteenthRoot P) := by
    ext x
    simp [roots]
  rw [hroots] at hupper'
  have hcard : roots.card ≤ oldRank + 1 := by
    simpa using (Finset.card_image_le :
      (Finset.univ.image (positiveThirteenthRoot P)).card ≤
        (Finset.univ : Finset (Fin (oldRank + 1))).card)
  have hupper : Module.finrank ℚ (SourceRadicalField P) ≤
      13 ^ (oldRank + 1) :=
    hupper'.trans (Nat.pow_le_pow_right (by norm_num) hcard)
  exact le_antisymm hupper hlower

/-- The named generator in the source radical field. -/
def radicalGenerator {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) :
    SourceRadicalField P :=
  ⟨positiveThirteenthRoot P i,
    IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

@[simp] theorem radicalGenerator_val {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) :
    (radicalGenerator P i : ℂ) = positiveThirteenthRoot P i := rfl

theorem radicalGenerator_pow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) :
    radicalGenerator P i ^ 13 =
      algebraMap ℚ (SourceRadicalField P) (radicalPrime P i : ℚ) := by
  apply Subtype.ext
  exact positiveThirteenthRoot_pow P i

theorem radicalGenerator_isIntegral {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) :
    IsIntegral ℤ (radicalGenerator P i) := by
  apply IsIntegral.of_pow (by norm_num : 0 < 13)
  rw [radicalGenerator_pow P i]
  simpa using
    (isIntegral_intCast (R := ℤ) (B := SourceRadicalField P)
      (radicalPrime P i : ℤ))

/-- The one-layer radical monomial representing the exponential at `l/13`. -/
def radicalMonomial {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters (Fin oldRank)) (coord : SourceCoordinates oldRank I)
    (lambda : I) (l : ℕ) : SourceRadicalField P :=
  (∏ r, radicalGenerator P r.castSucc ^ (coord.oldExponent lambda r * l)) *
    radicalGenerator P (Fin.last oldRank) ^ (coord.lastExponent lambda * l)

theorem radicalMonomial_isIntegral {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters (Fin oldRank)) (coord : SourceCoordinates oldRank I)
    (lambda : I) (l : ℕ) :
    IsIntegral ℤ (radicalMonomial P coord lambda l) := by
  apply IsIntegral.mul
  · exact IsIntegral.prod
      (fun r : Fin oldRank ↦
        radicalGenerator P r.castSucc ^ (coord.oldExponent lambda r * l))
      (fun r _ ↦ (radicalGenerator_isIntegral P r.castSucc).pow _)
  · exact (radicalGenerator_isIntegral P (Fin.last oldRank)).pow _

/-- Under the distinguished complex embedding, the fixed radical monomial
is exactly the algebraic exponential evaluated at `l/13`. -/
theorem val_radicalMonomial {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters (Fin oldRank)) (coord : SourceCoordinates oldRank I)
    (lambda : I) (l : ℕ) :
    (radicalMonomial P coord lambda l : ℂ) =
      Complex.exp
        (algebraicRate coord (oldLog P) (lastLog P) lambda *
          ((l : ℂ) / (P.q : ℂ))) := by
  rw [algebraicRate, add_mul, Complex.exp_add, Finset.sum_mul,
    Complex.exp_sum]
  unfold radicalMonomial
  push_cast
  change
    (∏ r, positiveThirteenthRoot P r.castSucc ^
      (coord.oldExponent lambda r * l)) *
        positiveThirteenthRoot P (Fin.last oldRank) ^
          (coord.lastExponent lambda * l) = _
  congr 1
  · apply Finset.prod_congr rfl
    intro r _hr
    unfold positiveThirteenthRoot oldLog
    simp only [radicalPrime_castSucc, VDPLParameters.q_eq]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · unfold positiveThirteenthRoot lastLog
    simp only [radicalPrime_last, VDPLParameters.q_eq]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- Scaling `l/q` once more by the level denominator gives denominator
`q^(J+1)`, not a deeper radical extension. -/
theorem scaledArgument_div_q_eq_ratCast {q J l : ℕ} (hq : q ≠ 0) :
    scaledArgument q J ((l : ℂ) / (q : ℂ)) =
      (((l : ℚ) / q ^ (J + 1) : ℚ) : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  unfold scaledArgument
  push_cast
  rw [pow_succ]
  field_simp

/-- The rational polynomial factor underlying `BakerSourceState.A`. -/
def rationalAuxiliaryFactor {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (x : ℚ) (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  (poweredDeltaHasse h (coord.deltaIndex lambda + 1) (m 0)).eval
      (x + coord.shift lambda) *
    ∏ r, (Erdos240Delta.delta (m r.succ)).eval
      ((bLast : ℚ) * coord.oldExponent lambda r -
        (b r : ℚ) * coord.lastExponent lambda)

/-- Casting the rational polynomial factor to `ℂ` gives the source factor. -/
theorem coe_rationalAuxiliaryFactor {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (x : ℚ) (m : VDPLMultiIndex (oldRank + 1)) :
    (rationalAuxiliaryFactor coord h b bLast lambda x m : ℂ) =
      auxiliaryFactor coord h b bLast lambda (x : ℂ) m := by
  simp only [rationalAuxiliaryFactor, auxiliaryFactor, poweredDeltaHasseEval,
    simpleDeltaEval]
  push_cast
  change _ =
    Polynomial.eval₂ (algebraMap ℚ ℂ) ((x : ℂ) + (coord.shift lambda : ℂ))
        (poweredDeltaHasse h (coord.deltaIndex lambda + 1) (m 0)) *
      ∏ r, Polynomial.eval₂ (algebraMap ℚ ℂ)
        ((bLast : ℂ) * (coord.oldExponent lambda r : ℂ) -
          (b r : ℂ) * (coord.lastExponent lambda : ℂ))
        (Erdos240Delta.delta (m r.succ))
  congr 1
  · rw [show (x : ℂ) + (coord.shift lambda : ℂ) =
        ((x + coord.shift lambda : ℚ) : ℂ) by push_cast; ring]
    exact (Polynomial.eval₂_at_apply (algebraMap ℚ ℂ)
      (x + (coord.shift lambda : ℚ))).symm
  · apply Finset.prod_congr rfl
    intro r _
    rw [show (bLast : ℂ) * (coord.oldExponent lambda r : ℂ) -
          (b r : ℂ) * (coord.lastExponent lambda : ℂ) =
        (((bLast : ℚ) * coord.oldExponent lambda r -
          (b r : ℚ) * coord.lastExponent lambda : ℚ) : ℂ) by push_cast; ring]
    exact (Polynomial.eval₂_at_apply (algebraMap ℚ ℂ)
      ((bLast : ℚ) * coord.oldExponent lambda r -
        (b r : ℚ) * coord.lastExponent lambda)).symm

/-- The common sharp denominator for an evaluation whose reduced rational
denominator is `den`. -/
def commonDeltaDenominator {oldRank : ℕ}
    (h deltaPowerBound den : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  (den : ℚ) ^ (2 * h * deltaPowerBound) *
    (Nat.lcmUpto h : ℚ) ^ (m 0)

/-- Each individual rational polynomial factor is cleared by the common
sharp denominator.  This is the exact denominator input to Lemma 3. -/
theorem isIntegral_commonDeltaDenominator_mul_rationalAuxiliaryFactor
    {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h deltaPowerBound : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (num den : ℕ) (hden : den ≠ 0)
    (hdelta : coord.deltaIndex lambda + 1 ≤ deltaPowerBound)
    (m : VDPLMultiIndex (oldRank + 1)) :
    IsIntegral ℤ
      (commonDeltaDenominator h deltaPowerBound den m *
        rationalAuxiliaryFactor coord h b bLast lambda ((num : ℚ) / den) m) := by
  let firstArgument : ℕ := num + coord.shift lambda * den
  obtain ⟨w0, hw0⟩ :=
    SharpDeltaIndependent.exists_int_cleared_poweredDeltaHasse_lcm
      h (coord.deltaIndex lambda + 1) (m 0) den firstArgument hden
  have hfirstArgument :
      ((firstArgument : ℕ) : ℚ) / den =
        (num : ℚ) / den + coord.shift lambda := by
    dsimp only [firstArgument]
    have hdenQ : (den : ℚ) ≠ 0 := by exact_mod_cast hden
    push_cast
    field_simp
  have hfirst : IsIntegral ℤ
      ((den : ℚ) ^ (2 * h * (coord.deltaIndex lambda + 1)) *
        (Nat.lcmUpto h : ℚ) ^ (m 0) *
          (poweredDeltaHasse h (coord.deltaIndex lambda + 1) (m 0)).eval
            ((num : ℚ) / den + coord.shift lambda)) := by
    rw [← hfirstArgument, hw0]
    exact isIntegral_intCast w0
  choose wr hwr using fun r : Fin oldRank ↦
    IntegerValuedPolynomial.exists_int_lcmUpto_pow_mul_eval_deltaHasse
      (m r.succ) 0
        (bLast * (coord.oldExponent lambda r : ℤ) -
          b r * (coord.lastExponent lambda : ℤ))
  have hold (r : Fin oldRank) : IsIntegral ℤ
      ((Erdos240Delta.delta (m r.succ)).eval
        ((bLast * (coord.oldExponent lambda r : ℤ) -
          b r * (coord.lastExponent lambda : ℤ) : ℤ) : ℚ)) := by
    have hwr' :
        (Erdos240Delta.delta (m r.succ)).eval
            ((bLast * (coord.oldExponent lambda r : ℤ) -
              b r * (coord.lastExponent lambda : ℤ) : ℤ) : ℚ) =
          (wr r : ℚ) := by
      simpa [Erdos240Delta.deltaHasse] using hwr r
    rw [hwr']
    exact isIntegral_intCast (wr r)
  let extra : ℚ :=
    (den : ℚ) ^ (2 * h * (deltaPowerBound - (coord.deltaIndex lambda + 1)))
  have hextra : IsIntegral ℤ extra := by
    exact (isIntegral_natCast den).pow _
  have holdProduct : IsIntegral ℤ
      (∏ r,
        (Erdos240Delta.delta (m r.succ)).eval
          ((bLast * (coord.oldExponent lambda r : ℤ) -
            b r * (coord.lastExponent lambda : ℤ) : ℤ) : ℚ)) :=
    IsIntegral.prod
      (fun r : Fin oldRank ↦
        (Erdos240Delta.delta (m r.succ)).eval
          ((bLast * (coord.oldExponent lambda r : ℤ) -
            b r * (coord.lastExponent lambda : ℤ) : ℤ) : ℚ))
      (fun r _ ↦ hold r)
  have hproduct : IsIntegral ℤ
      (extra *
        ((den : ℚ) ^ (2 * h * (coord.deltaIndex lambda + 1)) *
          (Nat.lcmUpto h : ℚ) ^ (m 0) *
            (poweredDeltaHasse h (coord.deltaIndex lambda + 1) (m 0)).eval
              ((num : ℚ) / den + coord.shift lambda)) *
        ∏ r,
          (Erdos240Delta.delta (m r.succ)).eval
            ((bLast * (coord.oldExponent lambda r : ℤ) -
              b r * (coord.lastExponent lambda : ℤ) : ℤ) : ℚ)) :=
    by
      simpa only [mul_assoc] using hextra.mul (hfirst.mul holdProduct)
  have hexponent :
      2 * h * deltaPowerBound =
        2 * h * (deltaPowerBound - (coord.deltaIndex lambda + 1)) +
          2 * h * (coord.deltaIndex lambda + 1) := by
    calc
      2 * h * deltaPowerBound =
          2 * h * ((deltaPowerBound - (coord.deltaIndex lambda + 1)) +
            (coord.deltaIndex lambda + 1)) := by rw [Nat.sub_add_cancel hdelta]
      _ = _ := by ring
  have heq :
      commonDeltaDenominator h deltaPowerBound den m *
          rationalAuxiliaryFactor coord h b bLast lambda ((num : ℚ) / den) m =
        extra *
          ((den : ℚ) ^ (2 * h * (coord.deltaIndex lambda + 1)) *
            (Nat.lcmUpto h : ℚ) ^ (m 0) *
              (poweredDeltaHasse h (coord.deltaIndex lambda + 1) (m 0)).eval
                ((num : ℚ) / den + coord.shift lambda)) *
          ∏ r,
            (Erdos240Delta.delta (m r.succ)).eval
              ((bLast * (coord.oldExponent lambda r : ℤ) -
                b r * (coord.lastExponent lambda : ℤ) : ℤ) : ℚ) := by
    rw [commonDeltaDenominator, rationalAuxiliaryFactor, hexponent, pow_add]
    dsimp only [extra]
    push_cast
    ring
  rw [heq]
  exact hproduct

/-! ## Algebraic lift at integral targets -/

/-- The rational prime monomial occurring in `g` at an integral target. -/
def rationalPrimeMonomial {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (lambda : I) (l : ℕ) : ℚ :=
  (∏ r, (alpha r : ℚ) ^ (coord.oldExponent lambda r * l)) *
    (alphaLast : ℚ) ^ (coord.lastExponent lambda * l)

/-- Positive rational bases turn the source exponential at an integral
target into the literal rational prime monomial. -/
theorem coe_rationalPrimeMonomial {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (lambda : I) (l : ℕ) :
    Complex.exp
        (algebraicRate coord
          (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
          (Real.log (alphaLast : ℝ) : ℂ) lambda * (l : ℂ)) =
      (rationalPrimeMonomial coord alpha alphaLast lambda l : ℂ) := by
  rw [BakerSourceState.exp_algebraicRate_mul_nat_eq
    coord alpha alphaLast halpha halphaLast lambda l]
  unfold rationalPrimeMonomial
  push_cast
  congr 1

/-- The rational lift of one complete algebraic term at an integral target. -/
def integralTargetTerm {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast q N : ℕ)
    (lambda : I) (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  rationalAuxiliaryFactor coord h b bLast lambda
      ((l : ℚ) / q ^ N) m *
    rationalPrimeMonomial coord alpha alphaLast lambda l

theorem scaledArgument_nat_eq_ratCast {q N l : ℕ} (hq : q ≠ 0) :
    scaledArgument q N (l : ℂ) = (((l : ℚ) / q ^ N : ℚ) : ℂ) := by
  have hqN : (q ^ N : ℚ) ≠ 0 := by
    exact_mod_cast pow_ne_zero N hq
  unfold scaledArgument
  push_cast
  field_simp

/-- The distinguished embedding maps the rational lift to the exact complex
term occurring in `g`. -/
theorem map_integralTargetTerm {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast q N : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (hq : q ≠ 0) (lambda : I) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (Algebra.ofId ℚ ℂ)
        (integralTargetTerm coord h b bLast alpha alphaLast q N lambda l m) =
      algebraicComplexTerm coord h b bLast
        (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
        (Real.log (alphaLast : ℝ) : ℂ) q N (l : ℂ) m lambda := by
  rw [integralTargetTerm, map_mul]
  change
    (rationalAuxiliaryFactor coord h b bLast lambda ((l : ℚ) / q ^ N) m : ℂ) *
        (rationalPrimeMonomial coord alpha alphaLast lambda l : ℂ) = _
  rw [algebraicComplexTerm, coe_rationalAuxiliaryFactor]
  rw [← scaledArgument_nat_eq_ratCast hq]
  rw [← coe_rationalPrimeMonomial coord alpha alphaLast halpha halphaLast]

/-- The rational lift is integral after multiplication by the common sharp
Delta denominator. -/
theorem isIntegral_denominator_mul_integralTargetTerm
    {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h deltaPowerBound : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast q N : ℕ)
    (hq : q ≠ 0) (lambda : I)
    (hdelta : coord.deltaIndex lambda + 1 ≤ deltaPowerBound)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    IsIntegral ℤ
      (commonDeltaDenominator h deltaPowerBound (q ^ N) m *
        integralTargetTerm coord h b bLast alpha alphaLast q N lambda l m) := by
  have hqN : q ^ N ≠ 0 := pow_ne_zero N hq
  have haux :=
    isIntegral_commonDeltaDenominator_mul_rationalAuxiliaryFactor
      coord h deltaPowerBound b bLast lambda l (q ^ N) hqN hdelta m
  have hold (r : Fin oldRank) : IsIntegral ℤ
      ((alpha r : ℚ) ^ (coord.oldExponent lambda r * l)) :=
    (isIntegral_natCast (alpha r)).pow _
  have holdProd : IsIntegral ℤ
      (∏ r, (alpha r : ℚ) ^ (coord.oldExponent lambda r * l)) :=
    IsIntegral.prod
      (fun r : Fin oldRank ↦
        (alpha r : ℚ) ^ (coord.oldExponent lambda r * l))
      (fun r _ ↦ hold r)
  have hlast : IsIntegral ℤ
      ((alphaLast : ℚ) ^ (coord.lastExponent lambda * l)) :=
    (isIntegral_natCast alphaLast).pow _
  have hmono : IsIntegral ℤ
      (rationalPrimeMonomial coord alpha alphaLast lambda l) := by
    exact holdProd.mul hlast
  simpa only [integralTargetTerm, mul_assoc, Nat.cast_pow] using haux.mul hmono

theorem commonDeltaDenominator_ne_zero {oldRank : ℕ}
    (h deltaPowerBound den : ℕ) (hden : den ≠ 0)
    (m : VDPLMultiIndex (oldRank + 1)) :
    commonDeltaDenominator h deltaPowerBound den m ≠ 0 := by
  unfold commonDeltaDenominator
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast hden)
  · exact pow_ne_zero _ (by exact_mod_cast Nat.lcmUpto_ne_zero h)

/-- Fully concrete Lemma 3 algebraic data at an integral target.  There are
no certificate, integrality, degree, or conjugate hypotheses: the field is
`ℚ`, the sharp denominator supplies integrality, and `ℚ` has only its
distinguished `ℚ`-embedding into `ℂ`. -/
def integralTargetCertificate
    {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I)
    (support : Finset I) (p : I → ℤ)
    (h deltaPowerBound : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast q N : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (hq : q ≠ 0)
    (hdelta : ∀ lambda ∈ support,
      coord.deltaIndex lambda + 1 ≤ deltaPowerBound)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    AlgebraicCertificateInputs (K := ℚ) coord support p h b bLast
      (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
      (Real.log (alphaLast : ℝ) : ℂ) q N (l : ℂ) m 0 where
  term := fun lambda ↦
    integralTargetTerm coord h b bLast alpha alphaLast q N lambda l m
  denominator := commonDeltaDenominator h deltaPowerBound (q ^ N) m
  sigma := Algebra.ofId ℚ ℂ
  scale :=
    (commonDeltaDenominator h deltaPowerBound (q ^ N) m : ℂ)
  scale_ne := by
    exact_mod_cast commonDeltaDenominator_ne_zero h deltaPowerBound (q ^ N)
      (pow_ne_zero N hq) m
  denominator_map := rfl
  termIntegral := by
    intro lambda hlambda
    exact isIntegral_denominator_mul_integralTargetTerm
      coord h deltaPowerBound b bLast alpha alphaLast q N hq lambda
        (hdelta lambda hlambda) l m
  term_map := by
    intro lambda _hlambda
    exact map_integralTargetTerm coord h b bLast alpha alphaLast q N
      halpha halphaLast hq lambda l m
  conjugateBound := 1
  conjugateBound_pos := by norm_num
  other_embeddings := by
    intro tau htau
    exfalso
    apply htau
    ext
  finrank_eq_thirteen_pow := by simp

/-! ## Algebraic lift at rational targets `l / 13` -/

/-- One complete algebraic term at a rational target, lifted to the fixed
one-layer source radical field. -/
def rationalTargetTerm {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (N : ℕ)
    (lambda : I) (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    SourceRadicalField P :=
  algebraMap ℚ (SourceRadicalField P)
      (rationalAuxiliaryFactor coord h b bLast lambda
        ((l : ℚ) / P.q ^ (N + 1)) m) *
    radicalMonomial P coord lambda l

/-- The distinguished complex embedding maps the rational-field lift to the
exact source term at `l/q`. -/
theorem map_rationalTargetTerm {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (N : ℕ)
    (lambda : I) (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    (SourceRadicalField P).val
        (rationalTargetTerm P coord h b bLast N lambda l m) =
      algebraicComplexTerm coord h b bLast (oldLog P) (lastLog P)
        P.q N ((l : ℂ) / (P.q : ℂ)) m lambda := by
  rw [rationalTargetTerm, map_mul]
  change
    (rationalAuxiliaryFactor coord h b bLast lambda
      ((l : ℚ) / P.q ^ (N + 1)) m : ℂ) *
        (radicalMonomial P coord lambda l : ℂ) = _
  rw [algebraicComplexTerm, coe_rationalAuxiliaryFactor]
  rw [← scaledArgument_div_q_eq_ratCast
    (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))]
  rw [val_radicalMonomial P coord lambda l]

/-- The sharp Delta denominator clears the rational target term in the
fixed radical field. -/
theorem isIntegral_denominator_mul_rationalTargetTerm
    {oldRank : ℕ} {I : Type*}
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (h deltaPowerBound : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (N : ℕ)
    (lambda : I) (hdelta : coord.deltaIndex lambda + 1 ≤ deltaPowerBound)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    IsIntegral ℤ
      (algebraMap ℚ (SourceRadicalField P)
          (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
        rationalTargetTerm P coord h b bLast N lambda l m) := by
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have haux :=
    isIntegral_commonDeltaDenominator_mul_rationalAuxiliaryFactor
      coord h deltaPowerBound b bLast lambda l (P.q ^ (N + 1))
        (pow_ne_zero _ hq) hdelta m
  have hauxK : IsIntegral ℤ
      (algebraMap ℚ (SourceRadicalField P)
        (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m *
          rationalAuxiliaryFactor coord h b bLast lambda
            ((l : ℚ) / P.q ^ (N + 1)) m)) :=
    IsIntegral.map (IsScalarTower.toAlgHom ℤ ℚ (SourceRadicalField P)) (by
      simpa only [Nat.cast_pow] using haux)
  have hradical := radicalMonomial_isIntegral P coord lambda l
  simpa only [rationalTargetTerm, map_mul, mul_assoc] using
    hauxK.mul hradical

/-- A literal finite sum over all number-field embeddings gives an automatic
uniform conjugate bound. -/
def rationalTargetConjugateBound
    {oldRank : ℕ} {I : Type*} [DecidableEq I]
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h deltaPowerBound : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (N l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  1 + ∑ tau : SourceRadicalField P →ₐ[ℚ] ℂ,
    ‖tau
      (algebraMap ℚ (SourceRadicalField P)
          (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
        algebraicAuxiliaryValue support p
          (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))‖

theorem rationalTargetConjugateBound_pos
    {oldRank : ℕ} {I : Type*} [DecidableEq I]
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h deltaPowerBound : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (N l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    0 < rationalTargetConjugateBound P coord support p h deltaPowerBound
      b bLast N l m := by
  unfold rationalTargetConjugateBound
  have hsum : 0 ≤ ∑ tau : SourceRadicalField P →ₐ[ℚ] ℂ,
      ‖tau
        (algebraMap ℚ (SourceRadicalField P)
            (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
          algebraicAuxiliaryValue support p
            (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))‖ := by
    positivity
  linarith

theorem norm_embedding_le_rationalTargetConjugateBound
    {oldRank : ℕ} {I : Type*} [DecidableEq I]
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h deltaPowerBound : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (N l : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) :
    ‖tau
      (algebraMap ℚ (SourceRadicalField P)
          (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
        algebraicAuxiliaryValue support p
          (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))‖ ≤
      rationalTargetConjugateBound P coord support p h deltaPowerBound
        b bLast N l m := by
  unfold rationalTargetConjugateBound
  have hsingle :
      ‖tau
        (algebraMap ℚ (SourceRadicalField P)
            (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
          algebraicAuxiliaryValue support p
            (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))‖ ≤
        ∑ tau' : SourceRadicalField P →ₐ[ℚ] ℂ,
          ‖tau'
            (algebraMap ℚ (SourceRadicalField P)
                (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
              algebraicAuxiliaryValue support p
                (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))‖ := by
    exact Finset.single_le_sum
      (f := fun tau' : SourceRadicalField P →ₐ[ℚ] ℂ ↦
        ‖tau'
          (algebraMap ℚ (SourceRadicalField P)
              (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
            algebraicAuxiliaryValue support p
              (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))‖)
      (fun tau' _ ↦ norm_nonneg (tau'
        (algebraMap ℚ (SourceRadicalField P)
            (commonDeltaDenominator h deltaPowerBound (P.q ^ (N + 1)) m) *
          algebraicAuxiliaryValue support p
            (fun lambda ↦ rationalTargetTerm P coord h b bLast N lambda l m))))
      (Finset.mem_univ tau)
  linarith

/-! ## The corrected source state at integral targets -/

/-- The head Delta power is uniformly bounded by the source parameter
`L₀ + 1`; it varies with the box index. -/
theorem state_deltaPower_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (lambda : LevelIndex P J) :
    (coordinatesForState state).deltaIndex lambda + 1 ≤ P.LzeroPlusOne := by
  change lambda.deltaIndexFin.val + 1 ≤ P.LzeroPlusOne
  rw [← P.Lzero_add_one_eq_LzeroPlusOne]
  exact Nat.add_le_add_right (Nat.le_of_lt_succ lambda.deltaIndexFin.isLt) 1

/-- The complete algebraic certificate for an actual corrected source state
at an integral point.  The old-coordinate factors are ordinary integer-valued
Delta polynomials, so no side-power hypothesis is required. -/
def stateIntegralTargetCertificate {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    AlgebraicCertificateInputs (K := ℚ)
      (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) (lastLog P) P.q J (l : ℂ) m 0 :=
  integralTargetCertificate (coordinatesForState state) state.support state.coeff
    P.h P.LzeroPlusOne b bLast P.old P.newPrime P.q J
    (fun r ↦ (P.old_prime r).pos) P.new_prime.pos
    (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))
    (fun lambda _hlambda ↦ state_deltaPower_le P state lambda) l m

/-- The explicit degree-one Liouville threshold supplied by the sharp
denominator at an integral point. -/
def stateIntegralLiouvilleThreshold {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  ((((1 : ℝ) ^ (13 ^ 0 - 1))⁻¹ /
      ‖(commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ J) m : ℂ)‖) / 2)

/-- **Source Lemma 3 at an integral point, with all structural and algebraic
inputs instantiated.**

The remaining assumptions are only the displayed numerical comparison
conditions, nonvanishing of the normalized last logarithmic coefficient,
and the asserted smallness of the logarithmic form.  In particular there is
no abstract integrality, denominator, field-degree, conjugate, or certificate
hypothesis. -/
theorem quantitative_lemma3_state_integral {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (B : SourceNumericalConditions
      (stateSourceMajorants P state b bLast (l : ℂ) m))
    (hbLast : bLast ≠ 0)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
      smallLinearFormBound P B.sourceConstant)
    (herrorToLiouville :
      errorEnvelope P B.sourceConstant B.errorMultiplier ≤
        stateIntegralLiouvilleThreshold P J m) :
    ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q J (l : ℂ) m‖ ≤
          growthEnvelope P B.sourceConstant B.growthMultiplier ∧
      ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J (l : ℂ) m -
        vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) P.q J (l : ℂ) m‖ ≤
            errorEnvelope P B.sourceConstant B.errorMultiplier ∧
      (vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J (l : ℂ) m = 0 ∨
        stateIntegralLiouvilleThreshold P J m ≤
          ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
            (oldLog P) P.q J (l : ℂ) m‖) := by
  simpa only [stateIntegralLiouvilleThreshold, stateIntegralTargetCertificate,
    integralTargetCertificate] using quantitative_lemma3
    (stateSourceMajorants P state b bLast (l : ℂ) m) B
    (stateIntegralTargetCertificate P state b bLast l m)
    hbLast hsmall herrorToLiouville

/-! ## The corrected source state at rational targets -/

/-- The complete algebraic certificate for the rational grid point `l/q`.
The field degree is the fixed `13^(oldRank+1)` and is independent of the
induction level `J`. -/
def stateRationalTargetCertificate {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    AlgebraicCertificateInputs (K := SourceRadicalField P)
      (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m
      (oldRank + 1) where
  term := fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
    P.h b bLast J lambda l m
  denominator := algebraMap ℚ (SourceRadicalField P)
    (commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ (J + 1)) m)
  sigma := (SourceRadicalField P).val
  scale :=
    (commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ (J + 1)) m : ℂ)
  scale_ne := by
    exact_mod_cast commonDeltaDenominator_ne_zero P.h P.LzeroPlusOne
      (P.q ^ (J + 1))
      (pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))) m
  denominator_map := rfl
  termIntegral := by
    intro lambda _hlambda
    exact isIntegral_denominator_mul_rationalTargetTerm P
      (coordinatesForState state) P.h P.LzeroPlusOne b bLast J lambda
      (state_deltaPower_le P state lambda) l m
  term_map := by
    intro lambda _hlambda
    exact map_rationalTargetTerm P (coordinatesForState state) P.h
      b bLast J lambda l m
  conjugateBound := rationalTargetConjugateBound P (coordinatesForState state)
    state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  conjugateBound_pos := rationalTargetConjugateBound_pos P
    (coordinatesForState state) state.support state.coeff P.h P.LzeroPlusOne
    b bLast J l m
  other_embeddings := by
    intro tau _htau
    exact norm_embedding_le_rationalTargetConjugateBound P
      (coordinatesForState state) state.support state.coeff P.h P.LzeroPlusOne
      b bLast J l m tau
  finrank_eq_thirteen_pow := finrank_sourceRadicalField P

/-- The explicit Liouville threshold at `l/q`. -/
def stateRationalLiouvilleThreshold {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  ((((rationalTargetConjugateBound P (coordinatesForState state)
      state.support state.coeff P.h P.LzeroPlusOne b bLast J l m) ^
      (13 ^ (oldRank + 1) - 1))⁻¹ /
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne
      (P.q ^ (J + 1)) m : ℂ)‖) / 2)

/-- **Source Lemma 3 at `l/q`, fully instantiated.**  As in the integral
version, the only remaining hypotheses are explicit real inequalities,
`bLast ≠ 0`, and the small-logarithmic-form bound. -/
theorem quantitative_lemma3_state_rational {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (B : SourceNumericalConditions
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ)) m))
    (hbLast : bLast ≠ 0)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
      smallLinearFormBound P B.sourceConstant)
    (herrorToLiouville :
      errorEnvelope P B.sourceConstant B.errorMultiplier ≤
        stateRationalLiouvilleThreshold P J state b bLast l m) :
    ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m‖ ≤
          growthEnvelope P B.sourceConstant B.growthMultiplier ∧
      ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m -
        vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m‖ ≤
            errorEnvelope P B.sourceConstant B.errorMultiplier ∧
      (vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
        stateRationalLiouvilleThreshold P J state b bLast l m ≤
          ‖vdplF (coordinatesForState state) state.support state.coeff P.h b bLast
            (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m‖) := by
  simpa only [stateRationalLiouvilleThreshold,
    stateRationalTargetCertificate] using quantitative_lemma3
    (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ)) m) B
    (stateRationalTargetCertificate P state b bLast l m)
    hbLast hsmall herrorToLiouville

end Erdos240.BakerLemma3Instantiation

#print axioms Erdos240.BakerLemma3Instantiation.finrank_sourceRadicalField
#print axioms Erdos240.BakerLemma3Instantiation.quantitative_lemma3_state_integral
#print axioms Erdos240.BakerLemma3Instantiation.quantitative_lemma3_state_rational

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerRadicalDescent
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerSourceState
import ErdosProblems.Erdos240.RadicalBasis
import ErdosProblems.Erdos240.BakerDeltaTriangularFamily

/-!
# The concrete residue quotient in source Lemma 6

This module connects the coefficient boxes used by `BakerSourceState` to the
radical coefficient extraction in `BakerRadicalDescent`.  The key point is
that the exponential coordinates, and only those coordinates, are divided by
the fixed auxiliary prime `q = 13` at a successor level.

The pair consisting of the residue vector and the quotient box index is
injective.  Consequently restricting a nonzero level-`J` coefficient family
to one residue fibre and pushing it to the quotient box gives a nonzero
level-`J+1` coefficient family with exactly the same height bound.

The analytic source has one further, genuinely non-definitional step: after
the split `lambda = rho + q*mu`, the Delta factors still contain `lambda`.
Van der Poorten--Loxton use their inner derivative induction and linear
combinations on p. 51 to replace this shifted factor `A'` by the standard
factor `A` indexed by `mu`.  The final section exposes the exact equality
which that polynomial argument has to prove; it does not identify the two
factors by definition.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerLemma6Descent

open Finset
open Erdos240
open Erdos240.BakerAuxiliary
open Erdos240.BakerLemma3
open Erdos240.BakerInduction
open Erdos240.BakerRadicalDescent
open Erdos240.BakerSourceState
open Erdos240.BakerTriangularTransport
open Erdos240.BakerDeltaTriangularFamily

private instance {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) : NeZero P.q :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)⟩

private theorem lambdaBox_ext {oldRank : ℕ} {L : BoxShape oldRank}
    {lambda mu : LambdaBox L}
    (hshift : lambda.shiftIndex = mu.shiftIndex)
    (hdelta : lambda.deltaIndexFin = mu.deltaIndexFin)
    (hold : lambda.oldExponentFin = mu.oldExponentFin)
    (hlast : lambda.lastExponentFin = mu.lastExponentFin) :
    lambda = mu := by
  cases lambda
  cases mu
  cases hshift
  cases hdelta
  cases hold
  cases hlast
  rfl

private theorem lambdaBox_ext_val {oldRank : ℕ} {L : BoxShape oldRank}
    {lambda mu : LambdaBox L}
    (hshift : lambda.shift = mu.shift)
    (hdelta : lambda.deltaIndex = mu.deltaIndex)
    (hold : ∀ r, lambda.oldExponent r = mu.oldExponent r)
    (hlast : lambda.lastExponent = mu.lastExponent) :
    lambda = mu := by
  apply lambdaBox_ext
  · apply Fin.ext
    exact hshift
  · apply Fin.ext
    exact hdelta
  · funext r
    apply Fin.ext
    exact hold r
  · apply Fin.ext
    exact hlast

/-! ## Successor quotient boxes -/

theorem scaledExponentMax_div_q {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J L : ℕ) :
    scaledExponentMax P J L / P.q = scaledExponentMax P (J + 1) L := by
  rw [scaledExponentMax_eq_div, scaledExponentMax_eq_div]
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- All exponential coordinates, with the distinguished last coordinate in
the last position. -/
def exponentVector {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (lambda : LevelIndex P J) : Fin (oldRank + 1) → ℕ :=
  Fin.lastCases lambda.lastExponent (fun r ↦ lambda.oldExponent r)

@[simp] theorem exponentVector_castSucc {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (lambda : LevelIndex P J)
    (r : Fin oldRank) :
    exponentVector lambda r.castSucc = lambda.oldExponent r := by
  simp [exponentVector]

@[simp] theorem exponentVector_last {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (lambda : LevelIndex P J) :
    exponentVector lambda (Fin.last oldRank) = lambda.lastExponent := by
  simp [exponentVector]

/-- The residue vector of the exponential coordinates modulo `13`. -/
def indexResidue {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (lambda : LevelIndex P J) : Fin (oldRank + 1) → Fin P.q :=
  exponentResidue P.q (exponentVector lambda)

/-- Divide every exponential coordinate by `13`, leaving the shift and
Delta-power coordinates unchanged.  Euclidean division of the exact floor
sides proves that this lands in the successor box. -/
def quotientIndex {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (lambda : LevelIndex P J) : LevelIndex P (J + 1) where
  shiftIndex := lambda.shiftIndex
  deltaIndexFin := lambda.deltaIndexFin
  oldExponentFin r := ⟨lambda.oldExponent r / P.q, by
    change lambda.oldExponent r / P.q < scaledExponentMax P (J + 1) (P.LiZero r) + 1
    rw [← scaledExponentMax_div_q P J (P.LiZero r)]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt))⟩
  lastExponentFin := ⟨lambda.lastExponent / P.q, by
    change lambda.lastExponent / P.q < scaledExponentMax P (J + 1) P.LlastZero + 1
    rw [← scaledExponentMax_div_q P J P.LlastZero]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.le_of_lt_succ lambda.lastExponentFin.isLt))⟩

@[simp] theorem quotientIndex_shift {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (lambda : LevelIndex P J) :
    (quotientIndex P J lambda).shift = lambda.shift := rfl

@[simp] theorem quotientIndex_deltaIndex {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (lambda : LevelIndex P J) :
    (quotientIndex P J lambda).deltaIndex = lambda.deltaIndex := rfl

@[simp] theorem quotientIndex_oldExponent {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (lambda : LevelIndex P J)
    (r : Fin oldRank) :
    (quotientIndex P J lambda).oldExponent r = lambda.oldExponent r / P.q := rfl

@[simp] theorem quotientIndex_lastExponent {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (lambda : LevelIndex P J) :
    (quotientIndex P J lambda).lastExponent = lambda.lastExponent / P.q := rfl

/-- Residues together with quotients recover a source-box index. -/
theorem indexResidue_quotientIndex_injective {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    Function.Injective (fun lambda : LevelIndex P J ↦
      (indexResidue lambda, quotientIndex P J lambda)) := by
  intro lambda mu h
  rcases Prod.mk.inj h with ⟨hres, hquot⟩
  apply lambdaBox_ext_val
  · simpa using congrArg (fun x ↦ x.shift) hquot
  · simpa using congrArg (fun x ↦ x.deltaIndex) hquot
  · intro r
    have hmod : lambda.oldExponent r % P.q = mu.oldExponent r % P.q := by
      have := congrFun hres r.castSucc
      simpa [indexResidue, exponentResidue, exponentVector] using
        congrArg Fin.val this
    have hdiv : lambda.oldExponent r / P.q = mu.oldExponent r / P.q := by
      have := congrArg (fun x ↦ x.oldExponent r) hquot
      simpa using this
    calc
      lambda.oldExponent r = lambda.oldExponent r % P.q +
          P.q * (lambda.oldExponent r / P.q) :=
        (Nat.mod_add_div _ _).symm
      _ = mu.oldExponent r % P.q + P.q * (mu.oldExponent r / P.q) := by
        rw [hmod, hdiv]
      _ = mu.oldExponent r := Nat.mod_add_div _ _
  ·
    have hmod : lambda.lastExponent % P.q = mu.lastExponent % P.q := by
      have := congrFun hres (Fin.last oldRank)
      simpa [indexResidue, exponentResidue, exponentVector] using
        congrArg Fin.val this
    have hdiv : lambda.lastExponent / P.q = mu.lastExponent / P.q := by
      have := congrArg LambdaBox.lastExponent hquot
      simpa using this
    calc
      lambda.lastExponent = lambda.lastExponent % P.q +
          P.q * (lambda.lastExponent / P.q) :=
        (Nat.mod_add_div _ _).symm
      _ = mu.lastExponent % P.q + P.q * (mu.lastExponent / P.q) := by
        rw [hmod, hdiv]
      _ = mu.lastExponent := Nat.mod_add_div _ _

/-! ## Pushing a selected residue fibre to the successor box -/

/-- Push an integer family through the quotient map after selecting a fixed
residue vector.  Injectivity of `(residue, quotient)` ensures that every sum
contains at most one nonzero old coefficient. -/
def quotientCoefficients {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (state : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q) :
    LevelIndex P (J + 1) → ℤ :=
  fun mu ↦ ∑ lambda,
    if indexResidue lambda = rho ∧ quotientIndex P J lambda = mu then
      state.coeff lambda else 0

theorem quotientCoefficients_apply_of_fiber {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho) :
    quotientCoefficients state rho (quotientIndex P J lambda) =
      state.coeff lambda := by
  classical
  rw [quotientCoefficients]
  rw [Finset.sum_eq_single lambda]
  · rw [if_pos ⟨hres, rfl⟩]
  · intro mu _hmu hne
    by_cases hmu : indexResidue mu = rho ∧
        quotientIndex P J mu = quotientIndex P J lambda
    · have hp : (indexResidue mu, quotientIndex P J mu) =
          (indexResidue lambda, quotientIndex P J lambda) := by
        rw [hmu.1, hres, hmu.2]
      exact (hne (indexResidue_quotientIndex_injective P J hp)).elim
    · rw [if_neg hmu]
  · simp

theorem quotientCoefficients_ne_zero {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q)
    (hrestrict : restrictCoefficients indexResidue rho state.coeff ≠ 0) :
    quotientCoefficients state rho ≠ 0 := by
  classical
  obtain ⟨lambda, hlambda⟩ : ∃ lambda,
      restrictCoefficients indexResidue rho state.coeff lambda ≠ 0 := by
    by_contra h
    push Not at h
    apply hrestrict
    funext lambda
    exact h lambda
  have hres : indexResidue lambda = rho := by
    by_contra hne
    exact hlambda (restrictCoefficients_apply_of_ne
      indexResidue rho state.coeff lambda hne)
  intro hzero
  have := congrFun hzero (quotientIndex P J lambda)
  rw [quotientCoefficients_apply_of_fiber state rho lambda hres] at this
  apply hlambda
  rw [restrictCoefficients_apply_of_eq indexResidue rho state.coeff lambda hres]
  exact this

theorem quotientCoefficients_abs_le {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q) :
    ∀ mu, |(quotientCoefficients state rho mu : ℝ)| ≤ P.coeffHeight := by
  classical
  intro mu
  by_cases hex : ∃ lambda, indexResidue lambda = rho ∧
      quotientIndex P J lambda = mu
  · obtain ⟨lambda, hres, hquot⟩ := hex
    rw [← hquot, quotientCoefficients_apply_of_fiber state rho lambda hres]
    exact state.coeff_height lambda
  · have hz : quotientCoefficients state rho mu = 0 := by
      simp only [quotientCoefficients]
      apply Finset.sum_eq_zero
      intro lambda _hlambda
      simp only [ite_eq_right_iff]
      intro h
      exact (hex ⟨lambda, h.1, h.2⟩).elim
    rw [hz]
    simpa using P.coeffHeight_pos.le

/-- The exact successor side selected by a residue fibre.  This is source
Lemma 6's `floor ((L-rho)/q)`, not in general
`floor (L(0)/q^(J+1))`. -/
def nextOldSide {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (r : Fin oldRank) : ℕ :=
  (state.oldSide r - (rho r.castSucc : ℕ)) / P.q

def nextLastSide {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q) : ℕ :=
  (state.lastSide - (rho (Fin.last oldRank) : ℕ)) / P.q

private theorem div_le_sub_div_of_mod_eq {oldRank e side residue : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (hmod : e % P.q = residue) (hle : e ≤ side) :
    e / P.q ≤ (side - residue) / P.q := by
  simp only [VDPLParameters.q] at hmod ⊢
  omega

theorem nextOldSide_le {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q) (r : Fin oldRank) :
    nextOldSide state rho r ≤ (levelBoxShape P (J + 1)).oldMax r := by
  change (state.oldSide r - (rho r.castSucc : ℕ)) / P.q ≤
    scaledExponentMax P (J + 1) (P.LiZero r)
  rw [← scaledExponentMax_div_q P J (P.LiZero r)]
  exact Nat.div_le_div_right ((Nat.sub_le _ _).trans (state.oldSide_le r))

theorem nextLastSide_le {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q) :
    nextLastSide state rho ≤ (levelBoxShape P (J + 1)).lastMax := by
  change (state.lastSide - (rho (Fin.last oldRank) : ℕ)) / P.q ≤
    scaledExponentMax P (J + 1) P.LlastZero
  rw [← scaledExponentMax_div_q P J P.LlastZero]
  exact Nat.div_le_div_right ((Nat.sub_le _ _).trans state.lastSide_le)

theorem quotientCoefficients_ne_zero_inside {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q) :
    ∀ mu, quotientCoefficients state rho mu ≠ 0 →
      (∀ r, mu.oldExponent r ≤ nextOldSide state rho r) ∧
        mu.lastExponent ≤ nextLastSide state rho := by
  classical
  intro mu hmu
  have hex : ∃ lambda, (indexResidue lambda = rho ∧
      quotientIndex P J lambda = mu) ∧ state.coeff lambda ≠ 0 := by
    by_contra h
    push Not at h
    apply hmu
    simp only [quotientCoefficients]
    apply Finset.sum_eq_zero
    intro lambda _hlambda
    by_cases hcond : indexResidue lambda = rho ∧
        quotientIndex P J lambda = mu
    · rw [if_pos hcond, h lambda hcond]
    · rw [if_neg hcond]
  obtain ⟨lambda, ⟨hres, hquot⟩, hcoeff⟩ := hex
  have hinside := state.coeff_ne_zero_inside lambda hcoeff
  constructor
  · intro r
    rw [← hquot, quotientIndex_oldExponent]
    apply div_le_sub_div_of_mod_eq P
    · have hr := congrFun hres r.castSucc
      simpa [indexResidue, exponentResidue, exponentVector] using
        congrArg Fin.val hr
    · exact hinside.1 r
  · rw [← hquot, quotientIndex_lastExponent]
    apply div_le_sub_div_of_mod_eq P
    · have hr := congrFun hres (Fin.last oldRank)
      simpa [indexResidue, exponentResidue, exponentVector] using
        congrArg Fin.val hr
    · exact hinside.2

/-- The selected fibre defines the genuine next-level state, carrying the
residue-dependent active sides from the source rather than resetting them to
the ambient canonical upper box. -/
def nextState {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (hrestrict : restrictCoefficients indexResidue rho state.coeff ≠ 0) :
    LevelState P (J + 1) :=
  LevelState.ofActiveCoefficients (quotientCoefficients state rho)
    (quotientCoefficients_ne_zero state rho hrestrict)
    (quotientCoefficients_abs_le state rho)
    (nextOldSide state rho) (nextLastSide state rho)
    (nextOldSide_le state rho) (nextLastSide_le state rho)
    (quotientCoefficients_ne_zero_inside state rho)
    (by omega) (by omega)

/-! ## Agreement with the source's intermediate `A'` -/

/-- Repackage a full residue vector in the old/last form used by
`BakerSourceState.residueLiftA`. -/
def exponentResidueData {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (rho : Fin (oldRank + 1) → Fin P.q) : ExponentResidue P where
  old r := rho r.castSucc
  last := rho (Fin.last oldRank)

/-- Euclidean division of the box coordinates gives exactly the agreement
predicate required by the source's intermediate affine factor `A'`. -/
theorem residueLiftAgreement_quotientIndex {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (rho : Fin (oldRank + 1) → Fin P.q) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho) :
    ResidueLiftAgreement (exponentResidueData P rho) lambda
      (quotientIndex P J lambda) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro r
    have hr := congrFun hres r.castSucc
    have hmod : lambda.oldExponent r % P.q = (rho r.castSucc : ℕ) := by
      simpa [indexResidue, exponentResidue, exponentVector] using
        congrArg Fin.val hr
    calc
      lambda.oldExponent r = lambda.oldExponent r % P.q +
          P.q * (lambda.oldExponent r / P.q) :=
        (Nat.mod_add_div _ _).symm
      _ = (rho r.castSucc : ℕ) +
          P.q * (quotientIndex P J lambda).oldExponent r := by
        rw [hmod, quotientIndex_oldExponent]
  ·
    have hr := congrFun hres (Fin.last oldRank)
    have hmod : lambda.lastExponent % P.q =
        (rho (Fin.last oldRank) : ℕ) := by
      simpa [indexResidue, exponentResidue, exponentVector] using
        congrArg Fin.val hr
    calc
      lambda.lastExponent = lambda.lastExponent % P.q +
          P.q * (lambda.lastExponent / P.q) :=
        (Nat.mod_add_div _ _).symm
      _ = (rho (Fin.last oldRank) : ℕ) +
          P.q * (quotientIndex P J lambda).lastExponent := by
        rw [hmod, quotientIndex_lastExponent]

/-- The actual old factor on a selected residue fibre is the source's
intermediate affine factor `A'`; it is deliberately not equated here with the
canonical successor factor `A`. -/
theorem A_div_q_eq_residueLiftA_quotient {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    A state b bLast lambda (z / (P.q : ℂ)) m =
      residueLiftA state (exponentResidueData P rho) b bLast
        (quotientIndex P J lambda) z m := by
  exact A_div_q_eq_residueLiftA state (exponentResidueData P rho) b bLast
    lambda (quotientIndex P J lambda)
      (residueLiftAgreement_quotientIndex P J rho lambda hres) z m

/-- The corresponding exponential splits into the selected radical residue
and the canonical quotient exponential. -/
theorem exp_algebraicRate_div_q_eq_residue_mul_quotient {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (rho : Fin (oldRank + 1) → Fin P.q) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ) :
    Complex.exp
        (algebraicRate coordinates logAlpha logAlphaLast lambda *
          (z / (P.q : ℂ))) =
      Complex.exp
          (residueRate (exponentResidueData P rho) logAlpha logAlphaLast *
            (z / (P.q : ℂ))) *
        Complex.exp
          (algebraicRate coordinates logAlpha logAlphaLast
            (quotientIndex P J lambda) * z) := by
  exact exp_algebraicRate_div_q_eq_residue_mul
    (exponentResidueData P rho) lambda (quotientIndex P J lambda)
    (residueLiftAgreement_quotientIndex P J rho lambda hres)
    logAlpha logAlphaLast z

/-! ## The exact radical basis in `ℂ` -/

/-- The fixed old primes followed by the distinguished varying prime. -/
def sourcePrime {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) :
    Fin (oldRank + 1) → ℕ :=
  Fin.lastCases P.newPrime P.old

@[simp] theorem sourcePrime_castSucc {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (r : Fin oldRank) :
    sourcePrime P r.castSucc = P.old r := by
  simp [sourcePrime]

@[simp] theorem sourcePrime_last {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    sourcePrime P (Fin.last oldRank) = P.newPrime := by
  simp [sourcePrime]

theorem sourcePrime_prime {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) :
    ∀ i, (sourcePrime P i).Prime := by
  intro i
  exact Fin.lastCases (by simpa [sourcePrime] using P.new_prime)
    (fun r ↦ by simpa [sourcePrime] using P.old_prime r) i

theorem sourcePrime_injective {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : Function.Injective (sourcePrime P) := by
  intro i j
  refine Fin.lastCases ?_ (fun ri ↦ ?_) i
  · refine Fin.lastCases (fun _ ↦ rfl) (fun rj h ↦ ?_) j
    simp only [sourcePrime_last, sourcePrime_castSucc] at h
    exact (P.new_fresh rj h.symm).elim
  · refine Fin.lastCases (fun h ↦ ?_) (fun rj h ↦ ?_) j
    · simp only [sourcePrime_castSucc, sourcePrime_last] at h
      exact (P.new_fresh ri h).elim
    · simp only [sourcePrime_castSucc] at h
      exact congrArg Fin.castSucc (P.old_injective h)

/-- The positive complex thirteenth root selected by the real logarithm. -/
def sourceThirteenthRoot {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) : ℂ :=
  Complex.exp ((Real.log (sourcePrime P i : ℝ) : ℂ) / 13)

theorem sourceThirteenthRoot_pow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (i : Fin (oldRank + 1)) :
    sourceThirteenthRoot P i ^ 13 =
      algebraMap ℚ ℂ (sourcePrime P i : ℚ) := by
  have hpR : (0 : ℝ) < sourcePrime P i := by
    exact_mod_cast (sourcePrime_prime P i).pos
  calc
    sourceThirteenthRoot P i ^ 13 =
        Complex.exp ((13 : ℂ) *
          ((Real.log (sourcePrime P i : ℝ) : ℂ) / 13)) := by
      symm
      exact Complex.exp_nat_mul _ _
    _ = Complex.exp (Real.log (sourcePrime P i : ℝ) : ℂ) := by
      congr 1
      field_simp
    _ = algebraMap ℚ ℂ (sourcePrime P i : ℚ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hpR]
      norm_num

/-- Kummer's exact degree theorem, transported to an arbitrary
characteristic-zero ambient field by `RadicalBasis`, gives the precise
linear independence needed for the source residue extraction directly in
`ℂ`. -/
theorem sourceThirteenthRootMonomials_linearIndependent {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    LinearIndependent ℚ
      (Erdos240.Kummer.thirteenthRootMonomial (sourceThirteenthRoot P)) := by
  exact Erdos240.Kummer.linearIndependent_thirteenthRootMonomials
    (sourcePrime P) (sourcePrime_prime P) (sourcePrime_injective P)
    (sourceThirteenthRoot P) (sourceThirteenthRoot_pow P)

/-- At a grid integer coprime to `13`, multiplication of all residue
exponents by that integer merely permutes the exact Kummer basis. -/
theorem sourceThirteenthRootMonomials_residueMul_linearIndependent
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (l : ℕ) (hcop : l.Coprime P.q) :
    LinearIndependent ℚ
      (fun rho : Fin (oldRank + 1) → Fin P.q ↦
        radicalResidueMonomial P.q (sourceThirteenthRoot P)
          (residueVectorMul P.q l rho)) := by
  change LinearIndependent ℚ
    (fun rho : Fin (oldRank + 1) → Fin 13 ↦
      radicalResidueMonomial 13 (sourceThirteenthRoot P)
        (residueVectorMul 13 l rho))
  have hbase : LinearIndependent ℚ
      (radicalResidueMonomial 13 (sourceThirteenthRoot P)) := by
    change LinearIndependent ℚ
      (Erdos240.Kummer.thirteenthRootMonomial (sourceThirteenthRoot P))
    exact sourceThirteenthRootMonomials_linearIndependent P
  exact linearIndependent_residueVectorMul 13 l
    (radicalResidueMonomial 13 (sourceThirteenthRoot P)) hbase hcop

/-! ## The source exponential as a rational radical expansion -/

/-- The logarithms of the fixed old primes. -/
def oldPrimeLog {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (r : Fin oldRank) : ℂ :=
  Real.log (P.old r : ℝ)

/-- The logarithm of the distinguished prime. -/
def lastPrimeLog {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) : ℂ :=
  Real.log (P.newPrime : ℝ)

/-- At an integral grid point, the residue exponential occurring after the
`z/q` split is literally the product of the selected positive thirteenth
roots.  This is the analytic-to-algebraic identification required before
Kummer linear independence can be applied. -/
theorem exp_residueRate_div_q_nat_eq_rootProduct {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (rho : Fin (oldRank + 1) → Fin P.q) (l : ℕ) :
    Complex.exp
        (residueRate (exponentResidueData P rho) (oldPrimeLog P)
          (lastPrimeLog P) * ((l : ℂ) / (P.q : ℂ))) =
      ∏ i, sourceThirteenthRoot P i ^ ((rho i : ℕ) * l) := by
  rw [Fin.prod_univ_castSucc]
  simp only [residueRate, exponentResidueData, oldPrimeLog, lastPrimeLog,
    sourceThirteenthRoot, sourcePrime_castSucc, sourcePrime_last]
  rw [add_mul, Complex.exp_add, Finset.sum_mul, Complex.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro r _hr
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [VDPLParameters.q]
    push_cast
    ring
  · rw [← Complex.exp_nat_mul]
    congr 1
    simp only [VDPLParameters.q]
    push_cast
    ring

/-- The rational prime tuple used for all quotient and carry factors. -/
def sourcePrimeRat {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) :
    Fin (oldRank + 1) → ℚ :=
  fun i ↦ sourcePrime P i

/-- After reducing `l * rho` modulo `13`, every carry is a rational prime
power.  Thus the coefficient multiplying a Kummer-basis monomial really is
rational, as required by coefficient extraction over `ℚ`. -/
theorem exp_residueRate_div_q_nat_eq_map_carry_mul_monomial
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    (rho : Fin (oldRank + 1) → Fin P.q) (l : ℕ) :
    Complex.exp
        (residueRate (exponentResidueData P rho) (oldPrimeLog P)
          (lastPrimeLog P) * ((l : ℂ) / (P.q : ℂ))) =
      algebraMap ℚ ℂ
          (rationalQuotientFactor P.q (sourcePrimeRat P)
            (fun i ↦ (rho i : ℕ) * l)) *
        radicalResidueMonomial P.q (sourceThirteenthRoot P)
          (residueVectorMul P.q l rho) := by
  rw [exp_residueRate_div_q_nat_eq_rootProduct]
  have hres : exponentResidue P.q (fun i ↦ (rho i : ℕ)) = rho := by
    funext i
    apply Fin.ext
    exact Nat.mod_eq_of_lt (rho i).isLt
  simpa only [hres] using
    (radicalMonomial_mul_eq_map_quotient_mul_residueMul P.q l
      (sourcePrimeRat P) (sourceThirteenthRoot P)
      (fun i ↦ by
        simpa only [VDPLParameters.q, sourcePrimeRat] using
          sourceThirteenthRoot_pow P i)
      (fun i ↦ (rho i : ℕ)))

/-- The entire algebraic exponential at `l/q` is a rational quotient factor
times the residue monomial selected by the exponent vector of `lambda`.
Unlike the preceding split-through-`A'` identity, this formulation absorbs
both quotient prime powers and residue carries in a single rational factor. -/
theorem exp_algebraicRate_div_q_nat_eq_map_quotient_mul_monomial
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (lambda : LevelIndex P J) (l : ℕ) :
    Complex.exp
        (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P) lambda *
          ((l : ℂ) / (P.q : ℂ))) =
      algebraMap ℚ ℂ
          (rationalQuotientFactor P.q (sourcePrimeRat P)
            (fun i ↦ exponentVector lambda i * l)) *
        radicalResidueMonomial P.q (sourceThirteenthRoot P)
          (residueVectorMul P.q l (indexResidue lambda)) := by
  have hroot :
      Complex.exp
          (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P) lambda *
            ((l : ℂ) / (P.q : ℂ))) =
        ∏ i, sourceThirteenthRoot P i ^ (exponentVector lambda i * l) := by
    rw [Fin.prod_univ_castSucc]
    simp only [algebraicRate, coordinates, oldPrimeLog, lastPrimeLog,
      sourceThirteenthRoot, sourcePrime_castSucc, sourcePrime_last,
      exponentVector_castSucc, exponentVector_last]
    rw [add_mul, Complex.exp_add, Finset.sum_mul, Complex.exp_sum]
    congr 1
    · apply Finset.prod_congr rfl
      intro r _hr
      rw [← Complex.exp_nat_mul]
      congr 1
      simp only [VDPLParameters.q]
      push_cast
      ring
    · rw [← Complex.exp_nat_mul]
      congr 1
      simp only [VDPLParameters.q]
      push_cast
      ring
  rw [hroot]
  exact radicalMonomial_mul_eq_map_quotient_mul_residueMul P.q l
    (sourcePrimeRat P) (sourceThirteenthRoot P)
    (fun i ↦ by
      simpa only [VDPLParameters.q, sourcePrimeRat] using
        sourceThirteenthRoot_pow P i)
    (exponentVector lambda)

/-- The rational coefficient multiplying one radical basis vector in the
old level-`J` auxiliary sum at `l/q`. -/
def rationalSourceAuxiliaryFactor {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (x : ℚ) (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  (Erdos240.DeltaPower.poweredDeltaHasse h
      (coord.deltaIndex lambda + 1) (m 0)).eval
      (x + coord.shift lambda) *
    ∏ r, (Erdos240Delta.delta (m r.succ)).eval
      ((bLast : ℚ) * coord.oldExponent lambda r -
        (b r : ℚ) * coord.lastExponent lambda)

/-- Casting the rational form of the corrected source factor gives its
complex analytic form. -/
theorem coe_rationalSourceAuxiliaryFactor {oldRank : ℕ} {I : Type*}
    (coord : SourceCoordinates oldRank I) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : I)
    (x : ℚ) (m : VDPLMultiIndex (oldRank + 1)) :
    (rationalSourceAuxiliaryFactor coord h b bLast lambda x m : ℂ) =
      auxiliaryFactor coord h b bLast lambda (x : ℂ) m := by
  simp only [rationalSourceAuxiliaryFactor, auxiliaryFactor,
    poweredDeltaHasseEval, simpleDeltaEval]
  push_cast
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
          (b r : ℚ) * coord.lastExponent lambda : ℚ) : ℂ) by
            push_cast; ring]
    exact (Polynomial.eval₂_at_apply (algebraMap ℚ ℂ)
      ((bLast : ℚ) * coord.oldExponent lambda r -
        (b r : ℚ) * coord.lastExponent lambda)).symm

theorem scaledArgument_div_q_eq_ratCast_local {q J l : ℕ} (hq : q ≠ 0) :
    scaledArgument q J ((l : ℂ) / (q : ℂ)) =
      (((l : ℚ) / q ^ (J + 1) : ℚ) : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  unfold scaledArgument
  push_cast
  rw [pow_succ]
  field_simp

def rationalRadicalFactor {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : LevelIndex P J)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  rationalSourceAuxiliaryFactor (coordinatesForState state) P.h b bLast lambda
      ((l : ℚ) / P.q ^ (J + 1)) m *
    rationalQuotientFactor P.q (sourcePrimeRat P)
      (fun i ↦ exponentVector lambda i * l)

theorem coe_rationalRadicalFactor {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : LevelIndex P J)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    (rationalRadicalFactor state b bLast lambda l m : ℂ) *
        radicalResidueMonomial P.q (sourceThirteenthRoot P)
          (residueVectorMul P.q l (indexResidue lambda)) =
      A state b bLast lambda ((l : ℂ) / (P.q : ℂ)) m *
        Complex.exp
          (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P) lambda *
            ((l : ℂ) / (P.q : ℂ))) := by
  change algebraMap ℚ ℂ
      (rationalSourceAuxiliaryFactor (coordinatesForState state) P.h b bLast lambda
          ((l : ℚ) / P.q ^ (J + 1)) m *
        rationalQuotientFactor P.q (sourcePrimeRat P)
          (fun i ↦ exponentVector lambda i * l)) * _ = _
  rw [map_mul]
  have haux := coe_rationalSourceAuxiliaryFactor
    (coordinatesForState state) P.h b bLast lambda
      ((l : ℚ) / P.q ^ (J + 1)) m
  change algebraMap ℚ ℂ
      (rationalSourceAuxiliaryFactor (coordinatesForState state) P.h b bLast lambda
        ((l : ℚ) / P.q ^ (J + 1)) m) = _ at haux
  rw [haux,
    exp_algebraicRate_div_q_nat_eq_map_quotient_mul_monomial]
  rw [A, scaledArgument_div_q_eq_ratCast_local (J := J) (l := l)
    (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))]
  ring

/-- Exact regrouping of the old source function at the rational grid into
the point-dependent Kummer basis.  Every coefficient of that basis is a
rational finite sum; no algebraic coefficient is hidden in the factor. -/
theorem gWithLogs_rationalGrid_eq_varyingRadicalEvaluation
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    gWithLogs state b bLast (oldPrimeLog P) (lastPrimeLog P)
        ((l : ℂ) / (P.q : ℂ)) m =
      varyingRadicalEvaluation state.support indexResidue
        (fun x rho ↦ radicalResidueMonomial P.q (sourceThirteenthRoot P)
          (residueVectorMul P.q x.1 rho)) state.coeff
        (fun lambda x ↦ rationalRadicalFactor state b bLast lambda x.1 x.2)
        (l, m) := by
  rw [gWithLogs_eq_sum]
  simp only [varyingRadicalEvaluation, LevelState.support]
  apply Finset.sum_congr rfl
  intro lambda _hlambda
  calc
    (state.coeff lambda : ℂ) *
          A state b bLast lambda ((l : ℂ) / (P.q : ℂ)) m *
          Complex.exp
            (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P) lambda *
              ((l : ℂ) / (P.q : ℂ))) =
        (state.coeff lambda : ℂ) *
          (A state b bLast lambda ((l : ℂ) / (P.q : ℂ)) m *
            Complex.exp
              (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P)
                lambda * ((l : ℂ) / (P.q : ℂ)))) := by ring
    _ = (state.coeff lambda : ℂ) *
          ((rationalRadicalFactor state b bLast lambda l m : ℂ) *
            radicalResidueMonomial P.q (sourceThirteenthRoot P)
              (residueVectorMul P.q l (indexResidue lambda))) := by
      rw [coe_rationalRadicalFactor state b bLast lambda l m]
    _ = algebraMap ℚ ℂ
          ((state.coeff lambda : ℚ) *
            rationalRadicalFactor state b bLast lambda l m) *
          radicalResidueMonomial P.q (sourceThirteenthRoot P)
            (residueVectorMul P.q l (indexResidue lambda)) := by
      rw [map_mul]
      have hc : algebraMap ℚ ℂ (state.coeff lambda : ℚ) =
          (state.coeff lambda : ℂ) := by norm_num
      have hf : algebraMap ℚ ℂ
          (rationalRadicalFactor state b bLast lambda l m) =
            (rationalRadicalFactor state b bLast lambda l m : ℂ) := by rfl
      rw [hc, hf]
      ring

/-- Concrete coprime-grid radical extraction for a source level.  It chooses
one residue fibre whose coefficients are nonzero, retains the old common
height bound, and proves every rational coefficient relation on the coprime
part of the next integral grid. -/
theorem exists_residue_fiber_vanishing {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J R S : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hvanish : ∀ l, 1 ≤ l → l ≤ R → l.Coprime P.q →
      ∀ m : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m ≤ S →
        gWithLogs state b bLast (oldPrimeLog P) (lastPrimeLog P)
          ((l : ℂ) / (P.q : ℂ)) m = 0) :
    ∃ rho : Fin (oldRank + 1) → Fin P.q,
      restrictCoefficients indexResidue rho state.coeff ≠ 0 ∧
      (∀ lambda,
        |(restrictCoefficients indexResidue rho state.coeff lambda : ℝ)| ≤
          P.coeffHeight) ∧
      ∀ l, 1 ≤ l → l ≤ R → l.Coprime P.q →
        ∀ m : VDPLMultiIndex (oldRank + 1),
          VDPLMultiIndex.weight m ≤ S →
          fiberEvaluation state.support indexResidue state.coeff
            (fun lambda x ↦
              rationalRadicalFactor state b bLast lambda x.1 x.2)
            rho (l, m) = 0 := by
  exact exists_radicalDescent_of_coprime_rationalGrid_vanishing
    state.support indexResidue
    (fun l _m rho ↦ radicalResidueMonomial P.q (sourceThirteenthRoot P)
      (residueVectorMul P.q l rho))
    (fun l hcop _m ↦
      sourceThirteenthRootMonomials_residueMul_linearIndependent P l hcop)
    state.coeff state.coeff_ne_zero
    (fun lambda l m ↦ rationalRadicalFactor state b bLast lambda l m)
    VDPLMultiIndex.weight R S P.coeffHeight state.coeff_height
    (by
      intro l hl hlR hcop m hm
      rw [← gWithLogs_rationalGrid_eq_varyingRadicalEvaluation]
      exact hvanish l hl hlR hcop m hm)

/-- Expanding the definition of the pushed coefficient family gives a
finite change-of-variables formula.  It is the sum-level counterpart of the
injectivity of `(residue, quotientIndex)`. -/
theorem sum_quotientCoefficients_mul {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ} (state : LevelState P J)
    (rho : Fin (oldRank + 1) → Fin P.q)
    (F : LevelIndex P (J + 1) → ℂ) :
    ∑ mu, (quotientCoefficients state rho mu : ℂ) * F mu =
      ∑ lambda, if indexResidue lambda = rho then
        (state.coeff lambda : ℂ) * F (quotientIndex P J lambda) else 0 := by
  classical
  simp only [quotientCoefficients, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lambda _hlambda
  by_cases hres : indexResidue lambda = rho
  · rw [if_pos hres]
    simp only [hres, true_and]
    rw [Finset.sum_eq_single (quotientIndex P J lambda)]
    · simp
    · intro mu _hmu hne
      rw [if_neg (fun h ↦ hne h.symm)]
      simp
    · simp
  · rw [if_neg hres]
    apply Finset.sum_eq_zero
    intro mu _hmu
    rw [if_neg (fun h ↦ hres h.1)]
    simp

/-! ## Identification of the extracted fibre with the intermediate `A'` -/

/-- The ordinary rational prime power belonging to a quotient index. -/
def quotientPrimePower {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (mu : LevelIndex P J) (l : ℕ) : ℚ :=
  (∏ r, (P.old r : ℚ) ^ (mu.oldExponent r * l)) *
    (P.newPrime : ℚ) ^ (mu.lastExponent * l)

theorem exp_algebraicRate_nat_eq_quotientPrimePower {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (mu : LevelIndex P J) (l : ℕ) :
    Complex.exp
        (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P) mu *
          (l : ℂ)) =
      (quotientPrimePower mu l : ℂ) := by
  unfold oldPrimeLog lastPrimeLog
  rw [exp_algebraicRate_mul_nat_eq coordinates P.old P.newPrime
    (fun r ↦ (P.old_prime r).pos) P.new_prime.pos mu l]
  change (∏ r, (P.old r : ℂ) ^ (mu.oldExponent r * l)) *
      (P.newPrime : ℂ) ^ (mu.lastExponent * l) = _
  unfold quotientPrimePower
  push_cast
  rfl

/-- The quotient part of `(rho + q*mu) * l` splits into a carry depending
only on `rho,l` and the ordinary prime power indexed by `mu`. -/
theorem rationalQuotientFactor_eq_carry_mul_quotientPrimePower
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (rho : Fin (oldRank + 1) → Fin P.q) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho) (l : ℕ) :
    rationalQuotientFactor P.q (sourcePrimeRat P)
        (fun i ↦ exponentVector lambda i * l) =
      rationalQuotientFactor P.q (sourcePrimeRat P)
          (fun i ↦ (rho i : ℕ) * l) *
        quotientPrimePower (quotientIndex P J lambda) l := by
  classical
  have hqpow : quotientPrimePower (quotientIndex P J lambda) l =
      ∏ i, sourcePrimeRat P i ^
        (exponentVector (quotientIndex P J lambda) i * l) := by
    rw [Fin.prod_univ_castSucc]
    simp only [quotientPrimePower, sourcePrimeRat, sourcePrime_castSucc,
      sourcePrime_last, exponentVector_castSucc, exponentVector_last]
  rw [rationalQuotientFactor, rationalQuotientFactor, hqpow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← pow_add]
  congr 1
  have hagree := residueLiftAgreement_quotientIndex P J rho lambda hres
  refine Fin.lastCases ?_ (fun r ↦ ?_) i
  · simp only [exponentQuotient_apply, exponentVector_last]
    change (lambda.lastExponent * l) / P.q =
      ((rho (Fin.last oldRank) : ℕ) * l) / P.q +
        (quotientIndex P J lambda).lastExponent * l
    have hlift : lambda.lastExponent =
        (rho (Fin.last oldRank) : ℕ) +
          P.q * (quotientIndex P J lambda).lastExponent := by
      simpa only [exponentResidueData] using hagree.lastExponent
    rw [hlift, Nat.add_mul, Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt P.one_lt_q)]
  · simp only [exponentQuotient_apply, exponentVector_castSucc]
    change (lambda.oldExponent r * l) / P.q =
      ((rho r.castSucc : ℕ) * l) / P.q +
        (quotientIndex P J lambda).oldExponent r * l
    have hlift : lambda.oldExponent r =
        (rho r.castSucc : ℕ) +
          P.q * (quotientIndex P J lambda).oldExponent r := by
      simpa only [exponentResidueData] using hagree.oldExponent r
    rw [hlift, Nat.add_mul, Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt P.one_lt_q)]

/-- Rational form of equation (12)'s intermediate Delta factor. -/
def rationalResidueLiftA {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (mu : LevelIndex P (J + 1)) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  rationalSourceAuxiliaryFactor
    (residueLiftCoordinates oldState (exponentResidueData P rho))
    P.h b bLast mu ((l : ℚ) / P.q ^ (J + 1)) m

theorem rationalSourceAuxiliaryFactor_eq_rationalResidueLiftA
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    rationalSourceAuxiliaryFactor (coordinatesForState oldState) P.h b bLast lambda
        ((l : ℚ) / P.q ^ (J + 1)) m =
      rationalResidueLiftA oldState rho b bLast
        (quotientIndex P J lambda) l m := by
  have hagree := residueLiftAgreement_quotientIndex P J rho lambda hres
  unfold rationalResidueLiftA rationalSourceAuxiliaryFactor
  unfold residueLiftCoordinates coordinatesForState coordinates
  simp only
  rw [hagree.shift, hagree.deltaIndex]
  congr 1
  apply Finset.prod_congr rfl
  intro r _hr
  rw [hagree.oldExponent r, hagree.lastExponent]

theorem coe_rationalResidueLiftA {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (mu : LevelIndex P (J + 1)) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (rationalResidueLiftA oldState rho b bLast mu l m : ℂ) =
      residueLiftA oldState (exponentResidueData P rho) b bLast mu
        (l : ℂ) m := by
  rw [rationalResidueLiftA, coe_rationalSourceAuxiliaryFactor]
  unfold residueLiftA
  congr 1
  unfold scaledArgument
  push_cast
  norm_num

/-- Rational coefficient of one quotient exponential in equation (12). -/
def rationalResidueLiftTerm {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (mu : LevelIndex P (J + 1)) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℚ :=
  rationalResidueLiftA oldState rho b bLast mu l m *
    quotientPrimePower mu l

theorem rationalRadicalFactor_eq_carry_mul_residueLiftTerm
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (lambda : LevelIndex P J)
    (hres : indexResidue lambda = rho) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    rationalRadicalFactor oldState b bLast lambda l m =
      rationalQuotientFactor P.q (sourcePrimeRat P)
          (fun i ↦ (rho i : ℕ) * l) *
        rationalResidueLiftTerm oldState rho b bLast
          (quotientIndex P J lambda) l m := by
  rw [rationalRadicalFactor,
    rationalSourceAuxiliaryFactor_eq_rationalResidueLiftA oldState rho b bLast
      lambda hres l m,
    rationalQuotientFactor_eq_carry_mul_quotientPrimePower P J rho lambda
      hres l]
  simp only [rationalResidueLiftTerm]
  ring

theorem coe_rationalResidueLiftTerm {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (mu : LevelIndex P (J + 1)) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (rationalResidueLiftTerm oldState rho b bLast mu l m : ℂ) =
      residueLiftA oldState (exponentResidueData P rho) b bLast mu
          (l : ℂ) m *
        Complex.exp
          (algebraicRate coordinates (oldPrimeLog P) (lastPrimeLog P) mu *
            (l : ℂ)) := by
  unfold rationalResidueLiftTerm
  push_cast
  rw [coe_rationalResidueLiftA,
    exp_algebraicRate_nat_eq_quotientPrimePower]

theorem residueLiftGWithLogs_eq_rationalResidueLiftTerm_sum
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (state : LevelState P (J + 1))
    (rho : Fin (oldRank + 1) → Fin P.q)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    residueLiftGWithLogs oldState state (exponentResidueData P rho)
        b bLast (oldPrimeLog P) (lastPrimeLog P) (l : ℂ) m =
      ∑ mu, (state.coeff mu : ℂ) *
        (rationalResidueLiftTerm oldState rho b bLast mu l m : ℂ) := by
  rw [residueLiftGWithLogs_eq_sum]
  apply Finset.sum_congr rfl
  intro mu _hmu
  rw [coe_rationalResidueLiftTerm]
  ring

/-- The selected rational fibre is a nonzero common carry times equation
(12)'s intermediate function.  This is the precise identification after
radical coefficient extraction and quotient reindexing. -/
theorem coe_fiberEvaluation_eq_carry_mul_residueLiftG
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (fiberEvaluation oldState.support indexResidue oldState.coeff
        (fun lambda x ↦
          rationalRadicalFactor oldState b bLast lambda x.1 x.2)
        rho (l, m) : ℂ) =
      (rationalQuotientFactor P.q (sourcePrimeRat P)
          (fun i ↦ (rho i : ℕ) * l) : ℂ) *
        residueLiftGWithLogs oldState (nextState oldState rho hrestrict)
          (exponentResidueData P rho) b bLast (oldPrimeLog P)
          (lastPrimeLog P) (l : ℂ) m := by
  rw [residueLiftGWithLogs_eq_rationalResidueLiftTerm_sum]
  change
    (fiberEvaluation oldState.support indexResidue oldState.coeff
        (fun lambda x ↦
          rationalRadicalFactor oldState b bLast lambda x.1 x.2)
        rho (l, m) : ℂ) =
      (rationalQuotientFactor P.q (sourcePrimeRat P)
          (fun i ↦ (rho i : ℕ) * l) : ℂ) *
        ∑ mu, (quotientCoefficients oldState rho mu : ℂ) *
          (rationalResidueLiftTerm oldState rho b bLast mu l m : ℂ)
  rw [sum_quotientCoefficients_mul]
  rw [Finset.mul_sum]
  simp only [fiberEvaluation, LevelState.support]
  push_cast
  apply Finset.sum_congr rfl
  intro lambda _hlambda
  by_cases hres : indexResidue lambda = rho
  · rw [restrictCoefficients_apply_of_eq indexResidue rho oldState.coeff
      lambda hres, if_pos hres,
      rationalRadicalFactor_eq_carry_mul_residueLiftTerm oldState rho b bLast
        lambda hres l m]
    push_cast
    ring
  · rw [restrictCoefficients_apply_of_ne indexResidue rho oldState.coeff
      lambda hres, if_neg hres]
    simp

theorem residueLiftGWithLogs_eq_zero_of_fiberEvaluation_eq_zero
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (rho : Fin (oldRank + 1) → Fin P.q)
    (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hzero : fiberEvaluation oldState.support indexResidue oldState.coeff
      (fun lambda x ↦
        rationalRadicalFactor oldState b bLast lambda x.1 x.2)
      rho (l, m) = 0) :
    residueLiftGWithLogs oldState (nextState oldState rho hrestrict)
        (exponentResidueData P rho) b bLast (oldPrimeLog P)
        (lastPrimeLog P) (l : ℂ) m = 0 := by
  have hcarry : (rationalQuotientFactor P.q (sourcePrimeRat P)
      (fun i ↦ (rho i : ℕ) * l) : ℂ) ≠ 0 := by
    apply Rat.cast_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    apply pow_ne_zero
    change (sourcePrime P i : ℚ) ≠ 0
    exact_mod_cast (sourcePrime_prime P i).ne_zero
  have h := coe_fiberEvaluation_eq_carry_mul_residueLiftG oldState rho
    hrestrict b bLast l m
  rw [hzero, Rat.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hcarry

/-! ## The inner triangular passage from equation (12) to canonical `g` -/

/-- Attach a fixed head derivative order to an old-coordinate multiindex. -/
def sourceMultiIndexOfHeadTail {oldRank S : ℕ} (head : ℕ)
    (tail : Fin oldRank → Fin (S + 1)) : VDPLMultiIndex (oldRank + 1) :=
  Fin.cases head (fun r ↦ (tail r : ℕ))

theorem weight_sourceMultiIndexOfHeadTail {oldRank S : ℕ} (head : ℕ)
    (tail : Fin oldRank → Fin (S + 1)) :
    VDPLMultiIndex.weight (sourceMultiIndexOfHeadTail head tail) =
      head + TensorFamily.totalDegree tail := by
  simp only [VDPLMultiIndex.weight, sourceMultiIndexOfHeadTail,
    Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    TensorFamily.totalDegree]

/-- The quotient-coordinate variables in the canonical successor Delta
factors. -/
def quotientDeltaPoint {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    {J : ℕ} (b : Fin oldRank → ℤ) (bLast : ℤ)
    (mu : LevelIndex P (J + 1)) (r : Fin oldRank) : ℂ :=
  (bLast : ℂ) * mu.oldExponent r - (b r : ℂ) * mu.lastExponent

/-- The constant part left in the `r`th Delta variable by the selected
residue vector. -/
def residueDeltaConstant {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)}
    (rho : ExponentResidue P) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (r : Fin oldRank) : ℂ :=
  (bLast : ℂ) * (rho.old r : ℕ) - (b r : ℂ) * (rho.last : ℕ)

/-- The tensor family of affine residue-lifted factors
`Delta(q*Y+c_r;m_r)`. -/
def residueLiftDeltaTensor {oldRank S : ℕ}
    (P : VDPLParameters (Fin oldRank)) (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ) :
    TensorFamily ℂ (Fin oldRank) (fun _ ↦ S) :=
  fun r ↦ affineOrdinaryDeltaFamilyComplex S (P.q : ℂ)
    (residueDeltaConstant rho b bLast r)
    (by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)))

/-- The tensor family of the canonical successor factors
`Delta(Y;m_r)`. -/
def canonicalDeltaTensor (oldRank S : ℕ) :
    TensorFamily ℂ (Fin oldRank) (fun _ ↦ S) :=
  fun _ ↦ ordinaryDeltaFamilyComplex S

/-- Everything in one term of equation (12) except the old-coordinate
Delta product.  It is unchanged by triangular row transport. -/
def residueLiftSpectatorWeight {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ)
    (head : ℕ) (mu : LevelIndex P J) : ℂ :=
  (state.coeff mu : ℂ) *
    poweredDeltaHasseEval P.h (mu.deltaIndex + 1) head
      (scaledArgument P.q J z + mu.shift) *
    Complex.exp
      (algebraicRate coordinates logAlpha logAlphaLast mu * z)

/-- Equation (12), for fixed head derivative order, is exactly a row
relation for the affine ordinary-Delta tensor family. -/
theorem residueLiftGWithLogs_eq_affineDeltaRow
    {oldRank S : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (state : LevelState P (J + 1))
    (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ)
    (head : ℕ) (tail : Fin oldRank → Fin (S + 1)) :
    residueLiftGWithLogs oldState state rho b bLast logAlpha logAlphaLast z
        (sourceMultiIndexOfHeadTail head tail) =
      (residueLiftDeltaTensor P rho b bLast).rowRelations
        (residueLiftSpectatorWeight state logAlpha
          logAlphaLast z head)
        (fun mu ↦ quotientDeltaPoint b bLast mu) tail := by
  rw [residueLiftGWithLogs_eq_sum]
  unfold TensorFamily.rowRelations TensorFamily.productEval
  apply Finset.sum_congr rfl
  intro mu _hmu
  unfold residueLiftSpectatorWeight residueLiftA auxiliaryFactor
  unfold residueLiftCoordinates
  simp only [sourceMultiIndexOfHeadTail, Fin.cases_zero, Fin.cases_succ,
    residueLiftDeltaTensor,
    eval_affineOrdinaryDeltaFamilyComplex]
  have hprod :
      (∏ r, simpleDeltaEval (tail r : ℕ)
        ((bLast : ℂ) *
            ((((rho.old r : ℕ) + P.q * mu.oldExponent r : ℕ) : ℂ)) -
          (b r : ℂ) *
            ((((rho.last : ℕ) + P.q * mu.lastExponent : ℕ) : ℂ)))) =
      ∏ r, Polynomial.eval₂ (algebraMap ℚ ℂ)
        ((P.q : ℂ) * quotientDeltaPoint b bLast mu r +
          residueDeltaConstant rho b bLast r)
        (Erdos240Delta.delta (tail r : ℕ)) := by
    apply Finset.prod_congr rfl
    intro r _hr
    unfold simpleDeltaEval quotientDeltaPoint residueDeltaConstant
    congr 2
    push_cast
    ring
  rw [hprod]
  ring

/-- The canonical successor `g`, for fixed head derivative order, is the
corresponding row relation for the ordinary Delta tensor family. -/
theorem gWithLogs_eq_canonicalDeltaRow
    {oldRank S : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ)
    (head : ℕ) (tail : Fin oldRank → Fin (S + 1)) :
    gWithLogs state b bLast logAlpha logAlphaLast z
        (sourceMultiIndexOfHeadTail head tail) =
      (canonicalDeltaTensor oldRank S).rowRelations
        (residueLiftSpectatorWeight state logAlpha
          logAlphaLast z head)
        (fun mu ↦ quotientDeltaPoint b bLast mu) tail := by
  rw [gWithLogs_eq_sum]
  unfold TensorFamily.rowRelations TensorFamily.productEval
  apply Finset.sum_congr rfl
  intro mu _hmu
  unfold residueLiftSpectatorWeight A auxiliaryFactor
  unfold coordinatesForState coordinates canonicalDeltaTensor
  simp only [sourceMultiIndexOfHeadTail, Fin.cases_zero, Fin.cases_succ,
    eval_ordinaryDeltaFamilyComplex]
  have hprod :
      (∏ r, simpleDeltaEval (tail r : ℕ)
        ((bLast : ℂ) * mu.oldExponent r -
          (b r : ℂ) * mu.lastExponent)) =
      ∏ r, Polynomial.eval₂ (algebraMap ℚ ℂ)
        (quotientDeltaPoint b bLast mu r)
        (Erdos240Delta.delta (tail r : ℕ)) := by
    apply Finset.prod_congr rfl
    intro r _hr
    rfl
  rw [hprod]
  ring

theorem weight_eq_head_add_tail {oldRank : ℕ}
    (m : VDPLMultiIndex (oldRank + 1)) :
    VDPLMultiIndex.weight m = m 0 + ∑ r : Fin oldRank, m r.succ := by
  simp only [VDPLMultiIndex.weight, Fin.sum_univ_succ]

/-- Source p. 51's inner induction, formalized as triangular transport on
the total-degree simplex.  Every coefficient and exponential spectator is
left unchanged; only `Delta(qY+c;m)` is replaced by `Delta(Y;m)`. -/
theorem gWithLogs_vanishing_of_residueLiftGWithLogs_vanishing
    {oldRank S : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (state : LevelState P (J + 1))
    (rho : ExponentResidue P)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (logAlpha : Fin oldRank → ℂ) (logAlphaLast z : ℂ)
    (hvanish : ∀ m : VDPLMultiIndex (oldRank + 1),
      VDPLMultiIndex.weight m ≤ S →
      residueLiftGWithLogs oldState state rho b bLast logAlpha logAlphaLast
        z m = 0) :
    ∀ m : VDPLMultiIndex (oldRank + 1),
      VDPLMultiIndex.weight m ≤ S →
      gWithLogs state b bLast logAlpha logAlphaLast z m = 0 := by
  classical
  intro m hm
  have hhead : m 0 ≤ S := (VDPLMultiIndex.component_le_weight m 0).trans hm
  let Srem := S - m 0
  let tail : Fin oldRank → Fin (Srem + 1) := fun r ↦
    ⟨m r.succ, by
      have hr : m r.succ ≤ ∑ i : Fin oldRank, m i.succ := by
        exact Finset.single_le_sum
          (f := fun i : Fin oldRank ↦ m i.succ)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
      have hw := weight_eq_head_add_tail m
      dsimp only [Srem]
      omega⟩
  have hsource : sourceMultiIndexOfHeadTail (m 0) tail = m := by
    funext i
    refine Fin.cases ?_ (fun r ↦ ?_) i
    · rfl
    · rfl
  let Paff : TensorFamily ℂ (Fin oldRank) (fun _ ↦ Srem) :=
    residueLiftDeltaTensor P rho b bLast
  let Pcan : TensorFamily ℂ (Fin oldRank) (fun _ ↦ Srem) :=
    canonicalDeltaTensor oldRank Srem
  let weight : LevelIndex P (J + 1) → ℂ :=
    residueLiftSpectatorWeight state logAlpha logAlphaLast z (m 0)
  let point : LevelIndex P (J + 1) → Fin oldRank → ℂ :=
    fun mu ↦ quotientDeltaPoint b bLast mu
  have haff : ∀ a : Fin oldRank → Fin (Srem + 1),
      TensorFamily.totalDegree a ≤ Srem →
      Paff.rowRelations weight point a = 0 := by
    intro a ha
    rw [← residueLiftGWithLogs_eq_affineDeltaRow oldState state rho b bLast
      logAlpha logAlphaLast z (m 0) a]
    apply hvanish
    rw [weight_sourceMultiIndexOfHeadTail]
    dsimp only [Srem] at ha
    omega
  have hcan := Paff.rowRelations_eq_zero_transport_on_simplex Pcan
    weight point haff tail
  have htail : TensorFamily.totalDegree tail ≤ Srem := by
    have hw := congrArg VDPLMultiIndex.weight hsource
    rw [weight_sourceMultiIndexOfHeadTail] at hw
    dsimp only [Srem]
    omega
  have hrow := hcan htail
  rw [← gWithLogs_eq_canonicalDeltaRow state b bLast logAlpha
    logAlphaLast z (m 0) tail] at hrow
  rwa [hsource] at hrow

/-- The concrete radical-descent output before the source's inner triangular
change of Delta basis.  This single statement packages every algebraic fact
that is already forced directly by Kummer independence:

* a nonzero residue fibre is selected;
* its coefficients become the successor coefficient family without any
  increase in height;
* its genuine active sides are the residue-dependent quotient sides and lie
  in the ambient successor box; and
* equation (12), represented by `residueLiftGWithLogs`, vanishes throughout
  the coprime part of the required grid and derivative budget.

The conclusion deliberately names the intermediate `A'`.  Replacing it by
the canonical successor `A` is the separate triangular-basis argument in the
second half of source Lemma 6, not a definitional equality. -/
theorem exists_successor_with_residueLift_vanishing
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J R S : ℕ}
    (oldState : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hvanish : ∀ l, 1 ≤ l → l ≤ R → l.Coprime P.q →
      ∀ m : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m ≤ S →
        gWithLogs oldState b bLast (oldPrimeLog P) (lastPrimeLog P)
          ((l : ℂ) / (P.q : ℂ)) m = 0) :
    ∃ (rho : Fin (oldRank + 1) → Fin P.q)
        (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0),
      let state := nextState oldState rho hrestrict
      state.coeff = quotientCoefficients oldState rho ∧
      state.coeff ≠ 0 ∧
      (∀ mu, |(state.coeff mu : ℝ)| ≤ P.coeffHeight) ∧
      state.oldSide = nextOldSide oldState rho ∧
      state.lastSide = nextLastSide oldState rho ∧
      (∀ r, state.oldSide r ≤ (levelBoxShape P (J + 1)).oldMax r) ∧
      state.lastSide ≤ (levelBoxShape P (J + 1)).lastMax ∧
      (∀ mu, state.coeff mu ≠ 0 →
        (∀ r, mu.oldExponent r ≤ state.oldSide r) ∧
          mu.lastExponent ≤ state.lastSide) ∧
      ∀ l, 1 ≤ l → l ≤ R → l.Coprime P.q →
        ∀ m : VDPLMultiIndex (oldRank + 1),
          VDPLMultiIndex.weight m ≤ S →
          residueLiftGWithLogs oldState state (exponentResidueData P rho)
            b bLast (oldPrimeLog P) (lastPrimeLog P) (l : ℂ) m = 0 := by
  obtain ⟨rho, hrestrict, _hheight, hfiber⟩ :=
    exists_residue_fiber_vanishing oldState b bLast hvanish
  refine ⟨rho, hrestrict, ?_⟩
  dsimp only
  refine ⟨rfl, (nextState oldState rho hrestrict).coeff_ne_zero,
    (nextState oldState rho hrestrict).coeff_height, rfl, rfl,
    (nextState oldState rho hrestrict).oldSide_le,
    (nextState oldState rho hrestrict).lastSide_le,
    (nextState oldState rho hrestrict).coeff_ne_zero_inside, ?_⟩
  intro l hl hlR hcop m hm
  apply residueLiftGWithLogs_eq_zero_of_fiberEvaluation_eq_zero oldState rho
    hrestrict b bLast l m
  exact hfiber l hl hlR hcop m hm

/-- Complete algebraic part of the actual `J → J+1` construction.  The
selected fibre gives a nonzero successor state with the same coefficient
height and genuine quotient sides, and the p. 51 triangular argument gives
the canonical successor `g` on every grid point at which the Kummer residue
permutation is invertible, namely `(l,q)=1`. -/
theorem exists_successor_with_canonical_coprime_vanishing
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J R S : ℕ}
    (oldState : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hvanish : ∀ l, 1 ≤ l → l ≤ R → l.Coprime P.q →
      ∀ m : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m ≤ S →
        gWithLogs oldState b bLast (oldPrimeLog P) (lastPrimeLog P)
          ((l : ℂ) / (P.q : ℂ)) m = 0) :
    ∃ (rho : Fin (oldRank + 1) → Fin P.q)
        (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0),
      let state := nextState oldState rho hrestrict
      state.coeff = quotientCoefficients oldState rho ∧
      state.coeff ≠ 0 ∧
      (∀ mu, |(state.coeff mu : ℝ)| ≤ P.coeffHeight) ∧
      state.oldSide = nextOldSide oldState rho ∧
      state.lastSide = nextLastSide oldState rho ∧
      (∀ r, state.oldSide r ≤ (levelBoxShape P (J + 1)).oldMax r) ∧
      state.lastSide ≤ (levelBoxShape P (J + 1)).lastMax ∧
      (∀ mu, state.coeff mu ≠ 0 →
        (∀ r, mu.oldExponent r ≤ state.oldSide r) ∧
          mu.lastExponent ≤ state.lastSide) ∧
      ∀ l, 1 ≤ l → l ≤ R → l.Coprime P.q →
        ∀ m : VDPLMultiIndex (oldRank + 1),
          VDPLMultiIndex.weight m ≤ S →
          gWithLogs state b bLast (oldPrimeLog P) (lastPrimeLog P)
            (l : ℂ) m = 0 := by
  obtain ⟨rho, hrestrict, hcoeff, hne, hheight, holdSide, hlastSide,
      holdSideLe, hlastSideLe, hinside, hresidue⟩ :=
    exists_successor_with_residueLift_vanishing oldState b bLast hvanish
  refine ⟨rho, hrestrict, hcoeff, hne, hheight, holdSide, hlastSide,
    holdSideLe, hlastSideLe, hinside, ?_⟩
  intro l hl hlR hcop m hm
  apply gWithLogs_vanishing_of_residueLiftGWithLogs_vanishing
    oldState (nextState oldState rho hrestrict) (exponentResidueData P rho)
    b bLast (oldPrimeLog P) (lastPrimeLog P) (l : ℂ)
  · intro m' hm'
    exact hresidue l hl hlR hcop m' hm'
  · exact hm

/-- `BakerInduction`-facing form of the concrete radical descent.  Its input
is exactly the rational-grid conclusion produced at level `J`; its output is
the nonzero successor state together with equation (12) on the coprime
integral grid of level `J+1`. -/
theorem exists_successor_residueLift_of_rationalExtrapolated
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hrat : RationalExtrapolatedAtLevel P (g oldState b bLast) J) :
    ∃ (rho : Fin (oldRank + 1) → Fin P.q)
        (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0),
      ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → l.Coprime P.q →
        ∀ m : VDPLMultiIndex (oldRank + 1),
          VDPLMultiIndex.weight m ≤ P.Sstep J →
          residueLiftGWithLogs oldState (nextState oldState rho hrestrict)
            (exponentResidueData P rho) b bLast (oldPrimeLog P)
            (lastPrimeLog P) (l : ℂ) m = 0 := by
  have hsource : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → l.Coprime P.q →
      ∀ m : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m ≤ P.Sstep J →
        gWithLogs oldState b bLast (oldPrimeLog P) (lastPrimeLog P)
          ((l : ℂ) / (P.q : ℂ)) m = 0 := by
    intro l hl hlR _hcop m hm
    have h := hrat l hl hlR (fromSourceMultiIndex P m)
      (by simpa only [weight_fromSourceMultiIndex] using hm)
    change gWithLogs oldState b bLast (oldLog P) (lastLog P)
      ((l : ℂ) / (P.q : ℂ)) m = 0
    simpa only [g, gSource, toSourceMultiIndex_fromSourceMultiIndex] using h
  obtain ⟨rho, hrestrict, _hcoeff, _hne, _hheight, _holdSide, _hlastSide,
    _holdSideLe, _hlastSideLe, _hinside, hzero⟩ :=
      exists_successor_with_residueLift_vanishing oldState b bLast hsource
  exact ⟨rho, hrestrict, hzero⟩

/-- Concrete `BakerInduction` adapter with the mathematically valid target:
rational-grid vanishing at level `J` constructs the nonzero quotient state
and the full predecessor-budget coprime descent output.  The budget remains
`Sstep J` here; the second interpolation on p. 52 uses part of this budget
before producing the smaller all-node seed at level `J+1`. -/
theorem exists_successor_coprimeSeed_of_rationalExtrapolated
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hrat : RationalExtrapolatedAtLevel P (g oldState b bLast) J) :
    ∃ (rho : Fin (oldRank + 1) → Fin P.q)
        (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0),
      CoprimeDescentAtLevel P
        (g (nextState oldState rho hrestrict) b bLast) J := by
  have hsource : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → l.Coprime P.q →
      ∀ m : VDPLMultiIndex (oldRank + 1),
        VDPLMultiIndex.weight m ≤ P.Sstep J →
        gWithLogs oldState b bLast (oldPrimeLog P) (lastPrimeLog P)
          ((l : ℂ) / (P.q : ℂ)) m = 0 := by
    intro l hl hlR _hcop m hm
    have h := hrat l hl hlR (fromSourceMultiIndex P m)
      (by simpa only [weight_fromSourceMultiIndex] using hm)
    change gWithLogs oldState b bLast (oldLog P) (lastLog P)
      ((l : ℂ) / (P.q : ℂ)) m = 0
    simpa only [g, gSource, toSourceMultiIndex_fromSourceMultiIndex] using h
  obtain ⟨rho, hrestrict, _hcoeff, _hne, _hheight, _holdSide, _hlastSide,
      _holdSideLe, _hlastSideLe, _hinside, hcanonical⟩ :=
    exists_successor_with_canonical_coprime_vanishing oldState b bLast hsource
  refine ⟨rho, hrestrict, ?_⟩
  intro l hl hlR hcop m hm
  change gWithLogs (nextState oldState rho hrestrict) b bLast
    (oldLog P) (lastLog P) (l : ℂ) (toSourceMultiIndex P m) = 0
  apply hcanonical l hl hlR hcop
  simpa only [weight_toSourceMultiIndex] using hm

/-! ## The second, analytic half of the successor step -/

/-- The literal repeated list of source interpolation nodes: the integers
`1,…,R` which are prime to `q`, each with multiplicity `M`. -/
def coprimeHermiteNodes (q R M : ℕ) : List ℂ :=
  (List.range R).flatMap fun i ↦
    if (i + 1).Coprime q then List.replicate M ((i + 1 : ℕ) : ℂ)
    else []

/-- An interpolation certificate whose node list is definitionally tied to
the coprime-node list used on pp. 51--52.  The quantitative fields inherited
from `RationalInterpolationCertificate` are exactly the contour bound,
Hermite-polynomial bound, and strict comparison with the Lemma 3 lower
bound. -/
structure CoprimeHermiteCertificate
    (f : ℂ → ℂ) (z : ℂ) (lower : ℝ) (q R M : ℕ) where
  certificate :
    Erdos240.BakerRationalExtrapolation.RationalInterpolationCertificate
      f z lower
  nodes_eq : certificate.nodes = coprimeHermiteNodes q R M

/-- The checked logical endpoint of the source's second Hermite
interpolation.  The certificate builder may use the coprime seed to prove
that the Hermite polynomial is controlled at the literal repeated coprime
nodes; the Lemma 3 alternative then forces every missing node to vanish.

The multiplicity `M` is exposed because the source instantiation takes
`M = floor(S/4)`, while the desired base multiindex budget is bounded by
`floor(3S/4)`. -/
theorem coprimeCompletionAtLevel_of_interpolation_certificates
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) (J M : ℕ)
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hbudget : P.Slevel (J + 1) ≤ P.Sstep J)
    (hcertificate : CoprimeDescentAtLevel P G J →
      ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → ¬ l.Coprime P.q →
        ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
          CoprimeHermiteCertificate (fun z ↦ F z m) (l : ℂ)
            (lower l m) P.q (P.R (J + 1)) M)
    (hliouville : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
        G (l : ℂ) m = 0 ∨ lower l m ≤ ‖F (l : ℂ) m‖) :
    CoprimeCompletionAtLevel P G J := by
  intro hcop
  intro l hl hlR m hm
  by_cases hlcop : l.Coprime P.q
  · simpa only [Nat.cast_one, div_one] using
      hcop l hl hlR hlcop m (le_trans hm hbudget)
  · have hz : G (l : ℂ) m = 0 :=
      Erdos240.BakerRationalExtrapolation.RationalInterpolationCertificate.force_zero
        (g := fun z ↦ G z m)
        (hcertificate hcop l hl hlR hlcop m hm).certificate
        (hliouville l hl hlR m hm)
    simpa only [Nat.cast_one, div_one] using hz

/-- Once the source-specific coprime Hermite certificates have been
constructed, the concrete residue state supplies the full all-node
`IntegralSeedAtLevel` demanded by the finite-level induction. -/
theorem exists_successor_integralSeed_of_rationalExtrapolated
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (oldState : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hrat : RationalExtrapolatedAtLevel P (g oldState b bLast) J)
    (complete : ∀ (rho : Fin (oldRank + 1) → Fin P.q)
      (hrestrict : restrictCoefficients indexResidue rho oldState.coeff ≠ 0),
      CoprimeCompletionAtLevel P
        (g (nextState oldState rho hrestrict) b bLast) J) :
    ∃ state : LevelState P (J + 1),
      IntegralSeedAtLevel P (g state b bLast) (J + 1) := by
  obtain ⟨rho, hrestrict, hcop⟩ :=
    exists_successor_coprimeSeed_of_rationalExtrapolated
      oldState b bLast hrat
  exact ⟨nextState oldState rho hrestrict,
    complete rho hrestrict hcop⟩

end Erdos240.BakerLemma6Descent

#print axioms Erdos240.BakerLemma6Descent.scaledExponentMax_div_q
#print axioms Erdos240.BakerLemma6Descent.indexResidue_quotientIndex_injective
#print axioms Erdos240.BakerLemma6Descent.quotientCoefficients_ne_zero
#print axioms Erdos240.BakerLemma6Descent.nextState
#print axioms Erdos240.BakerLemma6Descent.residueLiftAgreement_quotientIndex
#print axioms Erdos240.BakerLemma6Descent.A_div_q_eq_residueLiftA_quotient
#print axioms Erdos240.BakerLemma6Descent.exp_algebraicRate_div_q_eq_residue_mul_quotient
#print axioms Erdos240.BakerLemma6Descent.sourceThirteenthRootMonomials_linearIndependent
#print axioms Erdos240.BakerLemma6Descent.sourceThirteenthRootMonomials_residueMul_linearIndependent
#print axioms Erdos240.BakerLemma6Descent.exp_residueRate_div_q_nat_eq_rootProduct
#print axioms Erdos240.BakerLemma6Descent.exp_residueRate_div_q_nat_eq_map_carry_mul_monomial
#print axioms Erdos240.BakerLemma6Descent.exp_algebraicRate_div_q_nat_eq_map_quotient_mul_monomial
#print axioms Erdos240.BakerLemma6Descent.gWithLogs_rationalGrid_eq_varyingRadicalEvaluation
#print axioms Erdos240.BakerLemma6Descent.exists_residue_fiber_vanishing
#print axioms Erdos240.BakerLemma6Descent.sum_quotientCoefficients_mul
#print axioms Erdos240.BakerLemma6Descent.coe_rationalRadicalFactor
#print axioms Erdos240.BakerLemma6Descent.residueLiftGWithLogs_eq_zero_of_fiberEvaluation_eq_zero
#print axioms Erdos240.BakerLemma6Descent.residueLiftGWithLogs_eq_affineDeltaRow
#print axioms Erdos240.BakerLemma6Descent.gWithLogs_eq_canonicalDeltaRow
#print axioms Erdos240.BakerLemma6Descent.gWithLogs_vanishing_of_residueLiftGWithLogs_vanishing
#print axioms Erdos240.BakerLemma6Descent.exists_successor_with_canonical_coprime_vanishing
#print axioms Erdos240.BakerLemma6Descent.exists_successor_coprimeSeed_of_rationalExtrapolated
#print axioms Erdos240.BakerLemma6Descent.coprimeCompletionAtLevel_of_interpolation_certificates
#print axioms Erdos240.BakerLemma6Descent.exists_successor_integralSeed_of_rationalExtrapolated

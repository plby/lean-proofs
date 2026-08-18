/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.AppendixEncoding
import ErdosProblems.Erdos186.CFP.ProjectedProperization
import ErdosProblems.Erdos186.CFP.TrivialEnhancedWitness

/-!
# Assembly lemmas for the higher-dimensional CFP corollary

This file joins the translation-invariant Appendix encoding with the
source-correct nonempty theorem boundary.  The elementary small-input branch
is unconditional.  The remaining large-input step is the genuine projected
properization existence assertion of CFP Lemma 2.27.
-/

namespace Erdos186.CFP.HigherDimensionalCorollary

open scoped BigOperators
open Filter

noncomputable section

/-- Uniform fixed-scale constants returned by the nonempty integer theorem
necessarily have numerator at most denominator.  It suffices to apply the
theorem to the singleton `{1}` at scale one. -/
theorem scaleNum_le_scaleDen_of_integerConclusion
    {beta eta : ℝ} {scaleNum scaleDen D lossConstant : ℕ}
    (hout : ∀ (n : ℕ) (A : Finset ℤ) (s : ℕ),
      A.Nonempty →
      A ⊆ Finset.Icc 1 (n : ℤ) →
      (n : ℝ) ≤ Real.rpow (A.card : ℝ) beta →
      Real.rpow (A.card : ℝ) eta ≤ (s : ℝ) →
      (scaleDen : ℝ) * (s : ℝ) * Real.logb 2 (A.card : ℝ) ≤
        (scaleNum : ℝ) * (A.card : ℝ) →
      ∃ k loss : ℕ,
        Nonempty (FixedScaleWitness (integerPoints A) s D k loss
          scaleNum scaleDen) ∧
        (loss : ℝ) ≤ (lossConstant : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1) :
    scaleNum ≤ scaleDen := by
  obtain ⟨k, loss, ⟨W⟩, _hloss⟩ := hout 1 {1} 1
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp [Real.logb])
  have hscale := W.enhanced.scaleNum_le_scaleDen
  simpa only [W.scaleNum_eq, W.scaleDen_eq] using hscale

/-- For inputs of cardinality at least two, the upper-scale hypothesis gives
the simple natural bound `s ≤ scaleNum * |A|`. -/
theorem scale_le_scaleNum_mul_card
    (scaleNum scaleDen s card : ℕ) (hden : 0 < scaleDen)
    (hcard : 2 ≤ card)
    (hupper : (scaleDen : ℝ) * (s : ℝ) *
      Real.logb 2 (card : ℝ) ≤ (scaleNum : ℝ) * (card : ℝ)) :
    s ≤ scaleNum * card := by
  have hcardReal : (2 : ℝ) ≤ (card : ℝ) := by exact_mod_cast hcard
  have hlogbOne : 1 ≤ Real.logb 2 (card : ℝ) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    simpa using Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2)
      (zero_lt_two.trans_le hcardReal) hcardReal
  have hdenReal : (1 : ℝ) ≤ (scaleDen : ℝ) := by exact_mod_cast hden
  have hsNonneg : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hsBound : (s : ℝ) ≤ (scaleNum : ℝ) * (card : ℝ) := by
    calc
      (s : ℝ) ≤ (scaleDen : ℝ) * (s : ℝ) := by
        nlinarith
      _ ≤ (scaleDen : ℝ) * (s : ℝ) *
          Real.logb 2 (card : ℝ) :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) hsNonneg) hlogbOne
      _ ≤ (scaleNum : ℝ) * (card : ℝ) := hupper
  exact_mod_cast hsBound

/-- A single coarse parameter dominating every product appearing in the
canonical no-carry radius. -/
def coarseAppendixParameter (D s R : ℕ) : ℕ :=
  4 * (D + 1) * (s + 1) * (R + 1)

theorem four_le_coarseAppendixParameter (D s R : ℕ) :
    4 ≤ coarseAppendixParameter D s R := by
  simp only [coarseAppendixParameter]
  calc
    4 ≤ 4 * (D + 1) := Nat.le_mul_of_pos_right 4 (by omega)
    _ ≤ 4 * (D + 1) * (s + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ 4 * (D + 1) * (s + 1) * (R + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)

theorem D_le_coarseAppendixParameter (D s R : ℕ) :
    D ≤ coarseAppendixParameter D s R := by
  simp only [coarseAppendixParameter]
  calc
    D ≤ 4 * (D + 1) := by omega
    _ ≤ 4 * (D + 1) * (s + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ 4 * (D + 1) * (s + 1) * (R + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)

theorem s_le_coarseAppendixParameter (D s R : ℕ) :
    s ≤ coarseAppendixParameter D s R := by
  simp only [coarseAppendixParameter]
  have hfactorPos : 0 < 4 * (D + 1) := Nat.mul_pos (by omega) (by omega)
  have hfactor : 1 ≤ 4 * (D + 1) := by omega
  calc
    s ≤ s + 1 := by omega
    _ = 1 * (s + 1) := by simp
    _ ≤ (4 * (D + 1)) * (s + 1) := Nat.mul_le_mul_right _ hfactor
    _ ≤ (4 * (D + 1) * (s + 1)) * (R + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)

theorem R_le_coarseAppendixParameter (D s R : ℕ) :
    R ≤ coarseAppendixParameter D s R := by
  simp only [coarseAppendixParameter]
  have hfactorPos : 0 < 4 * (D + 1) * (s + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hfactor : 1 ≤ 4 * (D + 1) * (s + 1) := by omega
  calc
    R ≤ R + 1 := by omega
    _ = 1 * (R + 1) := by simp
    _ ≤ (4 * (D + 1) * (s + 1)) * (R + 1) :=
      Nat.mul_le_mul_right _ hfactor

theorem two_mul_s_mul_R_add_one_le_coarseAppendixParameter
    (D s R : ℕ) :
    2 * s * R + 1 ≤ coarseAppendixParameter D s R := by
  simp only [coarseAppendixParameter]
  have hfirst : 2 * s * R + 1 ≤ 2 * (s + 1) * (R + 1) := by
    have heq : 2 * (s + 1) * (R + 1) =
        2 * s * R + 2 * s + 2 * R + 2 := by ring
    rw [heq]
    omega
  calc
    2 * s * R + 1 ≤ 2 * (s + 1) * (R + 1) := hfirst
    _ ≤ 4 * (D + 1) * (s + 1) * (R + 1) := by
      gcongr
      omega

/-- Monomial domination of the witness-independent no-carry radius. -/
theorem uniformRadiusBound_le_coarseAppendixParameter_pow
    (D s ambient R : ℕ) :
    AppendixEncoding.uniformRadiusBound D s ambient R ≤
      coarseAppendixParameter D s R ^ (ambient + 4) := by
  let X := coarseAppendixParameter D s R
  let L := 2 * s * R
  let rho := D * (2 * (s * R) + 1) ^ ambient
  let T := s * rho * L
  have hX : 4 ≤ X := four_le_coarseAppendixParameter D s R
  have hD : D ≤ X := D_le_coarseAppendixParameter D s R
  have hs : s ≤ X := s_le_coarseAppendixParameter D s R
  have hR : R ≤ X := R_le_coarseAppendixParameter D s R
  have hL : L ≤ X := by
    dsimp only [L]
    have h := two_mul_s_mul_R_add_one_le_coarseAppendixParameter D s R
    omega
  have hbase : 2 * (s * R) + 1 ≤ X := by
    simpa only [Nat.mul_assoc] using
      two_mul_s_mul_R_add_one_le_coarseAppendixParameter D s R
  have hrho : rho ≤ X ^ (ambient + 1) := by
    dsimp only [rho]
    calc
      D * (2 * (s * R) + 1) ^ ambient ≤ X * X ^ ambient := by
        gcongr
      _ = X ^ (ambient + 1) := by
        rw [show ambient + 1 = ambient + 1 by rfl, pow_succ]
        ring
  have hrhoL : rho * L ≤ X ^ (ambient + 2) := by
    calc
      rho * L ≤ X ^ (ambient + 1) * X := Nat.mul_le_mul hrho hL
      _ = X ^ (ambient + 2) := by
        rw [show ambient + 2 = (ambient + 1) + 1 by omega, pow_succ]
        ring
  have hT : T ≤ X ^ (ambient + 3) := by
    dsimp only [T]
    calc
      s * rho * L = s * (rho * L) := by ring
      _ ≤ X * X ^ (ambient + 2) := Nat.mul_le_mul hs hrhoL
      _ = X ^ (ambient + 3) := by
        rw [show ambient + 3 = (ambient + 2) + 1 by omega, pow_succ]
        ring
  have hthreeRhoL : 3 * rho * L ≤ X ^ (ambient + 3) := by
    calc
      3 * rho * L = 3 * (rho * L) := by ring
      _ ≤ X * X ^ (ambient + 2) :=
        Nat.mul_le_mul (by omega) hrhoL
      _ = X ^ (ambient + 3) := by
        rw [show ambient + 3 = (ambient + 2) + 1 by omega, pow_succ]
        ring
  have honePow : 1 ≤ X ^ (ambient + 3) := Nat.one_le_pow _ _ (by omega)
  have hsum : T + 3 * (s * rho) * L ≤ X ^ (ambient + 4) := by
    have hthreeS : 3 * s ≤ X := by
      calc
        3 * s ≤ 4 * (s + 1) := by omega
        _ ≤ 4 * (D + 1) * (s + 1) := by
          gcongr
          omega
        _ ≤ 4 * (D + 1) * (s + 1) * (R + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        _ = X := by rfl
    have hsecond : 3 * (s * rho) * L ≤ X ^ (ambient + 3) := by
      calc
        3 * (s * rho) * L = (3 * s) * (rho * L) := by ring
        _ ≤ X * X ^ (ambient + 2) := Nat.mul_le_mul hthreeS hrhoL
        _ = X ^ (ambient + 3) := by
          rw [show ambient + 3 = (ambient + 2) + 1 by omega, pow_succ]
          ring
    calc
      T + 3 * (s * rho) * L ≤
          X ^ (ambient + 3) + X ^ (ambient + 3) :=
        Nat.add_le_add hT hsecond
      _ = 2 * X ^ (ambient + 3) := by omega
      _ ≤ X * X ^ (ambient + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = X ^ (ambient + 4) := by
        rw [show ambient + 4 = (ambient + 3) + 1 by omega, pow_succ]
        ring
  simp only [AppendixEncoding.uniformRadiusBound]
  change max (s * R) (max (3 * rho * L) (T + 3 * (s * rho) * L)) ≤
    X ^ (ambient + 4)
  apply max_le
  · calc
      s * R ≤ X * X := Nat.mul_le_mul hs hR
      _ ≤ X ^ (ambient + 4) := by
        have : 2 ≤ ambient + 4 := by omega
        have hpow := Nat.pow_le_pow_right (by omega : 0 < X) this
        simpa [pow_two] using hpow
  · apply max_le
    · exact hthreeRhoL.trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact hsum

/-- Degree of the coarse monomial controlling the encoded endpoint in
ambient dimension `d`. -/
def appendixEndpointDegree (d : ℕ) : ℕ :=
  1 + (d + 6) * (d + 1)

/-- The full Appendix endpoint is bounded by one monomial in the coarse
parameter.  This removes all nested `max` expressions from the outer
asymptotic calculation. -/
theorem appendixEndpointPolynomialBound_le_coarseAppendixParameter_pow
    (D s d R : ℕ) :
    AppendixEncoding.appendixEndpointPolynomialBound D s d R ≤
      coarseAppendixParameter D s R ^ appendixEndpointDegree d := by
  let X := coarseAppendixParameter D s R
  let U := AppendixEncoding.uniformRadiusBound D s (d + 1) R
  have hX : 4 ≤ X := four_le_coarseAppendixParameter D s R
  have hR : R ≤ X := R_le_coarseAppendixParameter D s R
  have hU : U ≤ X ^ (d + 5) := by
    simpa only [U, X, show d + 1 + 4 = d + 5 by omega] using
      uniformRadiusBound_le_coarseAppendixParameter_pow D s (d + 1) R
  have hpowOne : 1 ≤ X ^ (d + 5) := Nat.one_le_pow _ _ (by omega)
  have hbase : 2 * U + 2 ≤ X ^ (d + 6) := by
    calc
      2 * U + 2 ≤ 2 * X ^ (d + 5) + 2 := by omega
      _ ≤ X * X ^ (d + 5) := by nlinarith
      _ = X ^ (d + 6) := by
        rw [show d + 6 = (d + 5) + 1 by omega, pow_succ]
        ring
  simp only [AppendixEncoding.appendixEndpointPolynomialBound]
  change R * (2 * U + 2) ^ (d + 1) ≤ X ^ appendixEndpointDegree d
  calc
    R * (2 * U + 2) ^ (d + 1) ≤
        X * (X ^ (d + 6)) ^ (d + 1) := by gcongr
    _ = X ^ appendixEndpointDegree d := by
      simp only [appendixEndpointDegree, pow_mul]
      rw [pow_add]
      ring

/-- Translation-invariant endpoint bound directly for an encoded box set. -/
theorem appendixEncodedEndpoint_le_coarseAppendixParameter_pow
    {d D s : ℕ} {B : IntegerBox d} {A : Finset (LatticePoint d)}
    (hAB : A ⊆ B.carrier) :
    AppendixEncoding.appendixEncodedEndpoint D s B A ≤
      coarseAppendixParameter D s B.carrier.card ^ appendixEndpointDegree d :=
  (AppendixEncoding.appendixEncodedEndpoint_le_polynomialBound hAB).trans
    (appendixEndpointPolynomialBound_le_coarseAppendixParameter_pow
      D s d B.carrier.card)

/-- Real-power bound for the coarse parameter under the two source size
hypotheses.  The factor in front is fixed once the integer theorem's
constants have been chosen. -/
theorem coarseAppendixParameter_cast_le
    (D scaleNum s R card : ℕ) (beta : ℝ)
    (hcard : 1 ≤ card) (hbeta : 1 ≤ beta)
    (hs : s ≤ scaleNum * card)
    (hR : (R : ℝ) ≤ Real.rpow (card : ℝ) beta) :
    (coarseAppendixParameter D s R : ℝ) ≤
      (8 : ℝ) * (D + 1) * (scaleNum + 1) *
        Real.rpow (card : ℝ) (2 * beta) := by
  have hcardReal : (1 : ℝ) ≤ (card : ℝ) := by exact_mod_cast hcard
  have hcardPow : (card : ℝ) ≤ Real.rpow (card : ℝ) beta := by
    exact Real.self_le_rpow_of_one_le hcardReal hbeta
  have honePow : (1 : ℝ) ≤ Real.rpow (card : ℝ) beta :=
    hcardReal.trans hcardPow
  have hsReal : (s : ℝ) ≤ (scaleNum : ℝ) * (card : ℝ) := by
    exact_mod_cast hs
  have hsOne : (s + 1 : ℕ) ≤ scaleNum * card + card := by
    omega
  have hsOneReal : ((s + 1 : ℕ) : ℝ) ≤
      (scaleNum + 1 : ℕ) * Real.rpow (card : ℝ) beta := by
    calc
      ((s + 1 : ℕ) : ℝ) ≤ ((scaleNum * card + card : ℕ) : ℝ) := by
        exact_mod_cast hsOne
      _ = (scaleNum + 1 : ℕ) * (card : ℝ) := by
        push_cast
        ring
      _ ≤ (scaleNum + 1 : ℕ) * Real.rpow (card : ℝ) beta := by
        gcongr
  have hsOneReal' : (s : ℝ) + 1 ≤
      ((scaleNum : ℝ) + 1) * Real.rpow (card : ℝ) beta := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsOneReal
  have hROne : ((R + 1 : ℕ) : ℝ) ≤
      2 * Real.rpow (card : ℝ) beta := by
    push_cast
    linarith
  have hROne' : (R : ℝ) + 1 ≤
      2 * Real.rpow (card : ℝ) beta := by
    simpa only [Nat.cast_add, Nat.cast_one] using hROne
  simp only [coarseAppendixParameter]
  push_cast
  calc
    4 * ((D : ℝ) + 1) * ((s : ℝ) + 1) * ((R : ℝ) + 1) ≤
        4 * ((D : ℝ) + 1) *
          ((scaleNum + 1 : ℕ) * Real.rpow (card : ℝ) beta) *
            (2 * Real.rpow (card : ℝ) beta) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Nat.cast_add, Nat.cast_one] using hsOneReal
        · positivity
      · simpa only [Nat.cast_add, Nat.cast_one] using hROne
      · positivity
      · positivity
    _ = (8 : ℝ) * (D + 1) * (scaleNum + 1) *
        Real.rpow (card : ℝ) (2 * beta) := by
      push_cast
      change 4 * ((D : ℝ) + 1) *
          (((scaleNum : ℝ) + 1) * ((card : ℝ) ^ beta)) *
            (2 * ((card : ℝ) ^ beta)) =
        8 * ((D : ℝ) + 1) * ((scaleNum : ℝ) + 1) *
          ((card : ℝ) ^ (2 * beta))
      rw [show 2 * beta = beta + beta by ring,
        Real.rpow_add (show (0 : ℝ) < card by exact_mod_cast hcard)]
      ring

/-- Exponent used for the one-dimensional theorem after encoding a
`d`-dimensional box. -/
def appendixInputExponent (d : ℕ) (beta : ℝ) : ℝ :=
  2 * beta * (appendixEndpointDegree d : ℝ) + 1

theorem one_lt_appendixInputExponent {d : ℕ} {beta : ℝ}
    (hbeta : 0 < beta) : 1 < appendixInputExponent d beta := by
  have hdegree : 0 < appendixEndpointDegree d := by
    simp [appendixEndpointDegree]
  have hdegreeReal : (0 : ℝ) < appendixEndpointDegree d := by
    exact_mod_cast hdegree
  simp only [appendixInputExponent]
  nlinarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hbeta)
    hdegreeReal]

/-- Uniform outer numeric choice for the Appendix encoding.  Once the
integer theorem's fixed constants are known, one threshold absorbs their
coefficient; above it the encoded endpoint is bounded by the fixed exponent
`appendixInputExponent d beta`. -/
theorem exists_cardThreshold_appendixEncodedEndpoint_le
    (d D scaleNum : ℕ) (beta : ℝ) (hbeta : 1 < beta) :
    ∃ cutoff : ℕ, 1 ≤ cutoff ∧
      ∀ (B : IntegerBox d) (A : Finset (LatticePoint d)) (s : ℕ),
        cutoff ≤ A.card →
        A ⊆ B.carrier →
        (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) beta →
        s ≤ scaleNum * A.card →
        (AppendixEncoding.appendixEncodedEndpoint D s B A : ℝ) ≤
          Real.rpow (A.card : ℝ) (appendixInputExponent d beta) := by
  let degree := appendixEndpointDegree d
  let C : ℝ := 8 * (D + 1) * (scaleNum + 1)
  have heventual := tendsto_natCast_atTop_atTop.eventually_ge_atTop (C ^ degree)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventual
  refine ⟨max 1 threshold, le_max_left _ _, ?_⟩
  intro B A s hcard hAB hbox hs
  let card := A.card
  let R := B.carrier.card
  let X := coarseAppendixParameter D s R
  have hcardOne : 1 ≤ card := (le_max_left 1 threshold).trans hcard
  have hthresholdCard : threshold ≤ card :=
    (le_max_right 1 threshold).trans hcard
  have hC : C ^ degree ≤ (card : ℝ) := hthreshold card hthresholdCard
  have hcardPos : (0 : ℝ) < card := by exact_mod_cast hcardOne
  have hX : (X : ℝ) ≤ C * Real.rpow (card : ℝ) (2 * beta) := by
    simpa only [X, C, R, card] using
      coarseAppendixParameter_cast_le D scaleNum s R card beta
        hcardOne hbeta.le hs hbox
  have hendpointNat :
      AppendixEncoding.appendixEncodedEndpoint D s B A ≤ X ^ degree := by
    simpa only [X, R, degree] using
      appendixEncodedEndpoint_le_coarseAppendixParameter_pow hAB
  have hendpoint :
      (AppendixEncoding.appendixEncodedEndpoint D s B A : ℝ) ≤
        (X : ℝ) ^ degree := by
    exact_mod_cast hendpointNat
  have hpower : (X : ℝ) ^ degree ≤
      (C * Real.rpow (card : ℝ) (2 * beta)) ^ degree := by
    exact pow_le_pow_left₀ (by positivity) hX degree
  have hrpowPower :
      (Real.rpow (card : ℝ) (2 * beta)) ^ degree =
        Real.rpow (card : ℝ) (2 * beta * (degree : ℝ)) := by
    change (((card : ℝ) ^ (2 * beta)) ^ degree) =
      (card : ℝ) ^ (2 * beta * (degree : ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul hcardPos.le]
  calc
    (AppendixEncoding.appendixEncodedEndpoint D s B A : ℝ) ≤
        (X : ℝ) ^ degree := hendpoint
    _ ≤ (C * Real.rpow (card : ℝ) (2 * beta)) ^ degree := hpower
    _ = C ^ degree *
        Real.rpow (card : ℝ) (2 * beta * (degree : ℝ)) := by
      rw [mul_pow, hrpowPower]
    _ ≤ (card : ℝ) *
        Real.rpow (card : ℝ) (2 * beta * (degree : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hC
        (Real.rpow_nonneg hcardPos.le _)
    _ = Real.rpow (card : ℝ) (appendixInputExponent d beta) := by
      change (card : ℝ) * (card : ℝ) ^ (2 * beta * (degree : ℝ)) =
        (card : ℝ) ^ (2 * beta * (appendixEndpointDegree d : ℝ) + 1)
      rw [show degree = appendixEndpointDegree d by rfl,
        Real.rpow_add hcardPos, Real.rpow_one]
      ring

/-- Exact remaining geometric existence boundary in the Appendix reduction.
It is stated separately so the complete arithmetic and witness composition
can be checked before the Lemma 2.27 construction is plugged in. -/
def BoxProjectedProperizationStatement : Prop :=
  ∀ D : ℕ, ∃ factor : ℕ, 0 < factor ∧
    ∀ {d s k loss scaleNum scaleDen : ℕ}
      (B : IntegerBox d) (A : Finset (LatticePoint d))
      (W : FixedScaleWitness (AppendixEncoding.homogenizedBoxSet B A)
        s D k loss scaleNum scaleDen),
      factor ≤ k →
      Nonempty (ProjectedProperization.Data
        (factor := factor) (AppendixEncoding.boxDehomogenizeHom B)
        W.enhanced)

/-- Complete source-correct Appendix composition, conditional only on the
genuine Lemma 2.27 properization existence theorem.  No H-approximation,
no-carry, small-input, or numeric premise is exposed. -/
theorem nonemptyHigherDimensionalCorollary5_of_nonemptyIntegerTheorem15_of_projectedProperization
    (hInteger : NonemptyIntegerTheorem15)
    (hProperization : BoxProjectedProperizationStatement) :
    NonemptyHigherDimensionalCorollary5 := by
  intro d beta eta hbeta heta heta1
  let betaInteger := appendixInputExponent d beta
  have hbetaInteger : 1 < betaInteger := by
    exact one_lt_appendixInputExponent (d := d) (zero_lt_one.trans hbeta)
  obtain ⟨scaleNum, scaleDen, D, lossConstant,
      hnum, hden, hlossConstant, hIntegerOut⟩ :=
    hInteger betaInteger eta hbetaInteger heta heta1
  obtain ⟨factor, hfactor, hProperize⟩ := hProperization D
  have hnumDen : scaleNum ≤ scaleDen :=
    scaleNum_le_scaleDen_of_integerConclusion hIntegerOut
  have hnumTargetDen : scaleNum ≤ scaleDen * factor := by
    calc
      scaleNum ≤ scaleDen := hnumDen
      _ = scaleDen * 1 := by simp
      _ ≤ scaleDen * factor := Nat.mul_le_mul_left scaleDen hfactor
  obtain ⟨scaleCutoff, hscaleCutoff⟩ :=
    exists_cardThreshold_factor_le_dilation eta scaleNum scaleDen factor
      heta hnum hden
  obtain ⟨endpointCutoff, hendpointCutoffOne, hendpointCutoff⟩ :=
    exists_cardThreshold_appendixEncodedEndpoint_le d D scaleNum beta hbeta
  let cutoff := max 2 (max scaleCutoff endpointCutoff)
  refine ⟨scaleNum, scaleDen * factor, D, lossConstant + cutoff,
    hnum, Nat.mul_pos hden hfactor, Nat.add_pos_left hlossConstant cutoff, ?_⟩
  intro B A s hA hAB hbox hlower hupper
  have hs : 0 < s := scale_pos_of_nonempty hA heta.le hlower
  have hcardOne : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hA.card_pos
  have hlogNonneg : 0 ≤ Real.logb 2 (A.card : ℝ) := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hcardOne)
      (Real.log_pos (by norm_num)).le
  have hscaleLogNonneg : 0 ≤ (s : ℝ) * Real.logb 2 (A.card : ℝ) :=
    mul_nonneg (by positivity) hlogNonneg
  by_cases hlarge : cutoff ≤ A.card
  · have hcardTwo : 2 ≤ A.card :=
      (le_max_left 2 (max scaleCutoff endpointCutoff)).trans hlarge
    have hscaleCutoffCard : scaleCutoff ≤ A.card :=
      (le_max_of_le_right (le_max_left scaleCutoff endpointCutoff)).trans hlarge
    have hendpointCutoffCard : endpointCutoff ≤ A.card :=
      (le_max_of_le_right (le_max_right scaleCutoff endpointCutoff)).trans hlarge
    have hsUpper : s ≤ scaleNum * A.card :=
      scale_le_scaleNum_mul_card scaleNum (scaleDen * factor) s A.card
        (Nat.mul_pos hden hfactor) hcardTwo hupper
    have hendpoint :
        (AppendixEncoding.appendixEncodedEndpoint D s B A : ℝ) ≤
          Real.rpow (A.card : ℝ) betaInteger := by
      simpa only [betaInteger] using
        hendpointCutoff B A s hendpointCutoffCard hAB hbox hsUpper
    let encoded := AppendixEncoding.appendixEncodedIntegers D s B A
    have hencodedNonempty : encoded.Nonempty := by
      simpa only [encoded, AppendixEncoding.appendixEncodedIntegers] using
        Finset.image_nonempty.mpr hA
    have hencodedCard : encoded.card = A.card := by
      simpa only [encoded] using
        AppendixEncoding.card_appendixEncodedIntegers B A hs
    have hsourceUpper : (scaleDen : ℝ) * (s : ℝ) *
        Real.logb 2 (A.card : ℝ) ≤ (scaleNum : ℝ) * (A.card : ℝ) := by
      calc
        (scaleDen : ℝ) * (s : ℝ) * Real.logb 2 (A.card : ℝ) ≤
            ((scaleDen * factor : ℕ) : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) := by
          push_cast
          gcongr
          exact_mod_cast (show scaleDen ≤ scaleDen * factor by
            calc
              scaleDen = scaleDen * 1 := by simp
              _ ≤ scaleDen * factor := Nat.mul_le_mul_left _ hfactor)
        _ ≤ (scaleNum : ℝ) * (A.card : ℝ) := hupper
    obtain ⟨k, loss, ⟨WInteger⟩, hloss⟩ :=
      hIntegerOut (AppendixEncoding.appendixEncodedEndpoint D s B A)
        encoded s hencodedNonempty
        (by simpa only [encoded] using
          AppendixEncoding.appendixEncodedIntegers_subset_Icc hAB)
        (by simpa only [hencodedCard] using hendpoint)
        (by simpa only [hencodedCard] using hlower)
        (by simpa only [hencodedCard] using hsourceUpper)
    let WHomogenized :=
      AppendixEncoding.liftFixedScaleWitness_to_homogenizedBoxSet B A WInteger
    have hfactorK : factor ≤ k :=
      hscaleCutoff A.card s k hscaleCutoffCard hlower
        WInteger.scale_lower
    obtain ⟨Z⟩ := hProperize B A WHomogenized hfactorK
    let WFinal : FixedScaleWitness A s D Z.scale loss scaleNum
        (scaleDen * factor) :=
      ProjectedProperization.Data.transportFixed_boxDehomogenize
        B A WHomogenized hfactor Z
    refine ⟨Z.scale, loss, ⟨WFinal⟩, ?_⟩
    have hlossA : (loss : ℝ) ≤
        (lossConstant : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 := by
      simpa only [hencodedCard] using hloss
    calc
      (loss : ℝ) ≤ (lossConstant : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 := hlossA
      _ ≤ ((lossConstant + cutoff : ℕ) : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 := by
        have hcoeff : (lossConstant : ℝ) ≤
            ((lossConstant + cutoff : ℕ) : ℝ) := by
          exact_mod_cast (Nat.le_add_right lossConstant cutoff)
        calc
          (lossConstant : ℝ) * (s : ℝ) *
                Real.logb 2 (A.card : ℝ) + 1 =
              (lossConstant : ℝ) *
                ((s : ℝ) * Real.logb 2 (A.card : ℝ)) + 1 := by ring
          _ ≤ ((lossConstant + cutoff : ℕ) : ℝ) *
                ((s : ℝ) * Real.logb 2 (A.card : ℝ)) + 1 :=
            by
              have hmul := mul_le_mul_of_nonneg_right hcoeff hscaleLogNonneg
              linarith
          _ = ((lossConstant + cutoff : ℕ) : ℝ) * (s : ℝ) *
                Real.logb 2 (A.card : ℝ) + 1 := by ring
  · have hcardCutoff : A.card ≤ cutoff := by omega
    obtain ⟨k, loss, hW, hloss⟩ :=
      exists_fixedScaleWitness_of_card_le A s D scaleNum
        (scaleDen * factor) cutoff hA hs hnum (Nat.mul_pos hden hfactor)
          hnumTargetDen hcardCutoff
    refine ⟨k, loss, hW, hloss.trans ?_⟩
    have hcoeff : (cutoff : ℝ) ≤
        ((lossConstant + cutoff : ℕ) : ℝ) := by
      exact_mod_cast (show cutoff ≤ lossConstant + cutoff by omega)
    calc
      (cutoff : ℝ) * (s : ℝ) * Real.logb 2 (A.card : ℝ) + 1 =
          (cutoff : ℝ) *
            ((s : ℝ) * Real.logb 2 (A.card : ℝ)) + 1 := by ring
      _ ≤ ((lossConstant + cutoff : ℕ) : ℝ) *
            ((s : ℝ) * Real.logb 2 (A.card : ℝ)) + 1 := by
        have hmul := mul_le_mul_of_nonneg_right hcoeff hscaleLogNonneg
        linarith
      _ = ((lossConstant + cutoff : ℕ) : ℝ) * (s : ℝ) *
            Real.logb 2 (A.card : ℝ) + 1 := by ring

end


end Erdos186.CFP.HigherDimensionalCorollary

#print axioms
  Erdos186.CFP.HigherDimensionalCorollary.scaleNum_le_scaleDen_of_integerConclusion
#print axioms
  Erdos186.CFP.HigherDimensionalCorollary.nonemptyHigherDimensionalCorollary5_of_nonemptyIntegerTheorem15_of_projectedProperization

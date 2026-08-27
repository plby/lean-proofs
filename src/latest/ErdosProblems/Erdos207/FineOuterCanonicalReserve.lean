/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterPowerSandwich

/-!
# Canonical reserve for the first power-vortex transition

Stopping with roughly `N²/t` eligible pairs leaves quadratic centre of
order `N/t²`, exactly the next scale of a power vortex whose free exponent
drops by two.  The elementary division estimates below also give the clock
comparison factor `t` required by the inverse-power corridor.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def fineOuterReserve (outside t : ℕ) : ℕ := outside ^ 2 / t

def coupledOuterExponent : ℕ := 67

def fineOuterBuffer (outside t : ℕ) : ℝ :=
  fineOuterInitialOffset outside t / 2

lemma coupledOuterExponent_growth : 200 ≤ 3 * coupledOuterExponent := by
  norm_num [coupledOuterExponent]

lemma fineOuterReserve_pos
    {outside t : ℕ} (ht : 0 < t) (htN : t ≤ outside ^ 2) :
    0 < fineOuterReserve outside t := by
  unfold fineOuterReserve
  exact Nat.div_pos htN ht

/-- The loss from flooring `N²/t` costs only a factor two once the quotient
is nonzero. -/
lemma outside_sq_le_two_mul_fineOuterReserve
    {outside t : ℕ} (ht : 0 < t) (hreserve : 0 < fineOuterReserve outside t) :
    outside ^ 2 ≤ 2 * t * fineOuterReserve outside t := by
  let r := fineOuterReserve outside t
  have hlt : outside ^ 2 < (r + 1) * t := by
    apply (Nat.div_lt_iff_lt_mul ht).1
    simpa only [r, fineOuterReserve] using Nat.lt_succ_self (outside ^ 2 / t)
  have hr : r + 1 ≤ 2 * r := by omega
  calc
    outside ^ 2 ≤ (r + 1) * t := Nat.le_of_lt hlt
    _ ≤ (2 * r) * t := Nat.mul_le_mul_right t hr
    _ = 2 * t * fineOuterReserve outside t := by
      simp only [r]
      ring

/-- The fine initial pair lower bound places the canonical reserve below the
initial eligible-pair count. -/
lemma fineOuterReserve_le_initialEligible
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t : ℕ)
    (ht : 3 ≤ t)
    (hsmall : ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100)
    (hpairLower : (outside : ℝ) ^ 2 *
        (1 - 3 * (fineOuterCorridorError t : ℝ≥0)) ≤
      2 * (outerSharpEligiblePairs H X 0 : ℕ)) :
    fineOuterReserve outside t ≤ outerSharpEligiblePairs H X 0 := by
  have htpos : 0 < t := by omega
  have hmul : t * fineOuterReserve outside t ≤ outside ^ 2 := by
    unfold fineOuterReserve
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (outside ^ 2) t
  have hthree : 3 * fineOuterReserve outside t ≤ outside ^ 2 :=
    (Nat.mul_le_mul_right (fineOuterReserve outside t) ht).trans (by
      simpa only [Nat.mul_comm] using hmul)
  have hthreeReal : (3 : ℝ) * fineOuterReserve outside t ≤ outside ^ 2 := by
    exact_mod_cast hthree
  have hepsilon : (0 : ℝ) ≤ fineOuterCorridorError t := by positivity
  have hreserveReal : (fineOuterReserve outside t : ℝ) ≤
      outerSharpEligiblePairs H X 0 := by
    nlinarith
  exact_mod_cast hreserveReal

/-- Every clock value through the canonical stopping time is within factor
`t` of the initial eligible-pair count. -/
lemma initialEligible_le_t_mul_current
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t i : ℕ)
    (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hi : i ≤ outerSharpStopFuel H X (fineOuterReserve outside t))
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2) :
    (outerSharpEligiblePairs H X 0 : ℝ) ≤
      t * outerSharpEligiblePairs H X i := by
  have hsquare := outside_sq_le_two_mul_fineOuterReserve ht hreservePos
  have hcurrent := outerSharpEligiblePairs_stopFuel_floor H X
    hreserveInitial hi
  have hpairUpperNat : 2 * outerSharpEligiblePairs H X 0 ≤ outside ^ 2 := by
    exact_mod_cast hpairUpper
  have hchain : 2 * outerSharpEligiblePairs H X 0 ≤
      2 * t * outerSharpEligiblePairs H X i := by
    calc
      2 * outerSharpEligiblePairs H X 0 ≤ outside ^ 2 := hpairUpperNat
      _ ≤ 2 * t * fineOuterReserve outside t := hsquare
      _ ≤ 2 * t * outerSharpEligiblePairs H X i := by gcongr
  have hcancel : 2 * outerSharpEligiblePairs H X 0 ≤
      2 * (t * outerSharpEligiblePairs H X i) := by
    simpa only [mul_assoc] using hchain
  have hresult := Nat.le_of_mul_le_mul_left hcancel (by omega : 0 < 2)
  exact_mod_cast hresult

/-- Pointwise clock facts used by the power-window sandwich. -/
structure FineOuterCanonicalClockFacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t i : ℕ) : Prop where
  current_pos : 0 < outerSharpEligiblePairs H X i
  current_le_initial : outerSharpEligiblePairs H X i ≤
    outerSharpEligiblePairs H X 0
  compare : (outerSharpEligiblePairs H X 0 : ℝ) ≤
    t * outerSharpEligiblePairs H X i
  lower_clock : (outside : ℝ) ^ 2 ≤
    4 * t * outerSharpEligiblePairs H X i
  upper_clock : (outerSharpEligiblePairs H X i : ℝ) ≤
    (outside : ℝ) ^ 2

theorem fineOuterCanonicalClockFacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t i : ℕ)
    (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hi : i ≤ outerSharpStopFuel H X (fineOuterReserve outside t))
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2) :
    FineOuterCanonicalClockFacts H X outside t i := by
  have hcurrent := outerSharpEligiblePairs_stopFuel_floor H X
    hreserveInitial hi
  have hcompare := initialEligible_le_t_mul_current H X outside t i ht
    hreservePos hreserveInitial hi hpairUpper
  have hmono : outerSharpEligiblePairs H X i ≤
      outerSharpEligiblePairs H X 0 := by
    unfold outerSharpEligiblePairs
    omega
  have hupperInitial : (outerSharpEligiblePairs H X 0 : ℝ) ≤
      (outside : ℝ) ^ 2 := by nlinarith [hpairUpper]
  have hsquare := outside_sq_le_two_mul_fineOuterReserve ht hreservePos
  have hlowerNat : outside ^ 2 ≤
      4 * t * outerSharpEligiblePairs H X i := by
    calc
      outside ^ 2 ≤ 2 * t * fineOuterReserve outside t := hsquare
      _ ≤ 2 * t * outerSharpEligiblePairs H X i := by gcongr
      _ ≤ 4 * t * outerSharpEligiblePairs H X i := by gcongr <;> omega
  refine ⟨hreservePos.trans_le hcurrent, hmono, hcompare, ?_, ?_⟩
  · exact_mod_cast hlowerNat
  · exact_mod_cast hmono.trans (by exact_mod_cast hupperInitial)

/-- A positive reserve of at least four leaves enough room for the next
three-pair deletion at every strict preterminal step. -/
lemma canonicalStopFuel_clock
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) {reserve : ℕ}
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (hfour : 4 ≤ reserve) :
    3 * (outerSharpStopFuel H X reserve + 1) <
      outerSharpEligiblePairs H X 0 := by
  have hstep := three_mul_outerSharpStopFuel_le H X reserve
  omega

end

end Erdos207

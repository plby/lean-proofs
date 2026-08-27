/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterSharpStopFuel
import ErdosProblems.Erdos207.FineInitialPowerVortexPackage

/-!
# Fine perturbed barriers for the long outer phase

The quadratic pair-degree trajectory is normalized by the number of
vertices outside the first protected vortex level.  Its two affine pair
budgets use the exact eligible-pair clock and slopes on opposite sides of
three.  This file records the exact closed forms; all later estimates can
therefore be carried out without unfolding `affineSurvivalEnvelope`.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- The square-root scale left between the fine initial error `t⁻²⁰⁰` and
the macroscopic pair-degree trajectory. -/
def fineOuterCorridorExponent : ℕ := 100

def fineOuterCorridorError (t : ℕ) : ℝ≥0 :=
  (t : ℝ≥0)⁻¹ ^ fineOuterCorridorExponent

lemma fineOuterCorridorError_sq (t : ℕ) :
    fineOuterCorridorError t ^ 2 = fineInitialError t := by
  unfold fineOuterCorridorError fineOuterCorridorExponent fineInitialError
    fineInitialExponent
  rw [← pow_mul]

lemma fineOuterCorridorError_mul_pow
    {t : ℕ} (ht : 0 < t) :
    fineOuterCorridorError t * (t : ℝ≥0) ^ fineOuterCorridorExponent = 1 := by
  unfold fineOuterCorridorError
  rw [← mul_pow, inv_mul_cancel₀]
  · exact one_pow _
  · exact_mod_cast ht.ne'

lemma fineOuterCorridorError_le_one_hundredth
    {t : ℕ} (ht : 0 < t)
    (hlarge : 100 ≤ t ^ fineOuterCorridorExponent) :
    ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100 := by
  have hmul := fineOuterCorridorError_mul_pow ht
  have hlargeNN : (100 : ℝ≥0) ≤
      (t : ℝ≥0) ^ fineOuterCorridorExponent := by exact_mod_cast hlarge
  have hscaled := mul_le_mul_of_nonneg_right hlargeNN
    (show (0 : ℝ≥0) ≤ fineOuterCorridorError t by exact bot_le)
  have hscaledNN : (100 : ℝ≥0) * fineOuterCorridorError t ≤ 1 := by
    exact hscaled.trans_eq (by simpa [mul_comm] using hmul)
  have hscaledReal : (100 : ℝ) * fineOuterCorridorError t ≤ 1 := by
    exact_mod_cast hscaledNN
  norm_num at hscaledReal ⊢
  linarith

/-- A fixed rational multiple of the *initial* error, equivalently the square
of the corridor error.  The quadratic scale is essential: over the
`Theta(n^2)` outer clock, a slope perturbation on the larger corridor scale
would accumulate beyond every reserve compatible with the initial pair
trajectory. -/
def fineOuterSlopeError (t : ℕ) : ℝ≥0 :=
  65536 * fineOuterCorridorError t ^ 2

lemma fineOuterSlopeError_le_three
    {t : ℕ} (ht : 0 < t)
    (hlarge : 65536 ≤ 3 * t ^ fineOuterCorridorExponent) :
    fineOuterSlopeError t ≤ 3 := by
  have hmul := fineOuterCorridorError_mul_pow ht
  have hepsilon : fineOuterCorridorError t ≤ 1 := by
    unfold fineOuterCorridorError
    exact pow_le_one₀ (by positivity)
      (inv_le_one_of_one_le₀ (by exact_mod_cast ht))
  have hlargeNN : (65536 : ℝ≥0) ≤
      3 * (t : ℝ≥0) ^ fineOuterCorridorExponent := by exact_mod_cast hlarge
  unfold fineOuterSlopeError
  calc
    65536 * fineOuterCorridorError t ^ 2 ≤
        65536 * fineOuterCorridorError t := by
      gcongr
      simpa only [pow_two, mul_one] using
        mul_le_mul_of_nonneg_left hepsilon
          (show (0 : ℝ≥0) ≤ fineOuterCorridorError t by exact bot_le)
    _ ≤
        (3 * (t : ℝ≥0) ^ fineOuterCorridorExponent) *
          fineOuterCorridorError t := by gcongr
    _ = 3 := by rw [mul_assoc, mul_comm _ (fineOuterCorridorError t), hmul,
      mul_one]

def fineOuterUpperCoefficient (t : ℕ) : ℝ≥0 :=
  4 + 64 * fineOuterCorridorError t

def fineOuterLowerCoefficient (t : ℕ) : ℝ≥0 :=
  4 - 64 * fineOuterCorridorError t

def fineOuterUpperSlope (t : ℕ) : ℝ≥0 :=
  perturbedOuterUpperSlope (fineOuterSlopeError t)

def fineOuterLowerSlope (t : ℕ) : ℝ≥0 :=
  perturbedOuterLowerSlope (fineOuterSlopeError t)

lemma fineOuterUpperSlope_eq (t : ℕ) :
    fineOuterUpperSlope t = 3 - fineOuterSlopeError t := rfl

lemma fineOuterLowerSlope_eq (t : ℕ) :
    fineOuterLowerSlope t = 3 + fineOuterSlopeError t := rfl

/-- Exact upper barrier in terms of the live eligible-pair count. -/
lemma fineOuterUpperBarrier_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N : ℝ≥0) (t i : ℕ)
    (hslope : fineOuterSlopeError t ≤ 3)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    quadraticPairBarrier N (fineOuterUpperCoefficient t)
        (perturbedOuterUpperR0 H X) (fineOuterUpperSlope t) i =
      ((fineOuterUpperCoefficient t *
          ((outerSharpEligiblePairs H X i : ℕ) +
            (i : ℝ≥0) * fineOuterSlopeError t) ^ 2 * N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  unfold quadraticPairBarrier fineOuterUpperSlope
  rw [perturbedOuterUpperEnvelope_eq H X (fineOuterSlopeError t) i
    hslope hi]

/-- Exact lower barrier in terms of the live eligible-pair count. -/
lemma fineOuterLowerBarrier_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N : ℝ≥0) (t i : ℕ)
    (hpos : (i : ℝ≥0) * fineOuterLowerSlope t ≤
      perturbedOuterLowerR0 H X) :
    quadraticPairBarrier N (fineOuterLowerCoefficient t)
        (perturbedOuterLowerR0 H X) (fineOuterLowerSlope t) i =
      ((fineOuterLowerCoefficient t *
          ((outerSharpEligiblePairs H X i : ℕ) -
            (i : ℝ≥0) * fineOuterSlopeError t) ^ 2 * N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  unfold quadraticPairBarrier fineOuterLowerSlope
  rw [perturbedOuterLowerEnvelope_eq H X (fineOuterSlopeError t) i hpos]

/-- Before the stopping clock, the perturbed upper affine envelope is the
exact live budget plus its accumulated slope error. -/
lemma fineOuterUpperEnvelope_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (t i : ℕ)
    (hslope : fineOuterSlopeError t ≤ 3)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    affineSurvivalEnvelope (perturbedOuterUpperR0 H X)
        (fineOuterUpperSlope t) i =
      (outerSharpEligiblePairs H X i : ℕ) +
        (i : ℝ≥0) * fineOuterSlopeError t := by
  exact perturbedOuterUpperEnvelope_eq H X (fineOuterSlopeError t) i
    hslope hi

/-- The analogous exact formula for the lower affine envelope. -/
lemma fineOuterLowerEnvelope_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (t i : ℕ)
    (hpos : (i : ℝ≥0) * fineOuterLowerSlope t ≤
      perturbedOuterLowerR0 H X) :
    affineSurvivalEnvelope (perturbedOuterLowerR0 H X)
        (fineOuterLowerSlope t) i =
      (outerSharpEligiblePairs H X i : ℕ) -
        (i : ℝ≥0) * fineOuterSlopeError t := by
  exact perturbedOuterLowerEnvelope_eq H X (fineOuterSlopeError t) i hpos

/-- At the canonical stop clock, both affine envelopes remain strictly
positive provided the reserved pair budget dominates the accumulated slope
error. -/
lemma fineOuter_stop_barriers_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (t reserve : ℕ)
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (herror : (outerSharpStopFuel H X reserve : ℝ≥0) *
        fineOuterSlopeError t < reserve) :
    ((outerSharpStopFuel H X reserve : ℝ≥0) * fineOuterUpperSlope t <
        perturbedOuterUpperR0 H X) ∧
      ((outerSharpStopFuel H X reserve : ℝ≥0) * fineOuterLowerSlope t <
        perturbedOuterLowerR0 H X) := by
  let fuel := outerSharpStopFuel H X reserve
  let E0 := outerSharpEligiblePairs H X 0
  have hclockNat : 3 * fuel ≤ E0 - reserve := by
    simpa only [fuel, E0] using three_mul_outerSharpStopFuel_le H X reserve
  have hclock : (3 : ℝ≥0) * fuel ≤ (E0 - reserve : ℕ) := by
    exact_mod_cast hclockNat
  have hresNN : (reserve : ℝ≥0) ≤ E0 := by exact_mod_cast hreserve
  have hsplit : ((E0 - reserve : ℕ) : ℝ≥0) + reserve = E0 := by
    exact_mod_cast Nat.sub_add_cancel hreserve
  have hreservePos : (0 : ℝ≥0) < reserve := by
    exact (mul_nonneg (by positivity) (by positivity)).trans_lt herror
  constructor
  · have hupperSlope : fineOuterUpperSlope t ≤ 3 := by
      unfold fineOuterUpperSlope perturbedOuterUpperSlope
      exact tsub_le_self
    have hle : (fuel : ℝ≥0) * fineOuterUpperSlope t ≤
        (E0 - reserve : ℕ) := by
      calc
        (fuel : ℝ≥0) * fineOuterUpperSlope t ≤ fuel * 3 := by gcongr
        _ = 3 * fuel := by ring
        _ ≤ (E0 - reserve : ℕ) := hclock
    have hlt : ((E0 - reserve : ℕ) : ℝ≥0) < E0 := by
      calc
        ((E0 - reserve : ℕ) : ℝ≥0) <
            (E0 - reserve : ℕ) + reserve := lt_add_of_pos_right _ hreservePos
        _ = E0 := hsplit
    simpa only [fuel, E0, perturbedOuterUpperR0] using hle.trans_lt hlt
  · have hsum : (fuel : ℝ≥0) * fineOuterLowerSlope t =
        3 * fuel + fuel * fineOuterSlopeError t := by
      unfold fineOuterLowerSlope perturbedOuterLowerSlope
      ring
    rw [hsum]
    have hlt : (3 : ℝ≥0) * fuel + fuel * fineOuterSlopeError t <
        ((E0 - reserve : ℕ) : ℝ≥0) + reserve :=
      add_lt_add_of_le_of_lt hclock (by simpa only [fuel] using herror)
    simpa only [fuel, E0, perturbedOuterLowerR0, hsplit] using hlt

/-- Uniform relative control of both perturbed affine envelopes up to the
canonical stop.  This is the quantitative form used in all later polynomial
rate comparisons. -/
lemma fineOuter_envelopes_relative_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (t reserve : ℕ) (alpha : ℝ≥0)
    (hslope : fineOuterSlopeError t ≤ 3)
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (halpha : alpha ≤ 1)
    (haccum : (outerSharpStopFuel H X reserve : ℝ≥0) *
      fineOuterSlopeError t ≤ alpha * reserve) :
    ∀ i, i ≤ outerSharpStopFuel H X reserve →
      affineSurvivalEnvelope (perturbedOuterUpperR0 H X)
          (fineOuterUpperSlope t) i ≤
          (1 + alpha) * (outerSharpEligiblePairs H X i : ℕ) ∧
        (1 - alpha) * (outerSharpEligiblePairs H X i : ℕ) ≤
          affineSurvivalEnvelope (perturbedOuterLowerR0 H X)
            (fineOuterLowerSlope t) i := by
  intro i hi
  let fuel := outerSharpStopFuel H X reserve
  let Ri : ℝ≥0 := outerSharpEligiblePairs H X i
  have hreserveRiNat : reserve ≤ outerSharpEligiblePairs H X i :=
    outerSharpEligiblePairs_stopFuel_floor H X hreserve hi
  have hreserveRi : (reserve : ℝ≥0) ≤ Ri := by
    have hcast : (reserve : ℝ≥0) ≤
        (outerSharpEligiblePairs H X i : ℕ) := by exact_mod_cast hreserveRiNat
    simpa only [Ri] using hcast
  have hiNN : (i : ℝ≥0) ≤ fuel := by exact_mod_cast hi
  have hiterm : (i : ℝ≥0) * fineOuterSlopeError t ≤ alpha * Ri := by
    calc
      (i : ℝ≥0) * fineOuterSlopeError t ≤
          (fuel : ℝ≥0) * fineOuterSlopeError t := by gcongr
      _ ≤ alpha * reserve := by simpa only [fuel] using haccum
      _ ≤ alpha * Ri := by gcongr
  have hclockFuel : 3 * fuel ≤ outerSharpEligiblePairs H X 0 :=
    (three_mul_outerSharpStopFuel_le H X reserve).trans (Nat.sub_le _ _)
  have hclock : 3 * i ≤ outerSharpEligiblePairs H X 0 := by omega
  have hclockDiffNat : 3 * i ≤
      outerSharpEligiblePairs H X 0 - reserve := by
    exact (Nat.mul_le_mul_left 3 hi).trans
      (three_mul_outerSharpStopFuel_le H X reserve)
  have hclockDiff : (3 : ℝ≥0) * i ≤
      (outerSharpEligiblePairs H X 0 - reserve : ℕ) := by
    exact_mod_cast hclockDiffNat
  have htermReserve : (i : ℝ≥0) * fineOuterSlopeError t ≤ reserve := by
    calc
      (i : ℝ≥0) * fineOuterSlopeError t ≤
          (fuel : ℝ≥0) * fineOuterSlopeError t := by gcongr
      _ ≤ alpha * reserve := by simpa only [fuel] using haccum
      _ ≤ reserve := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right halpha (show (0 : ℝ≥0) ≤ reserve by positivity)
  have hsplit :
      ((outerSharpEligiblePairs H X 0 - reserve : ℕ) : ℝ≥0) + reserve =
        outerSharpEligiblePairs H X 0 := by
    exact_mod_cast Nat.sub_add_cancel hreserve
  have hiLower : (i : ℝ≥0) * fineOuterLowerSlope t ≤
      perturbedOuterLowerR0 H X := by
    rw [fineOuterLowerSlope_eq]
    have hsum : (i : ℝ≥0) * (3 + fineOuterSlopeError t) =
        3 * i + i * fineOuterSlopeError t := by ring
    rw [hsum]
    calc
      (3 : ℝ≥0) * i + i * fineOuterSlopeError t ≤
          (outerSharpEligiblePairs H X 0 - reserve : ℕ) + reserve :=
        add_le_add hclockDiff htermReserve
      _ = outerSharpEligiblePairs H X 0 := hsplit
      _ = perturbedOuterLowerR0 H X := rfl
  rw [fineOuterUpperEnvelope_eq H X t i hslope hclock,
    fineOuterLowerEnvelope_eq H X t i hiLower]
  constructor
  · change Ri + (i : ℝ≥0) * fineOuterSlopeError t ≤ (1 + alpha) * Ri
    calc
      Ri + (i : ℝ≥0) * fineOuterSlopeError t ≤ Ri + alpha * Ri := by gcongr
      _ = (1 + alpha) * Ri := by ring
  · change (1 - alpha) * Ri ≤
      Ri - (i : ℝ≥0) * fineOuterSlopeError t
    have hAlphaRi : alpha * Ri ≤ Ri := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right halpha (by positivity)
    have htermRi : (i : ℝ≥0) * fineOuterSlopeError t ≤ Ri :=
      hiterm.trans hAlphaRi
    apply (le_tsub_iff_right htermRi).2
    calc
      (1 - alpha) * Ri + (i : ℝ≥0) * fineOuterSlopeError t ≤
          (1 - alpha) * Ri + alpha * Ri := by gcongr
      _ = ((1 - alpha) + alpha) * Ri := by ring
      _ = Ri := by rw [tsub_add_cancel_of_le halpha, one_mul]

/-- Squaring the preceding affine-envelope bounds gives uniform relative
bounds for the actual real quadratic barriers. -/
lemma fineOuter_barriers_relative_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N : ℝ≥0)
    (t reserve : ℕ) (alpha : ℝ≥0)
    (hslope : fineOuterSlopeError t ≤ 3)
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (halpha : alpha ≤ 1)
    (haccum : (outerSharpStopFuel H X reserve : ℝ≥0) *
      fineOuterSlopeError t ≤ alpha * reserve) :
    ∀ i, i ≤ outerSharpStopFuel H X reserve →
      quadraticPairBarrier N (fineOuterUpperCoefficient t)
          (perturbedOuterUpperR0 H X) (fineOuterUpperSlope t) i ≤
        ((fineOuterUpperCoefficient t * (1 + alpha) ^ 2 *
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 :
            ℝ≥0) : ℝ) ∧
      ((fineOuterLowerCoefficient t * (1 - alpha) ^ 2 *
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 :
            ℝ≥0) : ℝ) ≤
        quadraticPairBarrier N (fineOuterLowerCoefficient t)
          (perturbedOuterLowerR0 H X) (fineOuterLowerSlope t) i := by
  intro i hi
  have henv := fineOuter_envelopes_relative_bounds H X t reserve alpha
    hslope hreserve halpha haccum i hi
  constructor
  · unfold quadraticPairBarrier
    exact_mod_cast (show fineOuterUpperCoefficient t *
        affineSurvivalEnvelope (perturbedOuterUpperR0 H X)
            (fineOuterUpperSlope t) i ^ 2 * N⁻¹ ^ 3 ≤
        fineOuterUpperCoefficient t * (1 + alpha) ^ 2 *
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 by
      calc
        fineOuterUpperCoefficient t *
              affineSurvivalEnvelope (perturbedOuterUpperR0 H X)
                (fineOuterUpperSlope t) i ^ 2 * N⁻¹ ^ 3 ≤
            fineOuterUpperCoefficient t *
              ((1 + alpha) *
                (outerSharpEligiblePairs H X i : ℕ)) ^ 2 * N⁻¹ ^ 3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left' henv.1 2)
              (by positivity)) (by positivity)
        _ = fineOuterUpperCoefficient t * (1 + alpha) ^ 2 *
            ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 := by
          ring)
  · unfold quadraticPairBarrier
    exact_mod_cast (show fineOuterLowerCoefficient t * (1 - alpha) ^ 2 *
        ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 ≤
        fineOuterLowerCoefficient t *
          affineSurvivalEnvelope (perturbedOuterLowerR0 H X)
            (fineOuterLowerSlope t) i ^ 2 * N⁻¹ ^ 3 by
      calc
        fineOuterLowerCoefficient t * (1 - alpha) ^ 2 *
              ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 =
            fineOuterLowerCoefficient t *
              ((1 - alpha) *
                (outerSharpEligiblePairs H X i : ℕ)) ^ 2 * N⁻¹ ^ 3 := by ring
        _ ≤ fineOuterLowerCoefficient t *
              affineSurvivalEnvelope (perturbedOuterLowerR0 H X)
                (fineOuterLowerSlope t) i ^ 2 * N⁻¹ ^ 3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left' henv.2 2)
              (by positivity)) (by positivity))

/-- The natural rounded schedules differ from the preceding relative
quadratic bounds only by the explicit real buffer and one unit of integer
rounding. -/
lemma fineOuter_rounded_relative_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N : ℝ≥0)
    (t reserve : ℕ) (alpha : ℝ≥0) (buffer : ℝ)
    (hslope : fineOuterSlopeError t ≤ 3)
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (halpha : alpha ≤ 1)
    (haccum : (outerSharpStopFuel H X reserve : ℝ≥0) *
      fineOuterSlopeError t ≤ alpha * reserve)
    (hbuffer : 0 ≤ buffer)
    (hlowerOne : ∀ i, i ≤ outerSharpStopFuel H X reserve →
      1 ≤ quadraticPairBarrier N (fineOuterLowerCoefficient t)
        (perturbedOuterLowerR0 H X) (fineOuterLowerSlope t) i - buffer) :
    ∀ i, i ≤ outerSharpStopFuel H X reserve →
      (roundedQuadraticUpper N (fineOuterUpperCoefficient t)
          (perturbedOuterUpperR0 H X) (fineOuterUpperSlope t) buffer i : ℝ) <
        (fineOuterUpperCoefficient t * (1 + alpha) ^ 2 *
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 :
            ℝ≥0) + buffer + 1 ∧
      ((fineOuterLowerCoefficient t * (1 - alpha) ^ 2 *
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3 :
            ℝ≥0) : ℝ) - buffer - 1 <
        roundedQuadraticLower N (fineOuterLowerCoefficient t)
          (perturbedOuterLowerR0 H X) (fineOuterLowerSlope t) buffer i := by
  intro i hi
  have hb := fineOuter_barriers_relative_bounds H X N t reserve alpha
    hslope hreserve halpha haccum i hi
  constructor
  · have hround := nonnegativeNatCeil_lt_add_one
      (add_nonneg (quadraticPairBarrier_nonneg N
        (fineOuterUpperCoefficient t) (perturbedOuterUpperR0 H X)
        (fineOuterUpperSlope t) i) hbuffer)
    unfold roundedQuadraticUpper
    exact hround.trans_le (by linarith [hb.1])
  · have hround := sub_one_lt_nonnegativeNatFloor (hlowerOne i hi)
    unfold roundedQuadraticLower
    linarith [hb.2]

end

end Erdos207

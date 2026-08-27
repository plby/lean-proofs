/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedPairBandPhase
import ErdosProblems.Erdos207.TimedPairBandTwoCutoffs

/-!
# Explicit linear pair-extension trajectories

The stopped pair-band theorem is stated for arbitrary deterministic targets.
This file supplies the concrete linear targets used for one phase.  The upper
target decreases at the slowest deletion rate forced by the pair floor and
the initial availability cap.  The lower target decreases at the fastest
deletion rate allowed by the pair cutoff and a deterministic availability
floor.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A pair target starting at its exact initial extension count and decreasing
at constant real rate `r`. -/
def linearPairTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (r : ℝ) (P : PairOn V) (i : ℕ) : ℝ :=
  fixedPairAvailableCountReal S₀ P.1 S₀ - (i : ℝ) * r

@[simp]
theorem linearPairTarget_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (r : ℝ) (P : PairOn V) :
    linearPairTarget S₀ r P 0 =
      fixedPairAvailableCountReal S₀ P.1 S₀ := by
  simp [linearPairTarget]

theorem linearPairTarget_succ_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (r : ℝ) (P : PairOn V) (i : ℕ) :
    linearPairTarget S₀ r P (i + 1) - linearPairTarget S₀ r P i = -r := by
  simp only [linearPairTarget, Nat.cast_add, Nat.cast_one]
  ring

/-- Slow rate used by the upper envelope. -/
def pairUpperLinearRate
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (δ Δ : ℕ) : ℝ :=
  (δ : ℝ) * ((3 * δ - 2 - Δ : ℕ) : ℝ) *
    (S₀.available.card : ℝ)⁻¹

/-- Fast rate used by the lower envelope. -/
def pairLowerLinearRate (Δ K Dmin : ℕ) : ℝ :=
  (Δ : ℝ) * ((3 * Δ + K : ℕ) : ℝ) * (Dmin : ℝ)⁻¹

theorem pairUpperLinearRate_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (δ Δ : ℕ) :
    0 ≤ pairUpperLinearRate S₀ δ Δ := by
  unfold pairUpperLinearRate
  positivity

theorem pairLowerLinearRate_nonneg (Δ K Dmin : ℕ) :
    0 ≤ pairLowerLinearRate Δ K Dmin := by
  unfold pairLowerLinearRate
  positivity

/-- The slow upper rate is no larger than the current forced deletion rate
inside the timed pair-band active region. -/
theorem pairUpperLinearRate_le_current
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {K Δ δ : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hS : PairTrajectoryInvariant F S₀ S)
    (hactive : timedPairBandActive F K Δ δ D i S)
    (halive : PairAlive P.1 S) :
    pairUpperLinearRate S₀ δ Δ ≤
      (S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * δ - 2 - Δ : ℕ) : ℝ) := by
  have hApos : 0 < S.available.card := card_pos.mpr hactive.1.1
  have hA₀pos : 0 < S₀.available.card :=
    hApos.trans_le (card_le_card hS.2)
  have hpairNat : δ ≤
      (availableTrianglesContainingPair S P.1).card :=
    hactive.1.2.2.2 P.1 P.2 halive
  have hpairReal : (δ : ℝ) ≤
      ((availableTrianglesContainingPair S P.1).card : ℝ) := by
    exact_mod_cast hpairNat
  have hcardReal : (S.available.card : ℝ) ≤
      (S₀.available.card : ℝ) := by
    exact_mod_cast card_le_card hS.2
  have hAposReal : (0 : ℝ) < (S.available.card : ℝ) := by
    exact_mod_cast hApos
  have hA₀posReal : (0 : ℝ) < (S₀.available.card : ℝ) := by
    exact_mod_cast hA₀pos
  have hinv : (S₀.available.card : ℝ)⁻¹ ≤
      (S.available.card : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hA₀posReal hAposReal).mpr hcardReal
  unfold pairUpperLinearRate
  calc
    (δ : ℝ) * ((3 * δ - 2 - Δ : ℕ) : ℝ) *
          (S₀.available.card : ℝ)⁻¹ ≤
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * δ - 2 - Δ : ℕ) : ℝ) *
            (S.available.card : ℝ)⁻¹ := by
      gcongr
    _ = (S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * δ - 2 - Δ : ℕ) : ℝ) := by ring

/-- The current cutoff deletion rate is no larger than the fast lower rate
when the deterministic schedule stays above `Dmin`. -/
theorem current_pairRate_le_pairLowerLinearRate
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {K Δ δ Dmin : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hactive : timedPairBandActive F K Δ δ D i S)
    (hDminPos : 0 < Dmin)
    (hDmin : Dmin ≤ D i) :
    (S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * Δ + K : ℕ) : ℝ) ≤
      pairLowerLinearRate Δ K Dmin := by
  have hApos : 0 < S.available.card := card_pos.mpr hactive.1.1
  have hDminA : Dmin ≤ S.available.card := hDmin.trans hactive.2
  have hpairNat :
      (availableTrianglesContainingPair S P.1).card ≤ Δ :=
    hactive.1.2.1 P.1 P.2
  have hpairReal :
      ((availableTrianglesContainingPair S P.1).card : ℝ) ≤ (Δ : ℝ) := by
    exact_mod_cast hpairNat
  have hDminReal : (Dmin : ℝ) ≤ (S.available.card : ℝ) := by
    exact_mod_cast hDminA
  have hDminPosReal : (0 : ℝ) < (Dmin : ℝ) := by
    exact_mod_cast hDminPos
  have hAposReal : (0 : ℝ) < (S.available.card : ℝ) := by
    exact_mod_cast hApos
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (Dmin : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hAposReal hDminPosReal).mpr hDminReal
  unfold pairLowerLinearRate
  calc
    (S.available.card : ℝ)⁻¹ *
          ((availableTrianglesContainingPair S P.1).card : ℝ) *
            ((3 * Δ + K : ℕ) : ℝ) ≤
        (Dmin : ℝ)⁻¹ * (Δ : ℝ) *
          ((3 * Δ + K : ℕ) : ℝ) := by
      gcongr
    _ = (Δ : ℝ) * ((3 * Δ + K : ℕ) : ℝ) *
        (Dmin : ℝ)⁻¹ := by ring

/-- The explicit upper target has the drift orientation required by the
upper-tail stopped theorem. -/
theorem linearPairUpperTarget_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {K Δ δ : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hS : PairTrajectoryInvariant F S₀ S)
    (hactive : timedPairBandActive F K Δ δ D i S)
    (halive : PairAlive P.1 S) :
    -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * δ - 2 - Δ : ℕ)) ≤
      linearPairTarget S₀ (pairUpperLinearRate S₀ δ Δ) P (i + 1) -
        linearPairTarget S₀ (pairUpperLinearRate S₀ δ Δ) P i := by
  rw [linearPairTarget_succ_sub]
  have h := pairUpperLinearRate_le_current hS hactive halive
  linarith

/-- The explicit lower target has the drift orientation required by the
lower-tail stopped theorem. -/
theorem linearPairLowerTarget_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {K Δ δ Dmin : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hactive : timedPairBandActive F K Δ δ D i S)
    (hDminPos : 0 < Dmin)
    (hDmin : Dmin ≤ D i) :
    linearPairTarget S₀ (pairLowerLinearRate Δ K Dmin) P (i + 1) -
        linearPairTarget S₀ (pairLowerLinearRate Δ K Dmin) P i ≤
      -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          (3 * Δ + K : ℕ)) := by
  rw [linearPairTarget_succ_sub]
  have h := current_pairRate_le_pairLowerLinearRate
    (S₀ := S₀) (P := P) hactive hDminPos hDmin
  calc
    -pairLowerLinearRate Δ K Dmin ≤
        -((S.available.card : ℝ)⁻¹ *
          ((availableTrianglesContainingPair S P.1).card : ℝ) *
            ((3 * Δ + K : ℕ) : ℝ)) := neg_le_neg h
    _ = -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          (3 * Δ + K : ℕ)) := by ring

/-- Uniform conditional-variance budget for a linear target of rate `r`. -/
def linearPairVarianceBudget (Δ K Dmin : ℕ) (r : ℝ) : ℝ :=
  2 * ((Dmin : ℝ)⁻¹ * (Δ : ℝ) *
      (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ))) + 2 * r ^ 2

theorem linearPairTarget_variance_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {K Δ δ Dmin : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (r : ℝ) (hactive : timedPairBandActive F K Δ δ D i S)
    (hDminPos : 0 < Dmin)
    (hDmin : Dmin ≤ D i) :
    2 * ((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)))) +
        2 * (linearPairTarget S₀ r P (i + 1) -
          linearPairTarget S₀ r P i) ^ 2 ≤
      linearPairVarianceBudget Δ K Dmin r := by
  rw [linearPairTarget_succ_sub]
  have hApos : 0 < S.available.card := card_pos.mpr hactive.1.1
  have hDminA : Dmin ≤ S.available.card := hDmin.trans hactive.2
  have hpairNat :
      (availableTrianglesContainingPair S P.1).card ≤ Δ :=
    hactive.1.2.1 P.1 P.2
  have hpairReal :
      ((availableTrianglesContainingPair S P.1).card : ℝ) ≤ (Δ : ℝ) := by
    exact_mod_cast hpairNat
  have hDminReal : (Dmin : ℝ) ≤ (S.available.card : ℝ) := by
    exact_mod_cast hDminA
  have hDminPosReal : (0 : ℝ) < (Dmin : ℝ) := by
    exact_mod_cast hDminPos
  have hAposReal : (0 : ℝ) < (S.available.card : ℝ) := by
    exact_mod_cast hApos
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (Dmin : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hAposReal hDminPosReal).mpr hDminReal
  unfold linearPairVarianceBudget
  have hmain :
      (S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ))) ≤
        (Dmin : ℝ)⁻¹ * (Δ : ℝ) *
          (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)) := by
    calc
      (S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ))) =
          (S.available.card : ℝ)⁻¹ *
            ((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)) := by ring
      _ ≤ (Dmin : ℝ)⁻¹ * (Δ : ℝ) *
            (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)) := by
        gcongr
  have hscaled := mul_le_mul_of_nonneg_left hmain (show (0 : ℝ) ≤ 2 by norm_num)
  simpa only [neg_sq] using add_le_add hscaled (le_refl (2 * r ^ 2))

/-- The full timed pair-band tail estimate instantiated with the explicit
linear upper and lower trajectories.  All process-dependent drift and
variance obligations have disappeared; the remaining assumptions are scalar
inequalities on the chosen phase parameters. -/
theorem probability_timedPairBand_linear_not_horizon_and_twoAway_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (K Δ δ JUpper Dmin : ℕ) (D : ℕ → ℕ)
    (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmall : 3 + K < δ)
    (hDpositive : ∀ i, i ≤ n → 0 < D i)
    (hDminPos : 0 < Dmin)
    (hDmin : ∀ i, i ≤ n → Dmin ≤ D i)
    (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + K) ≤ D i)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a + (n : ℝ) * pairLowerLinearRate Δ K Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ K Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudget Δ K Dmin (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudget Δ K Dmin
        (pairLowerLinearRate Δ K Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + K : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let qUpper := linearPairTarget S₀ (pairUpperLinearRate S₀ δ Δ)
    let qLower := linearPairTarget S₀ (pairLowerLinearRate Δ K Dmin)
    let active := timedPairBandActive F K Δ δ D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let rUpper := pairUpperLinearRate S₀ δ Δ
  let rLower := pairLowerLinearRate Δ K Dmin
  let qUpper := linearPairTarget S₀ rUpper
  let qLower := linearPairTarget S₀ rLower
  have hrUpper : 0 ≤ rUpper := pairUpperLinearRate_nonneg S₀ δ Δ
  have hrLower : 0 ≤ rLower := pairLowerLinearRate_nonneg Δ K Dmin
  apply probability_timedPairBand_not_horizon_and_twoAway_le_exp
    n F S₀ qUpper qLower K Δ δ JUpper D theta a v hInv₀ hδ hsmall
    hDpositive hfloor₀ hdecrease
  · intro P i _hi
    have hmul : 0 ≤ (i : ℝ) * rUpper := mul_nonneg (by positivity) hrUpper
    simpa only [qUpper, linearPairTarget_zero, linearPairTarget] using
      (show fixedPairAvailableCountReal S₀ P.1 S₀ - (i : ℝ) * rUpper +
          (fixedPairAvailableCountReal S₀ P.1 S₀ -
            fixedPairAvailableCountReal S₀ P.1 S₀) + a ≤
            ((Δ + 1 : ℕ) : ℝ) by
        linarith [hinitialCap P])
  · intro P i hi halive₀
    have hiReal : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * rLower ≤ (n : ℝ) * rLower := by
      exact mul_le_mul_of_nonneg_right hiReal hrLower
    simp only [qLower, linearPairTarget_zero, linearPairTarget]
    linarith [hfinalFloor P halive₀]
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    linarith
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    linarith
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S₀ rLower P i]
    linarith
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S₀ rLower P i]
    linarith
  · intro P i _hi S hS hactive halive
    exact linearPairUpperTarget_drift hS hactive halive
  · intro P i hi S _hS hactive _halive
    exact linearPairLowerTarget_drift hactive hDminPos (hDmin i hi.le)
  · intro P i hi S _hS hactive _halive
    exact (linearPairTarget_variance_le rUpper hactive hDminPos
      (hDmin i hi.le)).trans hvarianceUpper
  · intro P i hi S _hS hactive _halive
    exact (linearPairTarget_variance_le rLower hactive hDminPos
      (hDmin i hi.le)).trans hvarianceLower
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

/-- The slow upper rate bound in the two-cutoff active region. -/
theorem pairUpperLinearRate_le_current_twoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {Kpair Kglobal Δ δ : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hS : PairTrajectoryInvariant F S₀ S)
    (hactive : timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S)
    (halive : PairAlive P.1 S) :
    pairUpperLinearRate S₀ δ Δ ≤
      (S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * δ - 2 - Δ : ℕ) : ℝ) := by
  have hold : timedPairBandActive F Kglobal Δ δ D i S :=
    ⟨⟨hactive.1.1, hactive.1.2.1, hactive.1.2.2.2.1,
      hactive.1.2.2.2.2⟩, hactive.2⟩
  exact pairUpperLinearRate_le_current hS hold halive

/-- The fast lower rate bound in the two-cutoff active region. -/
theorem current_pairRate_le_pairLowerLinearRate_twoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {Kpair Kglobal Δ δ Dmin : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hactive : timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S)
    (hDminPos : 0 < Dmin) (hDmin : Dmin ≤ D i) :
    (S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * Δ + Kglobal : ℕ) : ℝ) ≤
      pairLowerLinearRate Δ Kglobal Dmin := by
  have hold : timedPairBandActive F Kglobal Δ δ D i S :=
    ⟨⟨hactive.1.1, hactive.1.2.1, hactive.1.2.2.2.1,
      hactive.1.2.2.2.2⟩, hactive.2⟩
  exact current_pairRate_le_pairLowerLinearRate
    (S₀ := S₀) (P := P) hold hDminPos hDmin

/-- Upper-target drift in the two-cutoff active region. -/
theorem linearPairUpperTarget_drift_twoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {Kpair Kglobal Δ δ : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hS : PairTrajectoryInvariant F S₀ S)
    (hactive : timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S)
    (halive : PairAlive P.1 S) :
    -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * δ - 2 - Δ : ℕ)) ≤
      linearPairTarget S₀ (pairUpperLinearRate S₀ δ Δ) P (i + 1) -
        linearPairTarget S₀ (pairUpperLinearRate S₀ δ Δ) P i := by
  rw [linearPairTarget_succ_sub]
  have h := pairUpperLinearRate_le_current_twoCutoffs hS hactive halive
  linarith

/-- Lower-target drift in the two-cutoff active region. -/
theorem linearPairLowerTarget_drift_twoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {Kpair Kglobal Δ δ Dmin : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (hactive : timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S)
    (hDminPos : 0 < Dmin) (hDmin : Dmin ≤ D i) :
    linearPairTarget S₀ (pairLowerLinearRate Δ Kglobal Dmin) P (i + 1) -
        linearPairTarget S₀ (pairLowerLinearRate Δ Kglobal Dmin) P i ≤
      -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          (3 * Δ + Kglobal : ℕ)) := by
  rw [linearPairTarget_succ_sub]
  have h := current_pairRate_le_pairLowerLinearRate_twoCutoffs
    (S₀ := S₀) (P := P) hactive hDminPos hDmin
  calc
    -pairLowerLinearRate Δ Kglobal Dmin ≤
        -((S.available.card : ℝ)⁻¹ *
          ((availableTrianglesContainingPair S P.1).card : ℝ) *
            ((3 * Δ + Kglobal : ℕ) : ℝ)) := neg_le_neg h
    _ = -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          (3 * Δ + Kglobal : ℕ)) := by ring

/-- Uniform variance budget with distinct pair-local and global cutoffs. -/
def linearPairVarianceBudgetTwoCutoffs
    (Δ Kpair Kglobal Dmin : ℕ) (r : ℝ) : ℝ :=
  2 * ((Dmin : ℝ)⁻¹ * (Δ : ℝ) *
      (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ))) +
    2 * r ^ 2

theorem linearPairTarget_variance_le_twoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {Kpair Kglobal Δ δ Dmin : ℕ} {D : ℕ → ℕ} {i : ℕ} {P : PairOn V}
    (r : ℝ)
    (hactive : timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S)
    (hDminPos : 0 < Dmin) (hDmin : Dmin ≤ D i) :
    2 * ((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
        2 * (linearPairTarget S₀ r P (i + 1) -
          linearPairTarget S₀ r P i) ^ 2 ≤
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin r := by
  rw [linearPairTarget_succ_sub]
  have hApos : 0 < S.available.card := card_pos.mpr hactive.1.1
  have hDminA : Dmin ≤ S.available.card := hDmin.trans hactive.2
  have hpairNat :
      (availableTrianglesContainingPair S P.1).card ≤ Δ :=
    hactive.1.2.1 P.1 P.2
  have hpairReal :
      ((availableTrianglesContainingPair S P.1).card : ℝ) ≤ (Δ : ℝ) := by
    exact_mod_cast hpairNat
  have hDminReal : (Dmin : ℝ) ≤ (S.available.card : ℝ) := by
    exact_mod_cast hDminA
  have hDminPosReal : (0 : ℝ) < (Dmin : ℝ) := by
    exact_mod_cast hDminPos
  have hAposReal : (0 : ℝ) < (S.available.card : ℝ) := by
    exact_mod_cast hApos
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (Dmin : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hAposReal hDminPosReal).mpr hDminReal
  unfold linearPairVarianceBudgetTwoCutoffs
  have hmain :
      (S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * Δ + Kglobal : ℕ) : ℝ))) ≤
        (Dmin : ℝ)⁻¹ * (Δ : ℝ) *
          (((3 + Kpair : ℕ) : ℝ) *
            ((3 * Δ + Kglobal : ℕ) : ℝ)) := by
    calc
      (S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ))) =
          (S.available.card : ℝ)⁻¹ *
            ((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)) := by ring
      _ ≤ (Dmin : ℝ)⁻¹ * (Δ : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * Δ + Kglobal : ℕ) : ℝ)) := by
        gcongr
  have hscaled := mul_le_mul_of_nonneg_left hmain (show (0 : ℝ) ≤ 2 by norm_num)
  simpa only [neg_sq] using add_le_add hscaled (le_refl (2 * r ^ 2))

/-- Linear two-cutoff pair-band estimate with all process-dependent
obligations discharged. -/
theorem probability_timedPairBand_linearTwoCutoffs_not_horizon_and_cutoffs_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Δ δ JUpper Dmin : ℕ) (D : ℕ → ℕ)
    (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmall : 3 + Kpair < δ)
    (hDpositive : ∀ i, i ≤ n → 0 < D i)
    (hDminPos : 0 < Dmin)
    (hDmin : ∀ i, i ≤ n → Dmin ≤ D i)
    (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + Kglobal) ≤ D i)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a +
          (n : ℝ) * pairLowerLinearRate Δ Kglobal Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ Kglobal Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairLowerLinearRate Δ Kglobal Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let qUpper := linearPairTarget S₀ (pairUpperLinearRate S₀ δ Δ)
    let qLower := linearPairTarget S₀
      (pairLowerLinearRate Δ Kglobal Dmin)
    let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasPairTwoAwayCutoff F Kpair z.2 ∧
      HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let rUpper := pairUpperLinearRate S₀ δ Δ
  let rLower := pairLowerLinearRate Δ Kglobal Dmin
  let qUpper := linearPairTarget S₀ rUpper
  let qLower := linearPairTarget S₀ rLower
  have hrUpper : 0 ≤ rUpper := pairUpperLinearRate_nonneg S₀ δ Δ
  have hrLower : 0 ≤ rLower := pairLowerLinearRate_nonneg Δ Kglobal Dmin
  apply probability_timedPairBandTwoCutoffs_not_horizon_and_cutoffs_le_exp
    n F S₀ qUpper qLower Kpair Kglobal Δ δ JUpper D theta a v
    hInv₀ hδ hsmall hDpositive hfloor₀ hdecrease
  · intro P i _hi
    have hmul : 0 ≤ (i : ℝ) * rUpper := mul_nonneg (by positivity) hrUpper
    simpa only [qUpper, linearPairTarget_zero, linearPairTarget] using
      (show fixedPairAvailableCountReal S₀ P.1 S₀ - (i : ℝ) * rUpper +
          (fixedPairAvailableCountReal S₀ P.1 S₀ -
            fixedPairAvailableCountReal S₀ P.1 S₀) + a ≤
            ((Δ + 1 : ℕ) : ℝ) by
        linarith [hinitialCap P])
  · intro P i hi halive₀
    have hiReal : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi
    have hmul : (i : ℝ) * rLower ≤ (n : ℝ) * rLower := by
      exact mul_le_mul_of_nonneg_right hiReal hrLower
    simp only [qLower, linearPairTarget_zero, linearPairTarget]
    linarith [hfinalFloor P halive₀]
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    linarith
  · intro P i _hi
    rw [show qUpper P (i + 1) - qUpper P i = -rUpper by
      exact linearPairTarget_succ_sub S₀ rUpper P i]
    linarith
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S₀ rLower P i]
    linarith
  · intro P i _hi
    rw [show qLower P (i + 1) - qLower P i = -rLower by
      exact linearPairTarget_succ_sub S₀ rLower P i]
    linarith
  · intro P i _hi S hS hactive halive
    exact linearPairUpperTarget_drift_twoCutoffs hS hactive halive
  · intro P i hi S _hS hactive _halive
    exact linearPairLowerTarget_drift_twoCutoffs
      hactive hDminPos (hDmin i hi.le)
  · intro P i hi S _hS hactive _halive
    exact (linearPairTarget_variance_le_twoCutoffs rUpper hactive hDminPos
      (hDmin i hi.le)).trans hvarianceUpper
  · intro P i hi S _hS hactive _halive
    exact (linearPairTarget_variance_le_twoCutoffs rLower hactive hDminPos
      (hDmin i hi.le)).trans hvarianceLower
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

end

end Erdos207

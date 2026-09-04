/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.AdjusterBase
import ErdosProblems.Erdos63.GrowthSchedule

/-!
# Numerical scales for Liu--Montgomery Claim 4.4

This file is graph-free.  It first packages the two Lemma 4.2 connector
schedules used by Claim 4.4.  Both schedules follow the canonical
`lmGrowthCurve`; the split square/cube workspaces are paid by one copy of the
canonical gain and the curve increment by a second copy.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Canonical connector schedules -/

/-- The workspace in the first (cube-seed) connector of Lemma 4.2. -/
def lm42CubeWorkspace (D m L : ℕ) : ℕ :=
  L + 2 + 2 * D + 2 * (m ^ 2 * D)

/-- The workspace in the second (square-seed) connector of Lemma 4.2. -/
def lm42SquareWorkspace (D m L : ℕ) : ℕ :=
  L + 2 + (3 * m + 1) + 2 * D

/-- Once the connector radius dominates the cycle length, the canonical
square/cube workspace has enough slack for the adaptive seed automatically:
either the endpoint already has the required starting size, or the
minimum-degree bootstrap pays the complete workspace. -/
theorem lm42CanonicalSeedDichotomy
    {d D m L : ℕ} (hm : 2 ≤ m) (hD : 0 < D) (hL : L ≤ m) :
    lm311AdaptiveSeed d ≤ m ^ 2 * D ∨
      lm311AdaptiveSeed d +
        max (lm42SquareWorkspace D m L) (lm42CubeWorkspace D m L) ≤ d - 1 := by
  let X := m ^ 2 * D
  have hmPos : 0 < m := by omega
  have hXPos : 0 < X := by
    dsimp [X]
    positivity
  have hmX : m ≤ X := by
    dsimp [X]
    nlinarith
  have hDX : D ≤ X := by
    dsimp [X]
    exact Nat.le_mul_of_pos_left D (pow_pos hmPos 2)
  have hmD : m ≤ m * D := Nat.le_mul_of_pos_right m hD
  have hDmD : D ≤ m * D := Nat.le_mul_of_pos_left D hmPos
  have hLmD : L ≤ m * D := hL.trans hmD
  have hmDX : m * D ≤ X := by
    dsimp [X]
    nlinarith
  have hSquare : lm42SquareWorkspace D m L ≤ 8 * X := by
    have hthree : 3 ≤ 2 * (m * D) := by omega
    have : lm42SquareWorkspace D m L ≤ 8 * (m * D) := by
      dsimp [lm42SquareWorkspace]
      omega
    exact this.trans (Nat.mul_le_mul_left 8 hmDX)
  have hCube : lm42CubeWorkspace D m L ≤ 4 * X := by
    have hLtwo : L + 2 ≤ X := by
      have htwoM : 2 * m ≤ m ^ 2 := by nlinarith
      calc
        L + 2 ≤ 2 * m := by omega
        _ ≤ m ^ 2 := htwoM
        _ ≤ m ^ 2 * D := Nat.le_mul_of_pos_right _ hD
        _ = X := by rfl
    have htwoD : 2 * D ≤ X := by
      dsimp [X]
      have htwoM2 : 2 ≤ m ^ 2 := by nlinarith
      simpa [mul_assoc, mul_comm] using Nat.mul_le_mul_right D htwoM2
    dsimp [lm42CubeWorkspace]
    omega
  have hWorkspace :
      max (lm42SquareWorkspace D m L) (lm42CubeWorkspace D m L) ≤ 8 * X :=
    max_le hSquare (hCube.trans (by omega))
  by_cases hsource : lm311AdaptiveSeed d ≤ X
  · exact Or.inl (by simpa [X] using hsource)
  · right
    have hXd : X ≤ d / 128 := by
      dsimp [lm311AdaptiveSeed] at hsource
      omega
    have hqPos : 0 < d / 128 := hXPos.trans_le hXd
    have hdecomp := Nat.div_add_mod d 128
    dsimp [lm311AdaptiveSeed]
    omega

/-- Source-radius form of `lm42CanonicalSeedDichotomy`.  In particular, the
connector seed alternative needed by Claim 4.4 has no additional asymptotic
hypothesis. -/
theorem lm42CanonicalSeedDichotomy_five_mul_lmGrowthRounds
    {N d D L : ℕ} (hN : 32 ≤ N) (hD : 0 < D)
    (hL : L ≤ lm311GirthBudget N) :
    lm311AdaptiveSeed d ≤ (5 * lmGrowthRounds N) ^ 2 * D ∨
      lm311AdaptiveSeed d +
        max (lm42SquareWorkspace D (5 * lmGrowthRounds N) L)
          (lm42CubeWorkspace D (5 * lmGrowthRounds N) L) ≤ d - 1 := by
  let q := lmGrowthDivisor N
  let r := lmGrowthRounds N
  let k := Nat.log 2 N
  have hq : 2 ≤ q := by
    dsimp [q, lmGrowthDivisor]
    have := lmGrowthDenominator_pos (hN.trans' (by omega))
    omega
  have hr : r = 2 * q * (k + 1) := by
    simp [r, q, k, lmGrowthRounds]
  have hrPos : 0 < r := by rw [hr]; positivity
  have hgirth : lm311GirthBudget N ≤ 5 * r := by
    have hfourq : 4 ≤ 2 * q := by omega
    have hh : 4 * (k + 1) ≤ (2 * q) * (k + 1) :=
      Nat.mul_le_mul_right (k + 1) hfourq
    calc
      lm311GirthBudget N = 2 * (k + 2) := by
        simp [lm311GirthBudget, k]
      _ ≤ 4 * (k + 1) := by omega
      _ ≤ (2 * q) * (k + 1) := hh
      _ = r := hr.symm
      _ ≤ 5 * r := by omega
  exact lm42CanonicalSeedDichotomy (by omega) hD (hL.trans hgirth)

/-- Named finite inequalities for the canonical Lemma 4.2 connector. -/
structure LM42CanonicalBounds (N d D m L : ℕ) : Prop where
  card_large : 32 ≤ N
  degree_pos : 1 ≤ d
  two_le_m : 2 ≤ m
  D_pos : 0 < D
  square_seed : lm311AdaptiveSeed d ≤ m ^ 2 * D ∨
    lm311AdaptiveSeed d + lm42SquareWorkspace D m L ≤ d - 1
  cube_seed : lm311AdaptiveSeed d ≤ m ^ 3 * D ∨
    lm311AdaptiveSeed d + lm42CubeWorkspace D m L ≤ d - 1
  square_warm : 2 * lmGrowthDivisor N ≤ m ^ 2 * D
  cube_warm : 2 * lmGrowthDivisor N ≤ m ^ 3 * D
  square_workspace : lm42SquareWorkspace D m L ≤
    lmGrowthGain N (m ^ 2 * D)
  cube_workspace : lm42CubeWorkspace D m L ≤
    lmGrowthGain N (m ^ 3 * D)
  radius_fit : 2 * (lmGrowthRounds N + 1) ≤ m
  cycle_length : L ≤ 2 * m

/-! ## The source radius `5 * lmGrowthRounds` -/

/-- At the source radius, the split workspaces automatically fit in one
canonical gain.  The adaptive seed is paid by the minimum-degree bootstrap
when it is larger than the endpoint expansion. -/
theorem lm42CanonicalBounds_five_mul_lmGrowthRounds
    {N d D L : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d) (hD : 0 < D)
    (hL : L ≤ lm311GirthBudget N)
    (hseed : lm311AdaptiveSeed d ≤ (5 * lmGrowthRounds N) ^ 2 * D ∨
      lm311AdaptiveSeed d +
        max (lm42SquareWorkspace D (5 * lmGrowthRounds N) L)
          (lm42CubeWorkspace D (5 * lmGrowthRounds N) L) ≤ d - 1) :
    LM42CanonicalBounds N d D (5 * lmGrowthRounds N) L := by
  let q := lmGrowthDivisor N
  let r := lmGrowthRounds N
  let m := 5 * r
  let k := Nat.log 2 N
  have hq : 0 < q := by
    simpa [q] using lmGrowthDivisor_pos (hN.trans' (by omega))
  have hr : r = 2 * q * (k + 1) := by
    simp [r, q, k, lmGrowthRounds]
  have hrPos : 0 < r := by rw [hr]; positivity
  have hm : m = 5 * r := rfl
  have hmPos : 0 < m := by simp [m, hrPos]
  have htwoM : 2 ≤ m := by simp [m]; omega
  have hqtwo : 2 ≤ q := by
    dsimp [q, lmGrowthDivisor]
    have := lmGrowthDenominator_pos (hN.trans' (by omega))
    omega
  have hfourq : 4 ≤ 2 * q := by omega
  have hgirthR : lm311GirthBudget N ≤ r := by
    have hh : 4 * (k + 1) ≤ (2 * q) * (k + 1) :=
      Nat.mul_le_mul_right (k + 1) hfourq
    calc
      lm311GirthBudget N = 2 * (k + 2) := by
        simp [lm311GirthBudget, k]
      _ ≤ 4 * (k + 1) := by omega
      _ ≤ (2 * q) * (k + 1) := hh
      _ = r := hr.symm
  have hgirth : lm311GirthBudget N ≤ m := by
    exact hgirthR.trans (by simp [m]; omega)
  have hLD : L ≤ m * D := by
    exact hL.trans hgirth |>.trans (Nat.le_mul_of_pos_right m hD)
  have hmD : m ≤ m * D := Nat.le_mul_of_pos_right m hD
  have hD_mD : D ≤ m * D := Nat.le_mul_of_pos_left D hmPos
  have htwoqr : 2 * q ≤ r := by
    rw [hr]
    exact Nat.le_mul_of_pos_right (2 * q) (by omega)
  have hseven : 7 * q ≤ m := by
    calc
      7 * q ≤ 5 * (2 * q) := by omega
      _ ≤ 5 * r := Nat.mul_le_mul_left 5 htwoqr
      _ = m := hm.symm
  have hfour : 4 * q ≤ m := hseven.trans' (by omega)
  have hwSquare : lm42SquareWorkspace D m L ≤ 7 * (m * D) := by
    dsimp [lm42SquareWorkspace]
    have hthree : 3 ≤ m * D := by omega
    omega
  have hwCube : lm42CubeWorkspace D m L ≤ 4 * (m ^ 2 * D) := by
    dsimp [lm42CubeWorkspace]
    have hm_le_m2D : m ≤ m ^ 2 * D := by
      calc
        m ≤ m * m := Nat.le_mul_of_pos_right m hmPos
        _ = m ^ 2 := by ring
        _ ≤ m ^ 2 * D := Nat.le_mul_of_pos_right _ hD
    have hD_le_m2D : D ≤ m ^ 2 * D := by
      have : 1 ≤ m ^ 2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (pow_pos hmPos 2))
      simpa [mul_comm] using Nat.mul_le_mul_right D this
    have htwo_le_m2D : 2 ≤ m ^ 2 * D := by omega
    have hLtwo : L + 2 ≤ m ^ 2 * D := by
      have hLm : L ≤ m := hL.trans hgirth
      have htwoM2 : 2 * m ≤ m ^ 2 := by nlinarith
      calc
        L + 2 ≤ 2 * m := by omega
        _ ≤ m ^ 2 := htwoM2
        _ ≤ m ^ 2 * D := Nat.le_mul_of_pos_right _ hD
    have htwoD : 2 * D ≤ m ^ 2 * D := by
      have htwoM2 : 2 ≤ m ^ 2 := by nlinarith
      simpa [mul_assoc, mul_comm] using Nat.mul_le_mul_right D htwoM2
    omega
  have hsqRate : lm42SquareWorkspace D m L ≤
      lmGrowthGain N (m ^ 2 * D) := by
    rw [lmGrowthGain]
    apply (Nat.le_div_iff_mul_le hq).2
    calc
      lm42SquareWorkspace D m L * q
          ≤ (7 * (m * D)) * q := Nat.mul_le_mul_right q hwSquare
      _ ≤ m ^ 2 * D := by
        have := Nat.mul_le_mul_right (m * D) hseven
        nlinarith
  have hcubeRate : lm42CubeWorkspace D m L ≤
      lmGrowthGain N (m ^ 3 * D) := by
    rw [lmGrowthGain]
    apply (Nat.le_div_iff_mul_le hq).2
    calc
      lm42CubeWorkspace D m L * q
          ≤ (4 * (m ^ 2 * D)) * q := Nat.mul_le_mul_right q hwCube
      _ ≤ m ^ 3 * D := by
        have := Nat.mul_le_mul_right (m ^ 2 * D) hfour
        nlinarith
  have hwarmSquare : 2 * q ≤ m ^ 2 * D := by
    calc
      2 * q ≤ m := by rw [hm, hr]; omega
      _ ≤ m * m := Nat.le_mul_of_pos_right m hmPos
      _ = m ^ 2 := by ring
      _ ≤ m ^ 2 * D := Nat.le_mul_of_pos_right _ hD
  have hsqCube : m ^ 2 * D ≤ m ^ 3 * D := by
    have : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega : 0 < m) (by omega)
    exact Nat.mul_le_mul_right D this
  refine
    { card_large := hN
      degree_pos := hd
      two_le_m := by simpa [m] using htwoM
      D_pos := hD
      square_seed := by
        rcases hseed with hsource | hdegree
        · exact Or.inl (by simpa [m] using hsource)
        · exact Or.inr (by
            apply (Nat.add_le_add_left (le_max_left
              (lm42SquareWorkspace D m L) (lm42CubeWorkspace D m L)) _).trans
            simpa [m] using hdegree)
      cube_seed := by
        rcases hseed with hsource | hdegree
        · exact Or.inl (by
            have hsquare : m ^ 2 * D ≤ m ^ 3 * D := hsqCube
            have hsource' : lm311AdaptiveSeed d ≤ m ^ 2 * D := by
              simpa [m] using hsource
            exact hsource'.trans hsquare)
        · exact Or.inr (by
            apply (Nat.add_le_add_left (le_max_right
              (lm42SquareWorkspace D m L) (lm42CubeWorkspace D m L)) _).trans
            simpa [m] using hdegree)
      square_warm := by simpa [m, q] using hwarmSquare
      cube_warm := by simpa [m, q] using hwarmSquare.trans hsqCube
      square_workspace := by simpa [m] using hsqRate
      cube_workspace := by simpa [m] using hcubeRate
      radius_fit := by
        have : 2 * (r + 1) ≤ 5 * r := by omega
        simpa [m, r] using this
      cycle_length := by
        have : L ≤ m := hL.trans hgirth
        simpa [m] using this.trans (Nat.le_mul_of_pos_left m (by omega)) }

/-- Source-radius specialization of the canonical connector constructor. -/
noncomputable def concreteLM42ConnectorScaleFiveRounds
    (N d D L : ℕ) (hN : 32 ≤ N) (hd : 1 ≤ d) (hD : 0 < D)
    (hL : L ≤ lm311GirthBudget N)
    (hseed : lm311AdaptiveSeed d ≤ (5 * lmGrowthRounds N) ^ 2 * D ∨
      lm311AdaptiveSeed d +
        max (lm42SquareWorkspace D (5 * lmGrowthRounds N) L)
          (lm42CubeWorkspace D (5 * lmGrowthRounds N) L) ≤ d - 1) :
    LM42ConnectorScale N d D (5 * lmGrowthRounds N) L
      (1 / 1024) ((1 / 64) * (d : ℝ)) :=
  let b := lm42CanonicalBounds_five_mul_lmGrowthRounds hN hd hD hL hseed
  concreteLM42ConnectorScale N d D (5 * lmGrowthRounds N) L
    (lm42SquareWorkspace D (5 * lmGrowthRounds N) L)
    (lm42CubeWorkspace D (5 * lmGrowthRounds N) L)
    b.card_large b.degree_pos b.two_le_m b.D_pos le_rfl le_rfl
    b.square_seed b.cube_seed b.square_warm b.cube_warm
    b.square_workspace b.cube_workspace b.radius_fit b.radius_fit
    b.cycle_length

/-! ## Claim 4.4 budget constructor -/

/-- Exact occupied-seed budget used in Claim 4.4. -/
def lm44SeedCap (protectedCap R maxRadius : ℕ) : ℕ :=
  protectedCap + 4 * R * (2 * maxRadius ^ 2 + 10 * maxRadius)

/-- Exact forbidden-ball budget used in Claim 4.4. -/
def lm44BallCap (protectedCap R maxRadius Delta separation : ℕ) : ℕ :=
  lm44SeedCap protectedCap R maxRadius * (Delta + 1) ^ separation

/-- Exact star-replacement workspace used in Claim 4.4. -/
def lm44StarBudget (deletedCap maxRadius targetOrder : ℕ) : ℕ :=
  deletedCap + 10 * maxRadius + targetOrder + 1

/-- Assemble `LM44Scale` after fixing its three bookkeeping budgets to their
literal source values.  All remaining premises are graph-free inequalities
or the two graph-free numerical certificates used by Lemmas 3.11 and 4.2. -/
noncomputable def SmallSimpleAdjusterCandidate.concreteLM44Scale
    (N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R initialDegree coreDegree : ℕ) (kappa : ℝ)
    (coreRadius coreDeltaOne coreDeltaSquare coreLocalRadius
      coreExpansionRadius : ℕ → ℕ)
    (hdeleted : deletedCap ≤ 10 * targetOrder)
    (hproper : deletedCap +
      lm44BallCap protectedCap R maxRadius Delta separation < N)
    (hinitial : ∀ u ≤ deletedCap,
      initialDegree * (N - u) ≤
        ((N - u) - 100 * targetOrder ^ 2) * (d - d / 2))
    (hretained : (8 * coreDegree) * N +
      2 * (lm44BallCap protectedCap R maxRadius Delta separation * Delta) ≤
        initialDegree * (N - deletedCap))
    (hcorePos : 0 < coreDegree) (hcoreFive : 5 ≤ coreDegree)
    (hkappa : 0 < kappa) (htarget : 0 < targetOrder)
    (htotal : 1 ≤ totalRadius) (hmaxTotal : maxRadius ≤ totalRadius)
    (hstar : targetOrder + lm44StarBudget deletedCap maxRadius targetOrder ≤
      Delta)
    (hradiusPos : ∀ n', coreDegree < n' → n' ≤ N → 0 < coreRadius n')
    (hradius : ∀ n', coreDegree < n' → n' ≤ N →
      minRadius ≤ coreRadius n' ∧ coreRadius n' ≤ maxRadius)
    (hfamily : ∀ n', coreDegree < n' → n' ≤ N →
      5 * coreExpansionRadius n' ≤ coreRadius n')
    (hnumOne : ∀ n', coreDegree < n' → n' ≤ N →
      LM311Numerics (1 / 1024) kappa n' 4 coreDegree
        ((coreRadius n') ^ 3) (coreDeltaOne n') (coreLocalRadius n')
        (coreExpansionRadius n') 1)
    (hnumSquare : ∀ n', coreDegree < n' → n' ≤ N →
      LM311Numerics (1 / 1024) kappa n' 4 coreDegree
        ((coreRadius n') ^ 3 * (coreRadius n') ^ 2) (coreDeltaSquare n')
        (coreLocalRadius n') (coreExpansionRadius n') 1)
    (hconnectorOne : ∀ n' L, coreDegree < n' → n' ≤ N →
      L ≤ lm311GirthBudget n' →
      LM42ConnectorScale n' coreDegree 1 (coreRadius n') L (1 / 1024) kappa)
    (hconnectorSquare : ∀ n' L, coreDegree < n' → n' ≤ N →
      L ≤ lm311GirthBudget n' →
      LM42ConnectorScale n' coreDegree ((coreRadius n') ^ 2) (coreRadius n') L
        (1 / 1024) kappa) :
    SmallSimpleAdjusterCandidate.LM44Scale N d targetOrder totalRadius Delta
      deletedCap protectedCap separation minRadius maxRadius R kappa where
  seedCap := lm44SeedCap protectedCap R maxRadius
  ballCap := lm44BallCap protectedCap R maxRadius Delta separation
  initialDegree := initialDegree
  coreDegree := coreDegree
  starBudget := lm44StarBudget deletedCap maxRadius targetOrder
  coreRadius := coreRadius
  coreDeltaOne := coreDeltaOne
  coreDeltaSquare := coreDeltaSquare
  coreLocalRadius := coreLocalRadius
  coreExpansionRadius := coreExpansionRadius
  deleted_le_ten_target := hdeleted
  seed_bound := le_rfl
  ball_bound := le_rfl
  deletion_proper := hproper
  initial_density := hinitial
  retained_density := hretained
  coreDegree_pos := hcorePos
  five_le_coreDegree := hcoreFive
  kappa_pos := hkappa
  target_pos := htarget
  one_le_total := htotal
  max_le_total := hmaxTotal
  star_workspace := le_rfl
  star_degree := hstar
  coreRadius_pos := hradiusPos
  coreRadius_bounds := hradius
  core_family_radius := hfamily
  num_one := hnumOne
  num_square := hnumSquare
  connector_one := hconnectorOne
  connector_square := hconnectorSquare

/-! ## Source-radius Claim 4.4 constructor -/

/-- Claim 4.4 with the source radius `5 * lmGrowthRounds`.  The connector
certificates are now automatic; the two k=4 Lemma 3.11 certificates remain
explicit inputs because they also determine the two squared reservoir
orders. -/
noncomputable def SmallSimpleAdjusterCandidate.concreteLM44ScaleFiveRounds
    (N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R initialDegree coreDegree : ℕ)
    (hdeleted : deletedCap ≤ 10 * targetOrder)
    (hproper : deletedCap +
      lm44BallCap protectedCap R maxRadius Delta separation < N)
    (hinitial : ∀ u ≤ deletedCap,
      initialDegree * (N - u) ≤
        ((N - u) - 100 * targetOrder ^ 2) * (d - d / 2))
    (hretained : (8 * coreDegree) * N +
      2 * (lm44BallCap protectedCap R maxRadius Delta separation * Delta) ≤
        initialDegree * (N - deletedCap))
    (hcoreLarge : 32 ≤ coreDegree) (htarget : 0 < targetOrder)
    (htotal : 1 ≤ totalRadius) (hmaxTotal : maxRadius ≤ totalRadius)
    (hstar : targetOrder + lm44StarBudget deletedCap maxRadius targetOrder ≤
      Delta)
    (hradius : ∀ n', coreDegree < n' → n' ≤ N →
      minRadius ≤ 5 * lmGrowthRounds n' ∧
        5 * lmGrowthRounds n' ≤ maxRadius)
    (hseed : ∀ n' D L, coreDegree < n' → n' ≤ N → 0 < D →
      L ≤ lm311GirthBudget n' →
      lm311AdaptiveSeed coreDegree ≤ (5 * lmGrowthRounds n') ^ 2 * D ∨
        lm311AdaptiveSeed coreDegree +
          max (lm42SquareWorkspace D (5 * lmGrowthRounds n') L)
            (lm42CubeWorkspace D (5 * lmGrowthRounds n') L) ≤ coreDegree - 1)
    (hnumOne : ∀ n', coreDegree < n' → n' ≤ N →
      LM311Numerics (1 / 1024) ((1 / 64) * (coreDegree : ℝ)) n' 4 coreDegree
        ((5 * lmGrowthRounds n') ^ 3)
        (((5 * lmGrowthRounds n') ^ 3) ^ 2)
        (Parameters.lm311LocalRadius n') (lmGrowthRounds n') 1)
    (hnumSquare : ∀ n', coreDegree < n' → n' ≤ N →
      LM311Numerics (1 / 1024) ((1 / 64) * (coreDegree : ℝ)) n' 4 coreDegree
        ((5 * lmGrowthRounds n') ^ 3 * (5 * lmGrowthRounds n') ^ 2)
        (((5 * lmGrowthRounds n') ^ 3 * (5 * lmGrowthRounds n') ^ 2) ^ 2)
        (Parameters.lm311LocalRadius n') (lmGrowthRounds n') 1) :
    SmallSimpleAdjusterCandidate.LM44Scale N d targetOrder totalRadius Delta
      deletedCap protectedCap separation minRadius maxRadius R
      ((1 / 64) * (coreDegree : ℝ)) := by
  apply SmallSimpleAdjusterCandidate.concreteLM44Scale N d targetOrder totalRadius
    Delta deletedCap protectedCap separation minRadius maxRadius R initialDegree
    coreDegree ((1 / 64) * (coreDegree : ℝ))
    (fun n ↦ 5 * lmGrowthRounds n)
    (fun n ↦ ((5 * lmGrowthRounds n) ^ 3) ^ 2)
    (fun n ↦ ((5 * lmGrowthRounds n) ^ 3 * (5 * lmGrowthRounds n) ^ 2) ^ 2)
    Parameters.lm311LocalRadius lmGrowthRounds hdeleted hproper hinitial hretained
  · omega
  · omega
  · positivity
  · exact htarget
  · exact htotal
  · exact hmaxTotal
  · exact hstar
  · intro n hn hN
    have hn32 : 32 ≤ n := hcoreLarge.trans hn.le
    have := lmGrowthDivisor_pos (hn32.trans' (by omega))
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, gt_iff_lt]
    positivity
  · exact hradius
  · intro n hn hN
    exact le_rfl
  · exact hnumOne
  · exact hnumSquare
  · intro n L hn hN hL
    exact concreteLM42ConnectorScaleFiveRounds n coreDegree 1 L
      (hcoreLarge.trans hn.le) (by omega) (by omega) hL
      (hseed n 1 L hn hN (by omega) hL)
  · intro n L hn hN hL
    have hn32 : 32 ≤ n := hcoreLarge.trans hn.le
    have hmPos : 0 < 5 * lmGrowthRounds n := by
      have := lmGrowthDivisor_pos (hn32.trans' (by omega))
      simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, gt_iff_lt]
      positivity
    exact concreteLM42ConnectorScaleFiveRounds n coreDegree
      ((5 * lmGrowthRounds n) ^ 2) L hn32 (by omega) (pow_pos hmPos 2) hL
      (hseed n ((5 * lmGrowthRounds n) ^ 2) L hn hN
        (pow_pos hmPos 2) hL)

/-! ## The k=4, one-protected-vertex Lemma 3.11 certificate -/

/-- Fixed local cost of the high-root schedule in the Claim 4.4 instance. -/
def lm44HighRootCost (i : ℕ) : ℕ :=
  lm311HighFixedBudget 4 1 + (2 * (i + 2) + 1) + 4 ^ 2 * (i + 3)

/-- Fixed cost of the reservoir schedule in the Claim 4.4 instance. -/
def lm44ReservoirCost (i : ℕ) : ℕ :=
  2 * 4 ^ 2 + 1 + 4 + (2 * (i + 2) + 1)

/-- Cost of the deficient-root schedule, including its late reservoir
contact term. -/
def lm44LowRootCost (D ell₀ i : ℕ) : ℕ :=
  4 * 4 ^ 2 + 2 * 1 + 2 * 4 + (2 * (i + 2) + 1) +
    4 ^ 2 * (i + 3) + (if i < ell₀ then 0 else 4 ^ 2 * D ^ 2)

/-- Fixed carrier cost before the late reservoir contact term. -/
noncomputable def lm44LowCarrierCost (n : ℕ) : ℕ :=
  2 * 1 + 2 * 4 ^ 2 + 2 * 4 + lm311GirthBudget n +
    4 ^ 2 * (3 * lmGrowthRounds n + 1)

/-- A common carrier budget dominating both the high-hub and low-reservoir
barriers. -/
noncomputable def lm44CarrierCost (n : ℕ) : ℕ :=
  max (lm311HighCarrierBudget n 4 1 (3 * lmGrowthRounds n + 1))
    (lm44LowCarrierCost n)

/-- The carrier seed pays its complete fixed cost from the first adaptive
gain, exactly as in the existing k=2 construction. -/
noncomputable def lm44CarrierStart (n d : ℕ) : ℕ :=
  max (2 * lmGrowthDivisor n * (lm44CarrierCost n + 1))
    (lm311AdaptiveSeed d)

/-- Low-reservoir cost, including the late contact with the retained
`D²`-reservoir. -/
noncomputable def lm44LowReservoirCost (n D ell₀ i : ℕ) : ℕ :=
  lm44LowCarrierCost n + (if i < ell₀ then 0 else 4 ^ 2 * D ^ 2)

/-- The largest phase cost at round `i`.  A single eventual estimate for
this function supplies all global-rate fields of `LM311Numerics`. -/
noncomputable def lm44GlobalPhaseCost (n D ell₀ i : ℕ) : ℕ :=
  max (lm44HighRootCost i)
    (max (lm311HighCarrierBudget n 4 1 (3 * lmGrowthRounds n + 1))
      (max (lm44ReservoirCost i)
        (max (lm44LowRootCost D ell₀ i)
          (lm44LowReservoirCost n D ell₀ i))))

/-- Exact graph-free inequalities not already proved by the adaptive growth
library for the Claim 4.4 Lemma 3.11 call.  This structure deliberately
isolates the two genuinely new eventual estimates (`root_local_cost` and
`global_phase_cost`) from routine geometry and packing arithmetic. -/
structure LM44LM311Bounds (n d D : ℕ) : Prop where
  card_large : 32 ≤ n
  degree_large : lm311DegreeThreshold ≤ d
  degree_le_card : d ≤ n
  expansion_pos : 0 < Parameters.lmExpansionOrder n
  local_radius : Parameters.lm311AdaptiveRounds n + 1 ≤
    Parameters.lm311LocalRadius n
  local_fit : 3 * Parameters.lm311LocalRadius n + 2 ≤ lmGrowthRounds n
  warm_large : 2 * lmGrowthDivisor n ≤ Parameters.lmExpansionOrder n ^ 4
  D_pos : 0 < D
  delta_warm : D ^ 2 ≤ Parameters.lmExpansionOrder n ^ 4
  carrier_start_card : lm44CarrierStart n d ≤ n
  carrier_high_hub : lm44CarrierStart n d ≤
    lm311HighHubSeed n d (D ^ 2) 4 1 (3 * lmGrowthRounds n + 1)
  carrier_delta : d - 1 ≤ D ^ 2 → lm44CarrierStart n d ≤ D ^ 2
  root_local_cost : ∀ i < Parameters.lm311AdaptiveRounds n,
    lm44LowRootCost D (Parameters.lm311LocalRadius n) i ≤
      lm311AdaptiveGain d
        (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i)
  global_phase_cost : ∀ i <
      Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm44GlobalPhaseCost n D (Parameters.lm311LocalRadius n) i ≤
      lmGrowthGain n (Parameters.lmExpansionOrder n ^ 4)
  packing :
    (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
        (D ^ 2 + 1) ^ (10 * Parameters.lm311LocalRadius n) <
      n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4)
  reservoir_half : D ^ 2 ≤ n / 2 + 1
  high_star :
    D + 1 + lm311GirthBudget n + 4 +
        4 ^ 2 * (3 * lmGrowthRounds n + 1) + 4 ^ 2 * D ≤ D ^ 2
  low_star : D + 1 + lm311GirthBudget n + 4 + 4 ^ 2 * D ≤ D ^ 2

theorem lm311AdaptiveSeed_le_claim44_source_seeds {d : ℕ}
    (hd : lm311DegreeThreshold ≤ d) :
    lm311AdaptiveSeed d ≤ lm311HighRootSeed d 4 1 ∧
      lm311AdaptiveSeed d ≤ lm311ReservoirSeed d 4 1 ∧
      lm311AdaptiveSeed d ≤ lm311LowRootSeed d 4 1 := by
  have hdlarge : 128 ≤ d := hd.trans' (by norm_num [lm311DegreeThreshold])
  have hdiv : d / 128 ≤ d := Nat.div_le_self _ _
  dsimp [lm311AdaptiveSeed, lm311HighRootSeed, lm311ReservoirSeed,
    lm311LowRootSeed, lm311HighFixedBudget]
  norm_num
  omega

/-- A carrier whose initial value contains `2*divisor*(cost+1)` pays `cost`
from one adaptive gain. -/
theorem lm44CarrierCost_le_adaptiveGain {n d : ℕ}
    (hn : 32 ≤ n) (hd : 1 ≤ d) (hstart : lm44CarrierStart n d ≤ n) :
    lm44CarrierCost n ≤ lm311AdaptiveGain d (lm44CarrierStart n d) := by
  let start := lm44CarrierStart n d
  let div := lmGrowthDivisor n
  let cost := lm44CarrierCost n
  have hdiv : 0 < div := by
    simpa [div] using lmGrowthDivisor_pos (hn.trans' (by omega))
  have hseed : lm311AdaptiveSeed d ≤ start := by
    exact le_max_right _ _
  have hcut : (d : ℝ) / 128 ≤ (start : ℝ) :=
    (lm311AdaptiveSeed_cutoff d).trans (by exact_mod_cast hseed)
  have hgrowth : 2 * (cost + 1) ≤ lmGrowthGain n start := by
    apply (Nat.le_div_iff_mul_le hdiv).2
    dsimp [start, lm44CarrierStart, div, lmGrowthGain]
    have hbase := le_max_left
      (2 * lmGrowthDivisor n * (lm44CarrierCost n + 1))
      (lm311AdaptiveSeed d)
    dsimp [cost]
    nlinarith
  have hexp := two_lmGrowthGain_le_expansion hn hd hcut hstart
  have hreal : (cost : ℝ) ≤
      (expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) start *
        (start : ℝ)) / 4 := by
    have hgrowthReal : ((2 * (cost + 1) : ℕ) : ℝ) ≤
        (lmGrowthGain n start : ℝ) := by exact_mod_cast hgrowth
    push_cast at hexp hgrowthReal
    nlinarith
  dsimp [lm311AdaptiveGain]
  exact Nat.le_floor hreal

theorem lm44CarrierCost_le_adaptiveGain_curve {n d i : ℕ}
    (hn : 32 ≤ n) (hd : 1 ≤ d) (hstart : lm44CarrierStart n d ≤ n) :
    lm44CarrierCost n ≤ lm311AdaptiveGain d
      (lm311AdaptiveCurve d (lm44CarrierStart n d) i) := by
  have hcost := lm44CarrierCost_le_adaptiveGain hn hd hstart
  have hseed : lm311AdaptiveSeed d ≤ lm44CarrierStart n d := le_max_right _ _
  have hcut : (d : ℝ) / 128 ≤ (lm44CarrierStart n d : ℝ) :=
    (lm311AdaptiveSeed_cutoff d).trans (by exact_mod_cast hseed)
  exact hcost.trans (lm311AdaptiveGain_mono_above hd hcut
    (lm311AdaptiveCurve_start_le d (lm44CarrierStart n d) i))

private theorem lm44Combined_rate {n d D start i s cost : ℕ}
    (b : LM44LM311Bounds n d D)
    (hstartCut : (d : ℝ) / 128 ≤ (start : ℝ))
    (hi : i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
    (hlocal : i < Parameters.lm311AdaptiveRounds n →
      cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d start i))
    (hglobal : cost ≤
      lm44GlobalPhaseCost n D (Parameters.lm311LocalRadius n) i)
    (his : lm311CombinedGrowth n d start i ≤ s) (hsn : s ≤ n / 2) :
    (((lm311CombinedGain n d start i + cost : ℕ) : ℝ) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans b.degree_large
  by_cases hilocal : i < Parameters.lm311AdaptiveRounds n
  · rw [lm311CombinedGrowth, if_pos hilocal] at his
    rw [lm311CombinedGain, if_pos hilocal]
    exact lm311AdaptiveGain_add_cost_le_expansion hd1
      (hstartCut.trans (by exact_mod_cast
        lm311AdaptiveCurve_start_le d start i)) his (hlocal hilocal)
  · apply lm311CombinedGlobal_rate b.card_large hd1 (by omega)
      (hstartCut.trans (by exact_mod_cast
        (le_max_right (Parameters.lmExpansionOrder n ^ 4) start)))
      ((hglobal.trans (b.global_phase_cost i hi))) his hsn

/-
/-- Concrete k=4, one-protected-vertex Lemma 3.11 numerics for an arbitrary
target order `D`.  The schedules are the adaptive/global schedules already
used in `GrowthSchedule`; `LM44LM311Bounds` contains exactly the new static
and phase-cost estimates. -/
noncomputable def concreteLM44LM311Numerics {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    LM311Numerics (1 / 1024) ((1 / 64) * (d : ℝ)) n 4 d D (D ^ 2)
      (Parameters.lm311LocalRadius n) (lmGrowthRounds n) 1 := by
  let localRounds := Parameters.lm311AdaptiveRounds n
  let ell₀ := Parameters.lm311LocalRadius n
  let m := lmGrowthRounds n
  let rounds := localRounds + m
  let seed := lm311AdaptiveSeed d
  let carrier := lm44CarrierStart n d
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans b.degree_large
  have hseedCut : (d : ℝ) / 128 ≤ (seed : ℝ) := by
    simpa [seed] using lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : seed ≤ carrier := by
    exact le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (carrier : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hseedSources := lm311AdaptiveSeed_le_claim44_source_seeds b.degree_large
  have hlocalPos : 0 < localRounds := by
    let stages := Parameters.lm311AdaptiveStages n
    have hstages : 0 < stages := by simp [stages, Parameters.lm311AdaptiveStages]
    have hstrict := lm311AdaptiveTime_strictMono hstages
    simpa [localRounds, stages, Parameters.lm311AdaptiveRounds,
      Parameters.lm311AdaptiveTime] using hstrict
  have hmPos : 0 < m := by
    have hdiv := lmGrowthDivisor_pos (b.card_large.trans' (by omega))
    dsimp [m, lmGrowthRounds]
    positivity
  have hellPos : 0 < ell₀ := by
    have hlocal : localRounds + 1 ≤ ell₀ := by
      simpa [localRounds, ell₀] using b.local_radius
    omega
  have hcombinedWarmSeed : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n seed := b.warm_large.trans (le_max_left _ _)
  have hcombinedWarmCarrier : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n carrier := b.warm_large.trans (le_max_left _ _)
  have hcombinedCutSeed : (d : ℝ) / 128 ≤
      (lm311CombinedStart n seed : ℝ) :=
    hseedCut.trans (by exact_mod_cast
      (le_max_right (Parameters.lmExpansionOrder n ^ 4) seed))
  have hcombinedCutCarrier : (d : ℝ) / 128 ≤
      (lm311CombinedStart n carrier : ℝ) :=
    hcarrierCut.trans (by exact_mod_cast
      (le_max_right (Parameters.lmExpansionOrder n ^ 4) carrier))
  have hrootLocal {i : ℕ} (hi : i < localRounds) :
      lm44HighRootCost i ≤
        lm311AdaptiveGain d (lm311AdaptiveCurve d seed i) := by
    have hiell : i < ell₀ := by
      have hlocal : localRounds + 1 ≤ ell₀ := by
        simpa [localRounds, ell₀] using b.local_radius
      omega
    apply (show lm44HighRootCost i ≤ lm44LowRootCost D ell₀ i by
      simp [lm44HighRootCost, lm44LowRootCost, lm311HighFixedBudget, hiell]) |>.trans
    simpa [localRounds, ell₀, seed] using b.root_local_cost i hi
  have hreservoirLocal {i : ℕ} (hi : i < localRounds) :
      lm44ReservoirCost i ≤
        lm311AdaptiveGain d (lm311AdaptiveCurve d seed i) := by
    have hiell : i < ell₀ := by
      have hlocal : localRounds + 1 ≤ ell₀ := by
        simpa [localRounds, ell₀] using b.local_radius
      omega
    apply (show lm44ReservoirCost i ≤ lm44LowRootCost D ell₀ i by
      simp [lm44ReservoirCost, lm44LowRootCost, hiell]
      omega) |>.trans
    simpa [localRounds, ell₀, seed] using b.root_local_cost i hi
  have hcarrierLocal {i : ℕ} : lm44CarrierCost n ≤
      lm311AdaptiveGain d (lm311AdaptiveCurve d carrier i) := by
    exact lm44CarrierCost_le_adaptiveGain_curve b.card_large hd1
      (by simpa [carrier] using b.carrier_start_card)
  refine
    { k_pos := by omega
      four_le_d := (by norm_num [lm311DegreeThreshold] :
        4 ≤ lm311DegreeThreshold).trans b.degree_large
      D_pos := b.D_pos
      ell₀_pos := hellPos
      m_pos := hmPos
      Delta_eq := rfl
      highRounds := rounds
      highRootGrowth := lm311CombinedGrowth n d seed
      highRootGain := lm311CombinedGain n d seed
      highHubGrowth := lm311CombinedGrowth n d carrier
      highHubGain := lm311CombinedGain n d carrier
      high_root_start := by
        rw [lm311CombinedGrowth_zero hlocalPos]
        simpa [seed] using hseedSources.1
      high_hub_start := by
        rw [lm311CombinedGrowth_zero hlocalPos]
        simpa [carrier, m] using b.carrier_high_hub
      high_root_next := by
        intro i hi
        apply lm311Combined_next b.degree_large b.expansion_pos
        rfl
      high_hub_next := by
        intro i hi
        exact lm311Combined_next b.degree_large b.expansion_pos hcarrierSeed
      high_root_lower := by
        intro i hi
        rw [show ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      high_hub_lower := by
        intro i hi
        rw [show ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      high_root_rate := by
        intro i hi s his hsn
        apply lm44Combined_rate b hseedCut (by simpa [rounds, localRounds, m] using hi)
          (fun hilocal ↦ hrootLocal (by simpa [localRounds] using hilocal))
        · exact le_max_left _ _
        · exact his
        · exact hsn
      high_hub_rate := by
        intro i hi s his hsn
        apply lm44Combined_rate b hcarrierCut
          (by simpa [rounds, localRounds, m] using hi)
          (fun _ ↦ (le_max_left _ _).trans hcarrierLocal)
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact his
        · exact hsn
      high_root_half := by
        simpa [rounds, localRounds, m, seed] using
          lm311Combined_half b.card_large hcombinedWarmSeed
      high_hub_half := by
        simpa [rounds, localRounds, m, carrier] using
          lm311Combined_half b.card_large hcombinedWarmCarrier
      high_connector := by
        have hlocal := b.local_radius
        have hfit := b.local_fit
        dsimp [rounds, localRounds, ell₀, m] at hlocal hfit ⊢
        omega
      high_star_budget := by simpa [m] using b.high_star
      packing := by simpa [ell₀] using b.packing
      reservoirRounds := localRounds
      reservoirGrowth := lm311AdaptiveCurve d seed
      reservoirGain := fun i ↦ lm311AdaptiveGain d (lm311AdaptiveCurve d seed i)
      reservoir_radius := by simpa [localRounds, ell₀] using b.local_radius
      reservoir_start := by simpa [seed] using hseedSources.2.1
      reservoir_next := by intro i hi; exact (lm311AdaptiveCurve_succ d seed i).le
      reservoir_seed_lower := by
        intro i hi
        rw [show ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact hseedCut.trans (by exact_mod_cast lm311AdaptiveCurve_start_le d seed i)
      reservoir_rate := by
        intro i hi s his hsn
        exact lm311AdaptiveGain_add_cost_le_expansion hd1
          (hseedCut.trans (by exact_mod_cast lm311AdaptiveCurve_start_le d seed i))
          his (hreservoirLocal (by simpa [localRounds] using hi))
      reservoir_target := by
        apply b.delta_warm.trans
        simpa [localRounds, seed] using
          lm311AdaptiveCurve_reaches_warmTarget b.degree_large b.expansion_pos
      reservoir_half := b.reservoir_half
      connectRounds := rounds
      lowRootGrowth := lm311CombinedGrowth n d seed
      lowRootGain := lm311CombinedGain n d seed
      lowReservoirGrowth := if d - 1 ≤ D ^ 2 then
        lm311CombinedGrowth n d carrier else fun _ ↦ 0
      lowReservoirGain := if d - 1 ≤ D ^ 2 then
        lm311CombinedGain n d carrier else fun _ ↦ 0
      low_root_start := by
        rw [lm311CombinedGrowth_zero hlocalPos]
        simpa [seed] using hseedSources.2.2
      low_reservoir_start := by
        by_cases hcase : d - 1 ≤ D ^ 2
        · rw [if_pos hcase, lm311CombinedGrowth_zero hlocalPos]
          simpa [carrier] using b.carrier_delta hcase
        · simp [hcase]
      low_root_next := by
        intro i hi
        apply lm311Combined_next b.degree_large b.expansion_pos
        rfl
      low_reservoir_next := by
        intro hcase i hi
        rw [if_pos hcase, if_pos hcase]
        exact lm311Combined_next b.degree_large b.expansion_pos hcarrierSeed
      low_root_lower := by
        intro i hi
        rw [show ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      low_reservoir_lower := by
        intro hcase i hi
        rw [if_pos hcase]
        rw [show ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      low_root_rate := by
        intro i hi s his hsn
        apply lm44Combined_rate b hseedCut (by simpa [rounds, localRounds, m] using hi)
        · intro hilocal
          simpa [localRounds, ell₀, seed] using
            b.root_local_cost i (by simpa [localRounds] using hilocal)
        · exact (le_max_right _ _).trans (le_max_right _ _)
        · exact his
        · exact hsn
      low_reservoir_rate := by
        intro hcase i hi s his hsn
        rw [if_pos hcase, if_pos hcase]
        apply lm44Combined_rate b hcarrierCut
          (by simpa [rounds, localRounds, m] using hi)
        · intro hilocal
          have hiell : i < ell₀ := by
            have hlocal := b.local_radius
            dsimp [localRounds, ell₀] at hlocal
            omega
          have hfixed : lm44LowReservoirCost n D ell₀ i =
              lm44LowCarrierCost n := by simp [lm44LowReservoirCost, hiell]
          rw [hfixed]
          exact (le_max_right _ _).trans hcarrierLocal
        · exact (le_max_right _ _).trans (le_max_right _ _ |>.trans
            (le_max_right _ _))
        · exact his
        · exact hsn
      low_root_half := by
        simpa [rounds, localRounds, m, seed] using
          lm311Combined_half b.card_large hcombinedWarmSeed
      low_reservoir_half := by
        intro hcase
        rw [if_pos hcase]
        simpa [rounds, localRounds, m, carrier] using
          lm311Combined_half b.card_large hcombinedWarmCarrier
      low_connector := by
        have hlocal := b.local_radius
        have hfit := b.local_fit
        dsimp [rounds, localRounds, ell₀, m] at hlocal hfit ⊢
        omega
      attach_radius := by
        have hfit := b.local_fit
        dsimp [ell₀, m] at hfit ⊢
        omega
      low_star_budget := b.low_star }
-/

private structure LM44K4Rates (n d D : ℕ) : Prop where
  highRoot : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ∀ s : ℕ, lm311CombinedGrowth n d (lm311AdaptiveSeed d) i ≤ s →
      s ≤ n / 2 →
      (((lm311CombinedGain n d (lm311AdaptiveSeed d) i +
        lm44HighRootCost i : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  highHub : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ∀ s : ℕ, lm311CombinedGrowth n d (lm44CarrierStart n d) i ≤ s →
      s ≤ n / 2 →
      (((lm311CombinedGain n d (lm44CarrierStart n d) i +
        lm311HighCarrierBudget n 4 1 (3 * lmGrowthRounds n + 1) : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  reservoir : ∀ i < Parameters.lm311AdaptiveRounds n, ∀ s : ℕ,
    lm311AdaptiveCurve d (lm311AdaptiveSeed d) i ≤ s → s ≤ n / 2 →
      (((lm311AdaptiveGain d
          (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) +
        lm44ReservoirCost i : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  lowRoot : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ∀ s : ℕ, lm311CombinedGrowth n d (lm311AdaptiveSeed d) i ≤ s →
      s ≤ n / 2 →
      (((lm311CombinedGain n d (lm311AdaptiveSeed d) i +
        lm44LowRootCost D (Parameters.lm311LocalRadius n) i : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  lowReservoir : d - 1 ≤ D ^ 2 →
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n, ∀ s : ℕ,
    lm311CombinedGrowth n d (lm44CarrierStart n d) i ≤ s → s ≤ n / 2 →
      (((lm311CombinedGain n d (lm44CarrierStart n d) i +
        lm44LowReservoirCost n D (Parameters.lm311LocalRadius n) i : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))

private theorem lm44Adaptive_lt_local {n d D i : ℕ}
    (b : LM44LM311Bounds n d D)
    (hi : i < Parameters.lm311AdaptiveRounds n) :
    i < Parameters.lm311LocalRadius n := by
  have hlocal := b.local_radius
  omega

private theorem lm44K4_highRoot_rate_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      ∀ s : ℕ, lm311CombinedGrowth n d (lm311AdaptiveSeed d) i ≤ s →
        s ≤ n / 2 →
        (((lm311CombinedGain n d (lm311AdaptiveSeed d) i +
          lm44HighRootCost i : ℕ) : ℝ) ≤
          expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans b.degree_large
  have hseedCut := lm311AdaptiveSeed_cutoff d
  intro i hi s his hsn
  apply lm44Combined_rate b hseedCut hi
  · intro hilocal
    have hiell := lm44Adaptive_lt_local b hilocal
    exact (show lm44HighRootCost i ≤
        lm44LowRootCost D (Parameters.lm311LocalRadius n) i by
      simp [lm44HighRootCost, lm44LowRootCost, lm311HighFixedBudget, hiell]) |>.trans
      (b.root_local_cost i hilocal)
  · simp [lm44GlobalPhaseCost]
  · exact his
  · exact hsn

private theorem lm44K4_highHub_rate_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      ∀ s : ℕ, lm311CombinedGrowth n d (lm44CarrierStart n d) i ≤ s →
        s ≤ n / 2 →
        (((lm311CombinedGain n d (lm44CarrierStart n d) i +
          lm311HighCarrierBudget n 4 1 (3 * lmGrowthRounds n + 1) : ℕ) : ℝ) ≤
          expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans b.degree_large
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm44CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm44CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  intro i hi s his hsn
  apply lm44Combined_rate b hcarrierCut hi
  · intro _
    exact (le_max_left _ _).trans
      (lm44CarrierCost_le_adaptiveGain_curve b.card_large hd1
        b.carrier_start_card)
  · simp [lm44GlobalPhaseCost]
  · exact his
  · exact hsn

private theorem lm44K4_reservoir_rate_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    ∀ i < Parameters.lm311AdaptiveRounds n, ∀ s : ℕ,
      lm311AdaptiveCurve d (lm311AdaptiveSeed d) i ≤ s → s ≤ n / 2 →
        (((lm311AdaptiveGain d
            (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) +
          lm44ReservoirCost i : ℕ) : ℝ) ≤
          expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans b.degree_large
  have hseedCut := lm311AdaptiveSeed_cutoff d
  intro i hi s his hsn
  apply lm311AdaptiveGain_add_cost_le_expansion hd1
    (hseedCut.trans (by exact_mod_cast
      lm311AdaptiveCurve_start_le d (lm311AdaptiveSeed d) i)) his
  have hiell := lm44Adaptive_lt_local b hi
  exact (show lm44ReservoirCost i ≤
      lm44LowRootCost D (Parameters.lm311LocalRadius n) i by
    simp [lm44ReservoirCost, lm44LowRootCost, hiell]
    omega) |>.trans (b.root_local_cost i hi)

private theorem lm44K4_lowRoot_rate_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      ∀ s : ℕ, lm311CombinedGrowth n d (lm311AdaptiveSeed d) i ≤ s →
        s ≤ n / 2 →
        (((lm311CombinedGain n d (lm311AdaptiveSeed d) i +
          lm44LowRootCost D (Parameters.lm311LocalRadius n) i : ℕ) : ℝ) ≤
          expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hseedCut := lm311AdaptiveSeed_cutoff d
  intro i hi s his hsn
  apply lm44Combined_rate b hseedCut hi
  · exact fun hilocal ↦ b.root_local_cost i hilocal
  · simp [lm44GlobalPhaseCost]
  · exact his
  · exact hsn

private theorem lm44K4_lowReservoir_rate_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    d - 1 ≤ D ^ 2 →
      ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n, ∀ s : ℕ,
      lm311CombinedGrowth n d (lm44CarrierStart n d) i ≤ s → s ≤ n / 2 →
        (((lm311CombinedGain n d (lm44CarrierStart n d) i +
          lm44LowReservoirCost n D (Parameters.lm311LocalRadius n) i : ℕ) : ℝ) ≤
          expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans b.degree_large
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm44CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm44CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  intro _ i hi s his hsn
  apply lm44Combined_rate b hcarrierCut hi
  · intro hilocal
    have hiell := lm44Adaptive_lt_local b hilocal
    rw [lm44LowReservoirCost, if_pos hiell]
    simp only [add_zero]
    exact (le_max_right _ _).trans
      (lm44CarrierCost_le_adaptiveGain_curve b.card_large hd1
        b.carrier_start_card)
  · simp [lm44GlobalPhaseCost]
  · exact his
  · exact hsn

private theorem lm44K4Rates_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) : LM44K4Rates n d D :=
  ⟨lm44K4_highRoot_rate_of_bounds b,
    lm44K4_highHub_rate_of_bounds b,
    lm44K4_reservoir_rate_of_bounds b,
    lm44K4_lowRoot_rate_of_bounds b,
    lm44K4_lowReservoir_rate_of_bounds b⟩

private structure LM44K4Setup (n d D : ℕ) : Prop where
  ell_pos : 0 < Parameters.lm311LocalRadius n
  m_pos : 0 < lmGrowthRounds n
  local_pos : 0 < Parameters.lm311AdaptiveRounds n
  seed_sources :
    lm311AdaptiveSeed d ≤ lm311HighRootSeed d 4 1 ∧
      lm311AdaptiveSeed d ≤ lm311ReservoirSeed d 4 1 ∧
      lm311AdaptiveSeed d ≤ lm311LowRootSeed d 4 1
  carrier_high_hub : lm44CarrierStart n d ≤
    lm311HighHubSeed n d (D ^ 2) 4 1 (3 * lmGrowthRounds n + 1)
  carrier_delta : d - 1 ≤ D ^ 2 → lm44CarrierStart n d ≤ D ^ 2

private theorem lm44K4Setup_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) : LM44K4Setup n d D := by
  have hlocalPos : 0 < Parameters.lm311AdaptiveRounds n := by
    have hstages : 0 < Parameters.lm311AdaptiveStages n := by
      simp [Parameters.lm311AdaptiveStages]
    have hstrict := lm311AdaptiveTime_strictMono hstages
    simpa [Parameters.lm311AdaptiveRounds, Parameters.lm311AdaptiveTime] using hstrict
  exact
    { ell_pos := by
        have hlocal := b.local_radius
        omega
      m_pos := by
        have hdiv := lmGrowthDivisor_pos (b.card_large.trans' (by omega))
        simp only [gt_iff_lt]
        positivity
      local_pos := hlocalPos
      seed_sources := lm311AdaptiveSeed_le_claim44_source_seeds b.degree_large
      carrier_high_hub := b.carrier_high_hub
      carrier_delta := b.carrier_delta }

private structure LM44K4HighGeometry (n d D : ℕ) : Prop where
  root_start : lm311CombinedGrowth n d (lm311AdaptiveSeed d) 0 ≤
    lm311HighRootSeed d 4 1
  hub_start : lm311CombinedGrowth n d (lm44CarrierStart n d) 0 ≤
    lm311HighHubSeed n d (D ^ 2) 4 1 (3 * lmGrowthRounds n + 1)
  root_next : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm311CombinedGrowth n d (lm311AdaptiveSeed d) (i + 1) ≤
      lm311CombinedGrowth n d (lm311AdaptiveSeed d) i +
        lm311CombinedGain n d (lm311AdaptiveSeed d) i
  hub_next : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm311CombinedGrowth n d (lm44CarrierStart n d) (i + 1) ≤
      lm311CombinedGrowth n d (lm44CarrierStart n d) i +
        lm311CombinedGain n d (lm44CarrierStart n d) i
  root_lower : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311CombinedGrowth n d (lm311AdaptiveSeed d) i : ℝ)
  hub_lower : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311CombinedGrowth n d (lm44CarrierStart n d) i : ℝ)
  root_half : n / 2 + 1 ≤ lm311CombinedGrowth n d (lm311AdaptiveSeed d)
    (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  hub_half : n / 2 + 1 ≤ lm311CombinedGrowth n d (lm44CarrierStart n d)
    (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  high_connector : 2 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n + 1) <
    3 * lmGrowthRounds n + 1
  reservoir_lower : ∀ i < Parameters.lm311AdaptiveRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i : ℝ)
  reservoir_target : D ^ 2 ≤
    lm311AdaptiveCurve d (lm311AdaptiveSeed d) (Parameters.lm311AdaptiveRounds n)

private theorem lm44K4HighGeometry_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) (setup : LM44K4Setup n d D) :
    LM44K4HighGeometry n d D := by
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm44CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm44CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hwarmSeed : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm311AdaptiveSeed d) :=
    b.warm_large.trans (le_max_left _ _)
  have hwarmCarrier : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm44CarrierStart n d) :=
    b.warm_large.trans (le_max_left _ _)
  exact
    { root_start := by
        rw [lm311CombinedGrowth_zero setup.local_pos]
        exact setup.seed_sources.1
      hub_start := by
        rw [lm311CombinedGrowth_zero setup.local_pos]
        exact setup.carrier_high_hub
      root_next := fun _ _ ↦ lm311Combined_next b.degree_large b.expansion_pos le_rfl
      hub_next := fun _ _ ↦ lm311Combined_next b.degree_large b.expansion_pos hcarrierSeed
      root_lower := by
        intro i _
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      hub_lower := by
        intro i _
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      root_half := lm311Combined_half b.card_large hwarmSeed
      hub_half := lm311Combined_half b.card_large hwarmCarrier
      high_connector := by
        have hlocal := b.local_radius
        have hfit := b.local_fit
        omega
      reservoir_lower := by
        intro i _
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact hseedCut.trans (by exact_mod_cast
          lm311AdaptiveCurve_start_le d (lm311AdaptiveSeed d) i)
      reservoir_target := b.delta_warm.trans
        (lm311AdaptiveCurve_reaches_warmTarget
          b.degree_large b.expansion_pos) }

private structure LM44K4LowGeometry (n d D : ℕ) : Prop where
  root_start : lm311CombinedGrowth n d (lm311AdaptiveSeed d) 0 ≤
    lm311LowRootSeed d 4 1
  reservoir_start :
    (if d - 1 ≤ D ^ 2 then lm311CombinedGrowth n d (lm44CarrierStart n d)
      else fun _ ↦ 0) 0 ≤ D ^ 2
  reservoir_next : d - 1 ≤ D ^ 2 →
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      (if d - 1 ≤ D ^ 2 then lm311CombinedGrowth n d (lm44CarrierStart n d)
        else fun _ ↦ 0) (i + 1) ≤
      (if d - 1 ≤ D ^ 2 then lm311CombinedGrowth n d (lm44CarrierStart n d)
        else fun _ ↦ 0) i +
      (if d - 1 ≤ D ^ 2 then lm311CombinedGain n d (lm44CarrierStart n d)
        else fun _ ↦ 0) i
  reservoir_lower : d - 1 ≤ D ^ 2 →
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      ((1 / 64) * (d : ℝ)) / 2 ≤
      ((if d - 1 ≤ D ^ 2 then lm311CombinedGrowth n d (lm44CarrierStart n d)
        else fun _ ↦ 0) i : ℝ)
  reservoir_half : d - 1 ≤ D ^ 2 → n / 2 + 1 ≤
    (if d - 1 ≤ D ^ 2 then lm311CombinedGrowth n d (lm44CarrierStart n d)
      else fun _ ↦ 0) (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  low_connector : 2 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n) + 1 <
    3 * lmGrowthRounds n + 1
  attach_radius : 3 * lmGrowthRounds n + 2 * Parameters.lm311LocalRadius n ≤
    5 * lmGrowthRounds n

private theorem lm44K4LowGeometry_of_bounds {n d D : ℕ}
    (b : LM44LM311Bounds n d D) (setup : LM44K4Setup n d D) :
    LM44K4LowGeometry n d D := by
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm44CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm44CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hwarmCarrier : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm44CarrierStart n d) :=
    b.warm_large.trans (le_max_left _ _)
  exact
    { root_start := by
        rw [lm311CombinedGrowth_zero setup.local_pos]
        exact setup.seed_sources.2.2
      reservoir_start := by
        by_cases hcase : d - 1 ≤ D ^ 2
        · rw [if_pos hcase, lm311CombinedGrowth_zero setup.local_pos]
          exact setup.carrier_delta hcase
        · simp [hcase]
      reservoir_next := by
        intro hcase i _
        rw [if_pos hcase, if_pos hcase]
        exact lm311Combined_next b.degree_large b.expansion_pos hcarrierSeed
      reservoir_lower := by
        intro hcase i _
        rw [if_pos hcase]
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      reservoir_half := by
        intro hcase
        rw [if_pos hcase]
        exact lm311Combined_half b.card_large hwarmCarrier
      low_connector := by
        have hlocal := b.local_radius
        have hfit := b.local_fit
        omega
      attach_radius := by
        have hfit := b.local_fit
        omega }

/-- Concrete k=4, one-protected-vertex Lemma 3.11 numerics for an arbitrary
target order `D`.  All expensive rate and geometry proofs are packaged in
separate declarations so this final record assembly stays within the default
elaboration budget. -/
noncomputable def concreteLM44LM311Numerics {n d D : ℕ}
    (b : LM44LM311Bounds n d D) :
    LM311Numerics (1 / 1024) ((1 / 64) * (d : ℝ)) n 4 d D (D ^ 2)
      (Parameters.lm311LocalRadius n) (lmGrowthRounds n) 1 := by
  let setup := lm44K4Setup_of_bounds b
  let rates := lm44K4Rates_of_bounds b
  let high := lm44K4HighGeometry_of_bounds b setup
  let low := lm44K4LowGeometry_of_bounds b setup
  exact
    { k_pos := by omega
      four_le_d := (by norm_num [lm311DegreeThreshold] :
        4 ≤ lm311DegreeThreshold).trans b.degree_large
      D_pos := b.D_pos
      ell₀_pos := setup.ell_pos
      m_pos := setup.m_pos
      Delta_eq := rfl
      highRounds := Parameters.lm311AdaptiveRounds n + lmGrowthRounds n
      highRootGrowth := lm311CombinedGrowth n d (lm311AdaptiveSeed d)
      highRootGain := lm311CombinedGain n d (lm311AdaptiveSeed d)
      highHubGrowth := lm311CombinedGrowth n d (lm44CarrierStart n d)
      highHubGain := lm311CombinedGain n d (lm44CarrierStart n d)
      high_root_start := high.root_start
      high_hub_start := high.hub_start
      high_root_next := high.root_next
      high_hub_next := high.hub_next
      high_root_lower := high.root_lower
      high_hub_lower := high.hub_lower
      high_root_rate := by
        simpa only [lm44HighRootCost, Nat.add_assoc] using rates.highRoot
      high_hub_rate := rates.highHub
      high_root_half := high.root_half
      high_hub_half := high.hub_half
      high_connector := high.high_connector
      high_star_budget := b.high_star
      packing := b.packing
      reservoirRounds := Parameters.lm311AdaptiveRounds n
      reservoirGrowth := lm311AdaptiveCurve d (lm311AdaptiveSeed d)
      reservoirGain := fun i ↦
        lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i)
      reservoir_radius := b.local_radius
      reservoir_start := setup.seed_sources.2.1
      reservoir_next := fun i _ ↦
        (lm311AdaptiveCurve_succ d (lm311AdaptiveSeed d) i).le
      reservoir_seed_lower := high.reservoir_lower
      reservoir_rate := by
        simpa only [lm44ReservoirCost, Nat.add_assoc] using rates.reservoir
      reservoir_target := high.reservoir_target
      reservoir_half := b.reservoir_half
      connectRounds := Parameters.lm311AdaptiveRounds n + lmGrowthRounds n
      lowRootGrowth := lm311CombinedGrowth n d (lm311AdaptiveSeed d)
      lowRootGain := lm311CombinedGain n d (lm311AdaptiveSeed d)
      lowReservoirGrowth := if d - 1 ≤ D ^ 2 then
        lm311CombinedGrowth n d (lm44CarrierStart n d) else fun _ ↦ 0
      lowReservoirGain := if d - 1 ≤ D ^ 2 then
        lm311CombinedGain n d (lm44CarrierStart n d) else fun _ ↦ 0
      low_root_start := low.root_start
      low_reservoir_start := low.reservoir_start
      low_root_next := high.root_next
      low_reservoir_next := low.reservoir_next
      low_root_lower := high.root_lower
      low_reservoir_lower := low.reservoir_lower
      low_root_rate := by
        simpa only [lm44LowRootCost, Nat.add_assoc] using rates.lowRoot
      low_reservoir_rate := by
        intro hcase
        rw [if_pos hcase, if_pos hcase]
        simpa only [lm44LowReservoirCost, lm44LowCarrierCost, Nat.add_assoc] using
          rates.lowReservoir hcase
      low_root_half := high.root_half
      low_reservoir_half := low.reservoir_half
      low_connector := low.low_connector
      attach_radius := low.attach_radius
      low_star_budget := b.low_star }

end Erdos63

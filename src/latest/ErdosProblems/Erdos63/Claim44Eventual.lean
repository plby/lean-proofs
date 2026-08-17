/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Claim44Numerics
import ErdosProblems.Erdos63.Claim43Numerics
import ErdosProblems.Erdos63.RobustNumerics

/-!
# Eventual numerical bounds for Liu--Montgomery Claim 4.4

This file isolates the ambient bookkeeping in the canonical Claim 4.4
specialization.  In particular, the density inequalities are reduced to the
two genuinely asymptotic estimates for the forbidden ball.
-/

open Filter

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The graph-free fields of the canonical Claim 4.4 scale which do not
belong to either Lemma 3.11 certificate or to the Lemma 4.2 connector. -/
structure LM43Claim44OuterBounds (N d : ℕ) : Prop where
  deleted_le : lm43DeletionCap N d ≤ 10 * lm43TargetOrder N d
  seed_bound :
    lm44SeedCap (lm43ProtectedCap N d) (lm43R N d)
        (lm43MaxRadius N d) ≤
      lm43Claim44SeedCap N d
  ball_bound :
    lm44BallCap (lm43ProtectedCap N d) (lm43R N d)
        (lm43MaxRadius N d) (lm43HighCutoff N d)
          (lm43Separation N d) ≤
      lm43Claim44BallCap N d
  deletion_proper :
    lm43DeletionCap N d + lm43Claim44BallCap N d < N
  initial_density : ∀ u ≤ lm43DeletionCap N d,
    lm43InitialDegree N d * (N - u) ≤
      ((N - u) - 100 * lm43TargetOrder N d ^ 2) * (d - d / 2)
  retained_density :
    (8 * lm43CoreDegree N d) * N +
        2 * (lm43Claim44BallCap N d * lm43HighCutoff N d) ≤
      lm43InitialDegree N d * (N - lm43DeletionCap N d)
  core_large : 32 ≤ lm43CoreDegree N d
  target_pos : 0 < lm43TargetOrder N d
  totalRadius_pos : 1 ≤ lm43TotalRadius N d
  maxRadius_le : lm43MaxRadius N d ≤ lm43TotalRadius N d
  star_budget :
    lm43TargetOrder N d + lm43Claim44StarBudget N d ≤
      lm43HighCutoff N d
  radius_bounds : ∀ n', lm43CoreDegree N d < n' → n' ≤ N →
    lm43MinRadius N d ≤ 5 * lmGrowthRounds n' ∧
      5 * lmGrowthRounds n' ≤ lm43MaxRadius N d

theorem lm43_claim44_seed_exact (N d : ℕ) :
    lm44SeedCap (lm43ProtectedCap N d) (lm43R N d)
        (lm43MaxRadius N d) =
      lm43Claim44SeedCap N d := by
  rfl

theorem lm43_claim44_ball_exact (N d : ℕ) :
    lm44BallCap (lm43ProtectedCap N d) (lm43R N d)
        (lm43MaxRadius N d) (lm43HighCutoff N d)
          (lm43Separation N d) =
      lm43Claim44BallCap N d := by
  rfl

/-! ## The strengthened local k=4 adaptive estimate -/

/-- The absolute degree threshold used by the adaptive clock has enough
slack for the `k = 4` deficient-root barrier.  This is the source-local
counterpart of `lm311AdaptiveCost_le_gain`, whose smaller coefficient is
specialized to `k = 2`. -/
theorem lm44AdaptiveCost_le_gain {d i : ℕ}
    (hd : lm311DegreeThreshold ≤ d) :
    18 * i + 127 ≤
      lm311AdaptiveGain d
        (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) := by
  let j := lm311AdaptiveStageAt i
  let base := 8 ^ j * lm311AdaptiveSeed d
  let block := Parameters.lm311AdaptiveBlock j
  have htime := lm311AdaptiveTime_stageAt_le i
  have hnext := lt_lm311AdaptiveTime_stageAt_succ i
  have hcheckpoint := lm311AdaptiveCurve_checkpoint (d := d) (j := j) hd
  have hcurveTime :
      lm311AdaptiveCurve d (lm311AdaptiveSeed d)
          (Parameters.lm311AdaptiveTime j) ≤
        lm311AdaptiveCurve d (lm311AdaptiveSeed d) i :=
    lm311AdaptiveCurve_mono d (lm311AdaptiveSeed d) htime
  have hbaseCurve : base ≤
      lm311AdaptiveCurve d (lm311AdaptiveSeed d) i :=
    hcheckpoint.trans hcurveTime
  have hd1 : 1 ≤ d :=
    (by norm_num [lm311DegreeThreshold] : 1 ≤ lm311DegreeThreshold).trans hd
  have hcutBase : (d : ℝ) / 128 ≤ (base : ℝ) := by
    have hseedCut := lm311AdaptiveSeed_cutoff d
    have hseedBase : lm311AdaptiveSeed d ≤ base := by
      dsimp [base]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact hseedCut.trans (by exact_mod_cast hseedBase)
  have hgainMono : lm311AdaptiveGain d base ≤
      lm311AdaptiveGain d
        (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) :=
    lm311AdaptiveGain_mono_above hd1 hcutBase hbaseCurve
  have hbaseGain := lm311AdaptiveGain_stage_lower (d := d) (j := j) hd
  have htimeUpper := Parameters.lm311AdaptiveTime_le (j + 1)
  have hiUpper : i ≤ 917504 * (j + 1) * (j + 3) ^ 2 := by
    change i < Parameters.lm311AdaptiveTime (j + 1) at hnext
    exact hnext.le.trans htimeUpper
  have hcostUpper : 18 * i + 127 ≤ 16515199 * (j + 3) ^ 3 := by
    have hprod : (j + 1) * (j + 3) ^ 2 ≤ (j + 3) ^ 3 := by
      calc
        (j + 1) * (j + 3) ^ 2 ≤ (j + 3) * (j + 3) ^ 2 := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = (j + 3) ^ 3 := by ring
    have hcubic : 1 ≤ (j + 3) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hscaled :
        18 * (917504 * ((j + 1) * (j + 3) ^ 2)) ≤
          18 * (917504 * (j + 3) ^ 3) := by
      gcongr
    have hconstant : 127 ≤ 127 * (j + 3) ^ 3 := by
      simpa only [mul_one] using Nat.mul_le_mul_left 127 hcubic
    calc
      18 * i + 127 ≤
          18 * (917504 * (j + 1) * (j + 3) ^ 2) + 127 := by omega
      _ ≤ 18 * (917504 * (j + 3) ^ 3) + 127 := by
        exact Nat.add_le_add_right (by simpa [mul_assoc] using hscaled) 127
      _ ≤ 18 * (917504 * (j + 3) ^ 3) +
          127 * (j + 3) ^ 3 := Nat.add_le_add_left hconstant _
      _ = 16515199 * (j + 3) ^ 3 := by ring
  have hfifth : (j + 3) ^ 5 ≤ 32 * 8 ^ (j + 1) := by
    let t := j + 1
    change (t + 2) ^ 5 ≤ 32 * 8 ^ t
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [pow_succ]
        have hpoly : (t + 3) ^ 5 ≤ 8 * (t + 2) ^ 5 := by
          calc
            (t + 3) ^ 5 ≤ (t + 3) ^ 5 +
                (7 * t ^ 5 + 65 * t ^ 4 + 230 * t ^ 3 +
                  370 * t ^ 2 + 235 * t + 13) := Nat.le_add_right _ _
            _ = 8 * (t + 2) ^ 5 := by ring
        calc
          (t + 3) ^ 5 ≤ 8 * (t + 2) ^ 5 := hpoly
          _ ≤ 8 * (32 * 8 ^ t) := Nat.mul_le_mul_left 8 ih
          _ = 32 * (8 ^ t * 8) := by ring
  have hblockCost : block * (18 * i + 127) ≤ base := by
    have hseed := lm311AdaptiveSeed_large hd
    calc
      block * (18 * i + 127)
          ≤ (65536 * (j + 3) ^ 2) *
              (16515199 * (j + 3) ^ 3) := by
            dsimp [block, Parameters.lm311AdaptiveBlock]
            gcongr <;> omega
      _ = (65536 * 16515199) * (j + 3) ^ 5 := by ring
      _ ≤ (65536 * 16515199) * (32 * 8 ^ (j + 1)) := by gcongr
      _ ≤ 8 ^ j * 2 ^ 53 := by
        rw [pow_succ]
        have hcoeff : (65536 * 16515199) * (32 * 8) ≤ 2 ^ 53 := by
          norm_num
        calc
          (65536 * 16515199) * (32 * (8 ^ j * 8)) =
              8 ^ j * ((65536 * 16515199) * (32 * 8)) := by ring
          _ ≤ 8 ^ j * 2 ^ 53 := Nat.mul_le_mul_left _ hcoeff
      _ ≤ 8 ^ j * lm311AdaptiveSeed d := Nat.mul_le_mul_left _ hseed
      _ = base := by rfl
  have hcostDiv : 18 * i + 127 ≤ base / block :=
    (Nat.le_div_iff_mul_le (lm311AdaptiveBlock_pos j)).2 <| by
      simpa [mul_comm] using hblockCost
  exact hcostDiv.trans hbaseGain |>.trans hgainMono

/-- During the adaptive phase the late `D²` contact term is absent, so the
literal deficient-root cost is covered by the strengthened adaptive gain. -/
theorem lm44LowRootCost_le_adaptiveGain {n d D i : ℕ}
    (hd : lm311DegreeThreshold ≤ d)
    (hi : i < Parameters.lm311AdaptiveRounds n)
    (hlocal : Parameters.lm311AdaptiveRounds n + 1 ≤
      Parameters.lm311LocalRadius n) :
    lm44LowRootCost D (Parameters.lm311LocalRadius n) i ≤
      lm311AdaptiveGain d
        (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) := by
  have hiell : i < Parameters.lm311LocalRadius n := by omega
  rw [lm44LowRootCost, if_pos hiell]
  norm_num
  have hgain := lm44AdaptiveCost_le_gain (d := d) (i := i) hd
  omega

/-! ## Pointwise assembly of the two Lemma 3.11 certificates -/

/-- The k=4 carrier is at most four copies of the already-normalized k=2
carrier.  This comparison lets the standard eventual scale pay the new
carrier seed without duplicating its logarithmic calculation. -/
theorem lm44CarrierCost_le_four_lm311CarrierCost (n : ℕ) :
    lm44CarrierCost n ≤ 4 * lm311CarrierCost n := by
  rw [lm44CarrierCost]
  apply max_le
  · simp only [lm311HighCarrierBudget, lm311HighFixedBudget,
      lm311CarrierCost]
    omega
  · simp only [lm44LowCarrierCost, lm311CarrierCost]
    omega

/-- Ambient, degree-free estimates sufficient for the Claim 4.4 k=4
Lemma 3.11 call at target order `D`. -/
structure LM44LM311AmbientBounds (n D : ℕ) : Prop where
  standard : LM311ScaleBounds n
  D_pos : 0 < D
  delta_warm : D ^ 2 ≤ Parameters.lmExpansionOrder n ^ 4
  carrier_room :
    512 * Parameters.lmExpansionOrder n + 128 ≤ D ^ 2
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

private theorem lm44CarrierBase_le_four_expansion {n : ℕ}
    (S : LM311ScaleBounds n) :
    2 * lmGrowthDivisor n * (lm44CarrierCost n + 1) ≤
      4 * Parameters.lmExpansionOrder n := by
  have hcost := lm44CarrierCost_le_four_lm311CarrierCost n
  have hone : lm44CarrierCost n + 1 ≤ 4 * (lm311CarrierCost n + 1) := by
    omega
  calc
    2 * lmGrowthDivisor n * (lm44CarrierCost n + 1)
        ≤ 2 * lmGrowthDivisor n * (4 * (lm311CarrierCost n + 1)) := by
          gcongr
    _ = 4 * (2 * lmGrowthDivisor n * (lm311CarrierCost n + 1)) := by ring
    _ ≤ 4 * Parameters.lmExpansionOrder n := Nat.mul_le_mul_left 4 S.carrier_base

private theorem lm44CarrierFacts_of_ambient {n d D : ℕ}
    (A : LM44LM311AmbientBounds n D)
    (hd : lm311DegreeThreshold ≤ d) (hdn : d ≤ n) :
    lm44CarrierStart n d ≤ n ∧
      lm44CarrierStart n d ≤
        lm311HighHubSeed n d (D ^ 2) 4 1 (3 * lmGrowthRounds n + 1) ∧
      (d - 1 ≤ D ^ 2 → lm44CarrierStart n d ≤ D ^ 2) := by
  let E := Parameters.lmExpansionOrder n
  let seed := lm311AdaptiveSeed d
  let carrier := lm44CarrierCost n
  let start := lm44CarrierStart n d
  let hub := lm311HighCarrierBudget n 4 1 (3 * lmGrowthRounds n + 1)
  have hEpos : 0 < E := by simpa [E] using A.standard.expansion_pos
  have hbase : 2 * lmGrowthDivisor n * (carrier + 1) ≤ 4 * E := by
    simpa [carrier, E] using lm44CarrierBase_le_four_expansion A.standard
  have hgenericCost : lm311CarrierCost n ≤ E := by
    have hdiv : 0 < lmGrowthDivisor n :=
      lmGrowthDivisor_pos (A.standard.card_large.trans' (by omega))
    have hfactor : 2 * lmGrowthDivisor n * (lm311CarrierCost n + 1) ≥
        lm311CarrierCost n := by
      nlinarith
    exact hfactor.trans A.standard.carrier_base
  have hcarrier : carrier ≤ 4 * E := by
    have hcost : carrier ≤ 4 * lm311CarrierCost n := by
      simpa [carrier] using lm44CarrierCost_le_four_lm311CarrierCost n
    exact hcost.trans (Nat.mul_le_mul_left 4 hgenericCost)
  have hhubCarrier : hub ≤ carrier := by
    dsimp [hub, carrier, lm44CarrierCost]
    exact le_max_left _ _
  have hhub : hub ≤ 4 * E := hhubCarrier.trans hcarrier
  have hseedD : 64 * seed ≤ d := by
    have hmod := Nat.mod_lt d (by norm_num : 0 < 128)
    have hdecomp := Nat.div_add_mod d 128
    dsimp [seed, lm311AdaptiveSeed]
    dsimp [lm311DegreeThreshold] at hd
    omega
  have hfourE : 4 * E ≤ E ^ 2 := by
    have hlarge : 4 ≤ E := by
      have hroom := A.carrier_room
      by_contra h
      have : E ≤ 3 := by omega
      have hbad : 512 * E + 128 ≤ E ^ 4 := hroom.trans A.delta_warm
      have himpossible : ∀ t : ℕ, t ≤ 3 → ¬(512 * t + 128 ≤ t ^ 4) := by
        intro t ht hle
        interval_cases t <;> norm_num at hle
      exact (himpossible E this) hbad
    nlinarith
  have hEsqN : E ^ 2 ≤ n := by
    exact A.standard.reservoir_half.trans (by
      have := A.standard.card_large
      omega)
  have hseedN : seed ≤ n := by
    have : seed ≤ d := by omega
    exact this.trans hdn
  have hstartN : start ≤ n := by
    dsimp [start, lm44CarrierStart]
    apply max_le
    · exact hbase.trans (hfourE.trans hEsqN)
    · exact hseedN
  have heighth : 8 * E ≤ D ^ 2 := by
    have := A.carrier_room
    omega
  have hbaseHub :
      2 * lmGrowthDivisor n * (carrier + 1) + hub ≤ D ^ 2 := by
    have := Nat.add_le_add hbase hhub
    omega
  have hseedHub : seed + hub ≤ max (d - 1) (D ^ 2) := by
    by_cases hlow : d - 1 ≤ D ^ 2
    · have : seed + hub ≤ D ^ 2 := by
        have hroom := A.carrier_room
        omega
      exact this.trans (le_max_right _ _)
    · have : seed + hub ≤ d - 1 := by
        have hroom := A.carrier_room
        omega
      exact this.trans (le_max_left _ _)
  have hstartHub : start + hub ≤ max (d - 1) (D ^ 2) := by
    dsimp [start, lm44CarrierStart]
    simpa only [max_add_add_right] using
      max_le (hbaseHub.trans (le_max_right _ _)) hseedHub
  have hhubStart : start ≤
      lm311HighHubSeed n d (D ^ 2) 4 1 (3 * lmGrowthRounds n + 1) := by
    dsimp [lm311HighHubSeed]
    exact Nat.le_sub_of_add_le (by simpa [hub] using hstartHub)
  have hstartDelta (hlow : d - 1 ≤ D ^ 2) : start ≤ D ^ 2 := by
    dsimp [start, lm44CarrierStart]
    apply max_le
    · exact hbase.trans (by omega)
    · have hroom := A.carrier_room
      omega
  exact ⟨hstartN, hhubStart, hstartDelta⟩

/-- Assemble the complete static `LM44LM311Bounds` record from degree-free
ambient estimates.  Uniformity in `d` is explicit. -/
theorem lm44LM311Bounds_of_ambient {n d D : ℕ}
    (A : LM44LM311AmbientBounds n D)
    (hd : lm311DegreeThreshold ≤ d) (hdn : d ≤ n) :
    LM44LM311Bounds n d D := by
  have hcarrier := lm44CarrierFacts_of_ambient A hd hdn
  exact
    { card_large := A.standard.card_large
      degree_large := hd
      degree_le_card := hdn
      expansion_pos := A.standard.expansion_pos
      local_radius := A.standard.local_radius
      local_fit := A.standard.local_fit
      warm_large := A.standard.warm_large
      D_pos := A.D_pos
      delta_warm := A.delta_warm
      carrier_start_card := hcarrier.1
      carrier_high_hub := hcarrier.2.1
      carrier_delta := hcarrier.2.2
      root_local_cost := by
        intro i hi
        exact lm44LowRootCost_le_adaptiveGain hd hi A.standard.local_radius
      global_phase_cost := A.global_phase_cost
      packing := A.packing
      reservoir_half := A.reservoir_half
      high_star := A.high_star
      low_star := A.low_star }

/-! ## The largest target: packing -/

/-- The packing term for the larger Claim 4.4 target
`D = (5 * lmGrowthRounds n)^5` is still `n ^ o(1)`. -/
theorem eventually_lm44_packing_five :
    ∀ᶠ n : ℕ in atTop,
      let R := 5 * lmGrowthRounds n
      let D := R ^ 5
      (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
          (D ^ 2 + 1) ^ (10 * Parameters.lm311LocalRadius n) <
        n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4) := by
  let C : ℝ := 553020
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards
      [eventually_ge_atTop (1 : ℕ),
        hlog.eventually (eventually_ge_atTop (2 : ℝ)),
        hlog.eventually (eventually_ge_atTop (C ^ 10 + 1)),
        hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
        Parameters.eventually_const_mul_log_log_pow_le_log 2700 6]
      with n hn hLtwo hLlarge hllone hsmall
  let L := Real.log (n : ℝ)
  let ll := Real.log L
  let R := 5 * lmGrowthRounds n
  let D := R ^ 5
  let ell₀ := Parameters.lm311LocalRadius n
  let girth := lm311GirthBudget n
  let factor := 4 ^ 2 + (4 + girth + 1)
  let base := D ^ 2 + 1
  let exponent := 10 * ell₀
  let tail := 2 * 4 ^ 2 + girth + 1 + 4
  have hLone : 1 ≤ L := hLtwo.trans' (by norm_num)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hll0 : 0 ≤ ll := zero_le_one.trans hllone
  have hq : (lmGrowthDenominator n : ℝ) ≤ 9217 * L ^ 2 := by
    have hlt : (lmGrowthDenominator n : ℝ) < 9216 * L ^ 2 + 1 := by
      simpa [lmGrowthDenominator, L] using
        (Nat.ceil_lt_add_one (by positivity : 0 ≤ 9216 * L ^ 2))
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hLone
    linarith
  have hk : ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 3 * L := by
    have hlogNat := Parameters.natLog_two_le_two_log hn
    change (Nat.log 2 n : ℝ) ≤ 2 * L at hlogNat
    linarith
  have hR : (R : ℝ) ≤ C * L ^ 3 := by
    dsimp [R, lmGrowthRounds, lmGrowthDivisor, C]
    push_cast
    change 5 * (2 * (2 * (lmGrowthDenominator n : ℝ)) *
      ((Nat.log 2 n : ℝ) + 1)) ≤ 553020 * L ^ 3
    calc
      5 * (2 * (2 * (lmGrowthDenominator n : ℝ)) *
            ((Nat.log 2 n : ℝ) + 1)) =
          (20 : ℝ) * (lmGrowthDenominator n : ℝ) *
            ((Nat.log 2 n : ℝ) + 1) := by ring
      _ ≤ 20 * (9217 * L ^ 2) * (3 * L) := by gcongr
      _ = 553020 * L ^ 3 := by ring
  have hRpow : (D : ℝ) ^ 2 ≤ C ^ 10 * L ^ 30 := by
    dsimp [D]
    push_cast
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg R) hR 10
    calc
      ((R : ℝ) ^ 5) ^ 2 = (R : ℝ) ^ 10 := by ring
      _ ≤ (C * L ^ 3) ^ 10 := hp
      _ = C ^ 10 * L ^ 30 := by ring
  have hbase : (base : ℝ) ≤ L ^ 33 := by
    have hbase0 : (base : ℝ) ≤ (C ^ 10 + 1) * L ^ 30 := by
      dsimp [base]
      push_cast
      have hL30one : 1 ≤ L ^ 30 := one_le_pow₀ hLone
      nlinarith
    have hcoeff : C ^ 10 + 1 ≤ L ^ 3 := by
      exact hLlarge.trans (by
        simpa only [pow_one] using pow_le_pow_right₀ hLone (by omega : 1 ≤ 3))
    calc
      (base : ℝ) ≤ (C ^ 10 + 1) * L ^ 30 := hbase0
      _ ≤ L ^ 3 * L ^ 30 :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hL0 30)
      _ = L ^ 33 := by ring
  have hbasePos : (0 : ℝ) < (base : ℝ) := by
    exact_mod_cast (by dsimp [base]; omega : 0 < base)
  have hlogBase : Real.log (base : ℝ) ≤ 33 * ll := by
    calc
      Real.log (base : ℝ) ≤ Real.log (L ^ 33) :=
        Real.log_le_log hbasePos hbase
      _ = 33 * ll := by simp [ll, Real.log_pow]
  have hellBounds := Parameters.lm311LocalRadius_bounds (n := n) (by
    have hll5 : 1 ≤ ll ^ 5 := one_le_pow₀ hllone
    change 1 ≤ 2 * ll ^ 5
    nlinarith)
  have hexponent : (exponent : ℝ) ≤ 40 * ll ^ 5 := by
    dsimp [exponent]
    push_cast
    change 10 * (ell₀ : ℝ) ≤ 40 * ll ^ 5
    have hlocal : (ell₀ : ℝ) ≤ 4 * ll ^ 5 := by
      simpa [ell₀, ll, L] using hellBounds.2
    nlinarith only [hlocal]
  have hgirth : (girth : ℝ) ≤ 4 * L + 4 := by
    dsimp [girth, lm311GirthBudget]
    push_cast
    have hlogNat := Parameters.natLog_two_le_two_log hn
    change (Nat.log 2 n : ℝ) ≤ 2 * L at hlogNat
    linarith
  have hfactorBound : (factor : ℝ) ≤ L ^ 6 := by
    have hrough : (factor : ℝ) ≤ 20 * L := by
      dsimp [factor]
      push_cast
      nlinarith
    have hL5 : (20 : ℝ) ≤ L ^ 5 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLtwo 5
      norm_num at hp
      linarith
    calc
      (factor : ℝ) ≤ 20 * L := hrough
      _ ≤ L ^ 5 * L := mul_le_mul_of_nonneg_right hL5 hL0
      _ = L ^ 6 := by ring
  have hfactorPos : (0 : ℝ) < (factor : ℝ) := by
    exact_mod_cast (by dsimp [factor]; omega : 0 < factor)
  have hlogFactor : Real.log (factor : ℝ) ≤ 6 * ll := by
    calc
      Real.log (factor : ℝ) ≤ Real.log (L ^ 6) :=
        Real.log_le_log hfactorPos hfactorBound
      _ = 6 * ll := by simp [ll, Real.log_pow]
  have htailBound : (tail : ℝ) ≤ L ^ 6 := by
    have hrough : (tail : ℝ) ≤ 25 * L := by
      dsimp [tail]
      push_cast
      nlinarith
    have hL5 : (25 : ℝ) ≤ L ^ 5 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLtwo 5
      norm_num at hp
      linarith
    calc
      (tail : ℝ) ≤ 25 * L := hrough
      _ ≤ L ^ 5 * L := mul_le_mul_of_nonneg_right hL5 hL0
      _ = L ^ 6 := by ring
  have htailPos : (0 : ℝ) < (tail : ℝ) := by
    exact_mod_cast (by dsimp [tail]; omega : 0 < tail)
  have hlogTail : Real.log (tail : ℝ) ≤ 6 * ll := by
    calc
      Real.log (tail : ℝ) ≤ Real.log (L ^ 6) :=
        Real.log_le_log htailPos htailBound
      _ = 6 * ll := by simp [ll, Real.log_pow]
  have hll_le_six : ll ≤ ll ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hllone (by omega : 1 ≤ 6)
  have hsmall' : 2700 * ll ^ 6 ≤ L := by simpa [L, ll] using hsmall
  have hlogProduct :
      Real.log (((factor * base ^ exponent : ℕ) : ℝ)) ≤ L / 2 := by
    rw [Nat.cast_mul, Nat.cast_pow,
      Real.log_mul hfactorPos.ne' (pow_ne_zero _ hbasePos.ne'), Real.log_pow]
    calc
      Real.log (factor : ℝ) + (exponent : ℝ) * Real.log (base : ℝ)
          ≤ 6 * ll + (40 * ll ^ 5) * (33 * ll) := by gcongr
      _ ≤ 1350 * ll ^ 6 := by
        have := mul_le_mul_of_nonneg_left hll_le_six
          (by norm_num : (0 : ℝ) ≤ 6)
        nlinarith [pow_nonneg hll0 5]
      _ ≤ L / 2 := by linarith
  have hlogTailHalf : Real.log (tail : ℝ) ≤ L / 2 := by
    calc
      Real.log (tail : ℝ) ≤ 6 * ll := hlogTail
      _ ≤ 1350 * ll ^ 6 := by
        have := mul_le_mul_of_nonneg_left hll_le_six
          (by norm_num : (0 : ℝ) ≤ 6)
        nlinarith
      _ ≤ L / 2 := by linarith
  have hproductPos : (0 : ℝ) <
      ((factor * base ^ exponent : ℕ) : ℝ) := by positivity
  have hproductExp : ((factor * base ^ exponent : ℕ) : ℝ) ≤
      Real.exp (L / 2) := by
    calc
      ((factor * base ^ exponent : ℕ) : ℝ) =
          Real.exp (Real.log ((factor * base ^ exponent : ℕ) : ℝ)) := by
            rw [Real.exp_log hproductPos]
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hlogProduct
  have htailExp : (tail : ℝ) ≤ Real.exp (L / 2) := by
    calc
      (tail : ℝ) = Real.exp (Real.log (tail : ℝ)) := by
        rw [Real.exp_log htailPos]
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hlogTailHalf
  have hexpTwo : 2 < Real.exp (L / 2) := by
    have htwo : (2 : ℝ) < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    exact htwo.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hsumReal :
      ((factor * base ^ exponent : ℕ) : ℝ) + (tail : ℝ) < (n : ℝ) := by
    calc
      ((factor * base ^ exponent : ℕ) : ℝ) + (tail : ℝ)
          ≤ 2 * Real.exp (L / 2) := by linarith
      _ < Real.exp (L / 2) * Real.exp (L / 2) := by
        nlinarith [Real.exp_pos (L / 2)]
      _ = Real.exp L := by rw [← Real.exp_add]; congr 1 <;> ring
      _ = (n : ℝ) := by
        change Real.exp (Real.log (n : ℝ)) = (n : ℝ)
        rw [Real.exp_log]
        exact_mod_cast (show 0 < n by omega)
  have hsumNat : factor * base ^ exponent + tail < n := by
    exact_mod_cast hsumReal
  have hpacking : factor * base ^ exponent < n - tail :=
    Nat.lt_sub_of_add_lt hsumNat
  simpa [R, D, ell₀, girth, factor, base, exponent, tail] using hpacking

/-! ## A common polynomial envelope -/

/-- One static quantity dominating every phase-specific k=4 barrier. -/
noncomputable def lm44StaticCost (n D : ℕ) : ℕ :=
  18 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n) +
    lm44CarrierCost n + 16 * D ^ 2 + 127

theorem lm44GlobalPhaseCost_le_static {n D i : ℕ}
    (hi : i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n) :
    lm44GlobalPhaseCost n D (Parameters.lm311LocalRadius n) i ≤
      lm44StaticCost n D := by
  rw [lm44GlobalPhaseCost]
  simp only [max_le_iff]
  constructor
  · dsimp [lm44HighRootCost, lm311HighFixedBudget, lm44StaticCost]
    omega
  constructor
  · have hhub :
        lm311HighCarrierBudget n 4 1 (3 * lmGrowthRounds n + 1) ≤
          lm44CarrierCost n := by
      dsimp [lm44CarrierCost]
      exact le_max_left _ _
    exact hhub.trans (by dsimp [lm44StaticCost]; omega)
  constructor
  · dsimp [lm44ReservoirCost, lm44StaticCost]
    omega
  constructor
  · dsimp [lm44LowRootCost, lm44StaticCost]
    split <;> omega
  · have hcarrier : lm44LowCarrierCost n ≤ lm44CarrierCost n := by
      dsimp [lm44CarrierCost]
      exact le_max_right _ _
    dsimp [lm44LowReservoirCost, lm44StaticCost]
    split <;> omega

/-- The source girth budget fits in a single canonical growth clock. -/
theorem lm311GirthBudget_le_lmGrowthRounds {n : ℕ} (hn : 32 ≤ n) :
    lm311GirthBudget n ≤ lmGrowthRounds n := by
  let q := lmGrowthDivisor n
  let k := Nat.log 2 n
  have hq : 2 ≤ q := by
    dsimp [q, lmGrowthDivisor]
    have := lmGrowthDenominator_pos (hn.trans' (by omega))
    omega
  have hfour : 4 ≤ 2 * q := by omega
  have hmul : 4 * (k + 1) ≤ (2 * q) * (k + 1) :=
    Nat.mul_le_mul_right (k + 1) hfour
  calc
    lm311GirthBudget n = 2 * (k + 2) := by
      simp [lm311GirthBudget, k]
    _ ≤ 4 * (k + 1) := by omega
    _ ≤ (2 * q) * (k + 1) := hmul
    _ = lmGrowthRounds n := by simp [lmGrowthRounds, q, k]

/-- Both star inequalities hold for any power `D = R^p`, `p ≥ 3`, of the
source radius once the standard card bound is available. -/
theorem lm44_star_bounds_of_radius_power {n R D : ℕ}
    (hn : 32 ≤ n) (hR : R = 5 * lmGrowthRounds n)
    (hD : R ^ 3 ≤ D) (hDR : D ≤ D ^ 2) :
    D + 1 + lm311GirthBudget n + 4 +
          4 ^ 2 * (3 * lmGrowthRounds n + 1) + 4 ^ 2 * D ≤ D ^ 2 ∧
      D + 1 + lm311GirthBudget n + 4 + 4 ^ 2 * D ≤ D ^ 2 := by
  have hgirth := lm311GirthBudget_le_lmGrowthRounds hn
  have hmPos : 0 < lmGrowthRounds n := by
    unfold lmGrowthRounds
    exact Nat.mul_pos
      (Nat.mul_pos (by omega) (lmGrowthDivisor_pos (hn.trans' (by omega))))
      (by omega)
  have hm4 : 4 ≤ lmGrowthRounds n := by
    unfold lmGrowthRounds
    have hdenOne : 1 ≤ lmGrowthDenominator n :=
      lmGrowthDenominator_pos (hn.trans' (by omega))
    have hdivTwo : 2 ≤ lmGrowthDivisor n := by
      rw [lmGrowthDivisor]
      simpa only [mul_one] using Nat.mul_le_mul_left 2 hdenOne
    have hlog : 1 ≤ Nat.log 2 n + 1 := by omega
    calc
      4 = 2 * 2 * 1 := by norm_num
      _ ≤ 2 * lmGrowthDivisor n * 1 := by gcongr
      _ ≤ 2 * lmGrowthDivisor n * (Nat.log 2 n + 1) :=
        Nat.mul_le_mul_left _ hlog
  have hR20 : 20 ≤ R := by rw [hR]; omega
  have hmR : lmGrowthRounds n ≤ R := by simp [hR]; omega
  have hDlarge : 8000 ≤ D := by
    calc
      8000 = 20 ^ 3 := by norm_num
      _ ≤ R ^ 3 := Nat.pow_le_pow_left hR20 3
      _ ≤ D := hD
  have hRself : R ≤ R ^ 3 := by
    have hRone : 1 ≤ R := by omega
    calc
      R = R * 1 := by omega
      _ ≤ R * R ^ 2 := Nat.mul_le_mul_left R (Nat.one_le_pow 2 R hRone)
      _ = R ^ 3 := by ring
  have hmD : lmGrowthRounds n ≤ D := hmR.trans (hRself.trans hD)
  have hscaled : 67 * D ≤ D ^ 2 := by
    have hmul := Nat.mul_le_mul_right D (show 67 ≤ D by omega)
    simpa [pow_two, mul_comm] using hmul
  constructor <;> omega

/-- Package two already-verified collections of ambient fields.  Keeping
this record assembly separate prevents the asymptotic proof from spending
its elaboration budget normalizing a pair of large structures. -/
theorem lm44LM311AmbientBounds_pair_of_fields {n D₃ D₅ : ℕ}
    (S : LM311ScaleBounds n)
    (hD₃pos : 0 < D₃) (hD₅pos : 0 < D₅)
    (hdeltaThree : D₃ ^ 2 ≤ Parameters.lmExpansionOrder n ^ 4)
    (hdeltaFive : D₅ ^ 2 ≤ Parameters.lmExpansionOrder n ^ 4)
    (hcarrierThree : 512 * Parameters.lmExpansionOrder n + 128 ≤ D₃ ^ 2)
    (hcarrierFive : 512 * Parameters.lmExpansionOrder n + 128 ≤ D₅ ^ 2)
    (hglobalThree : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      lm44GlobalPhaseCost n D₃ (Parameters.lm311LocalRadius n) i ≤
        lmGrowthGain n (Parameters.lmExpansionOrder n ^ 4))
    (hglobalFive : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      lm44GlobalPhaseCost n D₅ (Parameters.lm311LocalRadius n) i ≤
        lmGrowthGain n (Parameters.lmExpansionOrder n ^ 4))
    (hpackingThree :
      (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
          (D₃ ^ 2 + 1) ^ (10 * Parameters.lm311LocalRadius n) <
        n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4))
    (hpackingFive :
      (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
          (D₅ ^ 2 + 1) ^ (10 * Parameters.lm311LocalRadius n) <
        n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4))
    (hreservoirThree : D₃ ^ 2 ≤ n / 2 + 1)
    (hreservoirFive : D₅ ^ 2 ≤ n / 2 + 1)
    (hhighThree : D₃ + 1 + lm311GirthBudget n + 4 +
      4 ^ 2 * (3 * lmGrowthRounds n + 1) + 4 ^ 2 * D₃ ≤ D₃ ^ 2)
    (hlowThree : D₃ + 1 + lm311GirthBudget n + 4 + 4 ^ 2 * D₃ ≤ D₃ ^ 2)
    (hhighFive : D₅ + 1 + lm311GirthBudget n + 4 +
      4 ^ 2 * (3 * lmGrowthRounds n + 1) + 4 ^ 2 * D₅ ≤ D₅ ^ 2)
    (hlowFive : D₅ + 1 + lm311GirthBudget n + 4 + 4 ^ 2 * D₅ ≤ D₅ ^ 2) :
    LM44LM311AmbientBounds n D₃ ∧ LM44LM311AmbientBounds n D₅ :=
  ⟨{ standard := S
     D_pos := hD₃pos
     delta_warm := hdeltaThree
     carrier_room := hcarrierThree
     global_phase_cost := hglobalThree
     packing := hpackingThree
     reservoir_half := hreservoirThree
     high_star := hhighThree
     low_star := hlowThree },
   { standard := S
     D_pos := hD₅pos
     delta_warm := hdeltaFive
     carrier_room := hcarrierFive
     global_phase_cost := hglobalFive
     packing := hpackingFive
     reservoir_half := hreservoirFive
     high_star := hhighFive
     low_star := hlowFive }⟩

/-- Both canonical Claim 4.4 target orders satisfy all degree-free Lemma
3.11 estimates eventually.  The fifth-power target dominates every upper
bound, while the cube target supplies the common carrier room. -/
theorem eventually_lm44LM311AmbientBounds :
    ∀ᶠ n : ℕ in atTop,
      let R := 5 * lmGrowthRounds n
      LM44LM311AmbientBounds n (R ^ 3) ∧
        LM44LM311AmbientBounds n (R ^ 5) := by
  let B : ℝ := 18434
  let M : ℝ := 110604
  let C : ℝ := 553020
  let P : ℝ :=
    18 * (2 + M) + 4 * (20 + 12 * M) + 16 * C ^ 10 + 127
  let Q : ℝ := P * B + C ^ 10 + 1000
  have hB0 : (0 : ℝ) ≤ B := by norm_num [B]
  have hC0 : (0 : ℝ) ≤ C := by norm_num [C]
  have hP0 : (0 : ℝ) ≤ P := by
    dsimp [P]
    positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hreservReal :=
    Parameters.eventually_const_mul_log_pow_le_self (2 * C ^ 10) 30
  have hreserv := tendsto_natCast_atTop_atTop.eventually hreservReal
  filter_upwards
      [eventually_lm311ScaleBounds, eventually_lm44_packing_five,
        Parameters.eventually_lm311LocalRadius_le_lmLogCubeCeil,
        hlog.eventually (eventually_ge_atTop Q), hreserv]
      with n S hpacking hlocalCube hLlarge hreservN
  let L := Real.log (n : ℝ)
  let E := Parameters.lmExpansionOrder n
  let ell := Parameters.lm311LocalRadius n
  let a := Parameters.lm311AdaptiveRounds n
  let m := lmGrowthRounds n
  let div := lmGrowthDivisor n
  let R := 5 * m
  let D₃ := R ^ 3
  let D₅ := R ^ 5
  have hQone : (1 : ℝ) ≤ Q := by
    dsimp [Q]
    nlinarith [mul_nonneg hP0 hB0, pow_nonneg hC0 10]
  have hLone : (1 : ℝ) ≤ L := hQone.trans hLlarge
  have hL0 : (0 : ℝ) ≤ L := zero_le_one.trans hLone
  have hq : (lmGrowthDenominator n : ℝ) ≤ 9217 * L ^ 2 := by
    have hlt : (lmGrowthDenominator n : ℝ) < 9216 * L ^ 2 + 1 := by
      simpa [lmGrowthDenominator, L] using
        (Nat.ceil_lt_add_one (by positivity : 0 ≤ 9216 * L ^ 2))
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hLone
    linarith
  have hdiv : (div : ℝ) ≤ B * L ^ 2 := by
    dsimp [div, lmGrowthDivisor, B]
    push_cast
    nlinarith
  have hdivPos : 0 < div :=
    lmGrowthDivisor_pos (S.card_large.trans' (by omega))
  have hmUpper : (m : ℝ) ≤ M * L ^ 3 := by
    let k := Nat.log 2 n
    have hpowNat : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hpowNat
    have hlogPow : (k : ℝ) * Real.log 2 ≤ L := by
      have h := Real.log_le_log
        (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hpowReal
      simpa [L, Real.log_pow] using h
    have hk : (k : ℝ) ≤ 2 * L := by
      have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hk1 : (k : ℝ) + 1 ≤ 3 * L := by linarith
    have hmul : (lmGrowthDenominator n : ℝ) * ((k : ℝ) + 1) ≤
        (9217 * L ^ 2) * (3 * L) := by
      exact mul_le_mul hq hk1 (by positivity) (by positivity)
    dsimp [m, lmGrowthRounds, div, lmGrowthDivisor, M]
    push_cast
    nlinarith
  have hlogCube : (Parameters.lmLogCubeCeil n : ℝ) ≤ 2 * L ^ 3 := by
    have hlt : (Parameters.lmLogCubeCeil n : ℝ) < L ^ 3 + 1 := by
      simpa [Parameters.lmLogCubeCeil, L] using
        (Nat.ceil_lt_add_one (by positivity : 0 ≤ L ^ 3))
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hLone
    linarith
  have hell : (ell : ℝ) ≤ 2 * L ^ 3 := by
    have hcast : (ell : ℝ) ≤ (Parameters.lmLogCubeCeil n : ℝ) := by
      exact_mod_cast hlocalCube
    exact hcast.trans hlogCube
  have ha : (a : ℝ) ≤ 2 * L ^ 3 := by
    have hanat : a ≤ ell := by
      have := S.local_radius
      omega
    have hcast : (a : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hanat
    exact hcast.trans hell
  have hElow : L ^ 10 ≤ (E : ℝ) := by
    simpa [L, E] using Parameters.lmExpansionOrder_lower n
  have hEup : (E : ℝ) ≤ 2 * L ^ 10 := by
    simpa [L, E] using
      Parameters.lmExpansionOrder_le_two_mul (one_le_pow₀ hLone)
  have hgirth : (lm311GirthBudget n : ℝ) ≤ 4 * L + 4 := by
    dsimp [lm311GirthBudget]
    push_cast
    have hnatlog := Parameters.natLog_two_le_two_log
      (show 1 ≤ n by omega)
    change (Nat.log 2 n : ℝ) ≤ 2 * L at hnatlog
    nlinarith only [hnatlog]
  have hRupper : (R : ℝ) ≤ C * L ^ 3 := by
    dsimp [R, m, lmGrowthRounds, lmGrowthDivisor, C]
    push_cast
    change
      5 * (2 * (2 * (lmGrowthDenominator n : ℝ)) *
          ((Nat.log 2 n : ℝ) + 1)) ≤ 553020 * L ^ 3
    calc
      5 * (2 * (2 * (lmGrowthDenominator n : ℝ)) *
          ((Nat.log 2 n : ℝ) + 1)) =
          (20 : ℝ) * (lmGrowthDenominator n : ℝ) *
            ((Nat.log 2 n : ℝ) + 1) := by ring
      _
          ≤ 20 * (9217 * L ^ 2) * (3 * L) := by
            gcongr
            have hnatlog := Parameters.natLog_two_le_two_log
              (show 1 ≤ n by omega)
            change (Nat.log 2 n : ℝ) ≤ 2 * L at hnatlog
            linarith
      _ = 553020 * L ^ 3 := by ring
  have hRlower : 2 * L ^ 2 ≤ (R : ℝ) := by
    have hden := lmGrowthDenominator_lower n
    have hden' : 9216 * L ^ 2 ≤ (lmGrowthDenominator n : ℝ) := by
      simpa [L] using hden
    dsimp [R, m, lmGrowthRounds, lmGrowthDivisor]
    push_cast
    change
      2 * L ^ 2 ≤ 5 * (2 * (2 * (lmGrowthDenominator n : ℝ)) *
        ((Nat.log 2 n : ℝ) + 1))
    calc
      2 * L ^ 2 ≤ 20 * (9216 * L ^ 2) * 1 := by
        nlinarith [pow_nonneg hL0 2]
      _ ≤ 20 * (lmGrowthDenominator n : ℝ) *
          ((Nat.log 2 n : ℝ) + 1) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hden' (by norm_num)
            · exact_mod_cast (show 1 ≤ Nat.log 2 n + 1 by omega)
            · positivity
            · positivity
      _ = 5 * (2 * (2 * (lmGrowthDenominator n : ℝ)) *
          ((Nat.log 2 n : ℝ) + 1)) := by ring
  have hRpos : 0 < R := by
    have : (0 : ℝ) < (R : ℝ) := by
      have hLpos : (0 : ℝ) < L := zero_lt_one.trans_le hLone
      have : (0 : ℝ) < 2 * L ^ 2 :=
        mul_pos (by norm_num) (pow_pos hLpos 2)
      linarith
    exact_mod_cast this
  have hCL : C ≤ L := by
    apply le_trans ?_ hLlarge
    have hCone : (1 : ℝ) ≤ C := by norm_num [C]
    have hCpow : C ≤ C ^ 10 := by
      simpa only [pow_one] using pow_le_pow_right₀ hCone (by omega : 1 ≤ 10)
    have hCpowQ : C ^ 10 ≤ Q := by
      dsimp [Q]
      nlinarith [mul_nonneg hP0 hB0]
    exact hCpow.trans hCpowQ
  have hRleL4 : (R : ℝ) ≤ L ^ 4 := by
    calc
      (R : ℝ) ≤ C * L ^ 3 := hRupper
      _ ≤ L * L ^ 3 := mul_le_mul_of_nonneg_right hCL (pow_nonneg hL0 3)
      _ = L ^ 4 := by ring
  have hR10L40 : (R : ℝ) ^ 10 ≤ L ^ 40 := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg R) hRleL4 10).trans_eq (by ring)
  have hdeltaWarmFive : D₅ ^ 2 ≤ E ^ 4 := by
    have hreal : (D₅ : ℝ) ^ 2 ≤ (E : ℝ) ^ 4 := by
      calc
        (D₅ : ℝ) ^ 2 = (R : ℝ) ^ 10 := by simp [D₅]; ring
        _ ≤ L ^ 40 := hR10L40
        _ = (L ^ 10) ^ 4 := by ring
        _ ≤ (E : ℝ) ^ 4 :=
          pow_le_pow_left₀ (pow_nonneg hL0 10) hElow 4
    exact_mod_cast hreal
  have hcarrierRoomCube : 512 * E + 128 ≤ D₃ ^ 2 := by
    have hLfive : (5 : ℝ) ≤ L := by
      exact (show (5 : ℝ) ≤ C by norm_num [C]) |>.trans hCL
    have hLsq : (18 : ℝ) ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 5)]
    have hR6 : 64 * L ^ 12 ≤ (R : ℝ) ^ 6 := by
      have hp := pow_le_pow_left₀ (mul_nonneg (by norm_num) (pow_nonneg hL0 2))
        hRlower 6
      calc
        64 * L ^ 12 = (2 * L ^ 2) ^ 6 := by ring
        _ ≤ (R : ℝ) ^ 6 := hp
    have hreal : (512 : ℝ) * (E : ℝ) + 128 ≤ (D₃ : ℝ) ^ 2 := by
      calc
        (512 : ℝ) * (E : ℝ) + 128 ≤ 1152 * L ^ 10 := by
          have hL10one : 1 ≤ L ^ 10 := one_le_pow₀ hLone
          nlinarith
        _ = 64 * L ^ 10 * 18 := by ring
        _ ≤ 64 * L ^ 10 * L ^ 2 := by
          gcongr
        _ = 64 * L ^ 12 := by ring
        _ ≤ (R : ℝ) ^ 6 := hR6
        _ = (D₃ : ℝ) ^ 2 := by simp [D₃]; ring
    exact_mod_cast hreal
  have hgenericCarrier : (lm311CarrierCost n : ℝ) ≤
      (20 + 12 * M) * L ^ 3 := by
    dsimp [lm311CarrierCost]
    push_cast
    have hL3one : 1 ≤ L ^ 3 := one_le_pow₀ hLone
    have hLL3 : L ≤ L ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hLone (by omega : 1 ≤ 3)
    nlinarith
  have hcarrier44 : (lm44CarrierCost n : ℝ) ≤
      4 * (20 + 12 * M) * L ^ 3 := by
    have hnat := lm44CarrierCost_le_four_lm311CarrierCost n
    have hcast : (lm44CarrierCost n : ℝ) ≤
        4 * (lm311CarrierCost n : ℝ) := by exact_mod_cast hnat
    calc
      (lm44CarrierCost n : ℝ) ≤ 4 * (lm311CarrierCost n : ℝ) := hcast
      _ ≤ 4 * ((20 + 12 * M) * L ^ 3) :=
        mul_le_mul_of_nonneg_left hgenericCarrier (by norm_num)
      _ = 4 * (20 + 12 * M) * L ^ 3 := by ring
  have hR10 : (R : ℝ) ^ 10 ≤ C ^ 10 * L ^ 30 := by
    calc
      (R : ℝ) ^ 10 ≤ (C * L ^ 3) ^ 10 :=
        pow_le_pow_left₀ (Nat.cast_nonneg R) hRupper 10
      _ = C ^ 10 * L ^ 30 := by ring
  have hstatic : (lm44StaticCost n D₅ : ℝ) ≤ P * L ^ 30 := by
    have hL3L30 : L ^ 3 ≤ L ^ 30 := pow_le_pow_right₀ hLone (by omega)
    have hL30one : 1 ≤ L ^ 30 := one_le_pow₀ hLone
    dsimp [lm44StaticCost]
    push_cast
    change
      18 * ((a : ℝ) + (m : ℝ)) + (lm44CarrierCost n : ℝ) +
          16 * (D₅ : ℝ) ^ 2 + 127 ≤ P * L ^ 30
    have hDterm : (D₅ : ℝ) ^ 2 ≤ C ^ 10 * L ^ 30 := by
      calc
        (D₅ : ℝ) ^ 2 = (R : ℝ) ^ 10 := by simp [D₅]; ring
        _ ≤ C ^ 10 * L ^ 30 := hR10
    have ham : (a : ℝ) + (m : ℝ) ≤ (2 + M) * L ^ 3 := by
      calc
        (a : ℝ) + (m : ℝ) ≤ 2 * L ^ 3 + M * L ^ 3 :=
          add_le_add ha hmUpper
        _ = (2 + M) * L ^ 3 := by ring
    calc
      18 * ((a : ℝ) + (m : ℝ)) + (lm44CarrierCost n : ℝ) +
            16 * (D₅ : ℝ) ^ 2 + 127
          ≤ 18 * ((2 + M) * L ^ 3) +
              4 * (20 + 12 * M) * L ^ 3 +
              16 * (C ^ 10 * L ^ 30) + 127 := by gcongr
      _ ≤ 18 * ((2 + M) * L ^ 30) +
              4 * (20 + 12 * M) * L ^ 30 +
              16 * (C ^ 10 * L ^ 30) + 127 * L ^ 30 := by
            have hA : 18 * ((2 + M) * L ^ 3) ≤
                18 * ((2 + M) * L ^ 30) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hL3L30 (by positivity)
            have hB : 4 * (20 + 12 * M) * L ^ 3 ≤
                4 * (20 + 12 * M) * L ^ 30 := by
              exact mul_le_mul_of_nonneg_left hL3L30 (by positivity)
            have h127 : (127 : ℝ) ≤ 127 * L ^ 30 := by
              calc
                (127 : ℝ) = 127 * 1 := by ring
                _ ≤ 127 * L ^ 30 :=
                  mul_le_mul_of_nonneg_left hL30one
                    (show (0 : ℝ) ≤ 127 by norm_num)
            linarith only [hA, hB, h127]
      _ = P * L ^ 30 := by
            dsimp [P]
            ring
  have hcoeff : P * B ≤ L ^ 8 := by
    have hPBQ : P * B ≤ Q := by
      dsimp [Q]
      have htail : (0 : ℝ) ≤ C ^ 10 + 1000 :=
        add_nonneg (pow_nonneg hC0 10) (by norm_num)
      simpa [add_assoc] using
        (le_add_of_nonneg_right htail : P * B ≤ P * B + (C ^ 10 + 1000))
    have hPBL : P * B ≤ L := hPBQ.trans hLlarge
    exact hPBL.trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hLone (by omega : 1 ≤ 8))
  have hstaticProduct : lm44StaticCost n D₅ * div ≤ E ^ 4 := by
    have hreal :
        (lm44StaticCost n D₅ : ℝ) * (div : ℝ) ≤ (E : ℝ) ^ 4 := by
      calc
        (lm44StaticCost n D₅ : ℝ) * (div : ℝ)
            ≤ (P * L ^ 30) * (B * L ^ 2) :=
              mul_le_mul hstatic hdiv (Nat.cast_nonneg div) (by positivity)
        _ = (P * B) * L ^ 32 := by ring
        _ ≤ L ^ 8 * L ^ 32 :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hL0 32)
        _ = (L ^ 10) ^ 4 := by ring
        _ ≤ (E : ℝ) ^ 4 :=
          pow_le_pow_left₀ (pow_nonneg hL0 10) hElow 4
    exact_mod_cast hreal
  have hstaticGain : lm44StaticCost n D₅ ≤ lmGrowthGain n (E ^ 4) := by
    rw [lmGrowthGain]
    exact (Nat.le_div_iff_mul_le hdivPos).2 hstaticProduct
  have hreservoirFive : D₅ ^ 2 ≤ n / 2 + 1 := by
    have hreserv' : 2 * C ^ 10 * L ^ 30 ≤ (n : ℝ) := by
      simpa [L] using hreservN
    have htwiceReal : ((2 * D₅ ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      calc
        (2 : ℝ) * (D₅ : ℝ) ^ 2 = 2 * (R : ℝ) ^ 10 := by
          simp [D₅]
          ring
        _ ≤ 2 * (C ^ 10 * L ^ 30) := by gcongr
        _ ≤ (n : ℝ) := by simpa [mul_assoc] using hreserv'
    have htwice : 2 * D₅ ^ 2 ≤ n := by exact_mod_cast htwiceReal
    have : D₅ ^ 2 ≤ n / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      simpa [mul_comm] using htwice
    omega
  have hD₃D₅ : D₃ ≤ D₅ := by
    dsimp [D₃, D₅]
    exact Nat.pow_le_pow_right hRpos (by omega)
  have hD₃sqD₅sq : D₃ ^ 2 ≤ D₅ ^ 2 := Nat.pow_le_pow_left hD₃D₅ 2
  have hD₃self : D₃ ≤ D₃ ^ 2 := by
    have hone : 1 ≤ D₃ := by exact pow_pos hRpos 3
    have hmul := Nat.mul_le_mul_left D₃ hone
    simpa [pow_two] using hmul
  have hD₅self : D₅ ≤ D₅ ^ 2 := by
    have hone : 1 ≤ D₅ := by exact pow_pos hRpos 5
    have hmul := Nat.mul_le_mul_left D₅ hone
    simpa [pow_two] using hmul
  have hstarsThree := lm44_star_bounds_of_radius_power S.card_large rfl
    (D := D₃) le_rfl hD₃self
  have hstarsFive := lm44_star_bounds_of_radius_power S.card_large rfl
    (D := D₅) (by exact hD₃D₅) hD₅self
  have hglobalFive : ∀ i < a + m,
      lm44GlobalPhaseCost n D₅ ell i ≤ lmGrowthGain n (E ^ 4) := by
    intro i hi
    exact (lm44GlobalPhaseCost_le_static hi).trans hstaticGain
  have hglobalThree : ∀ i < a + m,
      lm44GlobalPhaseCost n D₃ ell i ≤ lmGrowthGain n (E ^ 4) := by
    intro i hi
    have hstaticMono : lm44StaticCost n D₃ ≤ lm44StaticCost n D₅ := by
      have hsq : D₃ ^ 2 ≤ D₅ ^ 2 := Nat.pow_le_pow_left hD₃D₅ 2
      dsimp [lm44StaticCost]
      omega
    exact (lm44GlobalPhaseCost_le_static hi).trans
      (hstaticMono.trans hstaticGain)
  have hpackingThree :
      (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
          (D₃ ^ 2 + 1) ^ (10 * ell) <
        n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4) := by
    apply lt_of_le_of_lt ?_ hpacking
    exact Nat.mul_le_mul_left _ <|
      Nat.pow_le_pow_left (Nat.add_le_add_right hD₃sqD₅sq 1) _
  have hdeltaWarmThree : D₃ ^ 2 ≤ E ^ 4 :=
    hD₃sqD₅sq.trans hdeltaWarmFive
  have hcarrierRoomFive : 512 * E + 128 ≤ D₅ ^ 2 :=
    hcarrierRoomCube.trans hD₃sqD₅sq
  have hpackingFive :
      (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
            (D₅ ^ 2 + 1) ^ (10 * ell) <
        n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4) := by
    change
      (4 ^ 2 + (4 + lm311GirthBudget n + 1)) *
            (D₅ ^ 2 + 1) ^ (10 * ell) <
        n - (2 * 4 ^ 2 + lm311GirthBudget n + 1 + 4) at hpacking
    exact hpacking
  apply lm44LM311AmbientBounds_pair_of_fields S
  · positivity
  · positivity
  · simpa [D₃, E] using hdeltaWarmThree
  · simpa [D₅, E] using hdeltaWarmFive
  · simpa [D₃, E] using hcarrierRoomCube
  · simpa [D₅, E] using hcarrierRoomFive
  · simpa [D₃, E, ell, a, m] using hglobalThree
  · simpa [D₅, E, ell, a, m] using hglobalFive
  · simpa [D₃, ell] using hpackingThree
  · simpa [D₅, ell] using hpackingFive
  · exact hD₃sqD₅sq.trans hreservoirFive
  · exact hreservoirFive
  · exact hstarsThree.1
  · exact hstarsThree.2
  · exact hstarsFive.1
  · exact hstarsFive.2

/-- The two exact k=4 Lemma 3.11 records, uniformly in every admissible
degree parameter. -/
theorem eventually_lm44LM311Bounds :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      lm311DegreeThreshold ≤ d → d ≤ n →
        let R := 5 * lmGrowthRounds n
        LM44LM311Bounds n d (R ^ 3) ∧
          LM44LM311Bounds n d (R ^ 5) := by
  filter_upwards [eventually_lm44LM311AmbientBounds] with n hn
  intro d hd hdn
  exact ⟨lm44LM311Bounds_of_ambient hn.1 hd hdn,
    lm44LM311Bounds_of_ambient hn.2 hd hdn⟩

/-- Threshold form used by the robust Claim 4.3 assembly: choosing the core
degree beyond the eventual ambient threshold makes both Lemma 3.11 records
available at every extracted order `coreDegree < n' ≤ N`. -/
theorem exists_threshold_lm44LM311Bounds :
    ∃ d₀ : ℕ, ∀ coreDegree : ℕ, d₀ ≤ coreDegree →
      ∀ N n' : ℕ, coreDegree < n' → n' ≤ N →
        let R := 5 * lmGrowthRounds n'
        LM44LM311Bounds n' coreDegree (R ^ 3) ∧
          LM44LM311Bounds n' coreDegree (R ^ 5) := by
  obtain ⟨n₀, htail⟩ := Filter.eventually_atTop.mp eventually_lm44LM311Bounds
  refine ⟨max lm311DegreeThreshold n₀, ?_⟩
  intro coreDegree hcore N n' hlt _
  have hdegree : lm311DegreeThreshold ≤ coreDegree :=
    (le_max_left _ _).trans hcore
  have hn₀n' : n₀ ≤ n' :=
    (le_max_right _ _).trans (hcore.trans hlt.le)
  exact htail n' hn₀n' coreDegree hdegree hlt.le

/-- The literal Claim 4.4 star workspace fits the source high-degree cutoff
as soon as the target order and candidate radius are nonzero. -/
theorem lm43_claim44_star_budget (N d : ℕ)
    (hD : 0 < lm43TargetOrder N d)
    (hm : 0 < lm43MaxRadius N d) :
    lm43TargetOrder N d + lm43Claim44StarBudget N d ≤
      lm43HighCutoff N d := by
  rw [lm43Claim44StarBudget_eq, lm43HighCutoff, lm43DeletionCap_eq]
  nlinarith

/-- A quarter-degree initial density survives deletion of the exceptional
set once twice its `100 D²` allowance fits beside the deletion budget. -/
theorem lm43_initial_density_of_room {N d target deleted : ℕ}
    (hroom : 200 * target ^ 2 + deleted ≤ N) :
    ∀ u ≤ deleted,
      (d / 4) * (N - u) ≤
        ((N - u) - 100 * target ^ 2) * (d - d / 2) := by
  intro u hu
  let A := N - u
  let B := A - 100 * target ^ 2
  have huN : u ≤ N := hu.trans (by omega)
  have hA : A + u = N := Nat.sub_add_cancel huN
  have htwice : 2 * (100 * target ^ 2) ≤ A := by
    dsimp [A]
    omega
  have hBA : B + 100 * target ^ 2 = A := by
    exact Nat.sub_add_cancel (by omega)
  have hAB : A ≤ 2 * B := by omega
  have hdquarter : 2 * (d / 4) ≤ d - d / 2 := by omega
  dsimp [A, B] at hAB ⊢
  nlinarith

/-- The retained-density estimate follows from very coarse quarter-order
bounds on the deletion set and the forbidden-ball incidence term. -/
theorem lm43_retained_density_of_ball_bounds {N d deleted ball Delta : ℕ}
    (hd : 64 ≤ d) (hdeleted : 4 * deleted ≤ N)
    (hball : ball * Delta ≤ N) :
    (8 * (d / 64)) * N + 2 * (ball * Delta) ≤
      (d / 4) * (N - deleted) := by
  let c := d / 64
  have hc : 1 ≤ c := by
    dsimp [c]
    omega
  have hc16 : 16 * c ≤ d / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    have hc64 : 64 * c ≤ d := by
      dsimp [c]
      simpa [mul_comm] using Nat.div_mul_le_self d 64
    nlinarith
  have hdeletedN : deleted ≤ N := by omega
  have hsplit : N - deleted + deleted = N := Nat.sub_add_cancel hdeletedN
  have hcore : 8 * c * N + 2 * N ≤ 16 * c * (N - deleted) := by
    nlinarith
  calc
    (8 * (d / 64)) * N + 2 * (ball * Delta)
        ≤ 8 * c * N + 2 * N := by
          dsimp [c]
          gcongr
    _ ≤ 16 * c * (N - deleted) := hcore
    _ ≤ (d / 4) * (N - deleted) := by gcongr

/-- Quarter-order bounds on both deleted pieces imply that their union is
a proper deletion. -/
theorem deletion_add_ball_lt_of_four_mul_le {N deleted ball : ℕ}
    (hN : 0 < N) (hdeleted : 4 * deleted ≤ N)
    (hball : 4 * ball ≤ N) :
    deleted + ball < N := by
  omega

/-- Pointwise assembly of all outer Claim 4.4 fields.  Thus subsequent
asymptotics only have to provide the three displayed ambient estimates. -/
theorem lm43Claim44OuterBounds_of_ambient
    {N d : ℕ} (hN : 0 < N)
    (hd : 64 * lm311DegreeThreshold ≤ d)
    (hdeleted : 4 * lm43DeletionCap N d ≤ N)
    (hroom : 200 * lm43TargetOrder N d ^ 2 +
      lm43DeletionCap N d ≤ N)
    (hball : 4 * lm43Claim44BallCap N d ≤ N)
    (hballDelta : lm43Claim44BallCap N d *
      lm43HighCutoff N d ≤ N)
    (htarget : 0 < lm43TargetOrder N d)
    (htotal : 1 ≤ lm43TotalRadius N d)
    (hmaxTotal : lm43MaxRadius N d ≤ lm43TotalRadius N d)
    (hmaxPos : 0 < lm43MaxRadius N d) :
    LM43Claim44OuterBounds N d := by
  refine
    { deleted_le := lm43DeletionCap_le_ten_target N d
      seed_bound := (lm43_claim44_seed_exact N d).le
      ball_bound := (lm43_claim44_ball_exact N d).le
      deletion_proper :=
        deletion_add_ball_lt_of_four_mul_le hN hdeleted hball
      initial_density := by
        simpa [lm43InitialDegree] using
          lm43_initial_density_of_room (N := N) (d := d)
            (target := lm43TargetOrder N d)
            (deleted := lm43DeletionCap N d) hroom
      retained_density := by
        apply lm43_retained_density_of_ball_bounds
        · norm_num [lm311DegreeThreshold] at hd ⊢
          omega
        · exact hdeleted
        · exact hballDelta
      core_large := by
        dsimp [lm43CoreDegree]
        apply (show 32 ≤ lm311DegreeThreshold by norm_num [lm311DegreeThreshold]) |>.trans
        apply (Nat.le_div_iff_mul_le (by omega : 0 < 64)).2
        simpa [mul_comm] using hd
      target_pos := htarget
      totalRadius_pos := htotal
      maxRadius_le := hmaxTotal
      star_budget := lm43_claim44_star_budget N d htarget hmaxPos
      radius_bounds := by
        intro n' hn' hN'
        simpa [lm43CoreRadius] using lm43_core_radius_bounds hn' hN' }

/-- The deletion cap and the `100 D²` exceptional-set allowance are
eventually negligible compared with the ambient order. -/
theorem eventually_lm43_claim44_deletion_room :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      4 * lm43DeletionCap N d ≤ N ∧
        200 * lm43TargetOrder N d ^ 2 + lm43DeletionCap N d ≤ N := by
  have htarget :=
    Parameters.eventually_lmExpansionOrder_mul_lmRadius_1024_le_ceil_log14
  have hsmallReal :=
    Parameters.eventually_const_mul_log_pow_le_self (812 : ℝ) 28
  have hsmall := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htarget, hsmall,
      hlog.eventually (eventually_ge_atTop (1 : ℝ))]
    with N htargetN hsmallN hlogOne
  intro d
  let L := Real.log (N : ℝ)
  have hLone : (1 : ℝ) ≤ L := by simpa [L] using hlogOne
  have hL14one : (1 : ℝ) ≤ L ^ 14 := one_le_pow₀ hLone
  have hceil : (⌈L ^ 14⌉₊ : ℝ) ≤ 2 * L ^ 14 := by
    apply le_of_lt
    calc
      (⌈L ^ 14⌉₊ : ℝ) < L ^ 14 + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      _ ≤ 2 * L ^ 14 := by linarith
  have htargetReal : (lm43TargetOrder N d : ℝ) ≤ 2 * L ^ 14 := by
    have htargetNat : lm43TargetOrder N d ≤ ⌈L ^ 14⌉₊ := by
      simpa [lm43TargetOrder, lm47InflatedOrder, L] using htargetN
    exact (by exact_mod_cast htargetNat :
      (lm43TargetOrder N d : ℝ) ≤ (⌈L ^ 14⌉₊ : ℝ)) |>.trans hceil
  have hL14L28 : L ^ 14 ≤ L ^ 28 :=
    pow_le_pow_right₀ hLone (by omega)
  have hroomReal :
      ((200 * lm43TargetOrder N d ^ 2 + lm43DeletionCap N d : ℕ) : ℝ) ≤
        812 * L ^ 28 := by
    rw [lm43DeletionCap_eq]
    push_cast
    calc
      (200 : ℝ) * (lm43TargetOrder N d : ℝ) ^ 2 +
            6 * (lm43TargetOrder N d : ℝ)
          ≤ 200 * (2 * L ^ 14) ^ 2 + 6 * (2 * L ^ 14) := by
            gcongr
      _ ≤ 812 * L ^ 28 := by
        nlinarith [pow_nonneg (zero_le_one.trans hLone) 28]
  have hsmall' : (812 : ℝ) * L ^ 28 ≤ (N : ℝ) := by
    simpa [L] using hsmallN
  have hroomNat :
      200 * lm43TargetOrder N d ^ 2 + lm43DeletionCap N d ≤ N := by
    exact_mod_cast hroomReal.trans hsmall'
  have hdeletedNat : 4 * lm43DeletionCap N d ≤ N := by
    rw [lm43DeletionCap_eq]
    have hreal : ((24 * lm43TargetOrder N d : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      calc
        (24 : ℝ) * (lm43TargetOrder N d : ℝ)
            ≤ 48 * L ^ 14 := by nlinarith
        _ ≤ 812 * L ^ 28 := by
          nlinarith [pow_nonneg (zero_le_one.trans hLone) 28]
        _ ≤ (N : ℝ) := hsmall'
    have : 24 * lm43TargetOrder N d ≤ N := by exact_mod_cast hreal
    omega
  exact ⟨hdeletedNat, hroomNat⟩

/-- The complete forbidden ball in canonical Claim 4.4 is eventually small
enough both for proper deletion and for the retained-density incidence
estimate.  The proof keeps the source `N^(1/8)` family size: the seed is at
most the fourth power of that scale, the bounded-degree ball at most its
fifth power, and the final high-degree cutoff at most its third power. -/
theorem eventually_lm43_claim44_ball_bounds :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      4 * lm43Claim44BallCap N d ≤ N ∧
        lm43Claim44BallCap N d * lm43HighCutoff N d ≤ N := by
  have htargetCeil :=
    Parameters.eventually_lmExpansionOrder_mul_lmRadius_1024_le_ceil_log14
  have htargetRoot :=
    eventually_const_mul_log_pow_le_rpow_eighth (2 : ℝ) (by norm_num) 14
  have hradiusRoot :=
    eventually_const_mul_log_pow_le_rpow_eighth
      (819201 : ℝ) (by norm_num) 3
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hroot : Tendsto
      (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards
      [htargetCeil, htargetRoot, hradiusRoot,
        eventually_five_mul_lmGrowthRounds_le_lmSimpleRadius,
        hlog.eventually (eventually_ge_atTop (327680401 : ℝ)),
        hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
        Parameters.eventually_const_mul_log_log_pow_le_log 2880 21,
        hroot.eventually (eventually_ge_atTop (200 : ℝ)),
        eventually_lm43_targetOrder_pos,
        eventually_lm43_candidateRadius_pos,
        eventually_ge_atTop (32 : ℕ)]
    with N htargetCeilN htargetRootN hradiusRootN hradiusSimpleN hLlarge
      hllone hllsmall hxlarge htargetPos hradiusPos hN
  intro d
  let L := Real.log (N : ℝ)
  let ll := Real.log L
  let x := (N : ℝ) ^ ((1 : ℝ) / 8)
  let target := lm43TargetOrder N d
  let radius := lm43MaxRadius N d
  let family := lm43R N d
  let Delta := lm43HighCutoff N d
  let separation := lm43Separation N d
  let seed := lm43Claim44SeedCap N d
  let ball := lm43Claim44BallCap N d
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hL : (327680401 : ℝ) ≤ L := by simpa [L] using hLlarge
  have hLone : (1 : ℝ) ≤ L := by
    exact (show (1 : ℝ) ≤ 327680401 by norm_num).trans hL
  have hL0 : (0 : ℝ) ≤ L := zero_le_one.trans hLone
  have hll : (1 : ℝ) ≤ ll := by simpa [ll, L] using hllone
  have hll0 : (0 : ℝ) ≤ ll := zero_le_one.trans hll
  have hx : (200 : ℝ) ≤ x := by simpa [x] using hxlarge
  have hx0 : (0 : ℝ) ≤ x := by
    exact (show (0 : ℝ) ≤ 200 by norm_num).trans hx
  have hxone : (1 : ℝ) ≤ x := by
    exact (show (1 : ℝ) ≤ 200 by norm_num).trans hx
  have htargetPos' : 0 < target := by simpa [target] using htargetPos d
  have hradiusPos' : 0 < radius := by
    simpa [radius, lm43MaxRadius] using hradiusPos d
  have hceil14 : (⌈L ^ 14⌉₊ : ℝ) ≤ 2 * L ^ 14 := by
    apply le_of_lt
    calc
      (⌈L ^ 14⌉₊ : ℝ) < L ^ 14 + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      _ ≤ 2 * L ^ 14 := by
        have := one_le_pow₀ hLone (n := 14)
        linarith
  have htargetPoly : (target : ℝ) ≤ 2 * L ^ 14 := by
    have htargetNat : target ≤ ⌈L ^ 14⌉₊ := by
      simpa [target, lm43TargetOrder, lm47InflatedOrder, L] using htargetCeilN
    exact (by exact_mod_cast htargetNat :
      (target : ℝ) ≤ (⌈L ^ 14⌉₊ : ℝ)) |>.trans hceil14
  have htargetX : (target : ℝ) ≤ x := by
    exact htargetPoly.trans (by simpa [L, x] using htargetRootN)
  have hradiusPoly : (radius : ℝ) ≤ 819201 * L ^ 3 := by
    have hradiusNat : radius ≤ Parameters.lmSimpleRadius (1 / 1024) N := by
      simpa [radius, lm43MaxRadius, lm43CandidateRadius, lm43CoreRadius] using
        hradiusSimpleN
    have hradiusCast : (radius : ℝ) ≤
        (Parameters.lmSimpleRadius (1 / 1024) N : ℝ) := by
      exact_mod_cast hradiusNat
    have hceil := Parameters.lmSimpleRadius_lt_add_one
      (n := N) (show (0 : ℝ) < 1 / 1024 by norm_num)
    norm_num at hceil
    have hL3one : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hLone
    linarith
  have hradiusX : (radius : ℝ) ≤ x :=
    hradiusPoly.trans (by simpa [L, x] using hradiusRootN)
  have hfamilyX : (family : ℝ) ≤ x := by
    dsimp [family, lm43R, lm43FamilyTarget, SourceLemma35Numerics.indexCard]
    simpa [x] using Nat.floor_le (Real.rpow_nonneg hN0 ((1 : ℝ) / 8))
  have hDeltaPoly : (Delta : ℝ) ≤ 327680400 * L ^ 17 := by
    dsimp [Delta, lm43HighCutoff]
    push_cast
    calc
      (200 : ℝ) * (radius : ℝ) * (target : ℝ)
          ≤ 200 * (819201 * L ^ 3) * (2 * L ^ 14) := by gcongr
      _ = 327680400 * L ^ 17 := by ring
  have hDeltaX3 : (Delta : ℝ) ≤ x ^ 3 := by
    calc
      (Delta : ℝ) ≤ 200 * x ^ 2 := by
        dsimp [Delta, lm43HighCutoff]
        push_cast
        nlinarith [mul_le_mul htargetX hradiusX
          (Nat.cast_nonneg radius) hx0]
      _ ≤ x ^ 3 := by nlinarith [sq_nonneg x]
  have hbasePoly : ((Delta + 1 : ℕ) : ℝ) ≤ L ^ 18 := by
    push_cast
    calc
      (Delta : ℝ) + 1 ≤ 327680401 * L ^ 17 := by
        have hL17one : (1 : ℝ) ≤ L ^ 17 := one_le_pow₀ hLone
        nlinarith
      _ ≤ L * L ^ 17 := by
        exact mul_le_mul_of_nonneg_right hL (pow_nonneg hL0 17)
      _ = L ^ 18 := by ring
  have hbasePos : (0 : ℝ) < ((Delta + 1 : ℕ) : ℝ) := by positivity
  have hlogBase : Real.log (((Delta + 1 : ℕ) : ℝ)) ≤ 18 * ll := by
    calc
      Real.log (((Delta + 1 : ℕ) : ℝ)) ≤ Real.log (L ^ 18) :=
        Real.log_le_log hbasePos hbasePoly
      _ = 18 * ll := by simp [ll, Real.log_pow]
  have hsep : (separation : ℝ) ≤ 20 * ll ^ 20 := by
    have hceil : (⌈ll ^ 20⌉₊ : ℝ) ≤ 2 * ll ^ 20 := by
      apply le_of_lt
      calc
        (⌈ll ^ 20⌉₊ : ℝ) < ll ^ 20 + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        _ ≤ 2 * ll ^ 20 := by
          have := one_le_pow₀ hll (n := 20)
          linarith
    dsimp [separation, lm43Separation, lm43AvoidingRadius]
    push_cast
    have hmul : (10 : ℝ) * (⌈ll ^ 20⌉₊ : ℝ) ≤
        10 * (2 * ll ^ 20) :=
      mul_le_mul_of_nonneg_left hceil (by norm_num)
    calc
      (10 : ℝ) * (⌈Real.log (Real.log (N : ℝ)) ^ 20⌉₊ : ℝ)
          ≤ 10 * (2 * ll ^ 20) := by simpa [ll, L] using hmul
      _ = 20 * ll ^ 20 := by ring
  have hsmall : 2880 * ll ^ 21 ≤ L := by
    simpa [ll, L] using hllsmall
  have hbranchX :
      ((((Delta + 1) ^ separation : ℕ) : ℝ)) ≤ x := by
    have hpowPos : (0 : ℝ) < ((((Delta + 1) ^ separation : ℕ) : ℝ)) := by
      positivity
    have hlogPow :
        Real.log ((((Delta + 1) ^ separation : ℕ) : ℝ)) ≤ L / 8 := by
      rw [Nat.cast_pow, Real.log_pow]
      calc
        (separation : ℝ) * Real.log (((Delta + 1 : ℕ) : ℝ))
            ≤ (20 * ll ^ 20) * (18 * ll) := by gcongr
        _ = 360 * ll ^ 21 := by ring
        _ ≤ L / 8 := by linarith
    calc
      ((((Delta + 1) ^ separation : ℕ) : ℝ)) =
          Real.exp (Real.log ((((Delta + 1) ^ separation : ℕ) : ℝ))) := by
            rw [Real.exp_log hpowPos]
      _ ≤ Real.exp (L / 8) := Real.exp_le_exp.mpr hlogPow
      _ = x := by
        dsimp [x, L]
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring
  have hprotectedX2 :
      (lm43ProtectedCap N d : ℝ) ≤ 106 * x ^ 2 := by
    rw [lm43ProtectedCap, lm43DeletionCap_eq]
    push_cast
    nlinarith [sq_nonneg ((target : ℝ) - x)]
  have hadjustersX3 :
      4 * (lm43R N d : ℝ) *
          (2 * (lm43MaxRadius N d : ℝ) ^ 2 +
            10 * (lm43MaxRadius N d : ℝ)) ≤ 48 * x ^ 3 := by
    change 4 * (family : ℝ) *
      (2 * (radius : ℝ) ^ 2 + 10 * (radius : ℝ)) ≤ 48 * x ^ 3
    have hrx2 : (radius : ℝ) ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg radius) hradiusX 2
    have hrleSq : (radius : ℝ) ≤ (radius : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ radius by exact_mod_cast hradiusPos']
    calc
      4 * (family : ℝ) *
          (2 * (radius : ℝ) ^ 2 + 10 * (radius : ℝ))
          ≤ 4 * x * (12 * x ^ 2) := by gcongr <;> nlinarith
      _ = 48 * x ^ 3 := by ring
  have hseedX4 : (seed : ℝ) ≤ x ^ 4 := by
    have hseedSum : (seed : ℝ) ≤ 106 * x ^ 2 + 48 * x ^ 3 := by
      dsimp [seed, lm43Claim44SeedCap]
      push_cast
      exact add_le_add hprotectedX2 hadjustersX3
    calc
      (seed : ℝ) ≤ 106 * x ^ 2 + 48 * x ^ 3 := hseedSum
      _ ≤ 154 * x ^ 3 := by
        have hx23 : x ^ 2 ≤ x ^ 3 := by
          calc
            x ^ 2 = x ^ 2 * 1 := by ring
            _ ≤ x ^ 2 * x :=
              mul_le_mul_of_nonneg_left hxone (pow_nonneg hx0 2)
            _ = x ^ 3 := by ring
        calc
          106 * x ^ 2 + 48 * x ^ 3 ≤ 106 * x ^ 3 + 48 * x ^ 3 := by
            gcongr
          _ = 154 * x ^ 3 := by ring
      _ ≤ x ^ 4 := by
        calc
          154 * x ^ 3 ≤ x * x ^ 3 := by
            gcongr
            linarith
          _ = x ^ 4 := by ring
  have hballX5 : (ball : ℝ) ≤ x ^ 5 := by
    dsimp [ball]
    rw [lm43Claim44BallCap_eq]
    simp only [Nat.cast_mul]
    change (seed : ℝ) *
      ((((Delta + 1) ^ separation : ℕ) : ℝ)) ≤ x ^ 5
    calc
      (seed : ℝ) * ((((Delta + 1) ^ separation : ℕ) : ℝ))
          ≤ x ^ 4 * x := mul_le_mul hseedX4 hbranchX
            (Nat.cast_nonneg _) (pow_nonneg hx0 4)
      _ = x ^ 5 := by ring
  have hx8 : x ^ 8 = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have hfourBallReal : ((4 * ball : ℕ) : ℝ) ≤ (N : ℝ) := by
    push_cast
    calc
      (4 : ℝ) * (ball : ℝ) ≤ 4 * x ^ 5 := by gcongr
      _ ≤ x ^ 8 := by
        have hfour : (4 : ℝ) ≤ x ^ 3 := by
          calc
            (4 : ℝ) ≤ 200 ^ 3 := by norm_num
            _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
        calc
          (4 : ℝ) * x ^ 5 ≤ x ^ 3 * x ^ 5 :=
            mul_le_mul_of_nonneg_right hfour (pow_nonneg hx0 5)
          _ = x ^ 8 := by ring
      _ = (N : ℝ) := hx8
  have hballDeltaReal : ((ball * Delta : ℕ) : ℝ) ≤ (N : ℝ) := by
    push_cast
    calc
      (ball : ℝ) * (Delta : ℝ) ≤ x ^ 5 * x ^ 3 :=
        mul_le_mul hballX5 hDeltaX3 (Nat.cast_nonneg Delta)
          (pow_nonneg hx0 5)
      _ = x ^ 8 := by ring
      _ = (N : ℝ) := hx8
  exact ⟨by exact_mod_cast hfourBallReal, by exact_mod_cast hballDeltaReal⟩

/-! ## Claim 4.6 workspace bookkeeping -/

/-- The workspace accumulated before Claim 4.6 is contained in the larger
forbidden-ball envelope already paid for in Claim 4.4. -/
theorem lm43Claim46WorkspaceCap_le_claim44BallCap (N d : ℕ) :
    lm43Claim46WorkspaceCap (lm43DeletionCap N d) (lm43R N d)
        (lm43MaxRadius N d) (lm43HighCutoff N d) (lm43BallRadius N d) ≤
      lm43Claim44BallCap N d := by
  let deleted := lm43DeletionCap N d
  let protectedCap := lm43ProtectedCap N d
  let R := lm43R N d
  let m := lm43MaxRadius N d
  let Delta := lm43HighCutoff N d
  let ell := lm43BallRadius N d
  let A := 2 * m ^ 2 + 10 * m
  let P := (Delta + 1) ^ ell
  let Q := (Delta + 1) ^ (10 * ell)
  have hdeleted : deleted ≤ protectedCap := by
    dsimp [deleted, protectedCap, lm43ProtectedCap]
    omega
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_pow₀ (by omega)
  have hPQ : P ≤ Q := by
    dsimp [P, Q]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hmA : 2 * m ^ 2 ≤ A := by
    dsimp [A]
    omega
  have hdeletedQ : deleted ≤ protectedCap * Q :=
    hdeleted.trans (Nat.le_mul_of_pos_right protectedCap hQone)
  have hfirst : A ≤ A * Q := Nat.le_mul_of_pos_right A hQone
  have hsecond : 2 * m ^ 2 * P ≤ A * Q := by
    calc
      2 * m ^ 2 * P ≤ 2 * m ^ 2 * Q := Nat.mul_le_mul_left _ hPQ
      _ ≤ A * Q := Nat.mul_le_mul_right Q hmA
  have hfamily : 2 * R * (A + 2 * m ^ 2 * P) ≤ 4 * R * A * Q := by
    calc
      2 * R * (A + 2 * m ^ 2 * P) ≤
          2 * R * (A * Q + A * Q) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hfirst hsecond)
      _ = 4 * R * A * Q := by ring
  change deleted + 2 * R * (A + 2 * m ^ 2 * P) ≤
    (protectedCap + 4 * R * A) * Q
  calc
    deleted + 2 * R * (A + 2 * m ^ 2 * P) ≤
        protectedCap * Q + 4 * R * A * Q := Nat.add_le_add hdeletedQ hfamily
    _ = (protectedCap + 4 * R * A) * Q := by ring

/-- The high-degree cutoff dominates four canonical growth divisors. -/
theorem four_lmGrowthDivisor_le_lm43HighCutoff
    {N d : ℕ} (hN : 32 ≤ N) :
    4 * lmGrowthDivisor N ≤ lm43HighCutoff N d := by
  have hq : lmGrowthDivisor N ≤ lmGrowthRounds N := by
    rw [lmGrowthRounds]
    calc
      lmGrowthDivisor N = lmGrowthDivisor N * 1 := by omega
      _ ≤ lmGrowthDivisor N * (2 * (Nat.log 2 N + 1)) := by
        gcongr
        omega
      _ = 2 * lmGrowthDivisor N * (Nat.log 2 N + 1) := by ring
  have hm : lmGrowthRounds N ≤ lm43MaxRadius N d := by
    simp only [lm43MaxRadius, lm43CandidateRadius, lm43CoreRadius]
    omega
  have htarget : 0 < lm43TargetOrder N d :=
    lm43TargetOrder_pos_of_two_le (by omega)
  rw [lm43HighCutoff]
  have : 4 * lmGrowthDivisor N ≤ 200 * lm43MaxRadius N d := by
    nlinarith
  exact this.trans (Nat.le_mul_of_pos_right _ htarget)

/-- The complete Claim 4.6 workspace fits in the first sharp auxiliary
growth increment and, together with the quarter-order starting set, remains
inside the ambient vertex set. -/
theorem eventually_lm43_claim46_workspace :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43Claim46WorkspaceCap (lm43DeletionCap N d) (lm43R N d)
          (lm43MaxRadius N d) (lm43HighCutoff N d) (lm43BallRadius N d) ≤
        lm43GrowthGain N (lm43K N) ∧
      lm43Claim46WorkspaceCap (lm43DeletionCap N d) (lm43R N d)
          (lm43MaxRadius N d) (lm43HighCutoff N d) (lm43BallRadius N d) +
        lm43K N ≤ N := by
  filter_upwards [eventually_lm43_claim44_ball_bounds,
      eventually_ge_atTop (32 : ℕ)] with N hball hN
  intro d
  let W := lm43Claim46WorkspaceCap (lm43DeletionCap N d) (lm43R N d)
    (lm43MaxRadius N d) (lm43HighCutoff N d) (lm43BallRadius N d)
  let B := lm43Claim44BallCap N d
  let Delta := lm43HighCutoff N d
  let q := lmGrowthDivisor N
  have hqpos : 0 < q := by
    simpa [q] using lmGrowthDivisor_pos (hN.trans' (by omega))
  have hWB : W ≤ B := by
    simpa only [W, B] using lm43Claim46WorkspaceCap_le_claim44BallCap N d
  have hfourq : 4 * q ≤ Delta := by
    simpa only [q, Delta] using
      four_lmGrowthDivisor_le_lm43HighCutoff (d := d) hN
  have hfourWq : 4 * (W * q) ≤ N := by
    calc
      4 * (W * q) = W * (4 * q) := by ring
      _ ≤ W * Delta := Nat.mul_le_mul_left W hfourq
      _ ≤ B * Delta := Nat.mul_le_mul_right Delta hWB
      _ ≤ N := (hball d).2
  have hWK : W * q ≤ lm43K N := by
    dsimp [lm43K]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    simpa [mul_comm] using hfourWq
  have hgain : W ≤ lm43GrowthGain N (lm43K N) := by
    change W ≤ lm43K N / q
    exact (Nat.le_div_iff_mul_le hqpos).2 hWK
  have hWleK : W ≤ lm43K N := hgain.trans (Nat.div_le_self _ _)
  have htwoK : 2 * lm43K N ≤ N := by
    dsimp [lm43K]
    omega
  exact ⟨hgain,
    (Nat.add_le_add hWleK le_rfl).trans (by simpa [two_mul] using htwoK)⟩

/-- Once the two forbidden-ball estimates are available, all outer fields
of the canonical Claim 4.4 certificate hold eventually and uniformly in the
degree parameter. -/
theorem eventually_lm43Claim44OuterBounds_of_ball
    (hball : ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      64 * lm311DegreeThreshold ≤ d →
        4 * lm43Claim44BallCap N d ≤ N ∧
          lm43Claim44BallCap N d * lm43HighCutoff N d ≤ N) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      64 * lm311DegreeThreshold ≤ d →
        LM43Claim44OuterBounds N d := by
  filter_upwards [hball, eventually_lm43_claim44_deletion_room,
      eventually_lm43_targetOrder_pos, eventually_lm43_total_radius_fields,
      eventually_lm43_candidateRadius_pos, eventually_ge_atTop (1 : ℕ)]
    with N hballN hroom htarget htotal hmax hN
  intro d hd
  have hmaxPos : 0 < lm43MaxRadius N d := by
    simpa [lm43MaxRadius] using hmax d
  exact lm43Claim44OuterBounds_of_ambient (by omega) hd
    (hroom d).1 (hroom d).2 (hballN d hd).1 (hballN d hd).2
    (htarget d) (htotal d).1 (htotal d).2 hmaxPos

theorem eventually_lm43Claim44OuterBounds :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      64 * lm311DegreeThreshold ≤ d →
        LM43Claim44OuterBounds N d := by
  apply eventually_lm43Claim44OuterBounds_of_ball
  filter_upwards [eventually_lm43_claim44_ball_bounds] with N hN
  intro d _
  exact hN d

/-! ## Final canonical Claim 4.4 scale -/

/-- Pointwise assembly of the canonical robust Claim 4.4 scale from the
outer ambient bookkeeping and the two uniform k=4 Lemma 3.11 records. -/
noncomputable def concreteLM43Claim44Scale {N d : ℕ}
    (outer : LM43Claim44OuterBounds N d)
    (hnum : ∀ n', lm43CoreDegree N d < n' → n' ≤ N →
      let R := 5 * lmGrowthRounds n'
      LM44LM311Bounds n' (lm43CoreDegree N d) (R ^ 3) ∧
        LM44LM311Bounds n' (lm43CoreDegree N d) (R ^ 5)) :
    SmallSimpleAdjusterCandidate.LM44Scale N d
      (lm43TargetOrder N d) (lm43TotalRadius N d)
      (lm43HighCutoff N d) (lm43DeletionCap N d)
      (lm43ProtectedCap N d) (lm43Separation N d)
      (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
      ((1 / 64) * (lm43CoreDegree N d : ℝ)) := by
  apply SmallSimpleAdjusterCandidate.concreteLM44ScaleFiveRounds
    N d (lm43TargetOrder N d) (lm43TotalRadius N d)
    (lm43HighCutoff N d) (lm43DeletionCap N d)
    (lm43ProtectedCap N d) (lm43Separation N d)
    (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
    (lm43InitialDegree N d) (lm43CoreDegree N d)
  · exact outer.deleted_le
  · simpa [lm43_claim44_ball_exact] using outer.deletion_proper
  · exact outer.initial_density
  · simpa [lm43_claim44_ball_exact] using outer.retained_density
  · exact outer.core_large
  · exact outer.target_pos
  · exact outer.totalRadius_pos
  · exact outer.maxRadius_le
  · simpa [lm43Claim44StarBudget_eq, lm44StarBudget] using outer.star_budget
  · exact outer.radius_bounds
  · intro n' D L hn' hN' hD hL
    have hnlarge : 32 ≤ n' := outer.core_large.trans (by omega)
    have hm : 2 ≤ 5 * lmGrowthRounds n' := by
      have hmPos : 0 < lmGrowthRounds n' := by
        unfold lmGrowthRounds
        exact Nat.mul_pos
          (Nat.mul_pos (by omega)
            (lmGrowthDivisor_pos (hnlarge.trans' (by omega))))
          (by omega)
      omega
    have hLm : L ≤ 5 * lmGrowthRounds n' := by
      exact hL.trans (lm311GirthBudget_le_lmGrowthRounds hnlarge) |>.trans
        (by omega)
    exact lm42CanonicalSeedDichotomy hm hD hLm
  · intro n' hn' hN'
    exact concreteLM44LM311Numerics (hnum n' hn' hN').1
  · intro n' hn' hN'
    have hb := (hnum n' hn' hN').2
    have hpow :
        (5 * lmGrowthRounds n') ^ 3 * (5 * lmGrowthRounds n') ^ 2 =
          (5 * lmGrowthRounds n') ^ 5 := by ring
    rw [hpow]
    exact concreteLM44LM311Numerics hb

/-- A single absolute degree threshold supplies the complete canonical
Claim 4.4 scale for every ambient order `N ≥ d`. -/
theorem exists_threshold_concreteLM43Claim44Scale :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      Nonempty (SmallSimpleAdjusterCandidate.LM44Scale N d
        (lm43TargetOrder N d) (lm43TotalRadius N d)
        (lm43HighCutoff N d) (lm43DeletionCap N d)
        (lm43ProtectedCap N d) (lm43Separation N d)
        (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
        ((1 / 64) * (lm43CoreDegree N d : ℝ))) := by
  obtain ⟨N₀, houter⟩ :=
    Filter.eventually_atTop.mp eventually_lm43Claim44OuterBounds
  obtain ⟨n₀, hbounds⟩ :=
    Filter.eventually_atTop.mp eventually_lm44LM311Bounds
  let d₀ := max N₀ (max (64 * lm311DegreeThreshold) (64 * n₀))
  refine ⟨d₀, ?_⟩
  intro d hd N hdN
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans (hd.trans hdN)
  have hdegreeD : 64 * lm311DegreeThreshold ≤ d :=
    (le_max_left (64 * lm311DegreeThreshold) (64 * n₀)).trans
      ((le_max_right N₀ _).trans hd)
  have hn₀core : n₀ ≤ lm43CoreDegree N d := by
    dsimp [lm43CoreDegree]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 64)).2
    have h64n₀ : 64 * n₀ ≤ d :=
      (le_max_right (64 * lm311DegreeThreshold) (64 * n₀)).trans
        ((le_max_right N₀ _).trans hd)
    simpa [mul_comm] using h64n₀
  have hdegreeCore : lm311DegreeThreshold ≤ lm43CoreDegree N d := by
    dsimp [lm43CoreDegree]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 64)).2
    simpa [mul_comm] using hdegreeD
  have outer := houter N hN₀ d hdegreeD
  refine ⟨concreteLM43Claim44Scale outer ?_⟩
  intro n' hn' hN'
  have hn₀n' : n₀ ≤ n' := hn₀core.trans hn'.le
  exact hbounds n' hn₀n' (lm43CoreDegree N d) hdegreeCore hn'.le

end Erdos63

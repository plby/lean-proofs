/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Claim44Eventual
import ErdosProblems.Erdos63.RobustSupply
import ErdosProblems.Erdos63.SourceLemma37Eventual

/-!
# Eventual numerical package for robust Liu--Montgomery adjusters

This file combines the two genuinely substantial uniform inputs—the routed
source Lemma 3.7 package and the canonical Claim 4.4 scale—with the scalar
eventual estimates already proved for the common parameter choice.
-/

open Filter

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

namespace SmallSimpleAdjusterCandidate

/-- The enlarged auxiliary target still fits below the quarter-order seed
used in Claim 4.6. -/
theorem eventually_lm43_ballTarget_le_K :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43BallTarget N d ≤ lm43K N := by
  have hsmall := Parameters.eventually_const_mul_log_pow_le_self
    (320 : ℝ) 42
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [eventually_lm43_target_envelopes, hsmallNat]
    with N htargets hsmallN
  intro d
  have hreal : (((4 * lm43BallTarget N d : ℕ) : ℝ)) ≤ (N : ℝ) := by
    push_cast
    calc
      (4 : ℝ) * lm43BallTarget N d ≤
          320 * Real.log (N : ℝ) ^ 42 := by
        nlinarith [(htargets d).2]
      _ ≤ (N : ℝ) := hsmallN
  have hnat : 4 * lm43BallTarget N d ≤ N := by exact_mod_cast hreal
  dsimp [lm43K]
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2 (by
    simpa [mul_comm] using hnat)

private theorem lm37FirstSlowGrowth_zero_eq_one :
    lm37FirstSlowGrowth 0 = 1 := by
  rw [lm37FirstSlowGrowth]
  norm_num

private theorem lm37FirstSlowGrowth_one_le_two :
    lm37FirstSlowGrowth 1 ≤ 2 := by
  apply Nat.le_of_lt_succ
  rw [lm37FirstSlowGrowth, Nat.floor_lt (Real.exp_pos _).le]
  norm_num
  exact Real.exp_one_lt_d9.trans (by norm_num)

private theorem lm43_source_start
    {N d : ℕ} (hd : 2 ^ 20 ≤ d) :
    lm37FirstSlowGrowth 0 < lm43MinRadius N d ^ 2 := by
  rw [lm37FirstSlowGrowth_zero_eq_one]
  have hmin : 5 ≤ lm43MinRadius N d := by
    have hpos : 0 < lm43MinRadius N d :=
      lm43MinRadius_pos ((by norm_num : 64 ≤ 2 ^ 20).trans hd)
    apply Nat.le_of_dvd hpos
    simp [lm43MinRadius, lm43MinRadiusFrom, lm43CoreRadius]
  nlinarith

private theorem lm43_source_start_one
    {d : ℕ} (hd : 2 ^ 20 ≤ d) :
    lm37FirstSlowGrowth 1 < lm37SourceMinSize d := by
  calc
    lm37FirstSlowGrowth 1 ≤ 2 := lm37FirstSlowGrowth_one_le_two
    _ < lm37SourceMinSize d := by
      simp only [lm37SourceMinSize, SourceLemma35Numerics.minFailedSize]
      omega

/-- Every scalar field of the robust package is automatic eventually in the
ambient order, uniformly in the degree parameter once the fixed bootstrap
threshold is imposed. -/
theorem eventually_lm43RobustSupplyNumericalPackage_of_data :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 2 ^ 20 ≤ d →
      LM43RoutedSourceNumericalPackage N d →
      Nonempty (SmallSimpleAdjusterCandidate.LM44Scale N d
        (lm43TargetOrder N d) (lm43TotalRadius N d)
        (lm43HighCutoff N d) (lm43DeletionCap N d)
        (lm43ProtectedCap N d) (lm43Separation N d)
        (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
        ((1 / 64) * (lm43CoreDegree N d : ℝ))) →
      Nonempty (LM43RobustSupplyNumericalPackage N d) := by
  filter_upwards [eventually_ge_atTop (32 : ℕ),
      eventually_lm43_R_pos,
      eventually_lm43_targetOrder_pos,
      eventually_lm43_candidateRadius_pos,
      eventually_lm43_avoidingRadius_pos,
      eventually_lm43_star_budgets,
      eventually_lm43_radius_budgets,
      eventually_lm43_claim46_workspace,
      eventually_lm43_ballTarget_le_K,
      eventually_lm43_denominator_fits,
      eventually_lm43_totalRadius_le_two_mul_lmSimpleRadius]
    with N hN hR htarget hmax hAvoid hstar hradius hworkspace hballK hden houtput
  intro d hd routed hclaim44
  obtain ⟨claim44⟩ := hclaim44
  have hdOne : 1 ≤ d := (by norm_num : 1 ≤ 2 ^ 20).trans hd
  exact ⟨
    { routed := routed
      claim44 := claim44
      card_large := hN
      degree_bootstrap := hd
      index_pos := hR d
      target_pos := htarget d
      maxRadius_pos := by simpa only [lm43MaxRadius] using hmax d
      highRadius_pos := by simpa only [lm43HighRadius] using hAvoid
      ballRadius_pos := by simpa only [lm43BallRadius] using hAvoid
      source_start := lm43_source_start hd
      source_start_one := lm43_source_start_one hd
      right_budget := (hstar d).1
      left_budget := (hstar d).2
      claim45_radius := (hradius d).1
      claim46_workspace := (hworkspace d).1
      claim46_room := (hworkspace d).2
      auxiliary_le_K := hballK d
      denominator_le_K := hden
      claim46_left_radius := (hradius d).2.1
      claim46_right_radius := (hradius d).2.2
      finalConnector := concreteLM43AdaptiveFinalConnectorCertificate hN hdOne
      output_radius := houtput d }⟩

/-- Uniform threshold constructor for the sole graph-free premise of the
finite robust-adjuster theorem. -/
theorem lm43RobustSupplyEventualNumerics_of_thresholds
    (hsource : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      LM43RoutedSourceNumericalPackage N d)
    (hclaim44 : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      Nonempty (SmallSimpleAdjusterCandidate.LM44Scale N d
        (lm43TargetOrder N d) (lm43TotalRadius N d)
        (lm43HighCutoff N d) (lm43DeletionCap N d)
        (lm43ProtectedCap N d) (lm43Separation N d)
        (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
        ((1 / 64) * (lm43CoreDegree N d : ℝ)))) :
    LM43RobustSupplyEventualNumerics := by
  obtain ⟨dSource, hSource⟩ := hsource
  obtain ⟨dClaim44, hClaim44⟩ := hclaim44
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.1 eventually_lm43RobustSupplyNumericalPackage_of_data
  let d₀ := max (2 ^ 20) (max dSource (max dClaim44 N₀))
  refine ⟨d₀, ?_⟩
  intro d hd N hdN
  have hdBootstrap : 2 ^ 20 ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdSource : dSource ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdClaim44 : dClaim44 ≤ d := by
    dsimp [d₀] at hd
    omega
  have hN₀N : N₀ ≤ N := by
    dsimp [d₀] at hd
    omega
  have hdNle : d ≤ N := Nat.le_of_lt hdN
  exact hN₀ N hN₀N d hdBootstrap (hSource d hdSource N hdNle)
    (hClaim44 d hdClaim44 N hdNle)

/-- The routed source estimates and the concrete Claim 4.4 construction
jointly discharge the sole graph-free premise of the robust supply theorem. -/
theorem lm43RobustSupplyEventualNumerics :
    LM43RobustSupplyEventualNumerics :=
  lm43RobustSupplyEventualNumerics_of_thresholds
    (exists_lm43_routedSourceNumericalPackage_threshold_of_geometry
      exists_lm43_sourceGeometricBounds_threshold)
    exists_threshold_concreteLM43Claim44Scale

/-- Unconditional inflated-order simple-adjuster supply used by the exact-path
assembly.  All numerical thresholds are chosen internally. -/
theorem liuMontgomery_lemma4_3_inflated_supply :
    ∃ d₀ : ℕ, ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj]
      (_B : Bipartition J) {d : ℕ},
      d₀ ≤ d →
      IsLMExpander J (1 / 1024) ((1 / 64) * (d : ℝ)) →
      (∀ v : W, d ≤ J.degree v) →
      ¬ SimpleGraph.IsContained (oneSubdivisionClique (d / 2)) J →
      ∀ U : Finset W, U.card ≤ lm47SimpleBudget (Fintype.card W) →
        ∃ A : Adjuster J (lm47InflatedOrder (Fintype.card W))
            (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card W)) 1,
          Disjoint U A.verts :=
  liuMontgomery_lemma4_3_finite_of_eventualNumerics
    lm43RobustSupplyEventualNumerics

end SmallSimpleAdjusterCandidate

end Erdos63

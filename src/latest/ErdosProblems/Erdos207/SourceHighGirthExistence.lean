/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFiniteMasterSchedule
import ErdosProblems.Erdos207.SourceInitialMasterBase
import ErdosProblems.Erdos207.CoverDownPacking

/-! # Unconditional eventual existence from the initial law, finite iteration and absorption -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem eventually_highGirthSteinerSystems_pos (q : ℕ) (hq : 1 ≤ q) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
      ∃ H : TripleSystem n, IsSteiner H ∧ GirthGreater q H := by
  obtain ⟨E⟩ := exists_source_ordinary_parameters q 4 2
  obtain ⟨rootPower, Rfixed, ell, length, tailLength, hfit, hlength,
    hrootMinimum, hrootGap, _, hRfixed, hbankExponent, hlength2, hsplit,
    hrootLower, hrootUpper, hfirstGap, hinitial⟩ :=
    eventually_exists_source_initial_master_base q 4 2 13 12 1 E.K hq (by norm_num) (by norm_num)
  let R := Rfixed+12*ell+1
  let v := fun i : Fin length ↦ retainedRatioExponent Rfixed 12 i.val
  let D := fun i : Fin length ↦ retainedStageExponent Rfixed 12 ell i.val
  let C0 := 2*ksssInitialGraphProductConstant q (initialErdosCoefficientBound q)
  let eta0 := sourceMasterEtaFloor q
  have hC0 : 1 ≤ C0 := by
    have hc : 1 ≤ ksssInitialGraphProductConstant q (initialErdosCoefficientBound q) :=
      (by norm_num : (1 : ℝ≥0) ≤ 2).trans (le_max_left _ _)
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ≥0) ≤ 2 by norm_num) hc zero_le zero_le
  have hgap := fun i : Fin length ↦ retained_stage_exponent_ratio_gap Rfixed 12 ell length tailLength rootPower E.K
    hsplit hrootLower.le hrootGap hfirstGap i
  obtain ⟨exponent, T, hT, hterminal⟩ := exists_source_finite_master_schedule q 4 2 length R rootPower 12 E v D C0 1 eta0
    (by norm_num) le_rfl (fun i ↦ (hgap i).1) (fun i ↦ (hgap i).2) (by norm_num)
    (by omega) hC0 le_rfl (sourceMasterEtaFloor_pos q) (sourceMasterEtaFloor_le_one q)
  let coefficient : ℝ≥0 := ∑ a : Fin (length+1), ∑ j : Fin (q+1), sourcePrefixFixedZ q a.val j.val
  let threshold := (max 2 T)^R+T+powerBankSubsetCoefficient q+⌈coefficient⌉₊
  obtain ⟨N₀, hN₀⟩ := hinitial threshold (exponent 0) 1 (by norm_num)
  refine ⟨N₀, ?_⟩
  intro n hn hadmissible
  obtain ⟨P, htThreshold, ht2, _hround, hnLower, hnUpper, hdensity, hsource, initialLaw, hinitialLaw⟩ :=
    hN₀ n hn hadmissible
  let t := dyadicPowerScale (Rfixed+12*ell) n
  let W := P.retainedVortex length hfit hlength
  let Gamma := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let ambient := outsideAvailableTriangles P.H P.B
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B) ambient
  let time := ksssDensityHorizon ((initialResidualPairs P.H).card : ℝ) (1/(t : ℝ)^2)
  let p := Real.toNNReal (ksssEdgeDensity ((initialResidualPairs P.H).card : ℝ) time)
  let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
    (initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ)) time))
  have hdensity' : 1/(t : ℝ≥0)^2 ≤ p ∧ p ≤ 2/(t : ℝ≥0)^2 ∧ p ≤ 1 ∧ eta0 ≤ eta ∧ eta ≤ 1 := hdensity
  have htNat : threshold ≤ t := htThreshold
  have htT : T ≤ t := by dsimp only [threshold] at htNat; omega
  have htScale : (max 2 T)^(Rfixed+12*ell+1) ≤ t := by
    change (max 2 T)^R ≤ t
    dsimp only [threshold] at htNat
    omega
  have htBank : powerBankSubsetCoefficient q ≤ t := by dsimp only [threshold] at htNat; omega
  have htCoefficient : ⌈coefficient⌉₊ ≤ t := by dsimp only [threshold] at htNat; omega
  have hfixed : ∀ (a : Fin (length+1)) (j : Fin (q+1)), sourcePrefixFixedZ q a.val j.val ≤ (t : ℝ≥0) := by
    intro a j
    have hinner : sourcePrefixFixedZ q a.val j.val ≤ ∑ j : Fin (q+1), sourcePrefixFixedZ q a.val j.val :=
      single_le_sum (f := fun j : Fin (q+1) ↦ sourcePrefixFixedZ q a.val j.val) (fun _ _ ↦ zero_le) (mem_univ j)
    have houter : (∑ j : Fin (q+1), sourcePrefixFixedZ q a.val j.val) ≤ coefficient :=
      single_le_sum (f := fun a : Fin (length+1) ↦ ∑ j : Fin (q+1), sourcePrefixFixedZ q a.val j.val)
        (fun _ _ ↦ zero_le) (mem_univ a)
    exact (hinner.trans houter).trans ((Nat.le_ceil coefficient).trans (by exact_mod_cast htCoefficient))
  let analytic := fun i : Fin length ↦
    dyadicPowerScale (ksssPowerDenominatorExponent q (2*(D i+1)) E.B ((26*q+12)*(D i+1)) (D i+1))
      (W.U i.castSucc).card
  have hgeometry : ∀ i : Fin length, T ≤ analytic i ∧ analytic i ≤ t ∧
      t^(E.P*v i) ≤ (analytic i)^(D i+1) ∧ t^(D i) ≤ (W.U i.castSucc).card ∧
      t^(D i-v i) ≤ (W.U i.succ).card ∧ (W.U i.castSucc).card ≤ t^(v i)*(W.U i.succ).card ∧
      t^12*(W.U i.succ).card ≤ 2*(W.U i.castSucc).card ∧
      (analytic i)^ksssPowerDenominatorExponent q (2*(D i+1)) E.B ((26*q+12)*(D i+1)) (D i+1) ≤
        (W.U i.castSucc).card := by
    intro i
    obtain ⟨_, _, hlo, _, hstepRatio, hratio, hinner, _, hscale, _, hat, hpower, ha, _⟩ :=
      E.retained_stage_scales P T hsplit hlength2 ht2 hrootLower.le hrootUpper hrootGap hfirstGap
        hnLower hnUpper htScale i
    exact ⟨ha, hat, hpower, hlo, hinner, hratio, hstepRatio, hscale⟩
  have hz : ∀ i : Fin length, ∀ j ∈ Icc 4 q, sourcePrefixZ q P.B i.val j ≤ (t : ℝ≥0)^(v i) := by
    intro i j hj
    exact P.sourcePrefixZ_power htBank hbankExponent i.val j
      (hfixed i.castSucc ⟨j, by have hjq := (mem_Icc.mp hj).2; omega⟩)
  have hfutureZ : ∀ a : Fin length, 0 < a.val → ∀ j ∈ Icc 4 q, sourcePrefixZ q P.B a.val j ≤ (t : ℝ≥0) := by
    intro a ha j hj
    exact sourcePrefixZ_le_base_of_ne_zero q a.val j P.B t (by exact_mod_cast P.base_ge_one) (by omega)
      (hfixed a.castSucc ⟨j, by have hjq := (mem_Icc.mp hj).2; omega⟩)
  have hnonempty : ∀ a, (W.U a).Nonempty := fun a ↦ P.nonempty (terminalJumpStage ell length hfit a)
  have hbase : ∃ law : FiniteLaw (MasterStateOn (Fin n)),
      IsResidualCompressedMasterLaw law W 0 (absorberErdosForbiddenConfigurationsOn q P.B)
        Gamma ambient p eta (17/(t : ℝ≥0)) C0 (1/(t : ℝ≥0)^(exponent 0)) 4 :=
    ⟨initialLaw, hinitialLaw⟩
  obtain ⟨law, hlaw⟩ := hterminal t htT W P.B ambient Gamma analytic
    (by simpa only [Fintype.card_fin] using hnUpper) hgeometry hz
    (fun a ↦ P.retainedVortex_level_card_lower hfit hlength a) hfutureZ
    p eta hdensity'.1 hdensity'.2.1 hdensity'.2.2.2.1 hdensity'.2.2.2.2 hnonempty hsource hbase
  have hxi : (17+length : ℕ)/(t : ℝ≥0) < 1 := by
    have ht0 : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by omega)
    apply (div_lt_one ht0).mpr
    exact_mod_cast (show 17+length < t by omega)
  obtain ⟨packing, hpacking⟩ := hlaw.exists_ksssOutsidePacking (P.retainedVortex_terminal hfit hlength) hxi
  exact highGirthSteiner_of_ksssCoverDownCertificate
    (ksssCoverDownCertificate_of_outsidePacking hadmissible P.absorption hpacking)

end

end Erdos207

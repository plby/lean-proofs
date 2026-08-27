/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualGradualMasterBase
import ErdosProblems.Erdos207.InitialMasterDensityScalars
import ErdosProblems.Erdos207.InitialMasterErrorPowers
import ErdosProblems.Erdos207.SourceMasterConstants

/-! # The actual initial base accommodates all thresholds chosen after the finite vortex -/

namespace Erdos207

open scoped Classical NNReal

noncomputable section

def HasSourceInitialDensityWindow
    {V : Type*} [Fintype V] [DecidableEq V] (q b t : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) : Prop :=
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let E : ℝ := (initialResidualPairs H).card
  let time := ksssDensityHorizon E (1/(t : ℝ)^b)
  let p := Real.toNNReal (ksssEdgeDensity E time)
  let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
    (initialErdosTrajectoryCoefficient V (S₀.available.card : ℝ)) time))
  1/(t : ℝ≥0)^b ≤ p ∧ p ≤ 2/(t : ℝ≥0)^b ∧ p ≤ 1 ∧ sourceMasterEtaFloor q ≤ eta ∧ eta ≤ 1

theorem eventually_exists_source_initial_master_base
    (q h b rootMinimum step Rfloor K : ℕ) (hq : 1 ≤ q) (hb : 1 ≤ b) (hstep : 0 < step) :
    ∃ rootPower Rfixed ell length m : ℕ, ∃ hfit : length ≤ ell, ∃ hlength : 0 < length,
      rootMinimum ≤ rootPower ∧ K*(2*step+1) ≤ rootPower ∧ Rfloor ≤ Rfixed ∧ 0 < Rfixed ∧
      powerBankSubsetExponent q rootPower+2 ≤ Rfixed ∧ 2 ≤ length ∧ length+m = ell ∧
      rootPower < step*m ∧ step*m ≤ rootPower+step ∧
      K*(Rfixed+step+1) ≤ Rfixed+step*ell ∧
      ∀ threshold exponent : ℕ, ∀ B0 : ℝ≥0, 0 < B0 →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
          ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale (Rfixed+step*ell) n) rootPower step,
            let t := dyadicPowerScale (Rfixed+step*ell) n
            threshold ≤ t ∧ 2 ≤ t ∧ 2^(Rfixed+step*ell) ≤ t ∧
            t^(Rfixed+step*ell) ≤ n ∧ n ≤ t^(Rfixed+step*ell+1) ∧
            HasSourceInitialDensityWindow q b t P.H P.B ∧
            HasAbsorberSourcePrefixBounds q P.B (P.retainedVortex length hfit hlength) ∧
            ∃ law : FiniteLaw (MasterStateOn (Fin n)),
              IsInitialResidualCompressedMasterLawWithError q h b t P.H P.B
                (P.retainedVortex length hfit hlength)
                (2*ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
                (B0/(t : ℝ≥0)^exponent) law := by
  obtain ⟨B, k, rootPower, Rfixed, ell, length, m, Nbase, hfit, hlength,
    hroot, hrootGap, hfloor, hfixed, hbank, hlength2, hsplit, hrootLo, hrootHi, hfirst, hbase⟩ :=
    eventually_exists_gradual_initial_master_base_with_bank q h b rootMinimum step (max Rfloor (b+1)) K hb hstep
  let R := Rfixed+step*ell
  have hR : 0 < R := by dsimp only [R]; omega
  refine ⟨rootPower, Rfixed, ell, length, m, hfit, hlength, hroot, hrootGap,
    (le_max_left _ _).trans hfloor, hfixed, hbank, hlength2, hsplit, hrootLo, hrootHi, hfirst, ?_⟩
  intro threshold exponent B0 hB0
  obtain ⟨Terror, hTerror, herror⟩ := eventually_initialPatternGraphError_le_power q h ell (R+1) exponent B0 hB0
  let target := max threshold (max 48 (max (powerAbsorberCoefficient q) Terror))
  obtain ⟨Nscale, hNscale⟩ := eventually_le_dyadicPowerScale hR target
  refine ⟨Nbase+Nscale+1, ?_⟩
  intro n hn hadmissible
  obtain ⟨P, ht2, hround, hsource, _initialLaw, _hinitial, law, hlaw⟩ := hbase n (by omega) hadmissible
  let t := dyadicPowerScale R n
  have htarget : target ≤ t := hNscale n (by omega)
  have htThreshold : threshold ≤ t := (le_max_left _ _).trans htarget
  have ht48 : 48 ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans htarget)
  have htCoefficient : powerAbsorberCoefficient q ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans htarget))
  have htError : Terror ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans htarget))
  have hn0 : n ≠ 0 := by omega
  have hnLower : t^R ≤ n := dyadicPowerScale_pow_le hn0
  have hnUpper : n ≤ t^(R+1) := by
    calc
      n ≤ 2^R*t^R := le_two_pow_mul_dyadicPowerScale_pow hR
      _ ≤ t*t^R := Nat.mul_le_mul_right _ hround
      _ = _ := (pow_succ' _ _).symm
  have hsupportGap : initialSupportPower rootPower+1 ≤ R := by
    have hs := initialSupportPower_le_bankSubsetExponent q rootPower hq
    dsimp only [R]
    omega
  have hdensityGap : b+1 ≤ R := by
    have hh := (le_max_right Rfloor (b+1)).trans hfloor
    dsimp only [R]
    omega
  have hdensity : HasSourceInitialDensityWindow q b t P.H P.B :=
    P.initial_master_density_scalars b R ht48 htCoefficient hnLower hsupportGap hdensityGap
  have herr : initialPatternGraphError q h ell n t ≤ B0/(t : ℝ≥0)^exponent :=
    herror t htError n hnUpper
  refine ⟨P, htThreshold, ht2, hround, hnLower, hnUpper, hdensity, hsource, law, ?_⟩
  exact (show IsResidualCompressedMasterLaw _ _ _ _ _ _ _ _ _ _ _ _ from hlaw).mono_constants le_rfl herr

end

end Erdos207

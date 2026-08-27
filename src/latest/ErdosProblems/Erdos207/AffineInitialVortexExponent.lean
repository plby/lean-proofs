/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualResidualMasterBase
import ErdosProblems.Erdos207.InitialRetainedVortexLaw

/-! # Initial laws with an ambient exponent affine in the vortex length -/

namespace Erdos207

open scoped Classical NNReal

noncomputable section

theorem eventually_exists_initial_pattern_law_affine_vortex_exponent_with_bank
    (q h rootMinimum b Rfloor : ℕ) (hb : 1 ≤ b) :
    ∃ B k rootPower Rfixed : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ Rfixed ∧ 0 < Rfixed ∧
      powerBankSubsetExponent q rootPower + 2 ≤ Rfixed ∧
      ∀ step ell : ℕ, 0 < ell → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale (Rfixed + step * ell) n) rootPower step,
          ∃ law, IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale (Rfixed + step * ell) n) P.H P.B P.W law ∧
            (∀ i : Fin ell, ∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix i.succ) j (absorberInducedConfigurationsOn q j P.B)
                (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
                (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
                  exactBankVortexCoefficient j (i.val + 1))) ∧
            (∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix 0) j (absorberInducedConfigurationsOn q j P.B)
                (2 * exactBankVortexOrderCoefficient q 0)
                (2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
                  exactBankVortexCoefficient j 0)) ∧
            (Admissible n → ∃ masterLaw, IsInitialResidualCompressedMasterLaw q h b
              (dyadicPowerScale (Rfixed + step * ell) n) P.H P.B P.W masterLaw) ∧
            HasRetainedInitialLaw P b B k law := by
  obtain ⟨B, hB, hpair, hconfiguration⟩ :=
    exists_ksss_indexed_envelope_exponent q (initialErdosCoefficientBound q)
  let s := ksssPowerErrorExponent b B
  let r := 2 * s + b * h + h ^ 2 + 2 * b + 1
  let rootPower := max rootMinimum (r + q * (5 * b + 3) + 4)
  have hrootMin : rootMinimum ≤ rootPower := le_max_left _ _
  have hrootSize : r + q * (5 * b + 3) + 4 ≤ rootPower := le_max_right _ _
  have hroot : 2 ≤ rootPower := by omega
  let u := powerAbsorberCrudeExponent q rootPower
  let k := dyadicCrudeExponent q u (5 * b + 2)
  let fixed := (initialRegularityCoefficientPower q rootPower + 2 + (s + 1) + b * q) +
    (initialSupportPower rootPower + (s + 1) + 2) + (156 * rootPower + 2) + Rfloor +
    (r + k + 1) + (u + ((r + 2) + q * (5 * b + 3) + 1)) + (b * h + h ^ 2 + s + 3 * b + 2) +
    (powerBankSubsetExponent q rootPower + rootPower + 2)
  let Rfixed := ksssPowerDenominatorExponent q b B k fixed
  have hfixedFloor : Rfloor ≤ Rfixed := by
    dsimp only [Rfixed, ksssPowerDenominatorExponent, fixed]
    omega
  have hfixedPos : 0 < Rfixed := by
    dsimp only [Rfixed, ksssPowerDenominatorExponent]
    omega
  have hbankFixed : powerBankSubsetExponent q rootPower + 2 ≤ Rfixed := by
    dsimp only [Rfixed, ksssPowerDenominatorExponent, fixed]
    omega
  refine ⟨B, k, rootPower, Rfixed, hrootMin, hfixedFloor, hfixedPos, hbankFixed, ?_⟩
  intro step ell hell
  let Rmin := fixed + step * ell
  let R := ksssPowerDenominatorExponent q b B k Rmin
  have hR_eq : R = Rfixed + step * ell := by
    dsimp only [R, Rfixed, Rmin, ksssPowerDenominatorExponent]
    omega
  rw [← hR_eq]
  have hRmin : Rmin ≤ R := by dsimp only [R, ksssPowerDenominatorExponent]; omega
  have hRpos : 0 < R := by dsimp only [R, ksssPowerDenominatorExponent]; omega
  have hrootGap : initialRegularityCoefficientPower q rootPower + 2 + (s + 1) + b * q ≤ R := by
    dsimp only [Rmin, fixed] at hRmin
    omega
  have hpairGap : initialSupportPower rootPower + (s + 1) + 2 ≤ R := by
    dsimp only [Rmin, fixed] at hRmin
    omega
  have habsorber : 156 * rootPower + 2 ≤ R := by dsimp only [Rmin, fixed] at hRmin; omega
  have hfree : step * ell + 1 ≤ R := by dsimp only [Rmin, fixed] at hRmin; omega
  have houterGap : r + k + 1 ≤ R := by dsimp only [Rmin, fixed] at hRmin; omega
  have hlocalGap : u + ((r + 2) + q * (5 * b + 3) + 1) ≤ R := by dsimp only [Rmin, fixed] at hRmin; omega
  have hstepLe : step * (ell - 1) ≤ step * ell :=
    Nat.mul_le_mul_left step (Nat.sub_le ell 1)
  have hsourceGap : powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1 ≤ R := by
    dsimp only [Rmin, fixed] at hRmin
    omega
  have hpatternRmin : b * h + h ^ 2 + ksssPowerErrorExponent b B + 3 * b + 2 ≤ Rmin := by
    dsimp only [Rmin, fixed, s]
    omega
  let threshold := max 32 (max (powerAbsorberCoefficient q)
    (max (powerAbsorberCrudeCoefficient q) (max (pairBankPolynomialCoefficient q)
      (max (2 ^ (q ^ 3) * (q + 1)) (max (2 ^ q) (max q
        (max (2 * (2 * q + 1) ^ (2 * q + 1)) (max (6 * (B + 2) * 2 ^ (B + 2))
          (max (2 * h + 36 * h ^ 2) (max (3 + h ^ 2)
            (max (45 * (q + 1) + 28) (4 * (q + 1) ^ (q + 2)))))))))))))
  let sourceThreshold := max threshold (powerBankSubsetCoefficient q)
  obtain ⟨T, hTmin, hT⟩ := exists_ksss_pattern_power_threshold q b B h Rmin sourceThreshold
    (initialErdosCoefficientBound q) hb hpatternRmin
  obtain ⟨Ncoeff, hNcoeff⟩ := eventually_ksss_power_coefficient_bounds q B R T
    (initialErdosCoefficientBound q) hRpos
  obtain ⟨Npackage, hNpackage⟩ := eventually_exists_initialPowerVortexPackage q h rootPower step ell R
    hell hroot habsorber hfree
  obtain ⟨Ntail, hNtail⟩ := eventually_polynomial_dyadic_geometric_lt R (6 + 2 * h ^ 2)
    (8 * (q + 1 : ℝ) ^ 2 + 5 * (ell + 1 : ℝ) + 2 * (ell + 1 : ℝ) * h ^ 2) (1 / 2) hRpos (by positivity) (by norm_num)
  refine ⟨Ncoeff + Npackage + Ntail + 1, ?_⟩
  intro n hn
  have hnpos : n ≠ 0 := by omega
  obtain ⟨P⟩ := hNpackage n (by omega)
  obtain ⟨htT, hcoeff⟩ := hNcoeff n (by omega)
  let t := dyadicPowerScale R n
  have hsourceThreshold : sourceThreshold ≤ t := hTmin.trans htT
  have hthreshold : threshold ≤ t := (le_max_left _ _).trans hsourceThreshold
  have hbankCoeff : powerBankSubsetCoefficient q ≤ t := (le_max_right _ _).trans hsourceThreshold
  have hbudgets : 32 ≤ t ∧ powerAbsorberCoefficient q ≤ t ∧ powerAbsorberCrudeCoefficient q ≤ t ∧
      pairBankPolynomialCoefficient q ≤ t ∧ 2 ^ (q ^ 3) * (q + 1) ≤ t ∧ 2 ^ q ≤ t ∧ q ≤ t ∧
      2 * (2 * q + 1) ^ (2 * q + 1) ≤ t ∧ 6 * (B + 2) * 2 ^ (B + 2) ≤ t ∧
      2 * h + 36 * h ^ 2 ≤ t ∧ 3 + h ^ 2 ≤ t ∧ 45 * (q + 1) + 28 ≤ t ∧
      4 * (q + 1) ^ (q + 2) ≤ t := by
    simpa only [threshold, max_le_iff] using hthreshold
  obtain ⟨ht, hc, hcrude, hempty, hvertex, hbinomial, horder, hconst, hdegree,
    hpatternCoeff, hedgeCoeff, hlocalRootCoeff, hlocalConst⟩ := hbudgets
  obtain ⟨law, hlaw⟩ := P.exists_initial_typical_pattern_law b B k Rmin r hb ht hc hcrude hempty hvertex hbinomial horder hconst
    (dyadicPowerScale_pow_le hnpos) hrootGap hpairGap hcoeff hB hpair hconfiguration rfl
    (by exact_mod_cast hdegree) rfl hrootSize houterGap hlocalGap hpatternCoeff hedgeCoeff hlocalRootCoeff hlocalConst
    (hT t htT k) (by simpa only [Nat.cast_add, Nat.cast_one] using hNtail n (by omega))
  refine ⟨P, law, hlaw, ?_, ?_, ?_, ?_⟩
  · intro i j hj hjq
    exact P.positive_prefix_sourceWellSpread (by omega) hell hbankCoeff hsourceGap
      (dyadicPowerScale_pow_le hnpos) i j hj hjq
  · intro j hj _hjq
    have hbankGap : powerBankSubsetExponent q rootPower ≤ R :=
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 1)).trans hsourceGap
    exact P.zero_prefix_sourceWellSpread hbankCoeff hbankGap (dyadicPowerScale_pow_le hnpos) j hj

  · intro hadmissible
    exact ⟨_, P.compressed_residual_master_of_initial_pattern_law hadmissible law hlaw⟩
  · have hlarge : 6 * t ^ initialSupportPower rootPower + 4 ≤ n := by
      have hbound := initial_support_density_power (t : ℝ) (initialSupportPower rootPower)
        (by exact_mod_cast (show 10 ≤ t by omega))
      have hp : t ^ (initialSupportPower rootPower + 1) ≤ n :=
        (Nat.pow_le_pow_right (by omega : 0 < t) (by omega : initialSupportPower rootPower + 1 ≤ R)).trans
          (dyadicPowerScale_pow_le hnpos)
      exact (show 6 * t ^ initialSupportPower rootPower + 4 ≤ t ^ (initialSupportPower rootPower + 1)
        by exact_mod_cast hbound).trans hp
    apply P.retained_initial_law law hlaw hb (by omega) (by omega) hc hlarge
      (by dsimp only [r] at hrootSize; omega) hcoeff.poisson hell hbankCoeff hsourceGap
    exact dyadicPowerScale_pow_le hnpos

theorem eventually_exists_initial_pattern_law_affine_vortex_exponent
    (q h rootMinimum b Rfloor : ℕ) (hb : 1 ≤ b) :
    ∃ B k rootPower Rfixed : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ Rfixed ∧ 0 < Rfixed ∧
      ∀ step ell : ℕ, 0 < ell → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale (Rfixed + step * ell) n) rootPower step,
          ∃ law, IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale (Rfixed + step * ell) n) P.H P.B P.W law ∧
            (∀ i : Fin ell, ∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix i.succ) j (absorberInducedConfigurationsOn q j P.B)
                (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
                (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
                  exactBankVortexCoefficient j (i.val + 1))) ∧
            (∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix 0) j (absorberInducedConfigurationsOn q j P.B)
                (2 * exactBankVortexOrderCoefficient q 0)
                (2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
                  exactBankVortexCoefficient j 0)) ∧
            (Admissible n → ∃ masterLaw, IsInitialResidualCompressedMasterLaw q h b
              (dyadicPowerScale (Rfixed + step * ell) n) P.H P.B P.W masterLaw) ∧
            HasRetainedInitialLaw P b B k law := by
  obtain ⟨B, k, rootPower, Rfixed, hroot, hfloor, hpos, _hbank, hrest⟩ :=
    eventually_exists_initial_pattern_law_affine_vortex_exponent_with_bank q h rootMinimum b Rfloor hb
  exact ⟨B, k, rootPower, Rfixed, hroot, hfloor, hpos, hrest⟩


end

end Erdos207

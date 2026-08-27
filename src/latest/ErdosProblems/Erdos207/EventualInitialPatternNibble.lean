/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPatternGraphLaw
import ErdosProblems.Erdos207.KSSSPatternCoefficientChoice
import ErdosProblems.Erdos207.PowerSourceWellSpread

/-! # Eventual initial nibble with all vortex degree and relative extension bands

This initial-stage theorem does not yet include the recursive distribution
or the final Steiner triple system.
-/

namespace Erdos207

open scoped Classical
open scoped NNReal

noncomputable section

theorem eventually_exists_initial_typical_pattern_law_with_source_bounds
    (q h rootMinimum step ell b Rfloor : ℕ) (hell : 0 < ell) (hb : 1 ≤ b) :
    ∃ B k rootPower R N₀ : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ R ∧ 0 < R ∧
      ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale R n) rootPower step,
          ∃ law, IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale R n) P.H P.B P.W law ∧
            (∀ i : Fin ell, ∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix i.succ) j (absorberInducedConfigurationsOn q j P.B)
                (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
                (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
                  exactBankVortexCoefficient j (i.val + 1))) ∧
            ∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix 0) j (absorberInducedConfigurationsOn q j P.B)
                (2 * exactBankVortexOrderCoefficient q 0)
                (2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
                  exactBankVortexCoefficient j 0) := by
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
  let Rmin := (initialRegularityCoefficientPower q rootPower + 2 + (s + 1) + b * q) +
    (initialSupportPower rootPower + (s + 1) + 2) + (156 * rootPower + 2) + (step * ell + 1) + Rfloor +
    (r + k + 1) + (u + ((r + 2) + q * (5 * b + 3) + 1)) + (b * h + h ^ 2 + s + 3 * b + 2) +
    (powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1)
  let R := ksssPowerDenominatorExponent q b B k Rmin
  have hRmin : Rmin ≤ R := by dsimp only [R, ksssPowerDenominatorExponent]; omega
  have hRpos : 0 < R := by dsimp only [R, ksssPowerDenominatorExponent]; omega
  have hrootGap : initialRegularityCoefficientPower q rootPower + 2 + (s + 1) + b * q ≤ R := by
    dsimp only [Rmin] at hRmin
    omega
  have hpairGap : initialSupportPower rootPower + (s + 1) + 2 ≤ R := by
    dsimp only [Rmin] at hRmin
    omega
  have habsorber : 156 * rootPower + 2 ≤ R := by dsimp only [Rmin] at hRmin; omega
  have hfree : step * ell + 1 ≤ R := by dsimp only [Rmin] at hRmin; omega
  have hRfloor : Rfloor ≤ R := by dsimp only [Rmin] at hRmin; omega
  have houterGap : r + k + 1 ≤ R := by dsimp only [Rmin] at hRmin; omega
  have hlocalGap : u + ((r + 2) + q * (5 * b + 3) + 1) ≤ R := by dsimp only [Rmin] at hRmin; omega
  have hsourceGap : powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1 ≤ R := by
    dsimp only [Rmin] at hRmin
    omega
  have hpatternRmin : b * h + h ^ 2 + ksssPowerErrorExponent b B + 3 * b + 2 ≤ Rmin := by
    dsimp only [Rmin, s]
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
  refine ⟨B, k, rootPower, R, Ncoeff + Npackage + Ntail + 1, hrootMin, hRfloor, hRpos, ?_⟩
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
  refine ⟨P, law, hlaw, ?_, ?_⟩
  · intro i j hj hjq
    exact P.positive_prefix_sourceWellSpread (by omega) hell hbankCoeff hsourceGap
      (dyadicPowerScale_pow_le hnpos) i j hj hjq
  · intro j hj _hjq
    have hbankGap : powerBankSubsetExponent q rootPower ≤ R :=
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 1)).trans hsourceGap
    exact P.zero_prefix_sourceWellSpread hbankCoeff hbankGap (dyadicPowerScale_pow_le hnpos) j hj

theorem eventually_exists_initial_typical_pattern_law
    (q h rootMinimum step ell b Rfloor : ℕ) (hell : 0 < ell) (hb : 1 ≤ b) :
    ∃ B k rootPower R N₀ : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ R ∧ 0 < R ∧
      ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale R n) rootPower step,
          ∃ law, IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale R n) P.H P.B P.W law := by
  obtain ⟨B, k, rootPower, R, N₀, hroot, hRfloor, hRpos, hN⟩ :=
    eventually_exists_initial_typical_pattern_law_with_source_bounds q h rootMinimum step ell b Rfloor hell hb
  refine ⟨B, k, rootPower, R, N₀, hroot, hRfloor, hRpos, ?_⟩
  intro n hn
  obtain ⟨P, law, hlaw, _hsource⟩ := hN n hn
  exact ⟨P, law, hlaw⟩

theorem eventually_exists_initial_typical_pattern_nibble
    (q h rootMinimum step ell b Rfloor : ℕ) (hell : 0 < ell) (hb : 1 ≤ b) :
    ∃ B k rootPower R N₀ : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ R ∧ 0 < R ∧
      ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale R n) rootPower step,
          ∃ S, IsInitialTypicalPatternOutcome q h b B k (dyadicPowerScale R n) P.H P.B P.W S := by
  obtain ⟨B, k, rootPower, R, N₀, hroot, hfloor, hR, h⟩ :=
    eventually_exists_initial_typical_pattern_law q h rootMinimum step ell b Rfloor hell hb
  refine ⟨B, k, rootPower, R, N₀, hroot, hfloor, hR, ?_⟩
  intro n hn
  obtain ⟨P, law, hlaw⟩ := h n hn
  obtain ⟨S, hmass⟩ := law.exists_mass_pos
  exact ⟨P, S, hlaw.1 S hmass⟩

theorem eventually_exists_initial_pattern_coupled_nibble
    (q h rootMinimum step ell b Rfloor : ℕ) (hell : 0 < ell) (hb : 1 ≤ b) :
    ∃ B k rootPower R N₀ : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ R ∧ 0 < R ∧
      ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale R n) rootPower step,
          ∃ S, IsInitialPatternOutcome q h b B k (dyadicPowerScale R n) P.H P.B P.W S := by
  obtain ⟨B, k, rootPower, R, N₀, hroot, hfloor, hR, h⟩ :=
    eventually_exists_initial_typical_pattern_nibble q h rootMinimum step ell b Rfloor hell hb
  refine ⟨B, k, rootPower, R, N₀, hroot, hfloor, hR, ?_⟩
  intro n hn
  obtain ⟨P, S, hS⟩ := h n hn
  exact ⟨P, S, hS.1⟩

end

end Erdos207

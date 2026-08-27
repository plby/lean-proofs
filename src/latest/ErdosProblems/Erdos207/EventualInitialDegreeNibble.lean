/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialDegreeCoupledNibble
import ErdosProblems.Erdos207.DegreeCoupledTailDecay

/-! # Eventual initial nibble with simultaneous degree regularity at every vortex level

Bounded-pattern extension counts and recursive distribution are still separate
requirements for the final Steiner-system construction.
-/

namespace Erdos207

open scoped Classical

noncomputable section

theorem eventually_exists_initial_degree_coupled_nibble
    (q h rootMinimum step ell b Rfloor : ℕ) (hell : 0 < ell) (hb : 1 ≤ b) :
    ∃ B k rootPower R N₀ : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ R ∧ 0 < R ∧
      ∀ n : ℕ, N₀ ≤ n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale R n) rootPower step,
          ∃ S, IsInitialCoupledOutcome q b B k (dyadicPowerScale R n) P.H P.B S ∧
            AllUncoveredNeighborBands P.W.U (initialResidualPairs P.H) (initialResidualPairs P.H).card
              (dyadicPowerScale R n) (ksssPowerErrorExponent b B) B
              (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (dyadicPowerScale R n : ℝ) ^ b)) S := by
  obtain ⟨B, hB, hpair, hconfiguration⟩ :=
    exists_ksss_indexed_envelope_exponent q (initialErdosCoefficientBound q)
  let s := ksssPowerErrorExponent b B
  let rootPower := max rootMinimum (2 * s + 2 * b + 3)
  have hrootMin : rootMinimum ≤ rootPower := le_max_left _ _
  have hrootSize : 2 * s + 2 * b + 3 ≤ rootPower := le_max_right _ _
  have hroot : 2 ≤ rootPower := by omega
  let k := dyadicCrudeExponent q (powerAbsorberCrudeExponent q rootPower) (5 * b + 2)
  let Rmin := (initialRegularityCoefficientPower q rootPower + 2 + (s + 1) + b * q) +
    (initialSupportPower rootPower + (s + 1) + 2) + (156 * rootPower + 2) + (step * ell + 1) + Rfloor
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
  let threshold := max (max 32 (max (powerAbsorberCoefficient q) (max (powerAbsorberCrudeCoefficient q)
    (max (pairBankPolynomialCoefficient q) (max (2 ^ (q ^ 3) * (q + 1))
      (max (2 ^ q) (max q (2 * (2 * q + 1) ^ (2 * q + 1))))))))) (6 * (B + 2) * 2 ^ (B + 2))
  obtain ⟨Ncoeff, hNcoeff⟩ := eventually_ksss_power_coefficient_bounds q B R threshold
    (initialErdosCoefficientBound q) hRpos
  obtain ⟨Npackage, hNpackage⟩ := eventually_exists_initialPowerVortexPackage q h rootPower step ell R
    hell hroot habsorber hfree
  obtain ⟨Ntail, hNtail⟩ := eventually_degree_coupled_failure_lt_one q (ell + 1) R hRpos
  refine ⟨B, k, rootPower, R, Ncoeff + Npackage + Ntail + 1, hrootMin, hRfloor, hRpos, ?_⟩
  intro n hn
  have hnpos : n ≠ 0 := by omega
  obtain ⟨P⟩ := hNpackage n (by omega)
  obtain ⟨hthreshold, hcoeff⟩ := hNcoeff n (by omega)
  let t := dyadicPowerScale R n
  have hbudgets : (32 ≤ t ∧ powerAbsorberCoefficient q ≤ t ∧
      powerAbsorberCrudeCoefficient q ≤ t ∧ pairBankPolynomialCoefficient q ≤ t ∧
      2 ^ (q ^ 3) * (q + 1) ≤ t ∧ 2 ^ q ≤ t ∧ q ≤ t ∧
      2 * (2 * q + 1) ^ (2 * q + 1) ≤ t) ∧ 6 * (B + 2) * 2 ^ (B + 2) ≤ t := by
    simpa only [threshold, max_le_iff, t] using hthreshold
  obtain ⟨⟨ht, hc, hcrude, hempty, hvertex, hbinomial, horder, hconst⟩, hdegree⟩ := hbudgets
  refine ⟨P, ?_⟩
  exact P.exists_initial_degree_coupled_nibble b B k Rmin hb ht hc hcrude hempty hvertex hbinomial horder
    hconst (dyadicPowerScale_pow_le hnpos) hrootGap hpairGap hcoeff hB hpair hconfiguration rfl
    (by exact_mod_cast hdegree) hrootSize
    (by simpa only [Nat.cast_add, Nat.cast_one] using hNtail n (by omega))

end

end Erdos207

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCorridorAlgebra
import ErdosProblems.Erdos207.InitialOuterEligibleCount
import Mathlib.Data.Nat.Choose.Cast

/-!
# Initial endpoint of the fine outer corridor

This is the cast-and-normalization bridge from cardinal inequalities to the
two initial barrier inequalities required by the recursive comparison.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem fineOuter_initial_barrier_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside lower₀ t : ℕ)
    (houtside : 0 < outside)
    (hsmall : ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100)
    (hpairLower : (outside : ℝ) ^ 2 *
        (1 - 3 * (fineOuterCorridorError t : ℝ≥0)) ≤
      2 * (outerSharpEligiblePairs H X 0 : ℕ))
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hlower₀ : (1 - 16 * (fineOuterCorridorError t : ℝ≥0)) * outside ≤
      (lower₀ : ℝ)) :
    (outside : ℝ) ≤
        quadraticPairBarrier (outside : ℝ≥0)
          (fineOuterUpperCoefficient t) (perturbedOuterUpperR0 H X)
          (fineOuterUpperSlope t) 0 ∧
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOuterLowerCoefficient t) (perturbedOuterLowerR0 H X)
          (fineOuterLowerSlope t) 0 ≤ (lower₀ : ℝ) := by
  let epsilon : ℝ := (fineOuterCorridorError t : ℝ≥0)
  let E : ℝ := (outerSharpEligiblePairs H X 0 : ℕ)
  let N : ℝ := outside
  have hepsilon : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := by positivity
  have hN : 0 < N := by
    have hN' : (0 : ℝ) < (outside : ℝ) := by exact_mod_cast houtside
    simpa only [N] using hN'
  have hcrossUpper : N ^ 4 ≤ (4 + 64 * epsilon) * E ^ 2 :=
    fine_upper_initial_crossmul hN.le hE hepsilon (by simpa [epsilon] using hsmall)
      (by simpa only [N, E, epsilon] using hpairLower)
  have hupper : N ≤ (4 + 64 * epsilon) * E ^ 2 * N⁻¹ ^ 3 :=
    le_mul_inv_cube_of_pow_four_le hN (by positivity) hcrossUpper
  have hsmall16 : epsilon ≤ 1 / 16 := by
    dsimp only [epsilon] at hsmall ⊢
    nlinarith
  have hcrossLower : (4 - 64 * epsilon) * E ^ 2 ≤
      (1 - 16 * epsilon) * N ^ 4 :=
    fine_lower_initial_crossmul hN.le hE hepsilon hsmall16
      (by simpa only [N, E] using hpairUpper)
  have hlower : (4 - 64 * epsilon) * E ^ 2 * N⁻¹ ^ 3 ≤
      (1 - 16 * epsilon) * N :=
    mul_inv_cube_le_of_crossmul hN hcrossLower
  have h64 : 64 * fineOuterCorridorError t ≤ (4 : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    change 64 * epsilon ≤ 4
    nlinarith
  constructor
  · simpa [quadraticPairBarrier, affineSurvivalEnvelope,
      fineOuterUpperCoefficient, perturbedOuterUpperR0, N, E, epsilon] using
        hupper
  · apply (show quadraticPairBarrier (outside : ℝ≥0)
        (fineOuterLowerCoefficient t) (perturbedOuterLowerR0 H X)
        (fineOuterLowerSlope t) 0 ≤
      (1 - 16 * epsilon) * N by
        simpa [quadraticPairBarrier, affineSurvivalEnvelope,
          NNReal.coe_sub h64, fineOuterLowerCoefficient,
          perturbedOuterLowerR0, N, E, epsilon] using hlower).trans
    simpa only [N, epsilon] using hlower₀

/-- The packaged absorber edge bound gives the two real eligible-pair
estimates used by either choice of quadratic corridor. -/
theorem FineInitialPowerVortexPackage.initialOuter_eligiblePair_bounds
    {q h n ell t T rootPower step : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell)
    (habsorberFits :
      (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156) ^ 2 ≤
        Nat.choose
          (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card 2)
    (hdefect :
      let outside :=
        (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156
      ((outside + 2 * absorberBound ^ 2 : ℕ) : ℝ) ≤
        3 * (fineOuterCorridorError T : ℝ≥0) * outside ^ 2) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let Hout := (internalOuterGraph G U)ᶜ
    let outside := (Finset.univ \ U).card
    (outside : ℝ) ^ 2 *
        (1 - 3 * (fineOuterCorridorError T : ℝ≥0)) ≤
        (2 : ℝ) * (outerSharpEligiblePairs Hout U 0 : ℕ) ∧
      (2 : ℝ) * (outerSharpEligiblePairs Hout U 0 : ℕ) ≤
        (outside : ℝ) ^ 2 := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let Hout := (internalOuterGraph G U)ᶜ
  let outside := (Finset.univ \ U).card
  let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
    (2 * t ^ rootPower) ^ 156
  let eligible := outerSharpEligiblePairs Hout U 0
  have heligibleLowerNat : Nat.choose outside 2 - absorberBound ^ 2 ≤
      eligible := by
    simpa only [outside, absorberBound, eligible, Hout, G, U, i] using
      P.toInitialPowerVortexPackage.initialEligiblePairs_lower hell
  have heligibleUpperNat : eligible ≤ Nat.choose outside 2 := by
    simpa only [eligible, Hout, outside] using
      outerSharpEligiblePairs_internalOuter_compl_zero_le G U
  have heligibleLower :
      (Nat.choose outside 2 : ℝ) - (absorberBound : ℝ) ^ 2 ≤ eligible := by
    have hcast : ((Nat.choose outside 2 - absorberBound ^ 2 : ℕ) : ℝ) ≤
        (eligible : ℝ) := by exact_mod_cast heligibleLowerNat
    rw [Nat.cast_sub habsorberFits] at hcast
    push_cast at hcast
    simpa [outside, absorberBound, U, i] using hcast
  have heligibleUpper : (eligible : ℝ) ≤ Nat.choose outside 2 := by
    exact_mod_cast heligibleUpperNat
  have hchoose : (Nat.choose outside 2 : ℝ) =
      (outside : ℝ) * (outside - 1) / 2 := by
    exact Nat.cast_choose_two ℝ outside
  constructor
  · rw [hchoose] at heligibleLower
    dsimp only [outside, absorberBound, U, i] at hdefect
    push_cast at hdefect
    have hdefect' : (outside : ℝ) + 2 * (absorberBound : ℝ) ^ 2 ≤
        3 * (fineOuterCorridorError T : ℝ≥0) * (outside : ℝ) ^ 2 := by
      simpa only [outside, absorberBound, U, i, Nat.cast_add, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat] using hdefect
    change (outside : ℝ) ^ 2 *
        (1 - 3 * (fineOuterCorridorError T : ℝ≥0)) ≤ 2 * eligible
    nlinarith
  · rw [hchoose] at heligibleUpper
    change 2 * (eligible : ℝ) ≤ (outside : ℝ) ^ 2
    have houtsideNonneg : (0 : ℝ) ≤ outside := by positivity
    nlinarith [sq_nonneg (outside : ℝ)]

/-- The packaged absorber edge bound supplies the relative eligible-pair
defect needed by `fineOuter_initial_barrier_bounds`. -/
theorem FineInitialPowerVortexPackage.initialOuter_barrier_bounds
    {q h n ell t rootPower step : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell)
    (houtside : 0 <
      (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card)
    (hsmall : ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100)
    (habsorberFits :
      (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156) ^ 2 ≤
        Nat.choose
          (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card 2)
    (hdefect :
      let outside :=
        (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156
      ((outside + 2 * absorberBound ^ 2 : ℕ) : ℝ) ≤
        3 * (fineOuterCorridorError t : ℝ≥0) * outside ^ 2)
    (hlower₀ :
      let outside :=
        (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let lower₀ :=
        outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
      (1 - 16 * (fineOuterCorridorError t : ℝ≥0)) * outside ≤
        (lower₀ : ℝ)) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let Hout := (internalOuterGraph G U)ᶜ
    let outside := (Finset.univ \ U).card
    let lower₀ :=
      outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
    (outside : ℝ) ≤
        quadraticPairBarrier (outside : ℝ≥0)
          (fineOuterUpperCoefficient t) (perturbedOuterUpperR0 Hout U)
          (fineOuterUpperSlope t) 0 ∧
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOuterLowerCoefficient t) (perturbedOuterLowerR0 Hout U)
          (fineOuterLowerSlope t) 0 ≤ (lower₀ : ℝ) := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let Hout := (internalOuterGraph G U)ᶜ
  let outside := (Finset.univ \ U).card
  let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
    (2 * t ^ rootPower) ^ 156
  let eligible := outerSharpEligiblePairs Hout U 0
  have heligibleLowerNat : Nat.choose outside 2 - absorberBound ^ 2 ≤
      eligible := by
    simpa only [outside, absorberBound, eligible, Hout, G, U, i] using
      P.toInitialPowerVortexPackage.initialEligiblePairs_lower hell
  have heligibleUpperNat : eligible ≤ Nat.choose outside 2 := by
    simpa only [eligible, Hout, outside] using
      outerSharpEligiblePairs_internalOuter_compl_zero_le G U
  have heligibleLower :
      (Nat.choose outside 2 : ℝ) - (absorberBound : ℝ) ^ 2 ≤ eligible := by
    have hcast : ((Nat.choose outside 2 - absorberBound ^ 2 : ℕ) : ℝ) ≤
        (eligible : ℝ) := by exact_mod_cast heligibleLowerNat
    rw [Nat.cast_sub habsorberFits] at hcast
    push_cast at hcast
    simpa [outside, absorberBound, U, i] using hcast
  have heligibleUpper : (eligible : ℝ) ≤ Nat.choose outside 2 := by
    exact_mod_cast heligibleUpperNat
  have hchoose : (Nat.choose outside 2 : ℝ) =
      (outside : ℝ) * (outside - 1) / 2 := by
    exact Nat.cast_choose_two ℝ outside
  have hpairLower : (outside : ℝ) ^ 2 *
        (1 - 3 * (fineOuterCorridorError t : ℝ≥0)) ≤
      2 * (eligible : ℝ) := by
    rw [hchoose] at heligibleLower
    dsimp only [outside, absorberBound, U, i] at hdefect
    push_cast at hdefect
    have hdefect' : (outside : ℝ) + 2 * (absorberBound : ℝ) ^ 2 ≤
        3 * (fineOuterCorridorError t : ℝ≥0) * (outside : ℝ) ^ 2 := by
      simpa only [outside, absorberBound, U, i, Nat.cast_add, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat] using hdefect
    nlinarith
  have hpairUpper : 2 * (eligible : ℝ) ≤ (outside : ℝ) ^ 2 := by
    rw [hchoose] at heligibleUpper
    nlinarith [sq_nonneg (outside : ℝ)]
  apply fineOuter_initial_barrier_bounds Hout U outside
    (outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1) t
    (by simpa only [outside, U, i] using houtside) hsmall hpairLower hpairUpper
  simpa only [outside, U, i] using hlower₀

end

end Erdos207

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialDyadicHierarchy
import ErdosProblems.Erdos207.MasterLawCompression

/-!
# The packaged initial power vortex

This structure is the interface between the absorber/initial-typicality
construction and the compressed master induction.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure InitialPowerVortexPackage
    (q h n ell t rootPower step : ℕ) where
  base_ge_one : 1 ≤ t
  H : SimpleGraph (Fin n)
  X : Finset (Fin n)
  B : TripleSystemOn (Fin n)
  W : Vortex (Fin n) ell
  rootCard : X.card = t ^ rootPower
  vortex_eq : W = separatedCardinalVortex H X B
    (powerFreeSize t step ell) (powerFreeSize_antitone t step ell
      base_ge_one)
  terminal : W.U (Fin.last ell) = X
  levelCard : ∀ i, i ≠ 0 →
    (W.U i).card = t ^ rootPower + powerFreeSize t step ell i
  nonempty : ∀ i, (W.U i).Nonempty
  absorption : HasHighGirthAbsorptionBank q H X B
  localization : HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B
  bankSupport : (verticesOn B).card ≤
    highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156
  graphSupport : (graphSupportFinset H).card ≤
    highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156
  graphDegree : ∀ v, H.degree v ≤
    highGirthAbsorberCardCoefficient (q + 2) * (2 * t ^ rootPower) ^ 156
  bankCard : B.card ≤
    (highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156) ^ 3
  rootBounds : HasPaddedAbsorberRootBounds q H X B
  rootLocalization : HasPaddedAbsorberRootLocalization q X B
  typical : IsIterationTypical W 0
    (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
    (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B)).available
    1 1 (t : ℝ≥0)⁻¹ h

theorem eventually_exists_initialPowerVortexPackage
    (q h rootPower step ell E : ℕ)
    (hell : 0 < ell) (hroot : 2 ≤ rootPower)
    (habsorberExp : 156 * rootPower + 2 ≤ E)
    (hfreeExp : step * ell + 1 ≤ E) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Nonempty (InitialPowerVortexPackage q h n ell
        (dyadicPowerScale E n) rootPower step) := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_exists_paddedAbsorber_with_initial_power_typicality
      q h rootPower step ell E hell hroot habsorberExp hfreeExp
  refine ⟨N₀, ?_⟩
  intro n hn
  obtain ⟨H, X, B, W, hX, hW, hterminal, hlevel, hnonempty,
      hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
      hrootLocalization, htyp⟩ := hN₀ n hn
  exact ⟨⟨one_le_dyadicPowerScale E n, H, X, B, W, hX, hW,
    hterminal, hlevel, hnonempty,
    hA, hlocal, hBsupport, hHsupport, hdegree, hBcard, hrootBounds,
    hrootLocalization, htyp⟩⟩

/-- At an admissible order the packaged initial state gives the base law of
the compressed induction. -/
theorem InitialPowerVortexPackage.exists_initialCompressedMasterLaw
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hadmissible : Admissible n) :
    ∃ law : FiniteLaw (MasterStateOn (Fin n)),
      IsCompressedMasterLaw law P.W 0
        (absorberErdosForbiddenConfigurationsOn q P.B)
        (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
        (outsideAvailableTriangles P.H P.B)
        1 1 (t : ℝ≥0)⁻¹ 1 0 h := by
  let Gzero := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState
    (absorberErdosForbiddenConfigurationsOn q P.B)
    (outsideAvailableTriangles P.H P.B)).available
  let ambient := outsideAvailableTriangles P.H P.B
  have hpoint : IsMasterStagePointwiseGood P.W 0
      (absorberErdosForbiddenConfigurationsOn q P.B) Gzero A
      ∅ ∅ 1 1 (t : ℝ≥0)⁻¹ h := by
    simpa only [Gzero, A] using
      initialMasterStagePointwiseGood_of_typical P.typical
  have heven : ∀ v : Fin n, Even ((neighborsIn Gzero univ v).card) := by
    simpa only [Gzero] using
      initialRemainder_even_of_admissible_absorber hadmissible P.absorption
  have hUzero : P.W.U 0 = univ := by
    rw [P.vortex_eq]
    exact separatedCardinalVortex_U_zero P.H P.X P.B
      (powerFreeSize t step ell)
      (powerFreeSize_antitone t step ell P.base_ge_one)
  have hsupport : GraphSupportedOn Gzero (P.W.U 0 : Set (Fin n)) := by
    rw [hUzero]
    intro u v _huv
    simp
  have hA : A ⊆ ambient := by
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let A₀ := outsideAvailableTriangles P.H P.B
    have hInv : AbsorberGreedyInvariant F A₀
        (absorberGreedyInitialState F A₀) :=
      absorberGreedyInitialState_invariant F A₀
        (fun _S hS ↦ absorberErdosForbidden_nonempty hS)
    simpa only [A, ambient, F, A₀] using hInv.2.1.2
  refine ⟨FiniteLaw.pure (initialMasterState Gzero A), ?_⟩
  exact initialCompressedMasterLaw_of_pointwise_subset heven hsupport hA hpoint

end

end Erdos207

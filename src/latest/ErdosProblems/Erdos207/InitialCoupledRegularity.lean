/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialDensityBounds
import ErdosProblems.Erdos207.InitialUnavailableTriangleCount
import ErdosProblems.Erdos207.InitialRootPowerBound
import ErdosProblems.Erdos207.KSSSInitialMargins

/-! # Actual initial coupled regularity from explicit small-support power budgets -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem initial_absorber_coupled_regularity
    {V : Type*} [Fintype V] [DecidableEq V]
    (q C u R s b : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (bank : TripleSystemOn V) (t : ℝ)
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) (ht : 3 ≤ t) (hconst : (2 : ℝ) ^ q ≤ t)
    (hbankCoefficient : (pairExactBankExtensionCoefficient q bank : ℝ) ≤ t ^ u)
    (hunavailable : (((graphSupportFinset H).card : ℝ) ^ 2 * Fintype.card V +
      ((verticesOn bank).card : ℝ) ^ 3) * pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) ≤
        t ^ u * Fintype.card V)
    (hbankVertices : ((verticesOn bank).card : ℝ) * (2 ^ (q ^ 3) * (q + 1) : ℕ) ≤ t ^ u)
    (hscale : t ^ R ≤ (Fintype.card V : ℝ)) (hgap : u + 2 + s + b * q ≤ R)
    (hratioScale : 6 ≤ t ^ b)
    (hpairLoss : 3 * (C : ℝ) + 2 ≤ (Fintype.card V : ℝ) / (2 * t ^ s)) :
    let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
    let Q := initialResidualPairs H
    let A : ℝ := S.available.card
    KSSSInitialRegularity (initialRestrictedAbsorberFamily q bank S.available) S q Q
      (initialErdosTrajectoryCoefficient V A) Q.card A (1 / t ^ s) := by
  dsimp only
  let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let Q := initialResidualPairs H
  let N : ℝ := Fintype.card V
  let A : ℝ := S.available.card
  let E : ℝ := Q.card
  have hN1 : (1 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast (show 1 ≤ Fintype.card V by omega)
  have hNpos : 0 < N := by linarith
  have htpos : 0 < t := by linarith
  have hcube : N ^ 3 ≤ 48 * A := by
    dsimp only [N, A, S]
    exact_mod_cast initial_globalAvailability_cube_le (q := q) hdegree hsupport hlarge
  have hApos : 0 < A := by have hpos := pow_pos hNpos 3; nlinarith only [hpos, hcube]
  have hpair := initial_pair_relative_degree_interval (q := q) hdegree hsupport hlarge
  change N / 6 ≤ A / E ∧ A / E ≤ N / 3 ∧ _ at hpair
  have hratio : N / t ^ b ≤ A / E :=
    (div_le_div_of_nonneg_left hNpos.le (by norm_num) hratioScale).trans hpair.1
  have hdisjoint : Disjoint S.available bank := by
    apply Finset.disjoint_left.mpr
    intro T hT hTB
    exact (mem_outsideAvailableTriangles_iff.mp (mem_legalAvailable_iff.mp hT).1).1 hTB
  have hlegal : ∀ T ∈ S.available, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ T :=
    fun _ hT ↦ (mem_legalAvailable_iff.mp hT).2
  have hbad : (((univ : TripleSystemOn V) \ S.available).card : ℝ) *
      pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) ≤ t ^ u * N := by
    have hcount : (((univ : TripleSystemOn V) \ S.available).card : ℝ) ≤
        ((graphSupportFinset H).card : ℝ) ^ 2 * N + ((verticesOn bank).card : ℝ) ^ 3 := by
      dsimp only [N, S]
      exact_mod_cast card_initial_unavailable_triangles_le q H bank
    exact (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)).trans hunavailable
  constructor
  · intro P hP
    exact initial_pair_relative_error_of_power_loss N t (3 * A / E) (3 * (C : ℝ) + 2) _ s
      hNpos.le htpos (by
        have hid : 3 * A / E = 3 * (A / E) := by ring
        rw [hid]
        linarith only [hpair.1])
      hpairLoss (hpair.2.2 P hP)
  · intro T hT j hj
    have hbankJ : ((verticesOn bank).card : ℝ) * (2 ^ (j ^ 3) * (j + 1) : ℕ) ≤ t ^ u := by
      have hcoef : 2 ^ (j ^ 3) * (j + 1) ≤ 2 ^ (q ^ 3) * (q + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (mem_Icc.mp hj).2 3))
          (Nat.add_le_add_right (mem_Icc.mp hj).2 1)
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcoef) (Nat.cast_nonneg _)).trans hbankVertices
    exact initial_root_configuration_power_regularity q j u R s b bank S.available T hT E A t hApos
      (mem_Icc.mp hj).1 (mem_Icc.mp hj).2 hdisjoint hlegal hN1 ht hconst hbankCoefficient hbad hbankJ
      hscale hgap hratio

end

end Erdos207

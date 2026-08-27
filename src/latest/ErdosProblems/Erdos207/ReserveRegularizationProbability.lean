/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveTriangleRegularization

/-! # Actual reserve-law probability of obtaining a regularized preliminary family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def HasReserveRegularizedTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U D : Finset V) (A : TripleSystemOn V)
    (p tau : ℝ≥0) (eta : ℝ) (omega : Sym2 V → Bool) : Prop :=
  ∃ B ⊆ reserveProtectedOuterAvailable G U (reserveEdges G U omega) A,
    ∀ e ∈ graphEdges (reserveProtectedOuterGraph G U (reserveEdges G U omega)),
      |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - (p : ℝ) ^ 2 * tau * D.card / 4| ≤
        eta * ((p : ℝ) ^ 2 * tau * D.card / 4)

theorem reserveEdgeLaw_probability_no_regularized_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U D : Finset V) (A : TripleSystemOn V)
    (p tau xi r : ℝ≥0) (hr1 : r ≤ 1)
    (hG : GraphSupportedOn G (D : Set V))
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hxi : xi ≤ 1 / 1536) (hr : r ≤ 1 / 24576)
    (hdensity : 6144 ≤ p ^ 4 * tau ^ 6 * D.card)
    (hinner : (U.card : ℝ≥0) ≤ p ^ 4 * tau ^ 6 * D.card / 1536)
    (hold : ∀ S ∈ smallCliqueFamily G D,
      |((properPatternExtensions A (cliquePattern S) univ).card : ℝ) -
        (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card| ≤
      (xi : ℝ) * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card) + S.card)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hfailure : 2 * (D.card : ℝ) ^ 2 *
      Real.exp (-eta ^ 2 * ((p : ℝ) ^ 2 * tau * D.card) / 16) < 1) :
    ((reserveEdgeLaw G U r hr1).probability
      (fun omega ↦ ¬ HasReserveRegularizedTriangles G U D A p tau eta omega) : ℝ) ≤
      12 * (D.card + 1 : ℝ) ^ 4 *
        Real.exp (-(r : ℝ) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card) / 8) := by
  classical
  let L := reserveEdgeLaw G U r hr1
  let a : ℝ := (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card / 2
  have hmin : ∀ S ∈ smallCliqueFamily G D,
      a ≤ ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) := by
    intro S hS
    have hm := (mem_smallCliqueFamily_iff G D S).mp hS
    have htarget := small_clique_target_lower p tau D.card S.card p.coe_nonneg
      (by exact_mod_cast hp1) tau.coe_nonneg (by exact_mod_cast htau1) (by positivity) hm.2.2.1
    have hdensityR : (6144 : ℝ) ≤ (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card := by exact_mod_cast hdensity
    have hxiR : (xi : ℝ) ≤ 1 / 1536 := by exact_mod_cast hxi
    have hbounds := proper_clique_error_two_sided _ _ xi S.card
      (by linarith) (by linarith) hm.2.2.1 (hold S hS)
    dsimp only [a]
    linarith [hbounds.1]
  have hcover : L.probability (fun omega ↦ ¬ HasReserveRegularizedTriangles G U D A p tau eta omega) ≤
      L.probability (fun omega ↦ ∃ S ∈ smallCliqueFamily G D,
        ReserveCliqueExtensionLossEvent G U A S r omega) := by
    apply L.probability_mono
    intro omega hbad
    by_contra hnone
    have hgood : ∀ S ∈ smallCliqueFamily G D, ¬ ReserveCliqueExtensionLossEvent G U A S r omega :=
      fun S hS hevent ↦ hnone ⟨S, hS, hevent⟩
    exact hbad (exists_reserveProtected_regularized_triangles G U D A p tau xi r omega hG
      hp hp1 htau htau1 hxi hr hdensity hinner hold hgood eta heta heta1 hfailure)
  have hcoverR : (L.probability
      (fun omega ↦ ¬ HasReserveRegularizedTriangles G U D A p tau eta omega) : ℝ) ≤
      L.probability (fun omega ↦ ∃ S ∈ smallCliqueFamily G D,
        ReserveCliqueExtensionLossEvent G U A S r omega) := by exact_mod_cast hcover
  apply hcoverR.trans
  have hbound := reserveEdgeLaw_probability_any_clique_extension_loss G U D A r hr1 a hA hmin
  have hexp : -(r : ℝ) * a / 4 =
      -(r : ℝ) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card) / 8 := by dsimp only [a]; ring
  rw [hexp] at hbound
  exact hbound

end

end Erdos207

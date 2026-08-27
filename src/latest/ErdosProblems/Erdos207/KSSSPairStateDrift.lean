/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectoryState
import ErdosProblems.Erdos207.PairStarScaledDrift
import ErdosProblems.Erdos207.PairStarJumpVariance
import ErdosProblems.Erdos207.KSSSPairCurvatureBound

/-! # The source pair drift derived from the actual coupled trajectory event -/

namespace Erdos207

open Finset

noncomputable section

def ksssThreatCoefficient (orders : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  3 + (∑ d ∈ orders, (d : ℝ) * b d) / 3

def ksssPairDriftCoefficient (q : ℕ) (b : ℕ → ℝ) : ℝ :=
  12 * ((q : ℝ) + 5) + 48 * ksssThreatCoefficient (ksssOrders q) b + 60

theorem ksssThreatCoefficient_nonneg
    (orders : Finset ℕ) (b : ℕ → ℝ) (hb : ∀ d ∈ orders, 0 ≤ b d) :
    0 ≤ ksssThreatCoefficient orders b := by
  have hh : 0 ≤ ∑ d ∈ orders, (d : ℝ) * b d :=
    sum_nonneg fun d hd ↦ mul_nonneg (Nat.cast_nonneg _) (hb d hd)
  unfold ksssThreatCoefficient
  positivity

theorem KSSSOnTrajectories.pair_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a b : ℕ → ℝ} {E₀ A₀ scale t : ℝ} {B : ℕ} {K : CrudeThresholds}
    (h : KSSSOnTrajectories F S q Q a E₀ A₀ scale B t)
    (hcrude : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E₀ * ksssEdgeDensity E₀ t)
    (hE : 0 < E₀) (hA : 0 < A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E₀ ^ d ≤ b d)
    (he : 2 ≤ ksssErrorEnvelope E₀ scale B t)
    (hsmall : ksssErrorEnvelope E₀ scale B t ≤ ksssPairTrajectory (ksssOrders q) a E₀ A₀ t / 4)
    (hcommon : (K.common : ℝ) ≤ ksssErrorEnvelope E₀ scale B t)
    (hlarge : 24 ≤ E₀ * ksssEdgeDensity E₀ t)
    (hxe : ksssPairTrajectory (ksssOrders q) a E₀ A₀ t ≤
      (E₀ * ksssEdgeDensity E₀ t) * ksssErrorEnvelope E₀ scale B t)
    (P : Finset V) (hP : P ∈ Q)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty) :
    |(restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hR).expectationReal
        (fun S' ↦ ((availableTrianglesContainingPair S' P).card : ℝ) -
          (availableTrianglesContainingPair S P).card) -
      ksssPairSlope (ksssOrders q) a E₀ A₀ t| ≤
      ksssPairDriftCoefficient q b * ksssErrorEnvelope E₀ scale B t /
        (E₀ * ksssEdgeDensity E₀ t) := by
  let x := ksssPairTrajectory (ksssOrders q) a E₀ A₀ t
  let H := ksssThreatTrajectory (ksssOrders q) a E₀ A₀ t
  let L := E₀ * ksssEdgeDensity E₀ t
  let e := ksssErrorEnvelope E₀ scale B t
  have hp := ksssEdgeDensity_pos hE hclock
  have hx := ksssPairTrajectory_pos (ksssOrders q) a hE hA hclock
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ b d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hHbounds := ksssThreatTrajectory_bounds (ksssOrders q) a b horders ha hab hE hA ht hclock
  have hH0 : 0 ≤ H := by dsimp only [H]; linarith only [hx, hHbounds.1]
  have hHabs : |H| ≤ ksssThreatCoefficient (ksssOrders q) b * x := by
    rw [abs_of_nonneg hH0]
    exact hHbounds.2
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  have hraw := restrictedGreedyKernel_pairStar_drift_source_scale hS (hQ P hP) hR
    L x e H ((q : ℝ) + 5) (ksssThreatCoefficient (ksssOrders q) b) hlarge hx hsmall
    (by positivity) (ksssThreatCoefficient_nonneg (ksssOrders q) b hb) hHabs
    (h.1 P hP) hglobal hxe
    (fun U hU ↦ h.closed_threat_error hcrude hS hpack hcard hcover he hcommon
      (mem_availableTrianglesContainingPair_iff.mp hU).1)
  have htransfer := restrictedGreedyKernel_expectationReal_pairCard_eq_current F S P
    (S.available \ availableTrianglesContainingPair S P) hR (fun r ↦ r)
  rw [htransfer, ksssPairSlope_eq_source_drift (ksssOrders q) a E₀ A₀ t horders hE.ne' hp.ne']
  change |_ - (-(3 / L) * (H - x))| ≤ _
  have hid : -(3 / L) * (H - x) = -(3 * (H - x) / L) := by ring
  rw [hid, sub_neg_eq_add]
  exact hraw

end

end Erdos207

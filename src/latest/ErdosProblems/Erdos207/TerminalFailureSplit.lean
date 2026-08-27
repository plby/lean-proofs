/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalCoverDown
import ErdosProblems.Erdos207.StoppedGreedyCandidateSurplus

/-!
# Splitting a terminal cover-down failure

At a fixed ordered pair, the exact KSSS count failure can occur only if one
of the two selected vertex stars is large or the rooted active forbidden
count is large.  This pointwise form is suited to a three-event probability
union bound and avoids introducing global maxima into the terminal law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The three elementary bad events at an ordered pair. -/
def TerminalStarRootBadAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (q d r : ℕ) (B : TripleSystemOn V) (e : DistinctPair V)
    (S : GreedyStateOn V) : Prop :=
  d ≤ (triplesThrough S.chosen e.1.1).card ∨
  d ≤ (triplesThrough S.chosen e.1.2).card ∨
  r ≤ (rootedActiveForbiddenConfigurations
    (absorberErdosForbiddenConfigurationsOn q B)
    S.chosen e.1.1 e.1.2).card

/-- Under the deterministic loss budget, a KSSS count failure forces one of
the two star failures or the rooted-threat failure. -/
theorem terminalStarRootBadAt_of_countFailure
    {V : Type*} [Fintype V] [DecidableEq V]
    {q d r : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V} {e : DistinctPair V}
    {S : GreedyStateOn V}
    (hpacking : IsPackingOn S.chosen)
    (hbudget : ∀ u v : V, u ≠ v → ¬H.Adj u v →
      H.degree u + H.degree v + B.card + (4 * d + r * q) ≤
        Fintype.card V - 2)
    (hfail : KSSSCountFailureAt q H X B e S) :
    TerminalStarRootBadAt q d r B e S := by
  by_contra hgood
  simp only [TerminalStarRootBadAt, not_or, not_le] at hgood
  obtain ⟨hu, hv, hroot⟩ := hgood
  obtain ⟨huv, _houtside, hfailure⟩ := hfail
  let R := (rootedActiveForbiddenConfigurations
    (absorberErdosForbiddenConfigurationsOn q B)
    S.chosen e.1.1 e.1.2).card
  let C := (packingCompatibleThirdVertices
    (outsideAvailableTriangles H B) S.chosen huv.1.ne).card
  let su := (triplesThrough S.chosen e.1.1).card
  let sv := (triplesThrough S.chosen e.1.2).card
  let hLoss := H.degree e.1.1 + H.degree e.1.2 + B.card
  have huvH : ¬H.Adj e.1.1 e.1.2 := by
    have hc : e.1.1 ≠ e.1.2 ∧ ¬H.Adj e.1.1 e.1.2 := by
      simpa using huv.2
    exact hc.2
  have htotal := card_sub_two_le_outside_candidate_add_absorber_losses
    (H := H) (B := B) huv.1.ne huvH
  have hcand := card_candidate_le_compatible_add_starCounts
    (A := outsideAvailableTriangles H B) hpacking huv.1
  have htotal' : Fintype.card V - 2 ≤
      C + (2 * su + 2 * sv) + hLoss := by
    dsimp [C, su, sv, hLoss]
    omega
  have hsu : su < d := by simpa only [su] using hu
  have hsv : sv < d := by simpa only [sv] using hv
  have hR : R < r := by simpa only [R] using hroot
  have hstars : 2 * su + 2 * sv < 4 * d := by omega
  have hRmul : R * q ≤ r * q :=
    Nat.mul_le_mul_right q (Nat.le_of_lt hR)
  have hvariable : (2 * su + 2 * sv) + R * q < 4 * d + r * q :=
    Nat.add_lt_add_of_lt_of_le hstars hRmul
  have hfixed : hLoss + (4 * d + r * q) ≤ Fintype.card V - 2 := by
    simpa [hLoss, Nat.add_assoc] using
      hbudget e.1.1 e.1.2 huv.1.ne huvH
  have hactual : hLoss + ((2 * su + 2 * sv) + R * q) <
      Fintype.card V - 2 :=
    (Nat.add_lt_add_left hvariable hLoss).trans_le hfixed
  have hfailure' : C ≤ R * q := by
    simpa only [C, R] using hfailure
  omega

/-- A three-event union bound for one terminal pair failure. -/
theorem probability_terminal_countFailure_le_star_star_root
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (state : Ω → GreedyStateOn V)
    (q d r : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (B : TripleSystemOn V) (e : DistinctPair V)
    (hpacking : L.SupportedOn (fun ω ↦ IsPackingOn (state ω).chosen))
    (hbudget : ∀ u v : V, u ≠ v → ¬H.Adj u v →
      H.degree u + H.degree v + B.card + (4 * d + r * q) ≤
        Fintype.card V - 2) :
    L.probability (fun ω ↦ KSSSCountFailureAt q H X B e (state ω)) ≤
      L.probability (fun ω ↦
        d ≤ (triplesThrough (state ω).chosen e.1.1).card) +
      L.probability (fun ω ↦
        d ≤ (triplesThrough (state ω).chosen e.1.2).card) +
      L.probability (fun ω ↦
        r ≤ (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          (state ω).chosen e.1.1 e.1.2).card) := by
  let A : Ω → Prop := fun ω ↦
    d ≤ (triplesThrough (state ω).chosen e.1.1).card
  let C : Ω → Prop := fun ω ↦
    d ≤ (triplesThrough (state ω).chosen e.1.2).card
  let R : Ω → Prop := fun ω ↦
    r ≤ (rootedActiveForbiddenConfigurations
      (absorberErdosForbiddenConfigurationsOn q B)
      (state ω).chosen e.1.1 e.1.2).card
  calc
    L.probability (fun ω ↦ KSSSCountFailureAt q H X B e (state ω)) ≤
        L.probability (fun ω ↦ A ω ∨ C ω ∨ R ω) := by
      apply L.probability_mono_of_supported hpacking
      intro ω hωPacking hω
      exact terminalStarRootBadAt_of_countFailure
        hωPacking hbudget hω
    _ ≤ L.probability A + L.probability C + L.probability R := by
      refine (L.probability_or_le A (fun ω ↦ C ω ∨ R ω)).trans ?_
      simpa only [add_assoc] using
        (add_le_add (le_refl (L.probability A))
          (L.probability_or_le C R))
    _ = _ := by rfl

end

end Erdos207

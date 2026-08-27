/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveStrongWellDistributed

/-!
# The initial-sparsification reserve law

The long initial random-greedy phase in Kwan--Sah--Sawhney--Simkin has a
different rôle from a later master-iteration step.  Every triangle chosen in
that phase has the ambient `|V|⁻¹` scale and therefore belongs to the
`initial` family in strong well-distributedness.  In particular, its
uncovered-edge density is allowed to be much smaller than one; it must not be
obtained from the monotone later-stage update starting at density one.

This file records the exact interface needed from the mixed
selected/uncovered/reserve product estimate for the initial phase.  Once that
estimate has been proved for a concrete finite law, strong
well-distributedness follows without any comparison with a preceding density.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The mixed estimate produced by the initial sparsification phase.  It
simultaneously prescribes selected triangles, edges left uncovered by the
selected family, and retained reserve edges. -/
def IsInitialReserveProductBound
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (selected : Omega -> TripleSystemOn V)
    (reserve : Omega -> Finset (Sym2 V))
    (p reserveDensity C b : ℝ≥0) : Prop :=
  ∀ (Ifix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)),
    L.probability (fun omega =>
        Ifix ⊆ selected omega ∧
        (∀ e ∈ Efix, e ∉ (coveredGraph (selected omega)).edgeSet) ∧
        Rfix ⊆ reserve omega) ≤
      C ^ (Ifix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * reserveDensity ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card + b)

/-- A mixed initial-phase product bound is exactly the reserve-aware strong
law with all selected triangles classified as initial and with an empty later
family. -/
theorem IsInitialReserveProductBound.toReserveStronglyWellDistributed
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {selected : Omega -> TripleSystemOn V}
    {reserve : Omega -> Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0}
    (h : IsInitialReserveProductBound L selected reserve
      p reserveDensity C b) :
    IsReserveStronglyWellDistributed L W k selected
      (fun _ => (∅ : TripleSystemOn V)) reserve
      p reserveDensity C b := by
  intro Ifix Dfix Efix Rfix _hdisjoint
  by_cases hD : Dfix = ∅
  · subst Dfix
    have hraw := h Ifix Efix Rfix
    have hevent :
        ReserveStrongDistributionEvent selected
          (fun _ => (∅ : TripleSystemOn V)) reserve
          Ifix ∅ Efix Rfix =
        (fun omega =>
          Ifix ⊆ selected omega ∧
          (∀ e ∈ Efix,
            e ∉ (coveredGraph (selected omega)).edgeSet) ∧
          Rfix ⊆ reserve omega) := by
      funext omega
      simp [ReserveStrongDistributionEvent, StrongDistributionEvent,
        and_assoc]
    rw [hevent]
    simpa [laterTriangleScale] using hraw
  · have himpossible :
        forall omega,
          ¬ ReserveStrongDistributionEvent selected
            (fun _ => (∅ : TripleSystemOn V)) reserve
            Ifix Dfix Efix Rfix omega := by
      intro omega hevent
      exact hD (subset_empty.mp hevent.1.2.1)
    calc
      L.probability
          (ReserveStrongDistributionEvent selected
            (fun _ => (∅ : TripleSystemOn V)) reserve
            Ifix Dfix Efix Rfix) ≤
          L.probability (fun _ => False) := by
        apply FiniteLaw.probability_mono
        intro omega hevent
        exact himpossible omega hevent
      _ = 0 := L.probability_false
      _ ≤ C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
          (p ^ Efix.card * reserveDensity ^ Rfix.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p Dfix + b) := zero_le

end

end Erdos207

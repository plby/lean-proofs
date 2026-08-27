/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryOuterResidual
import ErdosProblems.Erdos207.SupportedConditionedPreliminaryKernel

/-!
# Supported conditioned preliminary law for all outer residual edges

This is the relative, totalized form of the strengthened preliminary product
law.  It is the interface needed when an existing master packing is extended
by a conditioned preliminary phase.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem supportedConditionedRelativePreliminaryKernel_outerProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hGleave : G ≤ leaveGraph S₀.chosen)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    RelativePreliminaryReady n F
        Kpair Kglobal Kinc Delta delta I D S₀ ∧
      ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (supportedConditionedRelativePreliminaryKernel n F
          Kpair Kglobal Kinc Delta delta I D S₀).probability
            (fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
              E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2
  have hlower : 1 - epsilon ≤ L.probability Good := by
    rw [L.probability_not Good] at hinactive
    calc
      1 - epsilon ≤ 1 - (1 - L.probability Good) :=
        tsub_le_tsub_left hinactive 1
      _ = L.probability Good :=
        tsub_tsub_cancel_of_le (L.probability_le_one Good)
  have hready : RelativePreliminaryReady n F
      Kpair Kglobal Kinc Delta delta I D S₀ :=
    (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hready, ?_⟩
  have hraw : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
      L.probability (fun z ↦ Good z ∧
        Q ⊆ z.2.chosen \ S₀.chosen ∧
        E ⊆ preliminaryResidualOuterEdges G X z.2.chosen) ≤
          alpha ^ Q.card * eta ^ E.card := by
    intro Q E
    simpa only [L, Good, active] using
      (timedAggregateAveragePairBand_probability_active_newSelected_residualOuter_le
        n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
        alpha eta S₀ hInv₀ houtside₀ hHG hGleave hsmall hactive₀
        hupper hselected hsurvived Q E)
  intro Q E
  rw [supportedConditionedRelativePreliminaryKernel, dif_pos hready]
  have hconditioned := L.conditionOn_probability_mixedProduct_le Good
    (fun z ↦ z.2.chosen \ S₀.chosen)
    (fun z ↦ preliminaryResidualOuterEdges G X z.2.chosen)
    alpha eta hready hraw Q E
  have hden : 0 < 1 - epsilon := tsub_pos_iff_lt.mpr hepsilon
  have halpha : alpha / L.probability Good ≤ alpha / (1 - epsilon) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / L.probability Good ≤ eta / (1 - epsilon) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  exact hconditioned.trans (by gcongr)

end

end Erdos207

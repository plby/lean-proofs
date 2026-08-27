/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OutsidePairSurvival
import ErdosProblems.Erdos207.TimedAveragePairBand

/-!
# Outside-pair survival for the averaged long phase

The averaged availability stop adds two scalar predicates to the two-cutoff
pair-band stop.  They do not alter a live transition.  Consequently the same
pair-local jump argument preserves every eligible outside leave pair on the
common five-event law.
-/

namespace Erdos207

noncomputable section

/-- The averaged pair-band law preserves all outside pairs which remain in
the leave. -/
theorem timedAveragePairBandProcessLaw_supported_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H : SimpleGraph V) (X : Finset V)
    (S₀ : GreedyStateOn V) (Kpair Kglobal Δ δ I D : ℕ)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hsmall : 3 + Kpair < δ) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAveragePairBandActive F Kpair Kglobal Δ δ I D) S₀).SupportedOn
        (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
  have hsupport :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAveragePairBandActive F Kpair Kglobal Δ δ I D) S₀).SupportedOn
          (fun z ↦ GreedyInvariant F z.2 ∧
            OutsideLeavePairsAlive H X z.2) := by
    apply (FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
        GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2)
        ⟨hInv₀, houtside₀⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hout :=
        greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
          hz.2 hz.1 hactive.2.1.2.2.1 hactive.2.1.2.2.2.2 hsmall
      have hboth : (greedyKernel F z.2).SupportedOn
          (fun S' ↦ GreedyInvariant F S' ∧
            OutsideLeavePairsAlive H X S') := by
        intro S' hmass
        exact ⟨greedyKernel_supported hz.1 S' hmass, hout S' hmass⟩
      exact hboth.map
        (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S'))
        (fun _S' hS' ↦ hS')
    · exact FiniteLaw.supportedOn_pure _ hz
  intro z hmass
  exact (hsupport z hmass).2

end

end Erdos207

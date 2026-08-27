/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry
import ErdosProblems.Erdos207.OuterOnlyPreliminaryGeometry
import ErdosProblems.Erdos207.SupportedOuterPreliminaryKernel

/-!
# Conditioned preliminary law after exposing a crossing reserve

This is the exact KSSS order of operations.  A reserve is fixed first.  The
long preliminary process is then run only on triangles of
`G \ (R ∪ G[U])`.  Its residual-edge product estimate charges only genuinely
new residual edges, namely residual edges outside the already sampled
reserve.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The generic conditioned outer-residual law, specialized to the exact
reserve-protected preliminary graph. -/
theorem supportedConditionedReserveProtectedPreliminaryKernel_outerProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V)
    (reserve : Finset (Sym2 V)) (A P : TripleSystemOn V)
    (Kpair Kglobal Kinc Delta delta Icut Dcut M supply : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hInv : GreedyInvariant F (relativePreliminaryInitialState P A))
    (hGleave : G ≤ leaveGraph P)
    (halive : ∀ e ∈ reserveProtectedOuterEdges G U reserve,
      PairAlive e.toFinset
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A)))
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A)))
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta Icut Dcut j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut)
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive F Kpair Kglobal
          Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let S₀ := relativePreliminaryInitialState P
      (reserveProtectedOuterAvailable G U reserve A)
    RelativePreliminaryReady n F Kpair Kglobal Kinc Delta delta Icut
        Dcut S₀ ∧
      ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (supportedConditionedRelativePreliminaryKernel n F
          Kpair Kglobal Kinc Delta delta Icut Dcut S₀).probability
            (fun z ↦ Q ⊆ z.2.chosen \ P ∧
              E ⊆ preliminaryResidualOuterEdges
                (reserveProtectedOuterGraph G U reserve) U z.2.chosen) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
  dsimp only
  let Aprotected := reserveProtectedOuterAvailable G U reserve A
  let S₀ := relativePreliminaryInitialState P Aprotected
  let Gprotected := reserveProtectedOuterGraph G U reserve
  have hInv₀ : GreedyInvariant F S₀ := by
    exact hInv.restrictAvailable
      (reserveProtectedOuterAvailable_subset G U reserve A)
  have houtside : OutsideLeavePairsAlive Gprotectedᶜ U S₀ := by
    simpa only [Gprotected, S₀, Aprotected] using
      outsideLeavePairsAlive_compl_reserveProtectedOuterGraph halive
  have hdisjoint : Disjoint Gprotectedᶜ Gprotected := disjoint_compl_left
  have hprotectedLeave : Gprotected ≤ leaveGraph P :=
    (reserveProtectedOuterGraph_le G U reserve).trans hGleave
  have hbase := supportedConditionedRelativePreliminaryKernel_outerProductLaw
    n F Gprotectedᶜ Gprotected U Kpair Kglobal Kinc Delta delta
      Icut Dcut M supply hDcut hsupplyM h3supply alpha eta epsilon S₀
      hInv₀ houtside hdisjoint hprotectedLeave hsmall hactive₀ hupper
      hselected hsurvived hinactive hepsilon
  simpa only [S₀, Aprotected, Gprotected,
    relativePreliminaryInitialState_chosen] using hbase

/-- Restricting the tracked protected residual family to crossing edges not
already sampled gives the mixed law used by the augmented-reserve update. -/
theorem supportedConditionedReserveProtectedPreliminaryKernel_productLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V)
    (reserve : Finset (Sym2 V)) (A P : TripleSystemOn V)
    (Kpair Kglobal Kinc Delta delta Icut Dcut M supply : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hInv : GreedyInvariant F (relativePreliminaryInitialState P A))
    (hGleave : G ≤ leaveGraph P)
    (halive : ∀ e ∈ reserveProtectedOuterEdges G U reserve,
      PairAlive e.toFinset
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A)))
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A)))
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta Icut Dcut j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut)
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U reserve A))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive F Kpair Kglobal
          Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let S₀ := relativePreliminaryInitialState P
      (reserveProtectedOuterAvailable G U reserve A)
    RelativePreliminaryReady n F Kpair Kglobal Kinc Delta delta Icut
        Dcut S₀ ∧
      ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (supportedConditionedRelativePreliminaryKernel n F
          Kpair Kglobal Kinc Delta delta Icut Dcut S₀).probability
            (fun z ↦ Q ⊆ z.2.chosen \ P ∧
              E ⊆ preliminaryResidualCrossingEdges G U z.2.chosen \
                reserve) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
  dsimp only
  let S₀ := relativePreliminaryInitialState P
    (reserveProtectedOuterAvailable G U reserve A)
  have hbase :=
    supportedConditionedReserveProtectedPreliminaryKernel_outerProductLaw
      n F G U reserve A P Kpair Kglobal Kinc Delta delta Icut Dcut M
      supply hDcut hsupplyM h3supply alpha eta epsilon hInv hGleave
      halive hsmall hactive₀ hupper hselected hsurvived hinactive hepsilon
  refine ⟨hbase.1, ?_⟩
  intro Q E
  calc
    (supportedConditionedRelativePreliminaryKernel n F
        Kpair Kglobal Kinc Delta delta Icut Dcut S₀).probability
          (fun z ↦ Q ⊆ z.2.chosen \ P ∧
            E ⊆ preliminaryResidualCrossingEdges G U z.2.chosen \
              reserve) ≤
        (supportedConditionedRelativePreliminaryKernel n F
          Kpair Kglobal Kinc Delta delta Icut Dcut S₀).probability
          (fun z ↦ Q ⊆ z.2.chosen \ P ∧
            E ⊆ preliminaryResidualOuterEdges
              (reserveProtectedOuterGraph G U reserve) U z.2.chosen) := by
      apply FiniteLaw.probability_mono
      intro z hz
      exact ⟨hz.1, hz.2.trans
        (residualCrossing_sdiff_reserve_subset_protectedResidualOuter
          G U reserve z.2.chosen)⟩
    _ ≤ (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card := hbase.2 Q E

end

end Erdos207

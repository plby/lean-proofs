/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterOutsidePairSurvival

/-!
# The support-aware preliminary kernel of a master stage

For every occurring pointwise-good master state, the constrained stopped
greedy law starts from the current selected packing and current available
family.  Cumulative coverage and graph containment supply outside-pair
survival.  Conditioning on terminal activity then gives both the mixed
selection/residual-edge product estimate and all structural support required
by the internal-edge stage.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The relative preliminary state attached to a master outcome. -/
def masterRelativePreliminaryState
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (A I D : Omega → TripleSystemOn V) (omega : Omega) : GreedyStateOn V :=
  relativePreliminaryInitialState (I omega ∪ D omega) (A omega)

/-- The totalized conditioned preliminary kernel attached to every master
outcome. -/
def supportedMasterPreliminaryKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (Kpair Kglobal Kinc Delta delta Icut Dcut : ℕ)
    (A I D : Omega → TripleSystemOn V) (omega : Omega) :
    FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) :=
  supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut
    (masterRelativePreliminaryState A I D omega)

/-- The genuinely new triangles selected by the relative preliminary law. -/
def supportedMasterPreliminaryAdded
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (I D : Omega → TripleSystemOn V)
    (omega : Omega) (z : FiniteLaw.TimedState (GreedyStateOn V) n) :
    TripleSystemOn V :=
  z.2.chosen \ (I omega ∪ D omega)

/-- A conditioned master support supplies the exact preliminary product law
and the structural base event consumed by the internal-edge kernel. -/
theorem supportedMasterPreliminaryKernel_product_and_structure
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {p etaMaster xi : ℝ≥0} {h : ℕ}
    (n Kpair Kglobal Kinc Delta delta Icut Dcut M supply : ℕ)
    (hX : X = W.U i.succ)
    (hF : F = absorberErdosForbiddenConfigurationsOn q B)
    (hpoint : law.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W i.castSucc F (G omega) (A omega)
        (I omega) (D omega) p etaMaster xi h)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦
      G omega ≤ graphDifference (SimpleGraph.completeGraph V) H)
    (hGsupp : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (heven : law.SupportedOn fun omega ↦
      ∀ v, Even ((neighborsIn (G omega) univ v).card))
    (hh : 2 ≤ h)
    (hpositive : 0 < (1 - xi) *
      (p ^ 2 * etaMaster * (W.U i.succ).card))
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hsmall : 3 + Kpair < delta)
    (hactive0 : law.SupportedOn fun omega ↦
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta
        delta Icut Dcut 0 (masterRelativePreliminaryState A I D omega))
    (hupper : ∀ omega, 0 < law.mass omega → ∀ j S,
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta
        delta Icut Dcut j S → S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive : ∀ omega, 0 < law.mass omega →
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta
          delta Icut Dcut)
        (masterRelativePreliminaryState A I D omega)).probability
          (fun z ↦ ¬ timedAggregateAveragePairBandActive F Kpair Kglobal
            Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let Kpre := supportedMasterPreliminaryKernel n F Kpair Kglobal Kinc
      Delta delta Icut Dcut A I D
    let added := supportedMasterPreliminaryAdded I D
    (∀ omega, 0 < law.mass omega → ∀ Q E,
      (Kpre omega).probability (fun z ↦
        Q ⊆ added omega z ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) X
          (added omega z)) ≤
        (alpha / (1 - epsilon)) ^ Q.card *
          (eta / (1 - epsilon)) ^ E.card) ∧
      (law.jointBind Kpre).SupportedOn (fun z ↦
        (∀ v, Even ((neighborsIn (G z.1) univ v).card)) ∧
        G z.1 ≤ leaveGraph (I z.1 ∪ D z.1) ∧
        ConsistsOfTriangles (G z.1) (A z.1) ∧
        added z.1 z.2 ⊆ A z.1 ∧
        Disjoint (I z.1) (D z.1 ∪ added z.1 z.2) ∧
        IsPackingOn (I z.1 ∪ (D z.1 ∪ added z.1 z.2))) ∧
      (law.jointBind Kpre).SupportedOn (fun z ↦
        AvoidsForbidden (I z.1 ∪ (D z.1 ∪ added z.1 z.2)) F) := by
  dsimp only
  subst F
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S0 : Omega → GreedyStateOn V := masterRelativePreliminaryState A I D
  let Kpre : Omega → FiniteLaw
      (FiniteLaw.TimedState (GreedyStateOn V) n) :=
    supportedMasterPreliminaryKernel n F Kpair Kglobal Kinc Delta delta
      Icut Dcut A I D
  let added : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := supportedMasterPreliminaryAdded I D
  have hpointwise : ∀ omega, 0 < law.mass omega →
      RelativePreliminaryReady n F Kpair Kglobal Kinc Delta delta Icut
          Dcut (S0 omega) ∧
        ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
          (Kpre omega).probability (fun z ↦
            Q ⊆ added omega z ∧
            E ⊆ preliminaryResidualCrossingEdges (G omega) X
              (added omega z)) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
    intro omega hmass
    have hp := hpoint omega hmass
    have hInv : GreedyInvariant F (S0 omega) := by
      exact greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
        hp
    have houtside : OutsideLeavePairsAlive H X (S0 omega) := by
      apply outsideLeavePairsAlive_of_masterPointwiseGood i hX hp
        (hcover omega hmass) (hGsupp omega hmass) hh hpositive
    have hHG : Disjoint H (G omega) := by
      apply SimpleGraph.disjoint_left.mpr
      intro u v huvH huvG
      exact ((hsub omega hmass) huvG).2.2 huvH
    have hprod := supportedConditionedRelativePreliminaryKernel_productLaw
      n F H (G omega) X Kpair Kglobal Kinc Delta delta Icut Dcut M
      supply hDcut hsupplyM h3supply alpha eta epsilon (S0 omega) hInv
      houtside hHG hp.2.2.2.2.1 hsmall (hactive0 omega hmass)
      (hupper omega hmass) hselected hsurvived (hinactive omega hmass)
      hepsilon
    have hres : ∀ z : FiniteLaw.TimedState (GreedyStateOn V) n,
        preliminaryResidualCrossingEdges (G omega) X z.2.chosen =
          preliminaryResidualCrossingEdges (G omega) X
            (z.2.chosen \ (I omega ∪ D omega)) := by
      intro z
      exact preliminaryResidualCrossingEdges_sdiff_eq_of_le_leaveGraph
        hp.2.2.2.2.1
    simpa only [Kpre, supportedMasterPreliminaryKernel, S0,
      masterRelativePreliminaryState, added, supportedMasterPreliminaryAdded,
      relativePreliminaryInitialState_chosen, hres]
      using hprod
  refine ⟨fun omega hmass ↦ (hpointwise omega hmass).2, ?_, ?_⟩
  have htrajectory : ∀ omega, 0 < law.mass omega →
      (Kpre omega).SupportedOn fun z ↦
        RelativeGreedyTrajectory F (S0 omega) z.2 := by
    intro omega hmass
    exact supportedConditionedRelativePreliminaryKernel_supported_trajectory
      n F Kpair Kglobal Kinc Delta delta Icut Dcut (S0 omega)
      (greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
        (hpoint omega hmass)) (hpointwise omega hmass).1
  intro z hmass
  have hmasses :=
    (FiniteLaw.jointBind_mass_pos_iff law Kpre z.1 z.2).mp hmass
  have hp := hpoint z.1 hmasses.1
  have htraj := htrajectory z.1 hmasses.1 z.2 hmasses.2
  have hstruct := htraj.structural_newPart
    (I := I z.1) (D := D z.1) (A := A z.1) rfl rfl hp.1
  exact ⟨heven z.1 hmasses.1,
    hp.2.2.2.2.1, hp.2.2.2.2.2.1, hstruct.1,
    hstruct.2.1, hstruct.2.2⟩
  intro z hmass
  have hmasses :=
    (FiniteLaw.jointBind_mass_pos_iff law Kpre z.1 z.2).mp hmass
  have hp := hpoint z.1 hmasses.1
  have htraj :=
    supportedConditionedRelativePreliminaryKernel_supported_trajectory
      n F Kpair Kglobal Kinc Delta delta Icut Dcut (S0 z.1)
      (greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
        hp) (hpointwise z.1 hmasses.1).1 z.2 hmasses.2
  have hunion :
      I z.1 ∪ (D z.1 ∪ added z.1 z.2) = z.2.2.chosen := by
    simpa only [S0, masterRelativePreliminaryState,
      relativePreliminaryInitialState_chosen, added,
      supportedMasterPreliminaryAdded, ← union_assoc] using
        htraj.initial_union_added
  rw [hunion]
  exact htraj.1.2.1

end

end Erdos207

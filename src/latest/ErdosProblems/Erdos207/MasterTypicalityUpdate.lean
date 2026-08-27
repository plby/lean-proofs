/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationTypicalUpdate
import ErdosProblems.Erdos207.MasterIterationUpdate

/-!
# Typicality of the concrete master-stage update

This specializes deterministic typicality stability to the actual updated
stage graph and updated available family.  Thus the probabilistic work left
for IG1/IG3 is exactly the two displayed loss estimates, with no hidden
structural obligations.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The three explicit loss bounds (degree on the same level, degree on the
next level, and rooted extension loss) which imply typicality of the concrete
master-stage update. -/
def MasterTypicalityLossEvent
    {V : Type*} [Fintype V] [DecidableEq V] {ell : Nat}
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A I D M : TripleSystemOn V)
    (p eta xi xi' : NNReal) (h : Nat) : Prop :=
  (∀ i : Fin ell, next.val <= i.val ->
    ∀ v ∈ W.U i.castSucc,
    (((neighborsIn G (W.U i.castSucc) v) \
        neighborsIn (updatedStageGraph G (W.U next) M)
          (W.U i.castSucc) v).card : NNReal) <=
      (xi' - xi) * (p * (W.U i.castSucc).card)) ∧
  (∀ i : Fin ell, next.val <= i.val ->
    ∀ v ∈ W.U i.castSucc,
    (((neighborsIn G (W.U i.succ) v) \
        neighborsIn (updatedStageGraph G (W.U next) M)
          (W.U i.succ) v).card : NNReal) <=
      (xi' - xi) * (p * (W.U i.succ).card)) ∧
  (∀ i : Fin ell, next.val <= i.val ->
    ∀ iStar : Fin (ell + 1),
      (iStar = i.castSucc ∨ iStar = i.succ) ->
    ∀ Q : SimpleGraph V,
      Q <= updatedStageGraph G (W.U next) M ->
      GraphSupportedOn Q (W.U i.castSucc : Set V) ->
      (graphSupportFinset Q).card <= h ->
    (((iterationExtensionVertices A Q (W.U iStar)) \
        iterationExtensionVertices
          (updatedStageAvailable F (W.U next) A I D M)
          Q (W.U iStar)).card : NNReal) <=
      (xi' - xi) *
        (p ^ (graphSupportFinset Q).card *
          eta ^ (graphEdges Q).card * (W.U iStar).card))

theorem IsIterationTypical.updatedStage_of_loss
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A I D M : TripleSystemOn V}
    {p eta xi xi' : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta xi h)
    (hkn : k ≤ next) (hxi : xi ≤ xi')
    (hdegreeSame : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
      (((neighborsIn G (W.U i.castSucc) v) \
          neighborsIn (updatedStageGraph G (W.U next) M)
            (W.U i.castSucc) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeNext : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
      (((neighborsIn G (W.U i.succ) v) \
          neighborsIn (updatedStageGraph G (W.U next) M)
            (W.U i.succ) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U i.succ).card))
    (hextension : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph G (W.U next) M →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      (((iterationExtensionVertices A Q (W.U iStar)) \
          iterationExtensionVertices
            (updatedStageAvailable F (W.U next) A I D M)
            Q (W.U iStar)).card : ℝ≥0) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    IsIterationTypical W next
      (updatedStageGraph G (W.U next) M)
      (updatedStageAvailable F (W.U next) A I D M)
      p eta xi' h := by
  exact htyp.of_subset_loss hkn
    (updatedStageGraph_le G (W.U next) M)
    (updatedStageAvailable_subset F (W.U next) A I D M)
    hxi hdegreeSame hdegreeNext hextension

/-- On every old-typical supported state, the concrete loss event implies
next-stage typicality.  Consequently its probability is a lower bound for
the probability of next-stage typicality. -/
theorem FiniteLaw.probability_masterTypicalityLossEvent_le_updatedTypical
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat}
    (L : FiniteLaw Omega) (W : Vortex V ell)
    (k next : Fin (ell + 1)) (F : ForbiddenFamilyOn V)
    (G : Omega -> SimpleGraph V)
    (A I D M : Omega -> TripleSystemOn V)
    (p eta xi xi' : NNReal) (h : Nat)
    (hkn : k <= next) (hxixi' : xi <= xi')
    (hold : L.SupportedOn fun omega =>
      IsIterationTypical W k (G omega) (A omega) p eta xi h) :
    L.probability (fun omega =>
      MasterTypicalityLossEvent W next F (G omega) (A omega)
        (I omega) (D omega) (M omega) p eta xi xi' h) <=
    L.probability (fun omega =>
      IsIterationTypical W next
        (updatedStageGraph (G omega) (W.U next) (M omega))
        (updatedStageAvailable F (W.U next) (A omega) (I omega)
          (D omega) (M omega)) p eta xi' h) := by
  apply L.probability_mono_on_support
    (fun omega => IsIterationTypical W k (G omega) (A omega)
      p eta xi h) _ _ hold
  intro omega htyp hloss
  exact htyp.updatedStage_of_loss hkn hxixi'
    hloss.1 hloss.2.1 hloss.2.2

end

end Erdos207

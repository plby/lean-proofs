/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedMasterTypicalityLossCaps
import ErdosProblems.Erdos207.MasterTypicalityLossProbability

/-!
# Probability of the localized master typicality-loss event

The joint bad event uses the rooted-active cap localized to the current
vortex.  The same finite union argument then feeds the localized deterministic
T1--T3 estimate.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem probability_masterTypicalityLossEvent_of_localized_caps
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : Nat} (L : FiniteLaw Omega)
    (W : Vortex V ell) (k next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : Omega -> SimpleGraph V)
    (A I D R M : Omega -> TripleSystemOn V)
    (p eta xi xi' : NNReal) (h a r q : Nat)
    (caps : Omega -> V -> Nat) (epsilonStar epsilonRoot : NNReal)
    (hold : L.SupportedOn fun omega =>
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hstep : L.SupportedOn fun omega =>
      IsMasterCoverStep F (G omega) (W.U next) (A omega)
        (I omega) (D omega) (R omega ∪ M omega))
    (hstarBad : L.probability (fun omega =>
      ¬ LinkStarCapsGood (caps omega) (M omega)) <= epsilonStar)
    (hrootBad : L.probability (fun omega =>
      ¬ RootedActiveCapsGoodIn F
        (I omega ∪ (D omega ∪ (R omega ∪ M omega)))
        (W.U next) r) <= epsilonRoot)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (huniformStar : ∀ omega v,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤ a)
    (hdegreeBudgetSame : ∀ omega (i : Fin ell), next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) *
            ((triplesThrough (R omega) v).card + caps omega v) ≤
          (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeBudgetNext : ∀ omega (i : Fin ell), next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) *
            ((triplesThrough (R omega) v).card + caps omega v) ≤
          (xi' - xi) * (p * (W.U i.succ).card))
    (hextensionBudget : ∀ omega (i : Fin ell), next.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph (G omega) (W.U next)
          (R omega ∪ M omega) →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      ((graphSupportFinset Q).card : NNReal) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    1 - (epsilonStar + epsilonRoot) <=
      L.probability (fun omega =>
        MasterTypicalityLossEvent W next F (G omega) (A omega)
          (I omega) (D omega) (R omega ∪ M omega)
          p eta xi xi' h) := by
  let Star : Omega -> Prop := fun omega =>
    LinkStarCapsGood (caps omega) (M omega)
  let Root : Omega -> Prop := fun omega =>
    RootedActiveCapsGoodIn F
      (I omega ∪ (D omega ∪ (R omega ∪ M omega)))
      (W.U next) r
  let Good : Omega -> Prop := fun omega => Star omega ∧ Root omega
  let Base : Omega -> Prop := fun omega =>
    IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h ∧
      IsMasterCoverStep F (G omega) (W.U next) (A omega)
        (I omega) (D omega) (R omega ∪ M omega)
  have hbad : L.probability (fun omega => ¬ Good omega) <=
      epsilonStar + epsilonRoot := by
    calc
      L.probability (fun omega => ¬ Good omega) =
          L.probability (fun omega => ¬ Star omega ∨ ¬ Root omega) := by
        congr 1
        funext omega
        simp only [Good, not_and_or]
      _ <= L.probability (fun omega => ¬ Star omega) +
          L.probability (fun omega => ¬ Root omega) :=
        L.probability_or_le _ _
      _ <= epsilonStar + epsilonRoot := by
        exact add_le_add hstarBad hrootBad
  have hgood : 1 - (epsilonStar + epsilonRoot) <=
      L.probability Good := by
    rw [L.probability_not Good] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  apply hgood.trans
  apply L.probability_mono_on_support Base Good _
  · intro omega hmass
    exact ⟨hold omega hmass, hstep omega hmass⟩
  · intro omega hbase hgoodOmega
    exact masterTypicalityLossEvent_of_star_and_localized_rooted_caps
      (caps omega) hbase.1 hbase.2 hgoodOmega.1 hgoodOmega.2 hFcard
      (huniformStar omega) (hdegreeBudgetSame omega)
      (hdegreeBudgetNext omega) (hextensionBudget omega)

end

end Erdos207

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedNewPreliminaryResidualInternalKernel
import ErdosProblems.Erdos207.LocalizedNewRootedThreatProbability
import ErdosProblems.Erdos207.LocalizedRawInternalRootedConditioning

/-!
# Conditioning the raw internal law on newly activated rooted success
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem LocalizedNewRawResidualInternalOutcomeGood.complete_internalCover
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A Plegal P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ}
    {omega : Omega} {z : InternalEdgeGreedyStateOn V}
    (houtcome : LocalizedNewRawResidualInternalOutcomeGood
      W i F G A Plegal P0 bits D R omega z)
    (hroot : NewRootedActiveCapsGoodIn F (Plegal omega) z.chosen
      (A omega) (W.U i.succ) R) :
    GreedyReachable F (P0 omega) z.chosen ∧
      z.chosen ⊆ P0 omega ∪ A omega ∧
      (z.chosen \ P0 omega).card ≤
        (internalOuterEdges (G omega) (W.U i.succ)).card ∧
      ∀ e ∈ internalOuterEdges (G omega) (W.U i.succ),
        (coveredGraph z.chosen).Adj e.out.1 e.out.2 := by
  let E := preliminaryResidualInternalEdges
    (G omega) (W.U i.succ) (P0 omega)
  have hinv := houtcome.1
  have hsuccess := houtcome.2.2.2.2 hroot
  refine ⟨hinv.1, houtcome.2.1, ?_, ?_⟩
  · calc
      (z.chosen \ P0 omega).card ≤ E.toList.length := hinv.2.1
      _ = E.card := by simp
      _ ≤ (internalOuterEdges (G omega) (W.U i.succ)).card :=
        card_le_card
          (preliminaryResidualInternalEdges_subset_internalOuterEdges
            (G omega) (W.U i.succ) (P0 omega))
  · intro e he
    by_cases hcovered : (coveredGraph (P0 omega)).Adj e.out.1 e.out.2
    · exact coveredGraph_mono hinv.1.initial_subset hcovered
    · apply hsuccess.2 e
      apply mem_inter.mpr
      refine ⟨he, mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · exact internalOuterEdges_subset_outerGraphEdges
          (G omega) (W.U i.succ) he
      · intro heGraph
        exact hcovered (graph_adj_out_of_mem_graphEdges heGraph)

/-- Condition a raw internal update on the corrected rooted-cap event.  The
tail is evaluated in each fiber, where the old packing is fixed and every
relative remainder is nonempty. -/
theorem IsReserveStronglyWellDistributed.conditionOn_localizedNewRawResidualInternal_rootedSuccess
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {W : Vortex V ell} {level : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b κ : ℝ≥0}
    (i : Fin ell)
    (hreserve : IsReserveStronglyWellDistributed
      (law.jointBind (rawResidualInternalKernel W i F G A P0 bits D))
      W level (jointInitial initial)
      (jointLater later (rawResidualInternalAdded P0))
      (fun z ↦ reserve z.1) p reserveDensity C b)
    (Good : Omega → Prop)
    (hsupport :
      (law.jointBind
        (rawResidualInternalKernel W i F G A P0 bits D)).SupportedOn
          (fun z ↦ Good z.1 ∧
            LocalizedNewRawResidualInternalOutcomeGood
              W i F G A P0 P0 bits D R z.1 z.2))
    (hP0 : ∀ omega, Good omega →
      initial omega ∪ later omega = P0 omega)
    {q s : ℕ}
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hκ : ∀ omega, 0 < law.mass omega → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : LocalizedNewRootedThreatWitness
            V F (P0 omega) e.1.1 e.1.2 (W.U i.succ) ↦
          localizedNewRootedThreatRemainder z)
        (fun _ ↦ (D : ℝ≥0)⁻¹) κ)
    (hC4 : ∀ omega Q,
      (rawResidualInternalKernel W i F G A P0 bits D omega).probability
        (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
          ((D : ℝ≥0)⁻¹ ^ Q.card))
    (htail : newLocalizedRootedTail V 1 κ R q s < 1) :
    let J := law.jointBind
      (rawResidualInternalKernel W i F G A P0 bits D)
    let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
      NewRootedActiveCapsGoodIn F (P0 z.1)
        (P0 z.1 ∪ rawResidualInternalAdded P0 z.1 z.2)
        (A z.1) (W.U i.succ) R
    ∃ hpos : 0 < J.probability RootGood,
      let Lc := J.conditionOn RootGood hpos
      IsReserveStronglyWellDistributed Lc W level
          (jointInitial initial)
          (jointLater later (rawResidualInternalAdded P0))
          (fun z ↦ reserve z.1) p reserveDensity
          (C / (1 - newLocalizedRootedTail V 1 κ R q s)) b ∧
        Lc.SupportedOn (fun z ↦
          Good z.1 ∧
          GreedyReachable F (P0 z.1) z.2.chosen ∧
          z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
          (z.2.chosen \ P0 z.1).card ≤
            (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
          (∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ),
            (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) ∧
          NewRootedActiveCapsGoodIn F (P0 z.1) z.2.chosen
            (A z.1) (W.U i.succ) R) ∧
        1 - newLocalizedRootedTail V 1 κ R q s ≤
          J.probability RootGood := by
  dsimp only
  let K := rawResidualInternalKernel W i F G A P0 bits D
  let J := law.jointBind K
  let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
    NewRootedActiveCapsGoodIn F (P0 z.1)
      (P0 z.1 ∪ rawResidualInternalAdded P0 z.1 z.2)
      (A z.1) (W.U i.succ) R
  have hbad : J.probability (fun z ↦ ¬ RootGood z) ≤
      newLocalizedRootedTail V 1 κ R q s := by
    simpa only [J, K, RootGood] using
      law.jointBind_probability_not_newRootedActiveCapsGoodIn_le
        K (rawResidualInternalAdded P0) F P0 A (W.U i.succ)
        (fun _ ↦ (D : ℝ≥0)⁻¹) 1 κ R hFcard hκ
        (fun omega _hmass Q _hQcard ↦ by
          simpa only [setWeight, prod_const, one_mul] using hC4 omega Q)
  have hlower : 1 - newLocalizedRootedTail V 1 κ R q s ≤
      J.probability RootGood := by
    rw [J.probability_not RootGood] at hbad
    calc
      1 - newLocalizedRootedTail V 1 κ R q s ≤
          1 - (1 - J.probability RootGood) :=
        tsub_le_tsub_left hbad 1
      _ = J.probability RootGood :=
        tsub_tsub_cancel_of_le (J.probability_le_one RootGood)
  have hpos : 0 < J.probability RootGood :=
    (tsub_pos_iff_lt.mpr htail).trans_le hlower
  refine ⟨hpos, ?_⟩
  let Lc := J.conditionOn RootGood hpos
  have hconditioned := hreserve.conditionOn RootGood hpos
  have hden : 0 < 1 - newLocalizedRootedTail V 1 κ R q s :=
    tsub_pos_iff_lt.mpr htail
  have hfactor : C / J.probability RootGood ≤
      C / (1 - newLocalizedRootedTail V 1 κ R q s) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have hreserveLc : IsReserveStronglyWellDistributed Lc W level
      (jointInitial initial)
      (jointLater later (rawResidualInternalAdded P0))
      (fun z ↦ reserve z.1) p reserveDensity
      (C / (1 - newLocalizedRootedTail V 1 κ R q s)) b :=
    hconditioned.mono_factor hfactor
  have hsuppOld := hsupport.conditionOn hpos
  have hsuppRoot := J.conditionOn_supported RootGood hpos
  have hsuppLc : Lc.SupportedOn (fun z ↦
      Good z.1 ∧
      GreedyReachable F (P0 z.1) z.2.chosen ∧
      z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
      (z.2.chosen \ P0 z.1).card ≤
        (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
      (∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ),
        (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) ∧
      NewRootedActiveCapsGoodIn F (P0 z.1) z.2.chosen
        (A z.1) (W.U i.succ) R) := by
    intro z hz
    have hold := hsuppOld z hz
    have hrootUnion := hsuppRoot z hz
    have hsubset : P0 z.1 ⊆ z.2.chosen := hold.2.1.1.initial_subset
    have hunion : P0 z.1 ∪ rawResidualInternalAdded P0 z.1 z.2 =
        z.2.chosen := by
      exact union_sdiff_of_subset hsubset
    have hroot : NewRootedActiveCapsGoodIn F (P0 z.1) z.2.chosen
        (A z.1) (W.U i.succ) R := by
      simpa only [RootGood, hunion] using hrootUnion
    have hcomplete := hold.2.complete_internalCover hroot
    exact ⟨hold.1, hcomplete.1, hcomplete.2.1, hcomplete.2.2.1,
      hcomplete.2.2.2, hroot⟩
  exact ⟨hreserveLc, hsuppLc, hlower⟩

end

end Erdos207

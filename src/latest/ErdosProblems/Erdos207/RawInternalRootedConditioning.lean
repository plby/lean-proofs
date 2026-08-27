/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawInternalRootedExtraction

/-!
# Conditioning the raw internal law on terminal rooted success

The rooted-good event has explicit positive probability.  Conditioning on
it preserves reserve-aware strong distribution and turns retrospective
success into an ordinary support theorem, in the exact form consumed by the
existing residual-link pipeline.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Once the rooted cap holds, a raw residual-internal outcome has the same
complete internal-cover certificate as the old always-successful kernel.
Edges outside the residual schedule were already covered by `P0`. -/
theorem RawResidualInternalOutcomeGood.complete_internalCover
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ}
    {omega : Omega} {z : InternalEdgeGreedyStateOn V}
    (houtcome :
      RawResidualInternalOutcomeGood W i F G A P0 bits D R omega z)
    (hroot : RootedActiveCapsGood F z.chosen R) :
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

theorem IsReserveStronglyWellDistributed.conditionOn_rawResidualInternal_rootedSuccess
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {W : Vortex V ell} {level : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0}
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
            RawResidualInternalOutcomeGood W i F G A P0 bits D R
              z.1 z.2))
    (hP0 : ∀ omega, Good omega →
      initial omega ∪ later omega = P0 omega)
    (hC : 1 ≤ C) {q s : ℕ}
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      b ≤ setWeight (masterUnionTriangleWeight W level p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W level p) kappa)
    (htail : strongRootedTail V C kappa R q s < 1) :
    let J := law.jointBind
      (rawResidualInternalKernel W i F G A P0 bits D)
    let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
      RootedActiveCapsGood F
        (jointInitial initial z ∪
          jointLater later (rawResidualInternalAdded P0) z) R
    ∃ hpos : 0 < J.probability RootGood,
      let Lc := J.conditionOn RootGood hpos
      IsReserveStronglyWellDistributed Lc W level
          (jointInitial initial)
          (jointLater later (rawResidualInternalAdded P0))
          (fun z ↦ reserve z.1) p reserveDensity
          (C / (1 - strongRootedTail V C kappa R q s)) b ∧
        Lc.SupportedOn (fun z ↦
          Good z.1 ∧
          GreedyReachable F (P0 z.1) z.2.chosen ∧
          z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
          (z.2.chosen \ P0 z.1).card ≤
            (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
          (∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ),
            (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) ∧
          RootedActiveCapsGood F z.2.chosen R) ∧
        1 - strongRootedTail V C kappa R q s ≤ J.probability RootGood := by
  dsimp only
  let K := rawResidualInternalKernel W i F G A P0 bits D
  let J := law.jointBind K
  let RootGood : Omega × InternalEdgeGreedyStateOn V → Prop := fun z ↦
    RootedActiveCapsGood F
      (jointInitial initial z ∪
        jointLater later (rawResidualInternalAdded P0) z) R
  have hbad : J.probability (fun z ↦ ¬ RootGood z) ≤
      strongRootedTail V C kappa R q s := by
    simpa only [J, K, RootGood] using
      hreserve.toStrong.probability_not_rootedActiveCapsGood_le
        F R hC hFcard hb kappa hkappa
  have hlower : 1 - strongRootedTail V C kappa R q s ≤
      J.probability RootGood := by
    rw [J.probability_not RootGood] at hbad
    calc
      1 - strongRootedTail V C kappa R q s ≤
          1 - (1 - J.probability RootGood) := tsub_le_tsub_left hbad 1
      _ = J.probability RootGood :=
        tsub_tsub_cancel_of_le (J.probability_le_one RootGood)
  have hpos : 0 < J.probability RootGood :=
    (tsub_pos_iff_lt.mpr htail).trans_le hlower
  refine ⟨hpos, ?_⟩
  let Lc := J.conditionOn RootGood hpos
  have hconditioned := hreserve.conditionOn RootGood hpos
  have hden : 0 < 1 - strongRootedTail V C kappa R q s :=
    tsub_pos_iff_lt.mpr htail
  have hfactor : C / J.probability RootGood ≤
      C / (1 - strongRootedTail V C kappa R q s) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have hreserveLc : IsReserveStronglyWellDistributed Lc W level
      (jointInitial initial)
      (jointLater later (rawResidualInternalAdded P0))
      (fun z ↦ reserve z.1) p reserveDensity
      (C / (1 - strongRootedTail V C kappa R q s)) b := by
    exact hconditioned.mono_factor hfactor
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
      RootedActiveCapsGood F z.2.chosen R) := by
    intro z hz
    have hold := hsuppOld z hz
    have hrootAccumulated := hsuppRoot z hz
    have hsubset : P0 z.1 ⊆ z.2.chosen := hold.2.1.1.initial_subset
    have haccumulated :
        jointInitial initial z ∪
          jointLater later (rawResidualInternalAdded P0) z =
            z.2.chosen := by
      dsimp only [jointInitial, jointLater, rawResidualInternalAdded]
      rw [← union_assoc, hP0 z.1 hold.1]
      exact union_sdiff_of_subset hsubset
    have hroot : RootedActiveCapsGood F z.2.chosen R := by
      simpa only [RootGood, haccumulated] using hrootAccumulated
    have hcomplete := hold.2.complete_internalCover hroot
    exact ⟨hold.1, hcomplete.1, hcomplete.2.1, hcomplete.2.2.1,
      hcomplete.2.2.2, hroot⟩
  exact ⟨hreserveLc, hsuppLc, hlower⟩

end

end Erdos207

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyConditionedPreliminaryLaw
import ErdosProblems.Erdos207.PreliminaryInternalSafeComposition

/-!
# A complete outer-only preliminary/internal stage

This file starts from the deterministic empty master law, binds the
twice-conditioned outer-only preliminary law, upgrades its augmented reserve
at reserve density one, and finally binds the raw internal cover kernel.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Cancelling an exponential tail after a strict exponential cardinality
bound. -/
lemma mul_exp_neg_lt_one_of_lt_exp {a x : ℝ}
    (h : a < Real.exp x) : a * Real.exp (-x) < 1 := by
  calc
    a * Real.exp (-x) < Real.exp x * Real.exp (-x) :=
      mul_lt_mul_of_pos_right h (Real.exp_pos _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem exists_outerOnlyPreliminaryInternalStage
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage mid final : Fin (ell + 1)}
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (i : Fin ell) (hstagei : stage.val ≤ i.val)
    {pTypical etaTypical xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A pTypical etaTypical xi h)
    (htri : ConsistsOfTriangles G A)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hgap : (((W.U i.succ).card + 2 : ℕ) : ℝ≥0) <
      (1 - xi) * (pTypical ^ 2 * etaTypical * (W.U i.castSucc).card))
    (hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A))
    (Kpair Kglobal Kinc Delta delta Icut Dcut M supply d : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hsmallPre : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState ∅
          (outerOnlyAvailable (W.U i.succ) A)))
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
        (relativePreliminaryInitialState ∅
          (outerOnlyAvailable (W.U i.succ) A))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1)
    (htailInc : residualOuterIncidenceTail V
      (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
      (eta / (1 - epsilon)) (d + 1) < 1)
    (pPre CPre bPre : ℝ≥0)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hstageMid : stage ≤ mid) (hCPre : 1 ≤ CPre)
    (hpPre : 1 ≤ pPre)
    (halphaPre :
      alpha / (1 - epsilon) /
          (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (eta / (1 - epsilon)) (d + 1)) ≤ 1)
    (hbPre : 0 ≤ bPre)
    (hnewPre : ∀ Q : TripleOn V,
      alpha / (1 - epsilon) /
          (1 - residualOuterIncidenceTail V
            (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
            (eta / (1 - epsilon)) (d + 1)) ≤
        pPre / ((W.U (W.truncatedLevel mid Q)).card : ℝ≥0))
    (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (m a D R q : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (pTypical ^ 2 * etaTypical * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmallInternal : ∀ P : TripleSystemOn V,
      ((preliminaryResidualInternalEdges G (W.U i.succ) P).card : ℝ) <
        Real.exp (((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4))
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hscalar : 4 * d + R * q ≤ a)
    (CInt pFinal bFinal : ℝ≥0)
    (hmidFinal : mid ≤ final) (hCInt : 2 * CPre ≤ CInt)
    (hCIntOne : 1 ≤ CInt) (hpFinal : pPre ≤ pFinal)
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1) (hbFinal : bPre ≤ bFinal)
    (hnewInternal : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        pFinal / ((W.U (W.truncatedLevel final T)).card : ℝ≥0)) :
    let S₀ := relativePreliminaryInitialState ∅
      (outerOnlyAvailable (W.U i.succ) A)
    let K₀ := supportedConditionedRelativePreliminaryKernel n F
      Kpair Kglobal Kinc Delta delta Icut Dcut S₀
    let addedPre : FiniteLaw.TimedState (GreedyStateOn V) n →
        TripleSystemOn V := fun z ↦ z.2.chosen
    let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
        Finset (Sym2 V) := fun z ↦
      preliminaryResidualInternalEdges G (W.U i.succ) z.2.chosen
    let GoodPre : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
      ∀ v : V,
        (outerIncidentEdges (internalOuterGraph G (W.U i.succ))
          (W.U i.succ) v ∩ residual z).card < d + 1
    ∃ hGood : 0 < K₀.probability GoodPre,
      let Kpre := K₀.conditionOn GoodPre hGood
      let Lpre := (FiniteLaw.pure PUnit.unit).jointBind (fun _ ↦ Kpre)
      let Gpre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
          SimpleGraph V := fun _ ↦ G
      let Apre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
          TripleSystemOn V := fun _ ↦ A
      let Mpre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
          TripleSystemOn V := fun z ↦ addedPre z.2
      let Ppre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
          TripleSystemOn V := fun _ ↦ ∅
      let reservePre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
          Finset (Sym2 V) := fun z ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (Mpre z)
      ∃ bits :
          (PUnit × FiniteLaw.TimedState (GreedyStateOn V) n) → Sym2 V → Bool,
        let Aint := fun z ↦ pairSafeAvailable (Apre z) (Mpre z)
        let Kint := rawResidualInternalKernel W i F Gpre Aint Mpre bits D
        IsReserveStronglyWellDistributed (Lpre.jointBind Kint) W final
            (jointInitial
              (jointInitial (fun _ : PUnit ↦ (∅ : TripleSystemOn V))))
            (jointLater
              (jointLater (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
                (fun _ z ↦ addedPre z))
              (rawResidualInternalAdded Mpre))
            (fun z ↦ reservePre z.1) pFinal 1 (2 * CInt) bFinal ∧
          (Lpre.jointBind Kint).SupportedOn (fun z ↦
            0 < Lpre.mass z.1 ∧
              RawResidualInternalOutcomeGood W i F Gpre Aint Mpre bits D R
                z.1 z.2) ∧
          (Lpre.jointBind Kint).SupportedOn (fun z ↦
            Mpre z.1 ⊆ Apre z.1 ∧
              IsPackingOn (Mpre z.1) ∧
              AvoidsForbidden (Mpre z.1) F ∧
              TrianglesDisjointFrom (W.U i.succ) (Mpre z.1) ∧
              ∀ v : V,
                (scheduledEdgesAt
                  (preliminaryResidualInternalEdges
                    (Gpre z.1) (W.U i.succ) (Mpre z.1)) v).card ≤ d) := by
  dsimp only
  let S₀ := relativePreliminaryInitialState ∅
    (outerOnlyAvailable (W.U i.succ) A)
  let K₀ := supportedConditionedRelativePreliminaryKernel n F
    Kpair Kglobal Kinc Delta delta Icut Dcut S₀
  let addedPre : FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ z.2.chosen
  let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
      Finset (Sym2 V) := fun z ↦
    preliminaryResidualInternalEdges G (W.U i.succ) z.2.chosen
  let GoodPre : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∀ v : V,
      (outerIncidentEdges (internalOuterGraph G (W.U i.succ))
        (W.U i.succ) v ∩ residual z).card < d + 1
  obtain ⟨hGood, hGoodSupport, htrajectory, _hlower, hproduct,
      houterOnly, hincidence⟩ :=
    exists_conditionedOuterOnlyPreliminaryLaw n F G A ∅ i hstagei htyp
      hGsupp hh hgap hInv (by
        intro u v huv
        rw [leaveGraph_adj]
        exact ⟨huv.ne, by simp⟩) Kpair Kglobal Kinc Delta delta Icut
      Dcut M supply d hDcut hsupplyM h3supply alpha eta epsilon hsmallPre
      hactive₀ hupper hselected hsurvived hinactive hepsilon htailInc
  refine ⟨hGood, ?_⟩
  let Kpre := K₀.conditionOn GoodPre hGood
  let Lpre := (FiniteLaw.pure PUnit.unit).jointBind (fun _ ↦ Kpre)
  let Gpre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
      SimpleGraph V := fun _ ↦ G
  let Apre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun _ ↦ A
  let Mpre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ addedPre z.2
  let Ppre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun _ ↦ ∅
  let reservePre : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve G (W.U i.succ) ∅ (Mpre z)
  let alphaPre : ℝ≥0 := alpha / (1 - epsilon) /
    (1 - residualOuterIncidenceTail V
      (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
      (eta / (1 - epsilon)) (d + 1))
  have hcrossProduct : ∀ (_u : PUnit) (Q : TripleSystemOn V)
      (E : Finset (Sym2 V)),
      Kpre.probability (fun z ↦ Q ⊆ addedPre z ∧
        E ⊆ preliminaryResidualCrossingEdges G (W.U i.succ)
          (addedPre z)) ≤ alphaPre ^ Q.card * 1 ^ E.card + 0 := by
    intro _u Q E
    calc
      Kpre.probability (fun z ↦ Q ⊆ addedPre z ∧
          E ⊆ preliminaryResidualCrossingEdges G (W.U i.succ)
            (addedPre z)) ≤
          Kpre.probability (fun z ↦ Q ⊆ addedPre z ∧
            (∅ : Finset (Sym2 V)) ⊆ residual z) := by
        apply Kpre.probability_mono
        intro z hz
        exact ⟨hz.1, empty_subset _⟩
      _ ≤ alphaPre ^ Q.card *
          (eta / (1 - epsilon) /
            (1 - residualOuterIncidenceTail V
              (internalOuterGraph G (W.U i.succ)) (W.U i.succ)
              (eta / (1 - epsilon)) (d + 1))) ^
              (∅ : Finset (Sym2 V)).card := by
        simpa only [Kpre, K₀, GoodPre, S₀, addedPre, residual, alphaPre,
          sdiff_empty]
          using hproduct Q ∅
      _ = alphaPre ^ Q.card * 1 ^ E.card + 0 := by simp
  have hpreStrong : IsReserveStronglyWellDistributed Lpre W mid
      (jointInitial (fun _ : PUnit ↦ (∅ : TripleSystemOn V)))
      (jointLater (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
        (fun _ z ↦ addedPre z)) reservePre pPre 1 (2 * CPre) bPre := by
    have hbase := reserveStronglyWellDistributed_pure_empty W stage
    have hupdate := hbase.jointBind_preliminaryAugmentedReserve_of_numeric
      (K := fun _ : PUnit ↦ Kpre) (G := fun _ : PUnit ↦ G)
      (U := W.U i.succ) (p' := pPre) (reserveDensity' := 1)
      (C' := CPre) (b' := bPre) (alpha := alphaPre) (eta := 1)
      (epsilon := 0)
      (fun _ z ↦ addedPre z) hcrossProduct hnonempty hstageMid
      hCPre hCPre hpPre (by norm_num) (by norm_num) (by norm_num)
      halphaPre (by norm_num) (by norm_num) (by norm_num)
      (by simpa using hbPre) hnewPre
    simpa only [Lpre, Kpre, K₀, GoodPre, S₀, reservePre, Mpre,
      jointInitial, jointLater, alphaPre] using hupdate
  let Good : PUnit × FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ 0 < Lpre.mass z
  have hGoodSupport : Lpre.SupportedOn Good := fun _ hz ↦ hz
  have hmassK : ∀ z, Good z → 0 < Kpre.mass z.2 := by
    intro z hz
    exact (FiniteLaw.jointBind_mass_pos_iff
      (FiniteLaw.pure PUnit.unit) (fun _ ↦ Kpre) z.1 z.2).mp hz |>.2
  have htraj : ∀ z, Good z → RelativeGreedyTrajectory F S₀ z.2.2 := by
    intro z hz
    exact htrajectory z.2 (hmassK z hz)
  have hpacking : ∀ z, Good z → IsPackingOn (Ppre z ∪ Mpre z) := by
    intro z hz
    have hs := (htraj z hz).structural_newPart
      (I := (∅ : TripleSystemOn V)) (D := ∅)
      (A := outerOnlyAvailable (W.U i.succ) A) rfl rfl (by simp)
    simpa only [Ppre, Mpre, addedPre, empty_union, S₀,
      relativePreliminaryInitialState_chosen, sdiff_empty] using hs.2.2
  have havoid : ∀ z, Good z → AvoidsForbidden (Ppre z ∪ Mpre z) F := by
    intro z hz
    have hunion := (htraj z hz).initial_union_added
    have hinv := (htraj z hz).1.2.1
    simpa only [S₀, relativePreliminaryInitialState_chosen, sdiff_empty,
      empty_union, Ppre, Mpre, addedPre] using hinv
  have hold : ∀ z, Good z → ∀ T ∈ Apre z,
      TriangleAvoidsGraph (coveredGraph (Ppre z)) T := by
    intro z _hz T _hT u _hu v _hv _huv
    simp only [Ppre, coveredGraph_empty, SimpleGraph.bot_adj, not_false_eq_true]
  have houter : ∀ z, Good z → TrianglesDisjointFrom
      (W.U i.succ) (Mpre z) := by
    intro z hz
    simpa only [Mpre, addedPre, sdiff_empty] using
      houterOnly z.2 (hmassK z hz)
  have hinc : ∀ z, Good z → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges (Gpre z) (W.U i.succ)
          (Ppre z ∪ Mpre z)) v).card ≤ d := by
    intro z hz v
    simpa only [Gpre, Ppre, Mpre, empty_union, addedPre, residual] using
      hincidence z.2 (hmassK z hz) v
  have hsmallUniform : ∀ z, Good z →
      let E := preliminaryResidualInternalEdges
        (Gpre z) (W.U i.succ) (Ppre z ∪ Mpre z)
      (E.card : ℝ) *
        Real.exp (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1 := by
    intro z _hz
    dsimp only [Gpre, Ppre, Mpre, addedPre, empty_union]
    simp only [empty_union]
    have hneg :
        -(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4 =
          -((((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by ring
    rw [hneg]
    apply mul_exp_neg_lt_one_of_lt_exp
    exact hsmallInternal z.2.2.chosen
  obtain ⟨bits, hbits⟩ :=
    hpreStrong.exists_jointBind_rawResidualInternalKernel_of_outerOnly
      Good hGoodSupport (fun _ _ ↦ htyp) (fun _ _ ↦ htri) i hstagei
      (fun _ _ ↦ hGsupp) hpacking havoid hold houter hh reserveRate
      hreserveRate m a D d R q hD hm ha hsmallUniform hfamily hinc
      hscalar hnonempty hmidFinal hCInt hCIntOne hpFinal hfactor hbFinal
      hnewInternal
  refine ⟨bits, ?_⟩
  have hmain :
      IsReserveStronglyWellDistributed (Lpre.jointBind
          (rawResidualInternalKernel W i F Gpre
            (fun z ↦ pairSafeAvailable (Apre z) (Mpre z)) Mpre bits D))
          W final
          (jointInitial (jointInitial (fun _ : PUnit ↦
            (∅ : TripleSystemOn V))))
          (jointLater
            (jointLater (fun _ : PUnit ↦ (∅ : TripleSystemOn V))
              (fun _ z ↦ addedPre z))
            (rawResidualInternalAdded Mpre))
          (fun z ↦ reservePre z.1) pFinal 1 (2 * CInt) bFinal ∧
        (Lpre.jointBind
          (rawResidualInternalKernel W i F Gpre
            (fun z ↦ pairSafeAvailable (Apre z) (Mpre z)) Mpre bits D)).SupportedOn
          (fun z ↦ 0 < Lpre.mass z.1 ∧
            RawResidualInternalOutcomeGood W i F Gpre
              (fun z ↦ pairSafeAvailable (Apre z) (Mpre z)) Mpre bits D R
              z.1 z.2) := by
    simpa only [Good, Lpre, Gpre, Apre, Mpre, Ppre, reservePre, Kpre, K₀,
      GoodPre, S₀, residual, addedPre, jointInitial, jointLater, empty_union,
      sdiff_empty] using hbits
  refine ⟨hmain.1, hmain.2, ?_⟩
  intro z hz
  have hzpre : Good z.1 :=
    (FiniteLaw.jointBind_mass_pos_iff Lpre
      (rawResidualInternalKernel W i F Gpre
        (fun z ↦ pairSafeAvailable (Apre z) (Mpre z)) Mpre bits D)
      z.1 z.2).mp hz |>.1
  have hselected : Mpre z.1 ⊆ Apre z.1 := by
    intro T hT
    exact outerOnlyAvailable_subset (W.U i.succ) A
      ((htraj z.1 hzpre).added_subset_available (by
        simpa only [Mpre, addedPre, S₀, relativePreliminaryInitialState_chosen,
          sdiff_empty] using hT))
  have hpacking' : IsPackingOn (Mpre z.1) := by
    simpa only [Ppre, empty_union] using hpacking z.1 hzpre
  have havoid' : AvoidsForbidden (Mpre z.1) F := by
    simpa only [Ppre, empty_union] using havoid z.1 hzpre
  refine ⟨hselected, hpacking', havoid',
    houter z.1 hzpre, ?_⟩
  intro v
  simpa only [Gpre, Ppre, Mpre, empty_union] using hinc z.1 hzpre v

end

end Erdos207

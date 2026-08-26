import ErdosProblems.Erdos118.LastBodyRefinement

/-!
Last selected body markers are fixed at exact pending last-body states.
Refine their order while preserving the proved nonsingleton terminal
restriction, and transfer the uniform test to actual blue pending pairs.
-/

namespace Erdos118.LastMarkerRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open DecisionStates ClearPairs LastBodyRefinement BlueRuns

def lastMarker (S : Completed) : ℕ :=
  ((S.stem.done[lastIndex S]?).map (fun a ↦ a.values.length)).getD 0

theorem lastIndex_lt (S : Completed) (hne : S.stem.rootLabel ≠ []) :
    lastIndex S < S.stem.done.length := by
  have hm : S.stem.rootLabel.getLastD 0 ∈ S.stem.rootLabel := by
    cases he : S.stem.rootLabel with
    | nil => exact (hne he).elim
    | cons a l =>
      simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (a := a) (l := l))
  have hb := S.stem.label_before_root _ hm
  have hf := S.full
  dsimp only [lastIndex]
  omega

theorem lastMarker_mem (S : Completed) (hne : S.stem.rootLabel ≠ []) :
    lastMarker S ∈ S.stem.ordinary := by
  have hi := lastIndex_lt S hne
  unfold lastMarker
  rw [List.getElem?_eq_getElem hi]
  exact body_marker_mem S.stem S.stem.done[lastIndex S] (List.getElem_mem hi)

theorem lastMarker_of_extension (P : Pending) (S : Completed)
    (hP : ExactSlots.Exact (.leaf P)) (hroots : P.roots = [])
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) :
    lastMarker S = P.position.size := by
  have hl : LabelledFrames.LabelsExtend (.pending P) (.terminal S.stem S.full) :=
    ⟨fun C hC ↦ hext.labels.root C hC, hext.labels.bodies⟩
  obtain ⟨a, rest, hdone, _, hsize, _⟩ :=
    (cutExtension_of_prefix P S.stem S.full hl hext.decorated).bodies
  unfold lastMarker
  rw [lastIndex_of_extension P S hP hroots hext.labels, hdone]
  simp [hsize]

theorem lastMarkers_ne (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ []) :
    lastMarker S ≠ lastMarker T := by
  exact (foreign_ne hclear.disjoint (lastMarker_mem T hT)
    (S.stem.ordinary_sublist.subset (lastMarker_mem S hS))).symm

theorem pending_sizes_ne {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (P Q : Pending)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .leaf Q)) true) :
    P.position.size ≠ Q.position.size := by
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B o)
    (.leaf P, .leaf Q) hblue
  have hclear := ((GraphPayoff.payoff_true_iff B o S T).mp hpay).2.1
  have hP : P.position.size ∈ S.stem.ordinary :=
    (SkippedCuts.run_extensions hrun).1.ordinary.subset
      (by simp [State.ordinary, Position.ordinary])
  have hQ : Q.position.size ∈ T.stem.ordinary :=
    (SkippedCuts.run_extensions hrun).2.ordinary.subset
      (by simp [State.ordinary, Position.ordinary])
  exact (foreign_ne hclear.disjoint hQ (S.stem.ordinary_sublist.subset hP)).symm

theorem payoff_true_mono {B C : SimpleGraph G} (hCB : C ≤ B)
    (o : GraphPayoff.Orientation) (S T : Completed)
    (hpay : GraphPayoff.payoff C o S T = true) : GraphPayoff.payoff B o S T = true := by
  obtain ⟨hroot, hclear, horient, hedge⟩ := (GraphPayoff.payoff_true_iff C o S T).mp hpay
  exact (GraphPayoff.payoff_true_iff B o S T).mpr ⟨hroot, hclear, horient, hCB hedge⟩

theorem exists_refined {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∃ value : Bool, ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (lastLabel S).length ≠ 1 ∧
          @decide (lastMarker T < lastMarker S) (Classical.propDecidable _) = value := by
  obtain ⟨I, hIH, hI, D, hDB, hD, hblueD, hlast⟩ :=
    LastBodyRefinement.exists_refined hH B hB hinit
  obtain ⟨K, hKI, hK, C, hCD, hC, hblueC, value, htest⟩ :=
    IntrinsicAnnotations.refine_test hI D hD .inside hblueD
      (fun S T ↦ lastMarker T < lastMarker S)
  refine ⟨K, hKI.trans hIH, hK, C, hCD.trans hDB, hC, hblueC, value, ?_⟩
  intro S T hp
  exact ⟨hlast S T (payoff_true_mono hCD .inside S T hp), htest S T hp⟩

theorem pending_order {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (value : Bool)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      @decide (lastMarker T < lastMarker S) (Classical.propDecidable _) = value)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPR : P.roots = []) (hQR : Q.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    if value then Q.position.size < P.position.size else P.position.size < Q.position.size := by
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) hblue
  have hS := lastMarker_of_extension P S hP hPR (SkippedCuts.run_extensions hrun).1
  have hT := lastMarker_of_extension Q T hQ hQR (SkippedCuts.run_extensions hrun).2
  have htest := hall S T hpay
  cases value with
  | true =>
    have h := @of_decide_eq_true _ (Classical.propDecidable _) htest
    simpa only [hS, hT, ↓reduceIte] using h
  | false =>
    have h := @of_decide_eq_false _ (Classical.propDecidable _) htest
    rw [hS, hT] at h
    have hne := pending_sizes_ne hH B .inside P Q hblue
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

end Erdos118.LastMarkerRefinement

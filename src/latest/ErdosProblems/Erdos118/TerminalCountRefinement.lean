import ErdosProblems.Erdos118.LateMarkerExclusion
import ErdosProblems.Erdos118.EndpointRefinement

/-! The surviving early-marker subgraph has uniformly equal or strictly
ordered before-last selected counts. The terminal root labels are proved
nonempty, so the marker/count equivalence applies without an extra premise. -/

namespace Erdos118.TerminalCountRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open CutIndices SelectedGapCounts InsideCounts FirstBodyRefinement LastBodyRefinement
open LastMarkerRefinement

theorem selected_empty_of_root_nil (S T : Stem) (h : ExactAnnotations S T)
    (hroot : S.rootLabel = []) : selected S = ∅ := by
  by_contra he
  obtain ⟨⟨i, j⟩, hm⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨hi, hj⟩ := (mem_selected S i j).mp hm
  have hc := (h.body i hi j).mp hj
  have hr := (h.root (i + 1)).mpr ⟨i, j, hc, rfl⟩
  rw [hroot] at hr
  exact List.not_mem_nil hr

theorem lastLabel_nonempty (S : Completed) (T : Stem)
    (h : ExactAnnotations S.stem T) (hroot : S.stem.rootLabel ≠ []) : lastLabel S ≠ [] := by
  have hm : S.stem.rootLabel.getLastD 0 ∈ S.stem.rootLabel := by
    cases he : S.stem.rootLabel with
    | nil => exact (hroot he).elim
    | cons a l => simpa only [List.getLastD_cons] using List.getLastD_mem_cons (a := a) (l := l)
  obtain ⟨i, j, hc, hi⟩ := (h.root _).mp hm
  have he : i = lastIndex S := by unfold lastIndex; omega
  subst i
  have hib : lastIndex S < S.stem.bodyLabels.length := by
    simpa only [Stem.bodyLabels, List.length_map] using lastIndex_lt S hroot
  have hj := (h.body _ hib j).mpr hc
  have hj' : j ∈ lastLabel S := by
    simpa only [lastLabel, List.getElem?_eq_getElem hib, Option.getD_some] using hj
  exact List.ne_nil_of_mem hj'

theorem roots_nonempty (B : SimpleGraph G) (S T : Completed)
    (hpay : GraphPayoff.payoff B .inside S T = true) (hlast : (lastLabel S).length ≠ 1) :
    S.stem.rootLabel ≠ [] ∧ T.stem.rootLabel ≠ [] := by
  obtain ⟨hr, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hpay
  have hcount := selected_inside S T hc hr ho
  have hS : S.stem.rootLabel ≠ [] := by
    intro he
    rw [selected_empty_of_root_nil S.stem T.stem hc.exactLeft he, Finset.card_empty] at hcount
    omega
  refine ⟨hS, ?_⟩
  intro he
  rw [selected_empty_of_root_nil T.stem S.stem hc.exactRight he, Finset.card_empty] at hcount
  have hd := selected_card_decomposition S T.stem hc.exactLeft hS
  have hp : 0 < (lastLabel S).length := List.length_pos_iff.mpr
    (lastLabel_nonempty S T.stem hc.exactLeft hS)
  omega

theorem exists_early {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (firstLabel S).length ≠ 1 ∧ (lastLabel S).length ≠ 1 ∧ lastMarker S < lastMarker T := by
  obtain ⟨K, hKH, hK, C, hCB, hC, hb, value, hall⟩ :=
    EndpointRefinement.exists_refined hH B hB hinit
  cases value with
  | true =>
    exact (LateMarkerExclusion.not_blue hK C hC (fun S T hp ↦ (hall S T hp).1)
      (fun S T hp ↦ @of_decide_eq_true _ (Classical.propDecidable _) (hall S T hp).2.2)
      (fun S T hp ↦ (hall S T hp).2.1) hb).elim
  | false =>
    refine ⟨K, hKH, hK, C, hCB, hC, hb, ?_⟩
    intro S T hp
    obtain ⟨hf, hl, hv⟩ := hall S T hp
    have hn := @of_decide_eq_false _ (Classical.propDecidable _) hv
    obtain ⟨hS, hT⟩ := roots_nonempty C S T hp hl
    have he := lastMarkers_ne S T ((GraphPayoff.payoff_true_iff C .inside S T).mp hp).2.1 hS hT
    exact ⟨hf, hl, by omega⟩

theorem exists_alternative {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∃ aligned : Bool, ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (firstLabel S).length ≠ 1 ∧ (lastLabel S).length ≠ 1 ∧
        lastMarker S < lastMarker T ∧
        if aligned then beforeLast S = beforeLast T else beforeLast S < beforeLast T := by
  obtain ⟨I, hIH, hI, D, hDB, hD, hbD, hold⟩ := exists_early hH B hB hinit
  obtain ⟨K, hKI, hK, C, hCD, hC, hbC, value, htest⟩ :=
    IntrinsicAnnotations.refine_test hI D hD .inside hbD (fun S T ↦ beforeLast S = beforeLast T)
  refine ⟨K, hKI.trans hIH, hK, C, hCD.trans hDB, hC, hbC, value, ?_⟩
  intro S T hp
  obtain ⟨hf, hl, hm⟩ := hold S T (payoff_true_mono hCD .inside S T hp)
  obtain ⟨hS, hT⟩ := roots_nonempty C S T hp hl
  obtain ⟨hr, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff C .inside S T).mp hp
  have hle := (LastSuffixCounts.marker_lt_iff_before_le S T hc hr ho hS hT).mp hm
  refine ⟨hf, hl, hm, ?_⟩
  have ht := htest S T hp
  cases value with
  | true => exact @of_decide_eq_true _ (Classical.propDecidable _) ht
  | false =>
    have hn := @of_decide_eq_false _ (Classical.propDecidable _) ht
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

theorem pending_alternative {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (aligned : Bool)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      if aligned then beforeLast S = beforeLast T else beforeLast S < beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPR : P.roots = []) (hQR : Q.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    if aligned then (selected P.position.stem).card = (selected Q.position.stem).card
      else (selected P.position.stem).card < (selected Q.position.stem).card := by
  obtain ⟨S, T, hrun, hp⟩ := BlueRuns.blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) hblue
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  have h := hall S T hp
  rw [PendingCounts.beforeLast_of_extension P S hP hPR heP,
    PendingCounts.beforeLast_of_extension Q T hQ hQR heQ] at h
  exact h

theorem pending_label_sizes {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (aligned : Bool)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      if aligned then beforeLast S = beforeLast T else beforeLast S < beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPR : P.roots = []) (hQR : Q.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    if aligned then P.position.label.length = Q.position.label.length + 1
      else Q.position.label.length + 2 ≤ P.position.label.length := by
  have h := pending_alternative hH B aligned hall P Q hP hQ hPR hQR hblue
  have hc := PendingCounts.inside_count hH B P Q hP hQ hPR hQR hblue
  cases aligned <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

end Erdos118.TerminalCountRefinement

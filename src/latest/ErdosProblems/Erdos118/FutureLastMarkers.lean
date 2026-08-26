import ErdosProblems.Erdos118.PendingCounts

/-!
An unplayed selected body has a future last marker, beyond the old
decorated prefix. Chronological blue completions therefore rule out
remaining opposite roots in the uniform late-left-marker class.
-/

namespace Erdos118.FutureLastMarkers

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open LastBodyRefinement LastMarkerRefinement LastSuffixCounts BodySuffixCounts

theorem lastIndex_gt_of_roots (Q : Pending) (T : Completed) (hQ : Q.roots ≠ [])
    (hext : SkippedCuts.StateExtension (.leaf Q) (.complete T)) :
    Q.position.stem.done.length < lastIndex T := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil Q.roots hQ
  have hslot := Q.rootSlots.bounded j hj
  have hroot : T.stem.rootLabel = Q.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root _ rfl)
  have hjT : j ∈ T.stem.rootLabel := hroot ▸ hslot.2.2
  have hne := List.ne_nil_of_mem hjT
  have hle := (T.stem.label_pairwise.imp Nat.le_of_lt).rel_getLast hjT
  have he : T.stem.rootLabel.getLastD 0 = T.stem.rootLabel.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  unfold lastIndex
  rw [he]
  have hgt := hslot.1
  omega

theorem old_decorated_lt_lastMarker (Q : Pending) (T : Completed) (hQ : Q.roots ≠ [])
    (hext : SkippedCuts.StateExtension (.leaf Q) (.complete T)) :
    ∀ x ∈ Q.position.decorated, x < lastMarker T := by
  have hindex := lastIndex_gt_of_roots Q T hQ hext
  have hp : Q.position.toInterior.word <+: T.stem.ordinary := by
    rw [Position.toInterior_word]
    exact hext.ordinary
  have hpos : 0 < Q.position.ordinary.length := by
    simp [Position.ordinary, Stem.ordinary]
  have hlen : Q.position.toInterior.word.length = (Q.position.ordinary.length - 1) + 1 := by
    rw [Position.toInterior_word]
    omega
  have hcut := interior_length_cutoff hp hlen (lastIndex T)
  have hnot : ¬ offset T.stem (lastIndex T) ≤ Q.position.ordinary.length - 1 := by
    intro h
    have hle := hcut.mp h
    change lastIndex T ≤ (Q.position.stem.done.map Body.values).length at hle
    simp only [List.length_map] at hle
    omega
  have hpre : preword T <+: T.stem.ordinary := by
    rw [ordinary_split T]
    exact List.prefix_append _ _
  have hprelen : (preword T).length = offset T.stem (lastIndex T) := by
    simp only [preword, offset, List.length_cons, Nat.add_comm]
  have hqp : Q.position.ordinary <+: preword T :=
    List.prefix_of_prefix_length_le hext.ordinary hpre (by rw [hprelen]; omega)
  have hinc : (preword T ++ suffix T).Pairwise (· < ·) :=
    ordinary_split T ▸ T.stem.increasing.sublist T.stem.ordinary_sublist
  have hrootne := PendingCounts.rootLabel_ne_nil_of_extension Q T hext
  have hm : lastMarker T ∈ suffix T := by
    rw [← suffix_head T hrootne]
    cases hs : suffix T with
    | nil => exact (suffix_ne_nil T hrootne hs).elim
    | cons a xs => simp
  intro x hx
  obtain ⟨y, hy, hxy⟩ := DecoratedFrontiers.position_dominated Q.position x hx
  exact hxy.trans_lt ((List.pairwise_append.mp hinc).2.2 y (hqp.subset hy) _ hm)

theorem late_right_roots_nil {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      lastMarker T < lastMarker S)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hPR : P.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    Q.roots = [] := by
  by_contra hQ
  obtain ⟨S, T, hrun, hpay⟩ := BlueRuns.blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) hblue
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  have hS := lastMarker_of_extension P S hP hPR heP
  have hT := old_decorated_lt_lastMarker Q T hQ heQ
  have hrootne := PendingCounts.rootLabel_ne_nil_of_extension Q T heQ
  have hnew := SkippedCuts.run_right_future hrun
    (show P.position.size ∈ State.decorated (.leaf P) by
      simp [State.decorated, Position.decorated])
    (lastMarker T) (T.stem.ordinary_sublist.subset (lastMarker_mem T hrootne))
  have hlate := hall S T hpay
  rw [hS] at hlate
  rcases hnew with hold | hlt
  · exact (Nat.lt_irrefl _ (hT _ hold)).elim
  · omega

end Erdos118.FutureLastMarkers

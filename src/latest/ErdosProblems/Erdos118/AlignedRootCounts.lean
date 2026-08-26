import ErdosProblems.Erdos118.TerminalCountRefinement

/-! Uniformly aligned before-last counts force a positive right root
parameter whenever the fixed left root label is nonsingleton. -/

namespace Erdos118.AlignedRootCounts

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates CutIndices
open SelectedGapCounts InsideCounts LastBodyRefinement BlueRuns

theorem beforeLast_pos_iff (S : Completed) (T : Stem) (h : ExactAnnotations S.stem T) :
    0 < beforeLast S ↔ 1 < S.stem.rootLabel.length := by
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
    obtain ⟨ha, hbefore⟩ := Finset.mem_filter.mp ha
    obtain ⟨hai, haj⟩ := (mem_selected _ _ _).mp ha
    have hr := (h.root (a.1 + 1)).mpr ⟨a.1, a.2, (h.body _ hai _).mp haj, rfl⟩
    have hpos := List.length_pos_iff.mpr (List.ne_nil_of_mem hr)
    by_contra hn
    have he : S.stem.rootLabel.length = 1 := by omega
    obtain ⟨r, hlabel⟩ := List.length_eq_one_iff.mp he
    have har : a.1 + 1 = r := by simpa only [hlabel, List.mem_singleton] using hr
    simp only [lastIndex, hlabel, List.getLastD_cons, List.getLastD_nil] at hbefore
    omega
  · intro hlen
    cases hC : S.stem.rootLabel with
    | nil => simp [hC] at hlen
    | cons a tail =>
      cases tail with
      | nil => simp [hC] at hlen
      | cons b rest =>
        have hinc : (a :: b :: rest).Pairwise (· < ·) := hC ▸ S.stem.label_pairwise
        have hab : a < b := (List.pairwise_cons.mp hinc).1 b (by simp)
        have haC : a ∈ S.stem.rootLabel := by rw [hC]; simp
        have hbC : b ∈ S.stem.rootLabel := by rw [hC]; simp
        have hne := List.ne_nil_of_mem haC
        have hbl := (S.stem.label_pairwise.imp Nat.le_of_lt).rel_getLast hbC
        have hlast : S.stem.rootLabel.getLastD 0 = S.stem.rootLabel.getLast hne := by
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
          rfl
        have hal : a < S.stem.rootLabel.getLastD 0 := by rw [hlast]; exact hab.trans_le hbl
        obtain ⟨i, j, hc, hi⟩ := (h.root a).mp haC
        have har := S.stem.label_before_root a haC
        have hiS : i < S.stem.bodyLabels.length := by
          simp only [Stem.bodyLabels, List.length_map, S.full]
          omega
        have hs : (⟨i, j⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem :=
          (mem_selected _ _ _).mpr ⟨hiS, (h.body i hiS j).mpr hc⟩
        have hib : i < lastIndex S := by unfold lastIndex; omega
        exact Finset.card_pos.mpr ⟨⟨i, j⟩, Finset.mem_filter.mpr ⟨hs, hib⟩⟩

theorem right_root_length (B : SimpleGraph G) (S T : Completed)
    (hp : GraphPayoff.payoff B .inside S T = true) (heq : beforeLast S = beforeLast T)
    (hS : 1 < S.stem.rootLabel.length) : 1 < T.stem.rootLabel.length := by
  have hc := ((GraphPayoff.payoff_true_iff B .inside S T).mp hp).2.1
  have hs := (beforeLast_pos_iff S T.stem hc.exactLeft).mpr hS
  exact (beforeLast_pos_iff T S.stem hc.exactRight).mp (heq ▸ hs)

theorem right_setup_positive {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S = beforeLast T)
    (P : Pending) (hP : 1 < P.position.stem.rootLabel.length)
    {k : ℕ} (A : RootResponses.Setup k)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .body (ofRoot A))) true) :
    0 < k := by
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .body (ofRoot A)) hblue
  obtain ⟨heP, heA⟩ := SkippedCuts.run_extensions hrun
  have hS : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (heP.labels.root _ rfl)
  have hT : T.stem.rootLabel = A.stem.rootLabel :=
    Option.some.inj (heA.labels.root _ rfl)
  have ht := right_root_length B S T hp (hall S T hp) (hS ▸ hP)
  rw [hT, A.label_length] at ht
  omega

theorem second_root_setups {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S = beforeLast T)
    (P : Pending) (hP : 1 < P.position.stem.rootLabel.length)
    (hright : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .initial)) :
    ∃ k b : ℕ, 0 < k ∧ ∀ A : RootResponses.Setup k,
      (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .body (ofRoot A))) true := by
  obtain ⟨k, b, hb⟩ := BlueReservations.second_root_setups hH B hB .inside hinit P hright
  obtain ⟨A, hf⟩ := RootResponses.setup_above k hH b
  have hblue := hb A (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
  exact ⟨k, b, right_setup_positive hH B hall P hP A hblue, hb⟩

end Erdos118.AlignedRootCounts

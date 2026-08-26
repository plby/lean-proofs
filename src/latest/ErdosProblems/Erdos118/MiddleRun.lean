import ErdosProblems.Erdos118.SelectedLeafResponses
import ErdosProblems.Erdos118.InsideEndgame

/-!
An actual inside middle run leaves one selected left leaf pending and
exhausts the opposite last body. Both ordinary suffixes retain their
sampling alphabet and extra bound. The test final left response is not
included in the returned run.
-/

namespace Erdos118.MiddleRun

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays FreshCheckpoints

theorem final_left_test {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P Q : Pending) (j : ℕ) (hR : P.roots = []) (hL : P.leaves = [j])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) :
    Q.roots = [] ∧ Q.leaves = [] := by
  obtain ⟨A, _, _, hh, _⟩ := SelectedLeafResponses.respond hH Set.Subset.rfl
    B .inside false P (.leaf Q) j [] hL hblue 0
  obtain ⟨U, he, hUR, hUL⟩ := InsideEndgame.last_left_right_command hH B
    (LeafResponses.toPending P j [] hL A) (.leaf Q) hR rfl (by simp) hh
  have hQU : Q = U := State.leaf.inj he
  subst U
  exact ⟨hUR, hUL⟩

private def board (S : Pending × Pending) : State × State := (.leaf S.1, .leaf S.2)

private theorem board_wellFounded : WellFounded (fun T S : Pending × Pending ↦
    PairStep (board T) (board S)) := InvImage.wf board pairStep_wellFounded

theorem stop {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B : SimpleGraph G)
    (d : ℕ) (S : Pending × Pending) (hPR : S.1.roots = []) (hQR : S.2.roots = [])
    (hPL : S.1.leaves ≠ [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (board S)) true)
    (hready : (∃ j : ℕ, S.1.leaves = [j]) →
      RightBlue H (GraphPayoff.payoff B .inside) (board S)) :
    ∃ T : Pending × Pending, ∃ j : ℕ, T.1.leaves = [j] ∧ T.1.roots = [] ∧ T.2.roots = [] ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside) (board S) (board T) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (board T)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (board T) ∧
      FreshExtension K d (board S) (board T) := by
  induction S using board_wellFounded.induction with
  | h S ih =>
    by_cases hc : ∃ j : ℕ, S.1.leaves = [j]
    · obtain ⟨j, hj⟩ := hc
      exact ⟨S, j, hj, hPR, hQR, Relation.ReflTransGen.refl,
        hblue, hready ⟨j, hj⟩, fresh_refl K d (board S)⟩
    · rcases blue_command (GraphPayoff.payoff B .inside) (board S) rfl hblue with hl | hr
      · obtain ⟨j, rest, hL⟩ := List.exists_cons_of_ne_nil hPL
        have hrest : rest ≠ [] := by
          intro he
          subst rest
          exact hc ⟨j, hL⟩
        obtain ⟨A, hs, hb, hh, hf⟩ := SelectedLeafResponses.respond hK hKH
          B .inside false S.1 (.leaf S.2) j rest hL hl d
        let P := LeafResponses.toPending S.1 j rest hL A
        obtain ⟨T, k, hTL, hTR, hUR, hrun, hbT, hhT, hfT⟩ :=
          ih (P, S.2) hs.pairStep hPR hQR hrest hb (fun _ ↦ hh)
        have hslot := S.1.leafSlots.bounded j (hL ▸ List.mem_cons_self ..)
        have hf₀ : FreshExtension K d (board S) (board (P, S.2)) :=
          ⟨A.newWord, [], LeafResponses.position_ordinary A hslot.1 hslot.2.1,
            by simp [board], hf, by simp⟩
        exact ⟨T, k, hTL, hTR, hUR, Relation.ReflTransGen.head hs hrun,
          hbT, hhT, fresh_trans hf₀ hfT⟩
      · have hQL : S.2.leaves ≠ [] := by
          intro he
          exact hPL (InsideEndgame.last_right_command_left_last (hK.mono hKH)
            B S.1 S.2 hQR he hr).2
        obtain ⟨j, rest, hL⟩ := List.exists_cons_of_ne_nil hQL
        obtain ⟨A, hs, hb, _, hf⟩ := SelectedLeafResponses.respond hK hKH
          B .inside true S.2 (.leaf S.1) j rest hL hr d
        let Q := LeafResponses.toPending S.2 j rest hL A
        obtain ⟨T, k, hTL, hTR, hUR, hrun, hbT, hhT, hfT⟩ :=
          ih (S.1, Q) hs.pairStep hPR hQR hPL hb (fun he ↦ (hc he).elim)
        have hslot := S.2.leafSlots.bounded j (hL ▸ List.mem_cons_self ..)
        have hf₀ : FreshExtension K d (board S) (board (S.1, Q)) :=
          ⟨[], A.newWord, by simp [board],
            LeafResponses.position_ordinary A hslot.1 hslot.2.1, by simp, hf⟩
        exact ⟨T, k, hTL, hTR, hUR, Relation.ReflTransGen.head hs hrun,
          hbT, hhT, fresh_trans hf₀ hfT⟩

theorem endpoint {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B : SimpleGraph G)
    (d : ℕ) (P Q : Pending) (hPR : P.roots = []) (hQR : Q.roots = []) (hPL : P.leaves ≠ [])
    (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true)
    (hready : (∃ j : ℕ, P.leaves = [j]) →
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) :
    ∃ P' Q' : Pending, ∃ j : ℕ, SameBody P P' ∧ SameBody Q Q' ∧
      P'.leaves = [j] ∧ Q'.leaves = [] ∧
      ExactSlots.Exact (.leaf P') ∧ ExactSlots.Exact (.leaf Q') ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf Q) (.leaf P', .leaf Q') ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P', .leaf Q')) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P', .leaf Q') ∧
      FreshExtension K d (.leaf P, .leaf Q) (.leaf P', .leaf Q') := by
  obtain ⟨⟨P₁, Q₁⟩, j, hP₁L, hP₁R, hQ₁R, hrun, hb, hh, hf₁⟩ :=
    stop hK hKH B d (P, Q) hPR hQR hPL hblue hready
  have hQ₁L : Q₁.leaves ≠ [] := by
    intro he
    have hbad := (InsideEndgame.last_right_command_left_last
      (hK.mono hKH) B P₁ Q₁ hQ₁R he hh).2
    rw [hP₁L] at hbad
    cases hbad
  obtain ⟨k, rest, hL⟩ := List.exists_cons_of_ne_nil hQ₁L
  obtain ⟨A, hs, hb', hh', hf⟩ := SelectedLeafResponses.respond hK hKH
    B .inside true Q₁ (.leaf P₁) k rest hL hh d
  let Q₂ := LeafResponses.toPending Q₁ k rest hL A
  have hlast := final_left_test (hK.mono hKH) B P₁ Q₂ j hP₁R hP₁L hh'
  have hfull : ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
      (.leaf P, .leaf Q) (.leaf P₁, .leaf Q₂) := Relation.ReflTransGen.tail hrun hs
  have hslot := Q₁.leafSlots.bounded k (hL ▸ List.mem_cons_self ..)
  have hf₂ : FreshExtension K d (.leaf P₁, .leaf Q₁) (.leaf P₁, .leaf Q₂) :=
    ⟨[], A.newWord, by simp, LeafResponses.position_ordinary A hslot.1 hslot.2.1, by simp, hf⟩
  exact ⟨P₁, Q₂, j, run_last_body_left P P₁ (.leaf Q) (.leaf Q₂) hPR hfull,
    run_last_body_right Q Q₂ (.leaf P) (.leaf P₁) hQR hfull, hP₁L, hlast.2,
    ExactSlots.run_exact_left hfull hP, ExactSlots.run_exact_right hfull hQ,
    hfull, hb', hh', fresh_trans hf₁ hf₂⟩

end Erdos118.MiddleRun

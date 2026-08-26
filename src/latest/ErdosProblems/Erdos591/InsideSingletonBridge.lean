import ErdosProblems.Erdos591.ManagedMarkerReplay
import ErdosProblems.Erdos591.InsideLastFirstEndgame
import ErdosProblems.Erdos591.LastBodyUniformization
import ErdosProblems.Erdos591.FirstLeafGluingHistory

/-!
# Close the singleton last-body bridge after insertion of the third play

The first lower play waits before its last body. The second play has a
fresh recorded prefix and a managed opposite word. Reach the common last
marker, recover both singleton requests from their actual origin paths,
share their sole leaf, fire the opposite managed word, and close the triangle.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_singleton_bridge_triangle {N H J : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old fine upperOrigin : Concrete.Hist N)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinFine : (exactGame N blue).ArchitectWins J b σ fine)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromFine : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin fine)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true)
    (hmodeOld : old.position.mode = some true) (hmodeFine : fine.position.mode = some true)
    (hp : old.position.pending = some ⟨false, .advance 0⟩)
    {anchor : LabeledWord} {frontAtoms : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure old.position.board.left anchor)
    (hprefix : LabeledWord.LegalRun anchor frontAtoms fine.position.board.left)
    (hprefixPool : ∀ a ∈ frontAtoms, a.2 ∈ H ∧ max old.position.bound (b old) < a.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x)
    (hrelOld : old.position.board.left.relaxed = true)
    (hnOld : old.position.board.left.NoLeafPending) {i : ℕ}
    (hbeforeOld : LabeledWord.BeforeBody i old.position.board.left)
    (hnext : ∀ k ∈ old.position.board.left.rootLabel,
      old.position.board.left.bodyLabels.length < k → i ≤ k)
    (hbeforeFine : LabeledWord.BeforeBody i fine.position.board.left)
    (hrootOld : ∀ k ∈ old.position.board.left.rootLabel, k ≤ i)
    (hrootFine : ∀ k ∈ fine.position.board.left.rootLabel, k ≤ i)
    (hTrel : old.position.board.right.relaxed = true)
    (hTlast : ¬ Macro.Pending old.position.board.right)
    (hT : LabeledWord.SameStructure old.position.board.right upperOrigin.position.board.left)
    (hmanaged : ∃ M : Managed N J blue b σ true true upperOrigin.position.board.left
        fine.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target) :
    ¬ blue.CliqueFree 3 := by
  have hH : H.Infinite := hJ.mono hJH
  have hJN := hJH.trans hHN
  have pathH {p q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpath
  obtain ⟨su, st, d, hfine, hold, hsuP, hd, hstN, hshape, hsuM, hstM, hindex, hstOther, hM⟩ :=
    winning_managed_marker_replay_from_prefix hHN hJH hJ blue fine old hwinFine false false hp
      hsame hprefix hprefixPool hJfresh hrelOld hnOld hbeforeOld hnext hbeforeFine
      upperOrigin hmanaged
  change LabeledWord.SameStructure st.position.board.left su.position.board.left at hshape
  change su.position.board.left.markerEvent = true at hsuM
  change st.position.board.left.markerEvent = true at hstM
  change su.position.board.left.bodyLabels.length + 1 = i at hindex
  change st.position.board.right = old.position.board.right at hstOther
  have hwinST := hwinOld.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hold)
  obtain ⟨stBody, e, hrequest, hboard, hstP, _he⟩ :=
    winning_request_at_marker hHN hH blue hwinST false hstN hstM
  have holdBody := (Relation.ReflTransGen.single hold).tail hrequest
  have hfromST := hfromOld.trans holdBody
  have hfromSU := hfromFine.trans (pathH hfine)
  have hstartOld : old.position.board.left.parser ≠ .start :=
    LabeledWord.relaxed_ne_start ((Position.history_dataInvariant old).2.1 false).1 hrelOld
  have hstartFine : fine.position.board.left.parser ≠ .start :=
    hprefix.parser_ne_start (fun he => hstartOld (hsame.parser_eq.trans he))
  obtain ⟨as, has, _⟩ := follow_word_inputs holdBody 0 (fun _ => Nat.zero_le _) false
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs hfine 0 (fun _ => Nat.zero_le _) false
  have hrootST : ∀ k ∈ stBody.position.board.left.rootLabel,
      k ≤ stBody.position.board.left.bodyLabels.length + 1 := by
    intro k hk
    have hk' := hrootOld k (has.rootLabel_eq hstartOld ▸ hk)
    have hiST : stBody.position.board.left.bodyLabels.length + 1 = i := by
      rw [hboard, hshape.body_length]
      exact hindex
    rw [hiST]
    exact hk'
  have hrootSU : ∀ k ∈ su.position.board.left.rootLabel,
      k ≤ su.position.board.left.bodyLabels.length + 1 := by
    intro k hk
    have hk' := hrootFine k (hbs.rootLabel_eq hstartFine ▸ hk)
    rw [show su.position.board.left.bodyLabels.length + 1 = i from hindex]
    exact hk'
  have heOne : e = 1 := of_decide_eq_true (pending_last_body_observable hHN hH blue
    origin stBody false true hfromST hall hstP rfl
    (by simpa [hboard, Board.get] using hstM) hrootST)
  have hdOne : d = 1 := of_decide_eq_true (pending_last_body_observable hHN hH blue
    origin su false true hfromSU hall hsuP rfl hsuM hrootSU)
  let B := max (max stBody.position.bound (b stBody)) (max su.position.bound (b su))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hJ B 1 1 (by omega) (by omega)
  obtain ⟨lastST, lastSU, hsST, hsSU, hnST, hnSU, hS, hrST, hrSU, hiST, hiSU,
      hbST, hbSU, hoST, hoSU⟩ := first_leaf_gluing hJN hJ blue σ stBody su false false
    L L rfl rfl (by simpa only [heOne] using hstP) (by simpa only [hdOne] using hsuP)
    (by simpa [hboard, Board.get] using hstM) hsuM (by simpa [hboard, Board.get] using hshape)
    (le_max_left _ _) (le_max_right _ _)
  have hSTpath := holdBody.trans (pathH (Relation.ReflTransGen.single hsST))
  have hSUpath := hfine.tail hsSU
  have hwinLastSTH := hwinOld.of_reachable (exactGame N blue) hSTpath
  have hwinLastST := hwinLastSTH.mono (exactGame N blue) hJH (fun _ => le_rfl)
  have hwinLastSU := hwinFine.of_reachable (exactGame N blue) hSUpath
  have root_exhausted {v q : Concrete.Hist N}
      (hstep : (exactGame N blue).FollowStep σ J b v q)
      (hmarker : v.position.board.left.markerEvent = true)
      (hroot : ∀ k ∈ v.position.board.left.rootLabel,
        k ≤ v.position.board.left.bodyLabels.length + 1)
      (hlabels : q.position.board.left.bodyLabels = v.position.board.left.bodyLabels ++ [L.upper]) :
      ∀ k ∈ q.position.board.left.rootLabel, k ≤ q.position.board.left.bodyLabels.length := by
    obtain ⟨as, has, _⟩ := follow_step_word_inputs hstep false
    obtain ⟨r, hp⟩ := LabeledWord.marker_blocks hmarker
    have hrootEq := has.rootLabel_eq (by simp [Board.get, hp])
    intro k hk
    rw [hlabels, List.length_append, List.length_singleton]
    exact hroot k (hrootEq ▸ hk)
  have singleton_exhausted (w : LabeledWord)
      (hroot : ∀ k ∈ w.rootLabel, k ≤ w.bodyLabels.length)
      (hlabel : w.currentLabel = L.upper) (hidx : w.leafIndex = L.pivot) :
      ¬ Macro.Pending w := by
    rintro (⟨k, hk, hlt⟩ | ⟨_, j, hj, hlt⟩)
    · exact (not_lt_of_ge (hroot k hk)) hlt
    · have heq : j = L.pivot := Finset.card_le_one.mp L.upper_card.le j
        (hlabel ▸ hj) L.pivot L.pivot_upper
      rw [heq, hidx] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  have hSlastST : ¬ Macro.Pending lastST.position.board.left :=
    singleton_exhausted _ (root_exhausted hsST (by simpa [hboard] using hstM) hrootST hbST)
      (by simp [LabeledWord.currentLabel, show lastST.position.board.left.bodyLabels =
        stBody.position.board.left.bodyLabels ++ [L.upper] from hbST]) hiST
  have hSlastSU : ¬ Macro.Pending lastSU.position.board.left :=
    singleton_exhausted _ (root_exhausted hsSU hsuM hrootSU hbSU)
      (by simp [LabeledWord.currentLabel, show lastSU.position.board.left.bodyLabels =
        su.position.board.left.bodyLabels ++ [L.upper] from hbSU]) hiSU
  have hMlast : ∃ M : Managed N J blue b σ true true upperOrigin.position.board.left
        lastSU.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target := by
    change ∃ M : Managed N J blue b σ true true upperOrigin.position.board.left
      (lastSU.position.board.get (!false)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target
    rw [hoSU]
    exact hM
  obtain ⟨M, hMfrom⟩ := hMlast
  have hmodeLastSU := follow_mode_some hSUpath hmodeFine
  have hUlast := winning_no_pending_smaller hJN hJ blue hwinLastSU hmodeLastSU
    (M.not_start ((Position.history_dataInvariant lastSU).2.1 true).1)
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant lastSU).2.1 false).1 hrSU)
    hSlastSU
  obtain ⟨lastTU, _htuPath, hwinLastTU, _hnTU, hcU, _hrU, hTUother, _hTUmode, _hTUfresh⟩ :=
    M.fire_from hJN ((Position.history_dataInvariant lastSU).2.1 true).2 hUlast upperOrigin hMfrom
  have hTword : lastST.position.board.right = old.position.board.right := by
    have ho : lastST.position.board.right = stBody.position.board.right := hoST
    exact ho.trans (by simpa only [hboard] using hstOther)
  have hTshape : LabeledWord.SameStructure lastST.position.board.right
      lastTU.position.board.left := by
    have hTUleft : lastTU.position.board.left = upperOrigin.position.board.left := hTUother
    rw [hTword, hTUleft]
    exact hT
  have hUshape : LabeledWord.SameStructure lastSU.position.board.right
      lastTU.position.board.right := by
    obtain ⟨as, has⟩ := History.word_run lastSU true
    obtain ⟨bs, hbs⟩ := History.word_run lastTU true
    exact LabeledWord.sameStructure_of_initial_runs has.run hbs.run hcU.symm
  have hrelLastST : ∀ side, (lastST.position.board.get side).relaxed = true := by
    intro side
    cases side
    · exact hrST
    · simpa [Board.get, hTword] using hTrel
  have hrelLastSU : ∀ side, (lastSU.position.board.get side).relaxed = true := by
    intro side
    cases side
    · exact hrSU
    · exact M.relaxed_of_last ((Position.history_dataInvariant lastSU).2.1 true).1 hUlast
  have hlastST : BothLast lastST.position.board := by
    intro side
    cases side
    · exact hSlastST
    · simpa [Board.get, hTword] using hTlast
  have hlastSU : BothLast lastSU.position.board := by
    intro side
    cases side
    · exact hSlastSU
    · exact hUlast
  exact inside_triangle_of_last_first_forks hJN hJ blue lastST lastSU lastTU
    hwinLastST hwinLastSU hwinLastTU (follow_mode_some hSTpath hmodeOld) hmodeLastSU
    hlastST hlastSU hrelLastST hrelLastSU hS hTshape hUshape

#print axioms inside_singleton_bridge_triangle

end Erdos591.Positive.Game.Payoff

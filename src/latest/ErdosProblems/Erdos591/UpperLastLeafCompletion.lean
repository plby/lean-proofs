import ErdosProblems.Erdos591.NextLeafReplayHistory
import ErdosProblems.Erdos591.SharedExtensionCompletion

/-!
# Complete U after the last upper T leaf, retaining the T input prefix

The lower U complete response is already pending. Stop the upper play
at its last T selected leaf, append the fresh U continuation to the
retained prefix, and complete U in both histories. The T continuation
is kept as a literal legal run above an independent saved lower bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem upper_last_leaf_and_shared_completion {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (su upper : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ upper)
    (hmode : upper.position.mode = some true)
    {rSU : Request} (hpSU : su.position.pending = some rSU) (hsSU : rSU.side = true)
    (hstartU : su.position.board.right.parser ≠ .start)
    (hlastU : ¬ Macro.Pending su.position.board.right)
    {j : ℕ} (hup : LabeledWord.UpToLeaf j upper.position.board.left)
    (hstrict : upper.position.board.left.leafIndex < j)
    (hroot : ∀ i ∈ upper.position.board.left.rootLabel,
      i ≤ upper.position.board.left.bodyLabels.length)
    (hlast : ∀ i ∈ upper.position.board.left.currentLabel, i ≤ j)
    {anchor : LabeledWord} {frontU : List (Finset ℕ × ℕ)}
    (hU : LabeledWord.SameStructure su.position.board.right anchor)
    (hfrontU : LabeledWord.LegalRun anchor frontU upper.position.board.right)
    (hpoolU : ∀ a ∈ frontU, a.2 ∈ H ∧ max su.position.bound (b su) < a.2)
    (B : ℕ) :
    ∃ doneTU doneSU,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper doneTU ∧
      (exactGame N blue).FollowStep σ H b su doneSU ∧
      doneTU.position.pending = none ∧ doneSU.position.pending = none ∧
      doneTU.position.board.left.relaxed = true ∧
      ¬ Macro.Pending doneTU.position.board.left ∧
      doneTU.position.board.left.leafIndex = j ∧
      doneTU.position.board.left.bodyLabels = upper.position.board.left.bodyLabels ∧
      doneSU.position.board.left = su.position.board.left ∧
      doneTU.position.board.right.terminal = true ∧
      doneSU.position.board.right.terminal = true ∧
      LabeledWord.SameStructure doneSU.position.board.right doneTU.position.board.right ∧
      ∃ as, LabeledWord.LegalRun upper.position.board.left as doneTU.position.board.left ∧
        ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  let C := max B (max su.position.bound (b su))
  let c : Concrete.Hist N → ℕ := fun p => max (b p) C
  have hbc : ∀ p, b p ≤ c p := fun p => le_max_left (b p) C
  have hc : ∀ p, C ≤ c p := fun p => le_max_right (b p) C
  have hwinC := hwin.mono (exactGame N blue) (Set.Subset.refl H) hbc
  obtain ⟨tu, hpathC, _hn, hrel, hidx, hlabels, _hmarker, hsep⟩ :=
    winning_reach_selected_leaf_fresh hHN hH blue hwinC false j hup hstrict
  have hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper tu :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H) hbc hs)
      _ _ hpathC
  obtain ⟨ts, hts, htsPool⟩ := follow_word_inputs hpathC C hc false
  obtain ⟨r, k, hparse⟩ := hup.parser_leaves ((Position.history_dataInvariant upper).2.1 false).1
  have hrootEq := hts.rootLabel_eq (by simp [Board.get, hparse])
  have hcurrent : tu.position.board.left.currentLabel = upper.position.board.left.currentLabel :=
    congrArg (fun ls => ls.getLastD ∅) hlabels
  have hlastT : ¬ Macro.Pending tu.position.board.left := by
    rintro (⟨i, hi, hlt⟩ | ⟨_, i, hi, hlt⟩)
    · have hle := hroot i (hrootEq ▸ hi)
      change tu.position.board.left.bodyLabels = upper.position.board.left.bodyLabels at hlabels
      rw [hlabels] at hlt
      exact (not_lt_of_ge hle hlt).elim
    · have hle := hlast i (hcurrent ▸ hi)
      change tu.position.board.left.leafIndex = j at hidx
      rw [hidx] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hwinTU := hwin.of_reachable (exactGame N blue) hpath
  have hmTU := follow_mode_some hpath hmode
  have hwT := ((Position.history_dataInvariant tu).2.1 false).1
  have hstartT := LabeledWord.relaxed_ne_start hwT hrel
  have hliveU := winning_relaxed_other_unfinished hHN hH blue hwinTU false hrel hsep
  obtain ⟨us, hus, husPool⟩ := follow_word_inputs hpathC C hc true
  have hwholeU := hfrontU.append hus
  have hstartUpperU : tu.position.board.right.parser ≠ .start :=
    hwholeU.parser_ne_start (hU.parser_eq ▸ hstartU)
  have hlastUpperU := winning_no_pending_smaller hHN hH blue hwinTU hmTU
    hstartUpperU hstartT hlastT
  obtain ⟨pendingTU, rTU, htuPath, hbTU, hpTU, hsTU⟩ :=
    request_smaller_at_boundary hHN hH blue hwinTU hmTU hliveU hstartT hlastT
  have hrun : LabeledWord.LegalRun anchor (frontU ++ us)
      (pendingTU.position.board.get rTU.side) := by
    simpa only [hsTU, hbTU, Board.get] using hwholeU
  have hpool : ∀ a ∈ frontU ++ us,
      a.2 ∈ H ∧ su.position.bound < a.2 ∧ b su < a.2 := by
    intro a ha
    have hf : a.2 ∈ H ∧ max su.position.bound (b su) < a.2 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hpoolU a ha
      · exact ⟨(husPool a ha).1, (le_max_right _ _).trans_lt (husPool a ha).2⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  obtain ⟨doneSU, doneTU, hsuStep, htuStep, hsun, htun, hterm, hUshape,
      hsuOther, htuOther⟩ := complete_shared_extension hHN hH blue su pendingTU hpSU hpTU
    (by simpa only [hsSU, Board.get] using hstartU)
    (by simpa only [hsSU, Board.get] using hlastU)
    (by simpa only [hsTU, hbTU, Board.get] using hstartUpperU)
    (by simpa only [hsTU, hbTU, Board.get] using hlastUpperU)
    (by simpa only [hsSU, Board.get] using hU) hrun hpool
  have hSUother : doneSU.position.board.left = su.position.board.left := by
    simpa only [hsSU, Bool.not_true, Board.get] using hsuOther
  have hTUother : doneTU.position.board.left = tu.position.board.left := by
    simpa only [hsTU, hbTU, Bool.not_true, Board.get] using htuOther
  have hUshape' : LabeledWord.SameStructure doneSU.position.board.right
      doneTU.position.board.right := by simpa only [hsSU, hsTU, Board.get] using hUshape
  have htermTU : doneTU.position.board.right.terminal = true := by
    simpa only [hsTU, Board.get] using hterm
  have htermSU : doneSU.position.board.right.terminal = true := by
    change decide (doneSU.position.board.right.parser = .blocks 0) = true
    rw [hUshape'.parser_eq]
    exact htermTU
  exact ⟨doneTU, doneSU, hpath.trans (htuPath.tail htuStep), hsuStep, htun, hsun,
    by simpa only [hTUother, Board.get] using hrel,
    by simpa only [hTUother] using hlastT,
    by simpa only [hTUother, Board.get] using hidx,
    by simpa only [hTUother, Board.get] using hlabels,
    hSUother, htermTU, htermSU, hUshape', ts,
    by simpa only [hTUother, Board.get] using hts,
    fun a ha => ⟨(htsPool a ha).1, (le_max_left _ _).trans_lt (htsPool a ha).2⟩⟩

#print axioms upper_last_leaf_and_shared_completion

end Erdos591.Positive.Game.Payoff

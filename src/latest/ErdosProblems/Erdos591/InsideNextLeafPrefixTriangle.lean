import ErdosProblems.Erdos591.NextLeafReplayHistory
import ErdosProblems.Erdos591.SharedHeadTriangle
import ErdosProblems.Erdos591.SharedExtensionCompletion

/-!
# The strict finishing branch with a second lower T leaf

After the shared S leaf, ST waits for its next T leaf and SU waits
to complete U. Reach the last upper T leaf and replay it as the
next lower T leaf. The retained fresh U prefix can then be completed
in both upper and lower plays. Their exhausted S and T heads are
completed by one winning continuation of ST.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_next_leaf_prefix_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su upper : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinUpper : (exactGame N blue).ArchitectWins H b σ upper)
    (hmode : upper.position.mode = some true)
    (hpST : st.position.pending = some ⟨true, .advance 0⟩)
    {rSU : Request} (hpSU : su.position.pending = some rSU) (hsSU : rSU.side = true)
    (hstartS : su.position.board.left.parser ≠ .start)
    (hliveS : su.position.board.left.terminal = false)
    (hlastS : ¬ Macro.Pending su.position.board.left)
    (hstartU : su.position.board.right.parser ≠ .start)
    (hlastU : ¬ Macro.Pending su.position.board.right)
    (hS : LabeledWord.SameStructure su.position.board.left st.position.board.left)
    (hT : LabeledWord.SameStructure st.position.board.right upper.position.board.left)
    {j : ℕ} (hcoarse : LabeledWord.UpToLeaf j st.position.board.right)
    (hstrict : st.position.board.right.leafIndex < j)
    (hnext : ∀ i ∈ st.position.board.right.currentLabel,
      st.position.board.right.leafIndex < i → j ≤ i)
    (hfine : LabeledWord.UpToLeaf j upper.position.board.left)
    (hroot : ∀ i ∈ upper.position.board.left.rootLabel,
      i ≤ upper.position.board.left.bodyLabels.length)
    (hlast : ∀ i ∈ upper.position.board.left.currentLabel, i ≤ j)
    {anchor : LabeledWord} {frontU : List (Finset ℕ × ℕ)}
    (hU : LabeledWord.SameStructure su.position.board.right anchor)
    (hfrontU : LabeledWord.LegalRun anchor frontU upper.position.board.right)
    (hpoolU : ∀ a ∈ frontU, a.2 ∈ H ∧ max su.position.bound (b su) < a.2) :
    ¬ blue.CliqueFree 3 := by
  let B := max (max st.position.bound (b st)) (max su.position.bound (b su))
  obtain ⟨tu, st', hupper, hst, _htun, _hstn, hTshape, hTrel, _hstrel,
      hidx, hotherST, hruns, hlabels, _hmarker, hsep⟩ :=
    winning_next_leaf_replay_fresh hHN hH blue upper st hwinUpper false true hpST hT
      hcoarse hstrict hnext hfine B (le_max_left _ _)
  have hwinTU := hwinUpper.of_reachable (exactGame N blue) hupper
  have hmTU := follow_mode_some hupper hmode
  obtain ⟨ts, hts, _htsPool⟩ := hruns false
  obtain ⟨r, k, hparse⟩ := hfine.parser_leaves ((Position.history_dataInvariant upper).2.1 false).1
  have hrootEq := hts.rootLabel_eq (by simp only [Board.get, hparse]; simp)
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
  have hwT := ((Position.history_dataInvariant tu).2.1 false).1
  have hstartT := LabeledWord.relaxed_ne_start hwT hTrel
  have hliveT := LabeledWord.relaxed_not_terminal hwT.2.1 hwT.2.2 hTrel
  have hliveU := winning_relaxed_other_unfinished hHN hH blue hwinTU false hTrel hsep
  obtain ⟨us, hus, husPool⟩ := hruns true
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
  obtain ⟨doneSU, doneTU, hsuStep, htuStep, _hsun, _htun, hterm, hUshape,
      hsuOther, htuOther⟩ := complete_shared_extension hHN hH blue su pendingTU hpSU hpTU
    (by simpa only [hsSU, Board.get] using hstartU)
    (by simpa only [hsSU, Board.get] using hlastU)
    (by simpa only [hsTU, hbTU, Board.get] using hstartUpperU)
    (by simpa only [hsTU, hbTU, Board.get] using hlastUpperU)
    (by simpa only [hsSU, Board.get] using hU) hrun hpool
  have hSTother : st'.position.board.left = st.position.board.left := hotherST
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
  exact triangle_after_shared_last hHN hH blue st' doneSU doneTU
    (hwinST.of_reachable (exactGame N blue) (.single hst))
    (hwinSU.of_reachable (exactGame N blue) (.single hsuStep))
    (hwinTU.of_reachable (exactGame N blue) (htuPath.tail htuStep))
    (by simpa only [hSUother] using hstartS)
    (by simpa only [hTUother, Board.get] using hstartT)
    (by simpa only [hSUother] using hlastS)
    (by simpa only [hTUother] using hlastT) htermSU htermTU
    (by simpa only [hSUother] using hliveS)
    (by simpa only [hTUother, Board.get] using hliveT)
    hUshape'.coordinates_eq (by simpa only [hSUother, hSTother] using hS)
    (by simpa only [hTUother, Board.get] using hTshape.symm)

#print axioms inside_next_leaf_prefix_triangle

end Erdos591.Positive.Game.Payoff

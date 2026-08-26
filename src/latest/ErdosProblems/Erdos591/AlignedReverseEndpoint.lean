import ErdosProblems.Erdos591.AlignedCriticalEndpoint
import ErdosProblems.Erdos591.ReplySeparation

/-!
# Recovering the first penultimate endpoint by stopping the second word

Exact suffix balance is reversible in the aligned case. The first
relaxed endpoint can be recovered from its nonempty overtaken prefix.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_left_relaxed_of_right_separation {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hrel : p.position.board.right.relaxed = true)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0) :
    p.position.board.left.relaxed = true ∧
      p.position.board.left.coordinates.getLastD 0 <
        p.position.board.right.coordinates.getLastD 0 := by
  have hlastmem (xs : List ℕ) (hne : 0 < xs.length) : xs.getLastD 0 ∈ xs := by
    have hn : xs ≠ [] := by intro he; simp [he] at hne
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hn,
      Option.getD_some] using List.getLast_mem hn
  obtain ⟨as, ha⟩ := History.word_run p true
  have hrpos := ha.relaxed_coordinates_pos hrel
  have hlmem := hlastmem _ hpos
  have hrmem := hlastmem _ hrpos
  have hle := hsep _ hlmem
  have hne : p.position.board.left.coordinates.getLastD 0 ≠
      p.position.board.right.coordinates.getLastD 0 := by
    intro heq
    apply Finset.disjoint_left.mp (Position.history_dataInvariant p).2.2
      (LabeledWord.coordinate_mem_support hlmem)
    rw [heq]
    exact LabeledWord.coordinate_mem_support hrmem
  have hlt := lt_of_le_of_ne hle hne
  have hlive := winning_relaxed_other_unfinished hHN hH blue hwin true hrel hsep
  exact ⟨winning_overtaken_relaxed hHN hH blue hwin false hlive hpos hrmem hlt, hlt⟩

theorem winning_aligned_reverse_endpoint {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hr : p.position.board.right.relaxed = true)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0)
    (hbefore : p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody)
    (hpen : ∀ k ∈ p.position.board.right.rootLabel,
      k < p.position.board.right.lastSelectedBody → k ≤ p.position.board.right.bodyLabels.length)
    (hn : p.position.board.right.NoLeafPending) :
    p.position.board.left.relaxed = true ∧
      p.position.board.left.coordinates.getLastD 0 < p.position.board.right.coordinates.getLastD 0 ∧
      p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody ∧
      (∀ k ∈ p.position.board.left.rootLabel,
        k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length) ∧
      p.position.board.left.NoLeafPending := by
  have hwinP := hwin.of_reachable (exactGame N blue) hfrom
  obtain ⟨hl, horder⟩ := winning_left_relaxed_of_right_separation hHN hH blue hwinP hr hpos hsep
  obtain ⟨q, hpq, hq⟩ := hwinP.exists_terminal (exactGame N blue) hHN hH
  have hpath := hfrom.trans hpq
  obtain ⟨s, t, hc, hmax, hfirst, _hcard⟩ :=
    terminal_inside_clear_data blue origin q ha hop hboard hmode hwin hpath hq
  exact ⟨hl, horder, (history_aligned_penultimate_endpoint_iff (follow_history_path hpq)
    hc hmax hfirst (of_decide_eq_true (hall q true hpath hq)) hl hr horder).mpr
      ⟨hbefore, hpen, hn⟩⟩

#print axioms winning_left_relaxed_of_right_separation
#print axioms winning_aligned_reverse_endpoint

end Erdos591.Positive.Game.Payoff

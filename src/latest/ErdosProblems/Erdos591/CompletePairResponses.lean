import ErdosProblems.Erdos591.CompleteResponse
import ErdosProblems.Erdos591.SharedTailHistory

/-!
# A winning complete pair as two high complete-word responses

Erase the labels of a complete history word without changing its
coordinates or parser endpoint. A winning initial play on a high tail
therefore supplies two complete responses on that tail and the exact
winning board whose two coordinate words they represent.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

namespace CompleteResponse

theorem of_history_word {N : Set ℕ} (p : Concrete.Hist N) (side : Bool)
    (ht : (p.position.board.get side).terminal = true) :
    ∃ s : CompleteResponse, s.cursor.coordinates = (p.position.board.get side).coordinates ∧
      s.input = (p.position.board.get side).coordinates.toFinset := by
  obtain ⟨as, has⟩ := History.word_run p side
  obtain ⟨z, hz, hshape⟩ := (LabeledWord.SameStructure.refl LabeledWord.initial).finish_from_run
    has.run ht
  have hvalues : as.map Prod.snd = (p.position.board.get side).coordinates := by
    simpa [LabeledWord.initial] using (LabeledWord.runAtoms_coordinates has.run).symm
  have hsort := Erdos590.Larson.sort_toFinset_eq_self_of_pairwise
    ((Position.history_dataInvariant p).2.1 side).2
  exact ⟨⟨(p.position.board.get side).coordinates.toFinset, z,
    by simpa only [hsort, hvalues] using hz⟩, hshape.coordinates_eq, rfl⟩

end CompleteResponse

namespace Payoff

theorem winning_complete_pair_responses_above {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hwin : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial)) (B : ℕ) :
    ∃ q : Concrete.Hist N, Winning blue (q.position.mode.getD false) q.position.board ∧
      ∃ s t : CompleteResponse,
        s.cursor.coordinates = q.position.board.left.coordinates ∧
        t.cursor.coordinates = q.position.board.right.coordinates ∧
        (↑s.input : Set ℕ) ⊆ H ∧ (↑t.input : Set ℕ) ⊆ H ∧
        (∀ x ∈ s.input, B < x) ∧ ∀ x ∈ t.input, B < x := by
  let K := H \ Set.Iic B
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic B)
  have hKH : K ⊆ H := fun _ hx => hx.1
  have hwinK := hwin.mono (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨q, hpath, _hn, hdone, hw⟩ := winning_continuation (hKH.trans hHN) hK blue hwinK
  have hcoords (side : Bool) : ∀ x ∈ (q.position.board.get side).coordinates, x ∈ H ∧ B < x := by
    obtain ⟨as, has, hpool⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) side
    have hroot : (History.initial (Position.Next N) Position.initial).position.board.get side =
        LabeledWord.initial := by cases side <;> rfl
    have heq : (q.position.board.get side).coordinates = as.map Prod.snd := by
      simpa only [hroot, LabeledWord.initial, List.nil_append]
        using LabeledWord.runAtoms_coordinates has.run
    intro x hx
    rw [heq] at hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact ⟨(hpool a ha).1.1, lt_of_not_ge (hpool a ha).1.2⟩
  obtain ⟨s, hs, hsi⟩ := CompleteResponse.of_history_word q false
    (q.position.board.terminal_of_done hdone false)
  obtain ⟨t, ht, hti⟩ := CompleteResponse.of_history_word q true
    (q.position.board.terminal_of_done hdone true)
  refine ⟨q, hw, s, t, hs, ht, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hcoords false x (List.mem_toFinset.mp (hsi ▸ hx))).1
  · intro x hx
    exact (hcoords true x (List.mem_toFinset.mp (hti ▸ hx))).1
  · intro x hx
    exact (hcoords false x (List.mem_toFinset.mp (hsi ▸ hx))).2
  · intro x hx
    exact (hcoords true x (List.mem_toFinset.mp (hti ▸ hx))).2

#print axioms winning_complete_pair_responses_above

end Payoff

end Erdos591.Positive.Game

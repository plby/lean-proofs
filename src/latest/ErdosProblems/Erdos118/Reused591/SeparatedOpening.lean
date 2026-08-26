import ErdosProblems.Erdos118.Reused591.ForcedMoves
import ErdosProblems.Erdos118.Reused591.ZeroResponse

namespace Erdos118.Reused591

/-!
# Starting a word after the other word has completed

Freshness separates every coordinate of the new word from the completed
one. Clarity therefore forces its root label to be empty. This is the
second-request constraint in the zero-opening triangle construction.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem not_cut_of_separated {xs ys : List ℕ}
    (hsep : ∀ x ∈ xs, ∀ y ∈ ys, y < x) (k : ℕ) : ¬ Cut xs ys k := by
  rintro ⟨hk, y, hy, hlo, _⟩
  have hx : xs.getD k 0 ∈ xs := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem (by omega)
  exact not_lt_of_ge (hsep _ hx y hy).le hlo

theorem ClearSide.root_empty_of_separated {w : LabeledWord} {s t : G}
    (hc : ClearSide w s t) (hsep : ∀ x ∈ word s.val, ∀ y ∈ word t.val, y < x) :
    w.rootLabel = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hpos := (hc.root_bounds i hi).1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  obtain ⟨k, hk⟩ := (hc.root_exact j).mp hi
  exact not_cut_of_separated hsep _ hk.2.2

theorem winning_new_word_root_empty {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p q : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ q)
    (hpq : Relation.ReflTransGen (fun p q => History.Next q p) p q) (side : Bool)
    (hinit : p.position.board.get side = LabeledWord.initial)
    (hterm : (p.position.board.get (!side)).terminal = true)
    (hstart : (q.position.board.get side).parser ≠ .start) :
    (q.position.board.get side).rootLabel = ∅ := by
  obtain ⟨r, hqr, _, _, hr⟩ := winning_continuation hHN hH blue hwin
  obtain ⟨s, t, hc, hother⟩ := hr.side_clear side
  have hpr := hpq.trans (follow_history_path hqr)
  obtain ⟨as, has, haf⟩ := (History.reachable_word_extension hpr).2 side
  obtain ⟨bs, hbs, _⟩ := (History.reachable_word_extension hpr).2 (!side)
  have hsame := hbs.terminal_eq hterm
  have hroot : (r.position.board.get side).rootLabel = ∅ := by
    apply hc.root_empty_of_separated
    intro x hx y hy
    rw [hc.coordinates, LabeledWord.runAtoms_coordinates has.run, hinit] at hx
    have hx' : x ∈ as.map Prod.snd := by simpa [LabeledWord.initial] using hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx'
    rw [hother, hsame] at hy
    have hyb := ((Position.history_dataInvariant p).1 y
      (p.position.board.get_support_subset (!side) (LabeledWord.coordinate_mem_support hy))).2.2
    exact hyb.trans_lt (haf a ha)
  obtain ⟨cs, hcs, _⟩ :=
    (History.reachable_word_extension (follow_history_path hqr)).2 side
  exact (hcs.rootLabel_eq hstart).symm.trans hroot

theorem winning_pending_after_complete_size_zero {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {r : Request} (hp : p.position.pending = some r)
    (hinit : p.position.board.get r.side = LabeledWord.initial)
    (hterm : (p.position.board.get (!r.side)).terminal = true) : r.size = 0 := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hf := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hf)
  have hreply := (Concrete.response_spec hu).reply_spec hp
  obtain ⟨D, n, v, as, hcard, hread, htail⟩ := hreply.first_read
  have hstart := htail.parser_ne_start (LabeledWord.read_parser_ne_start hread)
  have hroot := winning_new_word_root_empty hHN hH blue hqwin
    (follow_history_path (Relation.ReflTransGen.single hf)) r.side hinit hterm hstart
  have hD : D = ∅ :=
    (LabeledWord.rootLabel_after_read hread htail (by simp [hinit, LabeledWord.initial])).symm.trans
      hroot
  rw [← hcard, hD]
  rfl

#print axioms winning_new_word_root_empty
#print axioms winning_pending_after_complete_size_zero

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591

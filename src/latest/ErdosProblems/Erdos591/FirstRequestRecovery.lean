import ErdosProblems.Erdos591.FirstBodyThinning

/-!
# Recovering a first-body request as two actual opening steps

Once a selected body marker is read, its root index remains passed in
every legal continuation. A reachable pending first-body marker with
no passed root index must therefore still be the first body request.
-/

namespace Erdos591.Positive.Game

theorem Reply.marker_passed_of_continuation {board next : Board} {r : Request} {u : Finset ℕ}
    (hr : Reply board r u next) (hm : (board.get r.side).markerEvent = true)
    {last : LabeledWord} {tail : List (Finset ℕ × ℕ)}
    (htail : LabeledWord.LegalRun (next.get r.side) tail last) : ¬ last.NoRootPassed := by
  obtain ⟨D, n, first, as, _hcard, hread, hrun⟩ := hr.first_read
  obtain ⟨k, hparse⟩ := LabeledWord.marker_blocks hm
  have hstart : (board.get r.side).parser ≠ .start := by simp [hparse]
  have hroot : last.rootLabel = (board.get r.side).rootLabel :=
    ((hrun.append htail).rootLabel_eq (LabeledWord.read_parser_ne_start hread)).trans
      (LabeledWord.read_rootLabel_eq hread hstart)
  have hfirst : (board.get r.side).record D n (Parser.normalize k n) = first := by
    simpa [LabeledWord.read, hparse, Parser.step] using hread
  have hlen := ((hrun.append htail).bodyLabels_prefix
    (LabeledWord.read_parser_ne_start hread)).length_le
  have hcount : (board.get r.side).bodyLabels.length + 1 ≤ last.bodyLabels.length := by
    simpa [← hfirst, LabeledWord.record, hparse] using hlen
  intro hno
  have hmem : (board.get r.side).bodyLabels.length + 1 ∈ last.rootLabel := by
    rw [hroot]
    exact LabeledWord.marker_body_mem hm
  exact (not_lt_of_ge hcount) (hno _ hmem)

theorem Position.Next.pending_exists_of_no_pending {N : Set ℕ} {p q : Position}
    (h : Position.Next N q p) (hp : p.pending = none) : ∃ r, q.pending = some r := by
  cases h with
  | request p flag r _ _ _ _ => exact ⟨r, rfl⟩
  | reply p r u board hpend _ _ _ => simp [hp] at hpend

namespace Payoff

open Erdos591.Negative.Exact

theorem first_body_request_two_steps {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    {a d : ℕ} (ha : 0 < a) (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hinit : origin.position.board.left = LabeledWord.initial)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨false, .advance d⟩)
    (hm : p.position.board.left.markerEvent = true) (hno : p.position.board.left.NoRootPassed) :
    ∃ q, (exactGame N blue).FollowStep σ H b origin q ∧
      (exactGame N blue).FollowStep σ H b q p := by
  rcases hpath.cases_head with heq | ⟨q, hoq, hqp⟩
  · simp [← heq, hinit, LabeledWord.initial, LabeledWord.markerEvent] at hm
  have hk : (exactGame N blue).kind origin = .builder :=
    (Concrete.kind_builder_iff (payoff blue) origin).mpr ⟨_, hop⟩
  obtain ⟨u, hu, huH, hub, hq⟩ : ∃ u, u ∈ (exactGame N blue).family origin ∧
      (↑u : Set ℕ) ⊆ H ∧ (∀ x ∈ u, b origin < x) ∧ q = Concrete.response origin u := by
    cases hoq.1 with
    | architect _ hh _ => simp [hk] at hh
    | builder u _ hu huH hub => exact ⟨u, hu, huH, hub, rfl⟩
  have hreply := (Concrete.response_spec hu).reply_spec hop
  have hqmarker : q.position.board.left.markerEvent = true := by
    rw [hq]
    exact hreply.initial_positive_marker hinit ha
      (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
  have hqnone := (History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hoq)).no_pending_after_reply hop
  rcases hqp.cases_head with heq | ⟨v, hqv, hvp⟩
  · subst p
    simp [hqnone] at hp
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hqv)
  have hboard := hnext.board_eq_of_no_pending hqnone
  have hvpending := hnext.pending_exists_of_no_pending hqnone
  obtain ⟨r, hvr⟩ := hvpending
  have hvm : v.position.board.left.markerEvent = true := by simpa [hboard] using hqmarker
  have hwinv := hwin.of_reachable (exactGame N blue) ((Relation.ReflTransGen.single hoq).tail hqv)
  obtain ⟨e, _he, hreq⟩ := winning_pending_marker hHN hH blue hwinv hvr false hvm
  have hvpe : v.position.pending = some ⟨false, .advance e⟩ := by simpa [hreq] using hvr
  rcases hvp.cases_head with heq | ⟨z, hvz, hzp⟩
  · subst p
    exact ⟨q, hoq, hqv⟩
  obtain ⟨input, hr⟩ := (History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hvz)).reply_of_pending hvpe
  obtain ⟨tail, ht, _⟩ := follow_word_inputs hzp 0 (fun _ => Nat.zero_le _) false
  exact (hr.marker_passed_of_continuation hvm ht hno).elim

theorem first_body_request_large_of_reachable {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    {a d : ℕ} (ha : 0 < a) (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hinit : origin.position.board.left = LabeledWord.initial)
    (hfirst : ∀ q v e, (exactGame N blue).FollowStep σ H b origin q →
      (exactGame N blue).FollowStep σ H b q v →
      v.position.pending = some ⟨false, .advance e⟩ → 2 ≤ e)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨false, .advance d⟩)
    (hm : p.position.board.left.markerEvent = true) (hno : p.position.board.left.NoRootPassed) :
    2 ≤ d := by
  obtain ⟨q, hoq, hqp⟩ := first_body_request_two_steps hHN hH blue origin p hwin
    ha hop hinit hpath hp hm hno
  exact hfirst q p d hoq hqp hp

#print axioms first_body_request_two_steps
#print axioms first_body_request_large_of_reachable

end Payoff

#print axioms Reply.marker_passed_of_continuation

end Erdos591.Positive.Game

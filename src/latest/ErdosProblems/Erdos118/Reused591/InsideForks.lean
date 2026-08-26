import ErdosProblems.Erdos118.Reused591.InitialManaged
import ErdosProblems.Erdos118.Reused591.PositiveSecondRequest

namespace Erdos118.Reused591

/-!
# The two delayed right-word plays for the inside construction

Run TU as the lower play. Its first word is retained for the right
word of ST, and its second for the right word of SU. Both target left
words remain fixed. The checkpoint fires at the last lower selections
and retains the post-response separation needed to resume each target.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem inside_install {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial)
    (upper : Bool → Concrete.Hist N) (sizes : Bool → ℕ)
    (hwins : ∀ s, (exactGame N blue).ArchitectWins H b σ (upper s))
    (hpos : ∀ s, 0 < sizes s)
    (hpend : ∀ s, (upper s).position.pending = some ⟨true, .advance (sizes s)⟩)
    (hinit : ∀ s, (upper s).position.board.right = LabeledWord.initial)
    (hmodes : ∀ s, (upper s).position.mode = some true) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      ∀ s, Nonempty (Managed N H blue b σ true true (upper s).position.board.left
        (q.position.board.get s)) := by
  let B := max (max p.position.bound (b p))
    (max (upper false).position.bound (b (upper false)))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B a (sizes false) ha (hpos false)
  have hi : p.position.board.get false = LabeledWord.initial := by
    simp [hboard, Board.initial, Board.get]
  obtain ⟨q₀, hs₀, hn₀, hm₀, ho₀, R₀, ht₀, hside₀, _⟩ :=
    prepare_root hHN hH blue (hwins false) false true L hp (hpend false) hi (hinit false)
      (le_max_left _ _) (le_max_right _ _)
  have MR₀ : Managed N H blue b σ true true (upper false).position.board.left
      (q₀.position.board.get false) :=
    .root R₀ hside₀ (by simp [ht₀, hside₀, Board.get]) (by simpa [ht₀] using hmodes false)
  have hwin₀ := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs₀)
  obtain ⟨q₁, hpath₁, hn₁, hr₁, ho₁, ⟨M₁⟩⟩ :=
    MR₀.first_body hHN hH blue hwin₀ false hn₀ hm₀
  have hpath₀₁ := hpath₁.head hs₀
  have hwin₁ := hwin.of_reachable (exactGame N blue) hpath₀₁
  have hi₁ : q₁.position.board.right = LabeledWord.initial := by
    simpa [hboard, Board.initial, Board.get] using ho₁.trans ho₀
  obtain ⟨q₂, d, hs₂, hb₂, hp₂, hd⟩ := winning_initial_right_request hHN hH blue htri hroot
    hwin₁ hn₁ hi₁ hr₁
  let C := max (max q₂.position.bound (b q₂))
    (max (upper true).position.bound (b (upper true)))
  obtain ⟨K⟩ := LastFirstLabels.exists_of_infinite hH C d (sizes true) hd (hpos true)
  have hi₂ : q₂.position.board.get true = LabeledWord.initial := by
    simpa [hb₂, Board.get] using hi₁
  obtain ⟨q₃, hs₃, _hn₃, _hm₃, ho₃, R₃, ht₃, hside₃, _⟩ :=
    prepare_root hHN hH blue (hwins true) true true K hp₂ (hpend true) hi₂ (hinit true)
      (le_max_left _ _) (le_max_right _ _)
  have MR₃ : Managed N H blue b σ true true (upper true).position.board.left
      (q₃.position.board.get true) :=
    .root R₃ hside₃ (by simp [ht₃, hside₃, Board.get]) (by simpa [ht₃] using hmodes true)
  refine ⟨q₃, (hpath₀₁.tail hs₂).tail hs₃, fun s => ?_⟩
  cases s with
  | false =>
      have heq : q₃.position.board.get false = q₁.position.board.get false := by
        simpa [hb₂] using ho₃
      rw [heq]
      exact ⟨M₁⟩
  | true => exact ⟨MR₃⟩

theorem inside_forks {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true)
    (upper : Bool → Concrete.Hist N) (sizes : Bool → ℕ)
    (hwins : ∀ s, (exactGame N blue).ArchitectWins H b σ (upper s))
    (hpos : ∀ s, 0 < sizes s)
    (hpend : ∀ s, (upper s).position.pending = some ⟨true, .advance (sizes s)⟩)
    (hinit : ∀ s, (upper s).position.board.right = LabeledWord.initial)
    (hmodes : ∀ s, (upper s).position.mode = some true) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ q.position.mode = some true ∧
      BothLast q.position.board ∧ ∀ s, (q.position.board.get s).relaxed = true ∧
        ∃ v : Concrete.Hist N, (exactGame N blue).ArchitectWins H b σ v ∧
          v.position.pending = none ∧ v.position.mode = some true ∧
          (v.position.board.right).coordinates = (q.position.board.get s).coordinates ∧
          v.position.board.right.relaxed = true ∧
          v.position.board.left = (upper s).position.board.left ∧
          ∀ y ∈ v.position.board.left.coordinates,
            y ≤ v.position.board.right.coordinates.getLastD 0 := by
  obtain ⟨q₀, hpath₀, hM₀⟩ := inside_install hHN hH blue htri hroot hwin ha hp hboard
    upper sizes hwins hpos hpend hinit hmodes
  obtain ⟨q, hpath, hwinq, hlast, hM⟩ := managed_checkpoint hHN hH blue
    (fun _ => true) (fun _ => true) (fun s => (upper s).position.board.left) q₀
    (hwin.of_reachable (exactGame N blue) hpath₀) hM₀
  have hfull := hpath₀.trans hpath
  refine ⟨q, hfull, hwinq, follow_mode_some hfull hmode, hlast, fun s => ?_⟩
  obtain ⟨M⟩ := hM s
  have hw := (Position.history_dataInvariant q).2.1 s
  obtain ⟨v, hv, hn, hc, hr, ho, hm, hsep⟩ := M.fire_fresh hHN hw.2 (hlast s)
  exact ⟨M.relaxed_of_last hw.1 (hlast s), v, hv, hn, hm, hc, hr, ho, hsep⟩

#print axioms inside_install
#print axioms inside_forks

end Erdos591.Positive.Game.Relay

end Erdos118.Reused591

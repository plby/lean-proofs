import ErdosProblems.Erdos591.InitialManaged

/-!
# Installing both delayed plays from an actual positive outside opening

The first root request supplies both upper root reserves. The lower
first word is advanced only to its first selected leaf before the
second root request is obtained. Both managed records are then present,
so the coupled checkpoint supplies the two shared-prefix winning plays.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem outside_install {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {a : ℕ} (ha : 0 < a)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some false) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      ∀ s, Nonempty (Managed N H blue b σ false false LabeledWord.initial
        (q.position.board.get s)) := by
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B a a ha ha
  have hi : p.position.board.get false = LabeledWord.initial := by
    simp [hboard, Board.initial, Board.get]
  obtain ⟨q₀, hs₀, hn₀, hm₀, ho₀, R₀, ht₀, hside₀, _⟩ :=
    prepare_root hHN hH blue hwin false false L hp hp hi hi le_rfl le_rfl
  have MR₀ : Managed N H blue b σ false false LabeledWord.initial
      (q₀.position.board.get false) :=
    .root R₀ hside₀ (by simp [ht₀, hside₀, hboard, Board.initial, Board.get])
      (by simpa [ht₀] using hmode)
  have hwin₀ := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs₀)
  obtain ⟨q₁, hpath₁, hn₁, hr₁, ho₁, ⟨M₁⟩⟩ :=
    MR₀.first_body hHN hH blue hwin₀ false hn₀ hm₀
  have hpath₀₁ := hpath₁.head hs₀
  have hwin₁ := hwin.of_reachable (exactGame N blue) hpath₀₁
  have hi₁ : q₁.position.board.get true = LabeledWord.initial := by
    simpa [hboard, Board.initial, Board.get] using ho₁.trans ho₀
  obtain ⟨q₂, d, hs₂, hb₂, hp₂, hd⟩ := outside_initial_right_request hHN hH blue hwin₁
    (follow_mode_some hpath₀₁ hmode) hn₁ hi₁ hr₁
    (M₁.unfinished ((Position.history_dataInvariant q₁).2.1 false).1)
  let C := max (max q₂.position.bound (b q₂)) (max p.position.bound (b p))
  obtain ⟨K⟩ := LastFirstLabels.exists_of_infinite hH C d a hd ha
  have hi₂ : q₂.position.board.get true = LabeledWord.initial := by simpa [hb₂] using hi₁
  obtain ⟨q₃, hs₃, _hn₃, _hm₃, ho₃, R₃, ht₃, hside₃, _⟩ :=
    prepare_root hHN hH blue hwin true false K hp₂ hp hi₂ hi
      (le_max_left _ _) (le_max_right _ _)
  have MR₃ : Managed N H blue b σ false false LabeledWord.initial
      (q₃.position.board.get true) :=
    .root R₃ hside₃ (by simp [ht₃, hside₃, hboard, Board.initial, Board.get])
      (by simpa [ht₃] using hmode)
  refine ⟨q₃, (hpath₀₁.tail hs₂).tail hs₃, fun s => ?_⟩
  cases s with
  | false =>
      have heq : q₃.position.board.get false = q₁.position.board.get false := by
        simpa [hb₂] using ho₃
      rw [heq]
      exact ⟨M₁⟩
  | true => exact ⟨MR₃⟩

theorem outside_forks {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {a : ℕ} (ha : 0 < a)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some false) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ q.position.mode = some false ∧
      BothLast q.position.board ∧ ∀ s, (q.position.board.get s).relaxed = true ∧
        ∃ v : Concrete.Hist N, (exactGame N blue).ArchitectWins H b σ v ∧
          v.position.pending = none ∧ v.position.mode = some false ∧
          (v.position.board.get false).coordinates = (q.position.board.get s).coordinates ∧
          (v.position.board.get false).relaxed = true ∧
          v.position.board.get true = LabeledWord.initial := by
  obtain ⟨q₀, hpath₀, hM₀⟩ := outside_install hHN hH blue hwin ha hp hboard hmode
  obtain ⟨q, hpath, hwinq, hlast, hM⟩ := managed_checkpoint hHN hH blue
    (fun _ => false) (fun _ => false) (fun _ => LabeledWord.initial) q₀
    (hwin.of_reachable (exactGame N blue) hpath₀) hM₀
  have hfull := hpath₀.trans hpath
  refine ⟨q, hfull, hwinq, follow_mode_some hfull hmode, hlast, fun s => ?_⟩
  obtain ⟨M⟩ := hM s
  have hw := (Position.history_dataInvariant q).2.1 s
  obtain ⟨v, hv, hn, hcoords, hr, ho, hm⟩ := M.fire hHN hw.2 (hlast s)
  exact ⟨M.relaxed_of_last hw.1 (hlast s), v, hv, hn, hm, hcoords, hr, ho⟩

#print axioms outside_install
#print axioms outside_forks

end Erdos591.Positive.Game.Relay

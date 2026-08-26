import ErdosProblems.Erdos118.Reused591.AdvanceResponse

namespace Erdos118.Reused591

/-!
# Two-word requests and replies

This is the structural core of the exact game. A request chooses an
unfinished word and either finishes it or advances with a legal label
size. Replies are the actual finite-input parses. Every reply strictly
decreases the pair of word potentials. Global input freshness, the
opening flag, and the terminal coloring belong to the history layer.
-/

namespace Erdos591.Positive.Game

structure Board where
  left : LabeledWord
  right : LabeledWord
  deriving DecidableEq, Countable

namespace Board

def initial : Board := ⟨LabeledWord.initial, LabeledWord.initial⟩

def get (b : Board) : Bool → LabeledWord
  | false => b.left
  | true => b.right

def update (b : Board) : Bool → LabeledWord → Board
  | false, w => { b with left := w }
  | true, w => { b with right := w }

def potential (b : Board) : WithTop (ℕ ×ₗ ℕ) ×ₗ WithTop (ℕ ×ₗ ℕ) :=
  toLex (Parser.potential b.left.parser, Parser.potential b.right.parser)

theorem update_decreases (b : Board) (side : Bool) (w : LabeledWord)
    (h : Parser.potential w.parser < Parser.potential (b.get side).parser) :
    (b.update side w).potential < b.potential := by
  cases side with
  | false => exact Prod.Lex.left _ _ h
  | true => exact Prod.Lex.right _ h

end Board

inductive Command where
  | finish
  | advance (size : ℕ)
  deriving DecidableEq, Countable

structure Request where
  side : Bool
  command : Command
  deriving DecidableEq, Countable

def Request.Legal (r : Request) (b : Board) : Prop :=
  match r.command with
  | .finish => (b.get r.side).terminal = false
  | .advance d => (b.get r.side).AllowedSize d

def Request.size (r : Request) : ℕ :=
  match r.command with
  | .finish => 0
  | .advance d => d

/-- Actual parser replies. The input includes label values as well as
word coordinates; it is always read in its strictly increasing order. -/
inductive Reply (b : Board) : Request → Finset ℕ → Board → Prop
  | finish (side : Bool) (u : Finset ℕ) (w : LabeledWord)
      (hlegal : (b.get side).terminal = false)
      (hrun : LabeledWord.finishParser.run (b.get side) (u.sort (· ≤ ·)) = some w) :
      Reply b ⟨side, .finish⟩ u (b.update side w)
  | advance (side : Bool) (d : ℕ) (u : Finset ℕ) (w : LabeledWord)
      (hlegal : (b.get side).AllowedSize d)
      (hrun : Advance.parser.run (.prelude ⟨b.get side, hlegal.1⟩ d [])
        (u.sort (· ≤ ·)) = some (.remainder w)) :
      Reply b ⟨side, .advance d⟩ u (b.update side w)

namespace Reply

theorem legal {b b' : Board} {r : Request} {u : Finset ℕ} (h : Reply b r u b') :
    r.Legal b := by
  cases h with
  | finish _ _ _ hlegal _ => exact hlegal
  | advance _ _ _ _ hlegal _ => exact hlegal

theorem decreases {b b' : Board} {r : Request} {u : Finset ℕ} (h : Reply b r u b') :
    b'.potential < b.potential := by
  cases h with
  | finish side u w hlegal hrun =>
      exact b.update_decreases side w (LabeledWord.finish_decreases hlegal hrun)
  | advance side d u w hlegal hrun =>
      obtain ⟨labels, n, rest, last, _, _, hlast, _, hlt, _⟩ :=
        Advance.run_result ⟨b.get side, hlegal.1⟩ d (u.sort (· ≤ ·)) (.remainder w) hrun
      have heq : w = last := Advance.State.remainder.inj hlast
      subst last
      exact b.update_decreases side w hlt

theorem nonempty {b b' : Board} {r : Request} {u : Finset ℕ} (h : Reply b r u b') :
    u.Nonempty := by
  cases h with
  | finish side u w hlegal hrun =>
      exact LabeledWord.finishParser.family_nonempty hlegal ⟨w, hrun⟩
  | advance side d u w hlegal hrun =>
      exact Advance.responses_nonempty (w := ⟨b.get side, hlegal.1⟩)
        (d := d) ⟨.remainder w, hrun⟩

theorem size_le_card {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') : r.size ≤ u.card := by
  cases h with
  | finish _ _ _ _ _ => exact Nat.zero_le _
  | advance side d u w hlegal hrun =>
      obtain ⟨labels, n, rest, first, last, hxs, hlen, _⟩ :=
        Advance.run_prelude ⟨b.get side, hlegal.1⟩ d []
          (u.sort (· ≤ ·)) (.remainder w) hrun
      have htotal := congrArg List.length hxs
      simp only [Finset.length_sort, List.length_append, List.length_cons, hlen] at htotal
      change d ≤ u.card
      omega

theorem deterministic {b b₁ b₂ : Board} {r : Request} {u : Finset ℕ}
    (h₁ : Reply b r u b₁) (h₂ : Reply b r u b₂) : b₁ = b₂ := by
  cases h₁ with
  | finish side u w₁ hlegal hrun₁ =>
      cases h₂ with
      | finish _ _ w₂ _ hrun₂ =>
          have heq : w₁ = w₂ := Option.some.inj (hrun₁.symm.trans hrun₂)
          exact congrArg (b.update side) heq
  | advance side d u w₁ hlegal hrun₁ =>
      cases h₂ with
      | advance _ _ _ w₂ _ hrun₂ =>
          have heq : w₁ = w₂ := Advance.State.remainder.inj
            (Option.some.inj (hrun₁.symm.trans hrun₂))
          exact congrArg (b.update side) heq

end Reply

def responseFamily (b : Board) (r : Request) : Set (Finset ℕ) :=
  {u | ∃ b', Reply b r u b'}

theorem responseFamily_thin (b : Board) (r : Request) :
    Erdos590.Larson.NashWilliams.FinThin (responseFamily b r) := by
  intro u hu v hv huv
  obtain ⟨b₁, h₁⟩ := hu
  obtain ⟨b₂, h₂⟩ := hv
  cases h₁ with
  | finish side u w₁ hlegal hrun₁ =>
      cases h₂ with
      | finish _ _ w₂ _ hrun₂ =>
          exact LabeledWord.finish_thin (b.get side) ⟨w₁, hrun₁⟩ ⟨w₂, hrun₂⟩ huv
  | advance side d u w₁ hlegal hrun₁ =>
      cases h₂ with
      | advance _ _ _ w₂ _ hrun₂ =>
          exact Advance.responses_thin ⟨b.get side, hlegal.1⟩ d
            ⟨.remainder w₁, hrun₁⟩ ⟨.remainder w₂, hrun₂⟩ huv

theorem responseFamily_exists (b : Board) (r : Request) (hr : r.Legal b)
    {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ responseFamily b r ∧ (↑u : Set ℕ) ⊆ H := by
  obtain ⟨side, cmd⟩ := r
  cases cmd with
  | finish =>
      obtain ⟨u, ⟨w, hw⟩, huH⟩ := LabeledWord.finish_exists (b.get side) hH
      exact ⟨u, ⟨b.update side w, .finish side u w hr hw⟩, huH⟩
  | advance d =>
      have hlegal : (b.get side).AllowedSize d := hr
      obtain ⟨u, ⟨q, hq⟩, huH⟩ := Advance.responses_exist ⟨b.get side, hlegal.1⟩ d hH
      obtain ⟨labels, n, rest, w, _, _, hw, _⟩ :=
        Advance.run_result ⟨b.get side, hlegal.1⟩ d (u.sort (· ≤ ·)) q hq
      rw [hw] at hq
      exact ⟨u, ⟨b.update side w, .advance side d u w hlegal hq⟩, huH⟩

theorem reply_wellFounded : WellFounded (fun b' b : Board => ∃ r u, Reply b r u b') :=
  (InvImage.wf Board.potential wellFounded_lt).mono fun _ _ h =>
    h.choose_spec.choose_spec.decreases

#print axioms responseFamily_exists
#print axioms reply_wellFounded

end Erdos591.Positive.Game

end Erdos118.Reused591

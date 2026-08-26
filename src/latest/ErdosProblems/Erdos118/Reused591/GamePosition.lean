import ErdosProblems.Erdos118.Reused591.GameBoard
import ErdosProblems.Erdos118.Reused591.GameHistory

namespace Erdos118.Reused591

/-!
# Legal game positions, opening flags, and fresh inputs

The last move is recorded explicitly, including the whole input set of
a builder response. Thus histories distinguish actual moves even if
some of their other state fields happen to agree.
-/

namespace Erdos591.Positive.Game

abbrev Move := (Bool × Request) ⊕ Finset ℕ

structure Position where
  board : Board
  mode : Option Bool
  pending : Option Request
  bound : ℕ
  lastMove : Option Move
  deriving DecidableEq, Countable

namespace Position

def initial : Position := ⟨Board.initial, none, none, 0, none⟩

def request (p : Position) (mode : Bool) (r : Request) : Position :=
  { p with mode := some mode, pending := some r, lastMove := some (.inl (mode, r)) }

def reply (p : Position) (u : Finset ℕ) (b : Board) : Position :=
  { p with board := b, pending := none, bound := u.sup id, lastMove := some (.inr u) }

/-- `true` is the inside flag. It is chosen on the opening request and
must be repeated unchanged on later requests. The opening request must
select the first word, represented by side `false`. -/
inductive Next (N : Set ℕ) : Position → Position → Prop
  | request (p : Position) (mode : Bool) (r : Request)
      (hturn : p.pending = none) (hlegal : r.Legal p.board)
      (hmode : p.mode = none ∨ p.mode = some mode)
      (hfirst : p.mode = none → r.side = false) : Next N (p.request mode r) p
  | reply (p : Position) (r : Request) (u : Finset ℕ) (b : Board)
      (hpending : p.pending = some r) (hreply : Reply p.board r u b)
      (huN : (↑u : Set ℕ) ⊆ N) (hfresh : ∀ x ∈ u, p.bound < x) :
      Next N (p.reply u b) p

def potential (p : Position) :
    (WithTop (ℕ ×ₗ ℕ) ×ₗ WithTop (ℕ ×ₗ ℕ)) ×ₗ ℕ :=
  toLex (p.board.potential, if p.pending.isNone then 1 else 0)

theorem Next.decreases {N : Set ℕ} {p q : Position} (h : Next N q p) :
    q.potential < p.potential := by
  cases h with
  | request p mode r hturn _ _ _ =>
      change Prod.Lex _ _ _ _
      simp only [potential, Position.request, hturn, Option.isNone_none, Option.isNone_some,
        ↓reduceIte]
      exact Prod.Lex.right _ (by simp)
  | reply p r u b _ hreply _ _ => exact Prod.Lex.left _ _ hreply.decreases

theorem next_wellFounded (N : Set ℕ) : WellFounded (Next N) :=
  (InvImage.wf potential wellFounded_lt).mono fun _ _ h => h.decreases

theorem Next.bound_le {N : Set ℕ} {p q : Position} (h : Next N q p) : p.bound ≤ q.bound := by
  cases h with
  | request _ _ _ _ _ _ _ => exact le_refl _
  | reply p r u b _ hreply _ hfresh =>
      obtain ⟨x, hx⟩ := hreply.nonempty
      exact (hfresh x hx).le.trans (Finset.le_sup (f := id) hx)

theorem Next.mode_some {N : Set ℕ} {p q : Position} (h : Next N q p)
    {mode : Bool} (hp : p.mode = some mode) : q.mode = some mode := by
  cases h with
  | request p m r _ _ hm _ =>
      rcases hm with hm | hm
      · simp [hp] at hm
      · exact hm.symm.trans hp
  | reply _ _ _ _ _ _ _ _ => exact hp

theorem Next.deterministic {N : Set ℕ} {p q t : Position}
    (hq : Next N q p) (ht : Next N t p) (hmove : q.lastMove = t.lastMove) : q = t := by
  cases hq with
  | request p mode r hturn hlegal hmode hfirst =>
      cases ht with
      | request _ mode' s _ _ _ _ =>
          have heq : (mode, r) = (mode', s) := Sum.inl.inj (Option.some.inj hmove)
          exact congrArg (fun mr => p.request mr.1 mr.2) heq
      | reply _ _ _ _ _ _ _ _ => simp [Position.request, Position.reply] at hmove
  | reply p r u b hpending hr huN hfresh =>
      cases ht with
      | request _ _ _ _ _ _ _ => simp [Position.request, Position.reply] at hmove
      | reply _ s v c hpending' hs _ _ =>
          have hrs : r = s := Option.some.inj (hpending.symm.trans hpending')
          have huv : u = v := Sum.inr.inj (Option.some.inj hmove)
          subst s
          subst v
          exact congrArg (p.reply u) (hr.deterministic hs)

def inputs (p : Position) : Finset ℕ :=
  match p.lastMove with
  | some (.inr u) => u
  | _ => ∅

def moveSize (p : Position) : ℕ :=
  match p.lastMove with
  | some (.inl (_, r)) => r.size
  | _ => 0

def pendingSize (p : Position) : ℕ :=
  match p.pending with
  | some r => r.size
  | none => 0

def phase (p : Position) : ℕ := if p.pending.isSome then 1 else 0

theorem Next.inputs_bound {N : Set ℕ} {p q : Position} (h : Next N q p)
    {x : ℕ} (hx : x ∈ q.inputs) : x ≤ q.bound := by
  cases h with
  | request p mode r _ _ _ _ => simp [inputs, Position.request] at hx
  | reply p r u b _ _ _ _ => exact Finset.le_sup (f := id) hx

theorem Next.pending_legal {N : Set ℕ} {p q : Position} (h : Next N q p)
    {r : Request} (hr : q.pending = some r) : r.Legal q.board := by
  cases h with
  | request p mode s _ hlegal _ _ =>
      have heq : s = r := Option.some.inj hr
      exact heq ▸ hlegal
  | reply p s u b _ _ _ _ => simp [Position.reply] at hr

/-- Every reachable position with no opening flag is the initial one;
every stored pending request is legal for its unchanged board. -/
def ControlInvariant (p : Position) : Prop :=
  (p.mode = none → p = initial) ∧ ∀ r, p.pending = some r → r.Legal p.board

@[simp] theorem controlInvariant_initial : initial.ControlInvariant := by
  simp [ControlInvariant, initial]

theorem Next.controlInvariant {N : Set ℕ} {p q : Position}
    (h : Next N q p) (hp : p.ControlInvariant) : q.ControlInvariant := by
  refine ⟨?_, fun _ hr => h.pending_legal hr⟩
  intro hq
  cases h with
  | request p mode r _ _ _ _ => simp [Position.request] at hq
  | reply p r u b hpend _ _ _ =>
      have hpi : p = initial := hp.1 hq
      simp [hpi, initial] at hpend

abbrev LegalHistory (N : Set ℕ) := History (Next N) initial

theorem history_controlInvariant {N : Set ℕ} (h : LegalHistory N) :
    h.position.ControlInvariant :=
  h.invariant ControlInvariant controlInvariant_initial fun _ _ hn hp => hn.controlInvariant hp

theorem history_next_wellFounded (N : Set ℕ) :
    WellFounded (History.Next (r := Next N) (root := initial)) :=
  History.next_wellFounded (next_wellFounded N)

#print axioms next_wellFounded
#print axioms history_controlInvariant

end Position

end Erdos591.Positive.Game

end Erdos118.Reused591

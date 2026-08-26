import ErdosProblems.Erdos118.Reused591.GamePosition
import ErdosProblems.Erdos118.Reused591.GameUniformization

namespace Erdos118.Reused591

/-!
# Conservative uniformization on the concrete legal-history game

The terminal payoff is a Boolean function of the fixed opening flag and
the final board. All moves, finite responses, freshness restrictions,
and histories are the concrete ones. The exact clarity/color payoff is
defined separately; no property of a payoff is assumed in this module.
-/

namespace Erdos591.Positive.Game.Concrete

abbrev Hist (N : Set ℕ) := Position.LegalHistory N

instance (N : Set ℕ) : Countable (Hist N) := by
  change Countable
    {path : List Position // History.ValidPath (Position.Next N) Position.initial path}
  infer_instance

def done (b : Board) : Bool := b.left.terminal && b.right.terminal

def kind {N : Set ℕ} (payoff : Bool → Board → Bool) (h : Hist N) : PositionKind :=
  match h.position.pending with
  | some _ => .builder
  | none => if done h.position.board then
      .terminal (payoff (h.position.mode.getD false) h.position.board)
    else .architect

theorem kind_builder_iff {N : Set ℕ} (payoff : Bool → Board → Bool) (h : Hist N) :
    kind payoff h = .builder ↔ ∃ r, h.position.pending = some r := by
  cases hp : h.position.pending with
  | some r => simp [kind, hp]
  | none =>
      cases hd : done h.position.board <;> simp [kind, hp, hd]

theorem kind_architect_iff {N : Set ℕ} (payoff : Bool → Board → Bool) (h : Hist N) :
    kind payoff h = .architect ↔ h.position.pending = none ∧ done h.position.board = false := by
  cases hp : h.position.pending with
  | some r => simp [kind, hp]
  | none =>
      cases hd : done h.position.board <;> simp [kind, hp, hd]

theorem exists_request {N : Set ℕ} {p : Position} (hp : p.ControlInvariant)
    (hturn : p.pending = none) (hdone : done p.board = false) :
    ∃ mode r, Position.Next N (p.request mode r) p := by
  cases hm : p.mode with
  | none =>
      have hpi : p = Position.initial := hp.1 hm
      subst p
      refine ⟨false, ⟨false, .finish⟩, ?_⟩
      exact .request _ _ _ rfl rfl (Or.inl rfl) (fun _ => rfl)
  | some mode =>
      have chooseSide (side : Bool) (hside : (p.board.get side).terminal = false) :
          ∃ mode r, Position.Next N (p.request mode r) p := by
        refine ⟨mode, ⟨side, .finish⟩, ?_⟩
        apply Position.Next.request p mode ⟨side, .finish⟩ hturn hside (Or.inr hm)
        intro hnone
        simp [hm] at hnone
      cases hl : p.board.left.terminal with
      | false => exact chooseSide false hl
      | true =>
          apply chooseSide true
          change p.board.right.terminal = false
          simpa [done, hl] using hdone

theorem architect_move {N : Set ℕ} (payoff : Bool → Board → Bool) (h : Hist N)
    (hk : kind payoff h = .architect) : ∃ k, History.Next k h := by
  obtain ⟨hturn, hdone⟩ := (kind_architect_iff payoff h).1 hk
  obtain ⟨mode, r, hr⟩ := exists_request (N := N)
    (Position.history_controlInvariant h) hturn hdone
  exact ⟨h.append (h.position.request mode r) hr, _, hr, rfl⟩

def family {N : Set ℕ} (h : Hist N) : Set (Finset ℕ) :=
  {u | ∃ r, h.position.pending = some r ∧
    u ∈ responseFamily h.position.board r ∧ (↑u : Set ℕ) ⊆ N ∧
    ∀ x ∈ u, h.position.bound < x}

theorem family_thin {N : Set ℕ} (h : Hist N) :
    Erdos590.Larson.NashWilliams.FinThin (family h) := by
  intro u hu v hv huv
  obtain ⟨r, hr, hu, _, _⟩ := hu
  obtain ⟨s, hs, hv, _, _⟩ := hv
  have hrs : r = s := Option.some.inj (hr.symm.trans hs)
  subst s
  exact responseFamily_thin h.position.board r hu hv huv

theorem family_exists {N : Set ℕ} (payoff : Bool → Board → Bool) (h : Hist N)
    (hk : kind payoff h = .builder) (M : Set ℕ) (hMN : M ⊆ N) (hM : M.Infinite)
    (habove : ∀ x ∈ M, h.position.bound < x) :
    ∃ u, u ∈ family h ∧ (↑u : Set ℕ) ⊆ M := by
  obtain ⟨r, hr⟩ := (kind_builder_iff payoff h).1 hk
  have hlegal := (Position.history_controlInvariant h).2 r hr
  obtain ⟨u, hu, huM⟩ := responseFamily_exists h.position.board r hlegal hM
  exact ⟨u, ⟨r, hr, hu, huM.trans hMN, fun x hx => habove x (huM hx)⟩, huM⟩

/-- A response is the history obtained by appending the actual reply
position, including its full recorded input set. -/
inductive Replies {N : Set ℕ} (h : Hist N) (u : Finset ℕ) : Hist N → Prop
  | mk (r : Request) (b : Board)
      (hpending : h.position.pending = some r) (hr : Reply h.position.board r u b)
      (huN : (↑u : Set ℕ) ⊆ N) (hfresh : ∀ x ∈ u, h.position.bound < x) :
      Replies h u (h.append (h.position.reply u b)
        (.reply h.position r u b hpending hr huN hfresh))

theorem Replies.mem_family {N : Set ℕ} {h k : Hist N} {u : Finset ℕ}
    (hk : Replies h u k) : u ∈ family h := by
  cases hk with
  | mk r b hp hr huN hfresh => exact ⟨r, hp, ⟨b, hr⟩, huN, hfresh⟩

theorem exists_replies {N : Set ℕ} {h : Hist N} {u : Finset ℕ} (hu : u ∈ family h) :
    ∃ k, Replies h u k := by
  obtain ⟨r, hp, ⟨b, hr⟩, huN, hfresh⟩ := hu
  exact ⟨_, .mk r b hp hr huN hfresh⟩

theorem Replies.next {N : Set ℕ} {h k : Hist N} {u : Finset ℕ}
    (hk : Replies h u k) : History.Next k h := by
  cases hk with
  | mk r b hp hr huN hfresh =>
      exact ⟨_, .reply h.position r u b hp hr huN hfresh, rfl⟩

theorem Replies.deterministic {N : Set ℕ} {h k l : Hist N} {u : Finset ℕ}
    (hk : Replies h u k) (hl : Replies h u l) : k = l := by
  cases hk with
  | mk r b hp hr huN hfresh =>
      cases hl with
      | mk s c hp' hs _ _ =>
          have hrs : r = s := Option.some.inj (hp.symm.trans hp')
          subst s
          have hbc : b = c := hr.deterministic hs
          subst c
          rfl

noncomputable def response {N : Set ℕ} (h : Hist N) (u : Finset ℕ) : Hist N := by
  classical
  exact if hex : ∃ k, Replies h u k then hex.choose else h

theorem response_spec {N : Set ℕ} {h : Hist N} {u : Finset ℕ}
    (hu : u ∈ family h) : Replies h u (response h u) := by
  have hex := exists_replies hu
  simpa only [response, dif_pos hex] using hex.choose_spec

theorem response_eq {N : Set ℕ} {h k : Hist N} {u : Finset ℕ}
    (hk : Replies h u k) : response h u = k :=
  (response_spec hk.mem_family).deterministic hk

/-- The concrete closed game. The default branch of `response` is never
used for a legal builder input, as certified by `response_spec`. -/
noncomputable def game (N : Set ℕ) (payoff : Bool → Board → Bool) :
    FiniteResponseGame (Hist N) N where
  kind := kind payoff
  next := History.Next
  wellFounded := Position.history_next_wellFounded N
  architect_move := architect_move payoff
  family := family
  response := response
  response_next _ _ _ hu := (response_spec hu).next
  thin h _ := family_thin h
  threshold h := h.position.bound
  response_exists := family_exists payoff

theorem uniformization {N : Set ℕ} (hN : N.Infinite) (payoff : Bool → Board → Bool) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃ (b : Hist N → ℕ) (v : Hist N → Bool),
      (game N payoff).ValueSystem H b v ∧
      (∀ p q, History.Next q p → b p ≤ b q) ∧
      ((∃ σ : (game N payoff).ArchitectStrategy,
          (game N payoff).ArchitectWins H b σ
            (History.initial (Position.Next N) Position.initial)) ∨
        (game N payoff).AllBuilderWins H b
          (History.initial (Position.Next N) Position.initial)) := by
  exact (game N payoff).conservative_uniformization hN History.past
    History.self_mem_past (fun _ _ h => History.past_mono h)
    (History.initial (Position.Next N) Position.initial)

#print axioms uniformization

end Erdos591.Positive.Game.Concrete

end Erdos118.Reused591

import ErdosProblems.Erdos591.AtomicTrace
import ErdosProblems.Erdos591.ReplayBudget

/-!
# Conservative replay of completed atomic traces

The spacing certificate refers to the proved finite-history bound with
an explicit original label-size budget. It can therefore retain the
larger finite set and larger label size from the original construction,
even when the replay deletes labels or omits other branches.
-/

namespace Erdos591.Positive.Game

theorem Request.Legal.not_done {r : Request} {b : Board} (hr : r.Legal b) :
    Concrete.done b = false := by
  cases hc : r.command with
  | finish => exact Board.not_done_of_live (by simpa [Request.Legal, hc] using hr)
  | advance d =>
      have hh : (b.get r.side).AllowedSize d := by simpa [Request.Legal, hc] using hr
      exact Board.not_done_of_live hh.1

namespace Concrete

/-- Append a genuine request and reply, preserving all the history data
needed to continue the replay. The bound is checked at the intervening
builder history, not at the earlier architect history. -/
theorem append_conservative_reply {N H : Set ℕ} (hHN : H ⊆ N)
    (payoff : Bool → Board → Bool) (bound : Hist N → ℕ)
    (h : Hist N) (mode : Bool) (r : Request) (u : Finset ℕ) (b' : Board)
    (hturn : h.position.pending = none)
    (hmode : h.position.mode = none ∨ h.position.mode = some mode)
    (hfirst : h.position.mode = none → r.side = false)
    (hr : Reply h.position.board r u b') (huH : (↑u : Set ℕ) ⊆ H)
    (hfresh : ∀ x ∈ u, h.position.bound < x)
    (hbound : ∀ ha : Position.Next N (h.position.request mode r) h.position,
      ∀ x ∈ u, bound (h.append (h.position.request mode r) ha) < x) :
    ∃ k : Hist N,
      Relation.ReflTransGen ((game N payoff).ConservativeStep H bound) h k ∧
      k.position.board = b' ∧ k.position.pending = none ∧
      k.position.mode = some mode ∧ k.position.bound = u.sup id ∧
      ReplayBudget.used k = ReplayBudget.used h ∪ u := by
  have ha : Position.Next N (h.position.request mode r) h.position :=
    .request _ _ _ hturn hr.legal hmode hfirst
  let h' := h.append (h.position.request mode r) ha
  have hpending : h'.position.pending = some r := by simp [h', Position.request]
  have hreply : Reply h'.position.board r u b' := by simpa [h', Position.request] using hr
  have hfresh' : ∀ x ∈ u, h'.position.bound < x := by
    simpa [h', Position.request] using hfresh
  have huN := huH.trans hHN
  have hb : Position.Next N (h'.position.reply u b') h'.position :=
    .reply _ _ _ _ hpending hreply huN hfresh'
  let k := h'.append (h'.position.reply u b') hb
  have hk : Replies h' u k := .mk r b' hpending hreply huN hfresh'
  have haKind : (game N payoff).kind h = .architect :=
    (kind_architect_iff payoff h).2 ⟨hturn, hr.legal.not_done⟩
  have hbKind : (game N payoff).kind h' = .builder :=
    (kind_builder_iff payoff h').2 ⟨r, hpending⟩
  have haStep : (game N payoff).ConservativeStep H bound h h' :=
    .architect h h' haKind ⟨_, ha, rfl⟩
  have hbStep : (game N payoff).ConservativeStep H bound h' k := by
    have hs : (game N payoff).ConservativeStep H bound h' ((game N payoff).response h' u) :=
      .builder h' u hbKind hk.mem_family huH (hbound ha)
    simpa only [game, response_eq hk] using hs
  refine ⟨k, (Relation.ReflTransGen.single haStep).tail hbStep, ?_, ?_, ?_, ?_, ?_⟩
  · simp [k, Position.reply]
  · simp [k, Position.reply]
  · simp [k, h', Position.reply, Position.request]
  · simp [k, Position.reply]
  · simp [k, h', Position.inputs, Position.reply, Position.request]

end Concrete

namespace Atomic

/-- Each atomic block was chosen above a finite retrospective budget.
`F'` may include numbers from branches omitted from this particular
trace, and `q` may be the label size before coarsening. -/
def Spaced {N : Set ℕ} (bound : Concrete.Hist N → ℕ)
    (F : Finset ℕ) (xs : List Atom) : Prop :=
  ∀ front a tail, xs = front ++ a :: tail →
    ∃ F' q, F ∪ (inputs front).toFinset ⊆ F' ∧ a.label.card ≤ q ∧
      ∀ x ∈ a.inputs, ReplayBudget.bound N bound F' q < x

theorem Spaced.tail {N : Set ℕ} {bound : Concrete.Hist N → ℕ}
    {F : Finset ℕ} {front tail : List Atom} (hs : Spaced bound F (front ++ tail)) :
    Spaced bound (F ∪ (inputs front).toFinset) tail := by
  intro pre a rest heq
  obtain ⟨F', q, hF, hq, hx⟩ := hs (front ++ pre) a rest
    (by simp [heq, List.append_assoc])
  refine ⟨F', q, ?_, hq, hx⟩
  simpa [Finset.union_assoc] using hF

theorem above_first_atom (a : Atom) (xs : List Atom) (B : ℕ)
    (hinc : (inputs (a :: xs)).Pairwise (· < ·))
    (ha : ∀ x ∈ a.inputs, B < x) : ∀ x ∈ inputs (a :: xs), B < x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact (ha a.value a.value_mem).trans
      ((List.pairwise_append.mp hinc).2.2 a.value a.value_mem x hx)

theorem Spaced.request_bound {N : Set ℕ} {bound : Concrete.Hist N → ℕ}
    {F : Finset ℕ} {a : Atom} {xs : List Atom} (hs : Spaced bound F (a :: xs))
    (h : Concrete.Hist N) (mode : Bool) (hused : ReplayBudget.used h ⊆ F)
    (ha : Position.Next N
      (h.position.request mode ⟨a.side, .advance a.label.card⟩) h.position) :
    ∀ x ∈ a.inputs,
      bound (h.append (h.position.request mode ⟨a.side, .advance a.label.card⟩) ha) < x := by
  obtain ⟨F', q, hF, hq, hx⟩ := hs [] a xs rfl
  have hused' : ReplayBudget.used h ⊆ F' := hused.trans (by simpa using hF)
  intro x hxa
  exact (ReplayBudget.request_lt_bound N bound F' q h mode
    ⟨a.side, .advance a.label.card⟩ ha hused' hq).trans (hx x hxa)

/-- A complete, properly scheduled atomic trace is a genuine
conservative play. Every input, including every retained label value,
is recorded in the resulting legal history. -/
theorem replay {N H : Set ℕ} (hHN : H ⊆ N) (payoff : Bool → Board → Bool)
    (bound : Concrete.Hist N → ℕ) (mode : Bool) (h : Concrete.Hist N)
    (F : Finset ℕ) (xs : List Atom) (last : Board)
    (ht : Trace h.position.board xs last) (hdone : Concrete.done last = true)
    (hinc : (inputs xs).Pairwise (· < ·)) (hs : Spaced bound F xs)
    (hH : ∀ x ∈ inputs xs, x ∈ H)
    (hfresh : ∀ x ∈ inputs xs, h.position.bound < x)
    (hused : ReplayBudget.used h ⊆ F) (hturn : h.position.pending = none)
    (hmode : h.position.mode = none ∨ h.position.mode = some mode)
    (hfirst : h.position.mode = none → ∀ a ∈ xs.head?, a.side = false) :
    ∃ k : Concrete.Hist N,
      Relation.ReflTransGen ((Concrete.game N payoff).ConservativeStep H bound) h k ∧
      k.position.board = last ∧ k.position.pending = none ∧
      (h.position.mode = some mode ∨ xs ≠ [] → k.position.mode = some mode) ∧
      ReplayBudget.used k = ReplayBudget.used h ∪ (inputs xs).toFinset := by
  cases hlist : xs with
  | nil =>
      rw [hlist] at ht
      cases ht
      refine ⟨h, .refl, rfl, hturn, ?_, by simp⟩
      rintro (hm | hn)
      · exact hm
      · exact (hn rfl).elim
  | cons a xs =>
      rw [hlist] at ht hinc hs hH hfresh hfirst
      obtain ⟨middle, tail, w, hxs, _, hr, httail⟩ := response_split ht hdone hinc
      let front := a :: middle
      let u := (inputs front).toFinset
      have hsplit : a :: xs = front ++ tail := by simp [front, hxs]
      have hpair : (inputs front ++ inputs tail).Pairwise (· < ·) := by
        simpa [hsplit] using hinc
      have hfrontinc := (List.pairwise_append.mp hpair).1
      have htailinc := (List.pairwise_append.mp hpair).2.1
      have hsep := (List.pairwise_append.mp hpair).2.2
      have hmem (x : ℕ) (hx : x ∈ u) : x ∈ inputs (a :: xs) := by
        rw [hsplit, inputs_append]
        exact List.mem_append_left _ (List.mem_toFinset.mp hx)
      obtain ⟨k, hpath, hkboard, hkturn, hkmode, hkbound, hkused⟩ :=
        Concrete.append_conservative_reply hHN payoff bound h mode
          ⟨a.side, .advance a.label.card⟩ u (h.position.board.update a.side w)
          hturn hmode (fun hm => hfirst hm a (by simp)) hr
          (fun x hx => hH x (hmem x hx)) (fun x hx => hfresh x (hmem x hx))
          (fun ha x hx => above_first_atom a middle _ hfrontinc
            (hs.request_bound h mode hused ha) x (List.mem_toFinset.mp hx))
      have htailtrace : Trace k.position.board tail last := hkboard.symm ▸ httail
      have hstail : Spaced bound (F ∪ u) tail :=
        Spaced.tail (by simpa only [hsplit] using hs)
      have hHtail : ∀ x ∈ inputs tail, x ∈ H := by
        intro x hx
        apply hH x
        rw [hsplit, inputs_append]
        exact List.mem_append_right _ hx
      have hfreshtail : ∀ x ∈ inputs tail, k.position.bound < x := by
        intro x hx
        rw [hkbound]
        have hv : a.value ∈ inputs front := List.mem_append_left _ a.value_mem
        have hpos : 0 < x := (Nat.zero_le _).trans_lt (hsep a.value hv x hx)
        apply (Finset.sup_lt_iff hpos).mpr
        intro y hy
        exact hsep y (List.mem_toFinset.mp hy) x hx
      have husedtail : ReplayBudget.used k ⊆ F ∪ u := by
        rw [hkused]
        exact Finset.union_subset_union hused (Finset.Subset.refl _)
      obtain ⟨l, hkl, hlboard, hlturn, hlmode, hlused⟩ :=
        replay hHN payoff bound mode k (F ∪ u) tail last htailtrace hdone
          htailinc hstail hHtail hfreshtail husedtail hkturn (Or.inr hkmode)
          (fun hn => by simp [hkmode] at hn)
      refine ⟨l, hpath.trans hkl, hlboard, hlturn, fun _ => hlmode (Or.inl hkmode), ?_⟩
      rw [hlused, hkused, hsplit, inputs_append, List.toFinset_append]
      exact Finset.union_assoc _ _ _
termination_by xs.length
decreasing_by
  have hlen := congrArg List.length hxs
  have hlen₀ := congrArg List.length hlist
  simp only [List.length_append] at hlen
  simp only [List.length_cons] at hlen₀
  omega

theorem replay_initial {N H : Set ℕ} (hHN : H ⊆ N)
    (payoff : Bool → Board → Bool) (bound : Concrete.Hist N → ℕ) (mode : Bool)
    (xs : List Atom) (last : Board) (ht : Trace Board.initial xs last)
    (hdone : Concrete.done last = true) (hinc : (inputs xs).Pairwise (· < ·))
    (hs : Spaced bound ∅ xs) (hH : ∀ x ∈ inputs xs, x ∈ H)
    (hpos : ∀ x ∈ inputs xs, 0 < x) (hfirst : ∀ a ∈ xs.head?, a.side = false) :
    ∃ k : Concrete.Hist N,
      Relation.ReflTransGen ((Concrete.game N payoff).ConservativeStep H bound)
        (History.initial (Position.Next N) Position.initial) k ∧
      k.position.board = last ∧ k.position.pending = none ∧
      k.position.mode = some mode ∧ ReplayBudget.used k = (inputs xs).toFinset := by
  have hne : xs ≠ [] := by
    intro heq
    subst xs
    cases ht
    simp [Concrete.done, Board.initial, LabeledWord.initial, LabeledWord.terminal] at hdone
  obtain ⟨k, hp, hb, ht, hm, hu⟩ := replay hHN payoff bound mode
    (History.initial (Position.Next N) Position.initial) ∅ xs last ht hdone
    hinc hs hH hpos (by simp) rfl (Or.inl rfl) (fun _ => hfirst)
  exact ⟨k, hp, hb, ht, hm (Or.inr hne), by simpa using hu⟩

#print axioms replay
#print axioms replay_initial

end Atomic

end Erdos591.Positive.Game

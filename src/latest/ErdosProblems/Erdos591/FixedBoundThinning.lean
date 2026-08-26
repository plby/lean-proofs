import ErdosProblems.Erdos591.ArchitectBudget
import ErdosProblems.Erdos591.FastSequence
import ErdosProblems.Erdos591.TerminalUniformization

/-!
# Local terminal thinning with the original continuation bound

A fast infinite pool absorbs any new history-dependent bound. The fixed
origin's old inputs remain unchanged and need not lie in the new pool.
Only finite sets of nonpending histories are used in the budget; the
fixed strategy determines the one following request at each of them.
-/

namespace Erdos591.Positive.Game.Concrete

variable {N H : Set ℕ} {payoff : Bool → Board → Bool}
  {b : Hist N → ℕ} {σ : (game N payoff).ArchitectStrategy}

theorem Replies.used_eq {p q : Hist N} {u : Finset ℕ} (h : Replies p u q) :
    ReplayBudget.used q = ReplayBudget.used p ∪ u := by
  cases h
  simp [ReplayBudget.used_append, Position.inputs, Position.reply]

theorem Replies.pending_none {p q : Hist N} {u : Finset ℕ} (h : Replies p u q) :
    q.position.pending = none := by
  cases h
  simp [Position.reply]

theorem follow_step_used {p q : Hist N}
    (hs : (game N payoff).FollowStep σ H b p q) :
    ∀ x ∈ ReplayBudget.used q, x ∈ ReplayBudget.used p ∨ x ∈ H := by
  cases hs.1 with
  | architect q hk hnext =>
      have hnone := ((kind_architect_iff payoff p).mp hk).1
      obtain ⟨z, hz, rfl⟩ := hnext
      cases hz with
      | request _ mode r _ _ _ _ =>
          simpa [ReplayBudget.used_append, Position.inputs, Position.request] using
            (fun x hx => Or.inl hx :
              ∀ x ∈ ReplayBudget.used p, x ∈ ReplayBudget.used p ∨ x ∈ H)
      | reply _ r u board hp _ _ _ => simp [hnone] at hp
  | builder u hk hu huH hub =>
      intro x hx
      change x ∈ ReplayBudget.used (response p u) at hx
      rw [(response_spec hu).used_eq] at hx
      exact (Finset.mem_union.mp hx).elim Or.inl (fun h => Or.inr (huH h))

theorem follow_used {p q : Hist N}
    (hpath : Relation.ReflTransGen ((game N payoff).FollowStep σ H b) p q) :
    ∀ x ∈ ReplayBudget.used q, x ∈ ReplayBudget.used p ∨ x ∈ H := by
  induction hpath with
  | refl => exact fun _ hx => Or.inl hx
  | tail _ hs ih =>
      intro x hx
      exact (follow_step_used hs x hx).elim (ih x) Or.inr

theorem pending_follow_predecessor {p q : Hist N}
    (hpath : Relation.ReflTransGen ((game N payoff).FollowStep σ H b) p q)
    (hk : (game N payoff).kind q = .builder) :
    q = p ∨ ∃ r, Relation.ReflTransGen ((game N payoff).FollowStep σ H b) p r ∧
      ∃ hr : (game N payoff).kind r = .architect, q = σ.move r hr := by
  cases hpath with
  | refl => exact Or.inl rfl
  | @tail r q hpath hs =>
      cases hs.1 with
      | architect q hr hnext => exact Or.inr ⟨r, hpath, hr, hs.2 hr⟩
      | builder u hr hu huH hub =>
          obtain ⟨request, hp⟩ := (kind_builder_iff payoff _).mp hk
          change (response r u).position.pending = some request at hp
          simp [(response_spec hu).pending_none] at hp

/-- The new pool ensures that every path from the fixed origin obeys
the prescribed bound `c`, even when it is only assumed to obey `b`. -/
theorem exists_bound_absorbing_pool (hH : H.Infinite)
    (σ : (game N payoff).ArchitectStrategy) (b c : Hist N → ℕ) (p : Hist N) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∀ q,
      Relation.ReflTransGen ((game N payoff).FollowStep σ L b) p q →
        Relation.ReflTransGen ((game N payoff).FollowStep σ L c) p q := by
  classical
  let F := ReplayBudget.used p
  obtain ⟨f, hf, hfH, hfast, _⟩ := FastSequence.exists_above_finite_bounds hH F
    (fun E => max (c p) (ArchitectBudget.bound σ c E))
  let L := Set.range f
  have hLH : L ⊆ H := by rintro x ⟨n, rfl⟩; exact hfH n
  have hL : L.Infinite := Set.infinite_range_of_injective hf.injective
  have response_bound {r : Hist N}
      (hpath : Relation.ReflTransGen ((game N payoff).FollowStep σ L b) p r)
      (hk : (game N payoff).kind r = .builder) (u : Finset ℕ)
      (hu : u ∈ (game N payoff).family r) (huL : (↑u : Set ℕ) ⊆ L) :
      ∀ x ∈ u, c r < x := by
    intro x hx
    obtain ⟨n, hfn⟩ := huL hx
    rcases pending_follow_predecessor hpath hk with rfl | ⟨v, hpv, hv, hrv⟩
    · exact hfn ▸ (le_max_left _ _).trans_lt (hfast n)
    · have hbound : v.position.bound ≤ r.position.bound := by
        rw [hrv]
        obtain ⟨z, hz, heq⟩ := σ.legal v hv
        rw [heq, History.position_append]
        exact hz.bound_le
      have hfresh : r.position.bound < x := by
        obtain ⟨s, hp, hr, huN, huFresh⟩ := hu
        exact huFresh x hx
      have hF : ReplayBudget.used v ⊆ F ∪ (Finset.range n).image f := by
        intro y hy
        rcases follow_used hpv y hy with hyF | hyL
        · exact Finset.mem_union_left _ hyF
        · obtain ⟨m, hfm⟩ := hyL
          have hyx := ((ReplayBudget.used_bound v y hy).trans hbound).trans_lt hfresh
          have hmn : m < n := hf.lt_iff_lt.mp (by simpa only [hfm, hfn] using hyx)
          exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmn, hfm⟩)
      have hc := (ArchitectBudget.request_lt_bound σ c _ v hF hv).2.1
      rw [← hrv] at hc
      exact hc.trans (hfn ▸ (le_max_right _ _).trans_lt (hfast n))
  refine ⟨L, hLH, hL, ?_⟩
  intro q hpath
  induction hpath with
  | refl => exact .refl
  | @tail r q hpr hs ih =>
      apply ih.tail
      refine ⟨?_, hs.2⟩
      cases hs.1 with
      | architect q hk hnext => exact .architect _ q hk hnext
      | builder u hk hu huL hub =>
          exact .builder _ u hk hu huL (response_bound hpr hk u hu huL)

theorem terminal_finite_uniformization_fixed_bound {C : Type*} [Finite C]
    (hHN : H ⊆ N) (hH : H.Infinite) (b : Hist N → ℕ)
    (σ : (game N payoff).ArchitectStrategy) (color : Hist N → C) (p : Hist N) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ value : C, ∀ q w,
      Relation.ReflTransGen ((game N payoff).FollowStep σ L b) p q →
        (game N payoff).kind q = .terminal w → color q = value := by
  obtain ⟨K, hKH, hK, c, _hbc, value, hvalue⟩ :=
    (game N payoff).terminal_finite_uniformization hHN hH b σ color p
  obtain ⟨L, hLK, hL, hpaths⟩ := exists_bound_absorbing_pool hK σ b c p
  refine ⟨L, hLK.trans hKH, hL, value, ?_⟩
  intro q w hpath hterm
  apply hvalue q w _ hterm
  exact Relation.ReflTransGen.mono (fun _ _ hs =>
    FiniteResponseGame.FollowStep.mono (game N payoff) hLK (fun _ => le_rfl) hs)
    _ _ (hpaths q hpath)

#print axioms exists_bound_absorbing_pool
#print axioms terminal_finite_uniformization_fixed_bound

end Erdos591.Positive.Game.Concrete

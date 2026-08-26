import ErdosProblems.Erdos591.GamePosition
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finset.Powerset

/-!
# Finite retrospective-history budgets

The pending request size is an explicit parameter. Completed requests
are bounded by the number of inputs already used; no bound on arbitrary
future label-size requests is asserted.
-/

namespace Erdos591.Positive.Game

namespace Position

theorem Next.lengthBudget_step {N : Set ℕ} {p q : Position} (h : Next N q p)
    (F : Finset ℕ) (hF : ∀ x ∈ F, x ≤ p.bound) (n : ℕ)
    (hn : n ≤ 2 * F.card + p.phase) :
    n + 1 ≤ 2 * (F ∪ q.inputs).card + q.phase := by
  cases h with
  | request p mode r hturn _ _ _ =>
      simp only [phase, hturn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] at hn
      simpa [Position.inputs, Position.request, phase] using Nat.add_le_add_right hn 1
  | reply p r u b hpending hr _ hfresh =>
      have hdisj : Disjoint F u := Finset.disjoint_left.mpr fun x hx hxu =>
        (not_lt_of_ge (hF x hx)) (hfresh x hxu)
      have hcard := Finset.card_union_of_disjoint hdisj
      have hpos : 0 < u.card := Finset.card_pos.mpr hr.nonempty
      simp only [phase, hpending, Option.isSome_some, ↓reduceIte] at hn
      simp only [Position.inputs, Position.reply, phase, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega

theorem Next.requestBudget_mono {N : Set ℕ} {p q : Position} (h : Next N q p)
    (F : Finset ℕ) :
    max F.card p.pendingSize ≤ max (F ∪ q.inputs).card q.pendingSize := by
  cases h with
  | request p mode r hturn _ _ _ =>
      simp [pendingSize, hturn, Position.inputs, Position.request]
  | reply p r u b hpending hr _ _ =>
      have hF : F.card ≤ (F ∪ u).card := Finset.card_le_card Finset.subset_union_left
      have hu : u.card ≤ (F ∪ u).card := Finset.card_le_card Finset.subset_union_right
      simpa [pendingSize, hpending, Position.inputs, Position.reply] using
        (max_le hF (hr.size_le_card.trans hu))

theorem Next.moveSize_le_budget {N : Set ℕ} {p q : Position} (h : Next N q p)
    (F : Finset ℕ) : q.moveSize ≤ max (F ∪ q.inputs).card q.pendingSize := by
  cases h with
  | request p mode r _ _ _ _ =>
      simp [moveSize, pendingSize, Position.inputs, Position.request]
  | reply p r u b _ _ _ _ =>
      simp [moveSize, pendingSize, Position.inputs, Position.reply]

end Position

namespace ReplayBudget

def used {N : Set ℕ} (h : Position.LegalHistory N) : Finset ℕ :=
  h.val.toFinset.biUnion Position.inputs

@[simp] theorem used_initial (N : Set ℕ) :
    used (History.initial (Position.Next N) Position.initial) = ∅ := by
  simp [used, History.initial]

@[simp] theorem used_append {N : Set ℕ} (h : Position.LegalHistory N) (p : Position)
    (hp : Position.Next N p h.position) : used (h.append p hp) = used h ∪ p.inputs := by
  simp [used, History.append, Finset.union_comm]

theorem inputs_subset_used {N : Set ℕ} {h : Position.LegalHistory N} {p : Position}
    (hp : p ∈ h.val) : p.inputs ⊆ used h := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hp, hx⟩

theorem used_bound {N : Set ℕ} (h : Position.LegalHistory N) :
    ∀ x ∈ used h, x ≤ h.position.bound := by
  apply History.induction (fun h => ∀ x ∈ used h, x ≤ h.position.bound) ?_ ?_ h
  · simp
  · intro k p hp ih x hx
    rw [used_append] at hx
    rw [History.position_append]
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (ih x hx).trans hp.bound_le
    · exact hp.inputs_bound hx

theorem length_bound {N : Set ℕ} (h : Position.LegalHistory N) :
    h.val.length ≤ 2 * (used h).card + h.position.phase := by
  apply History.induction (fun h => h.val.length ≤ 2 * (used h).card + h.position.phase) ?_ ?_ h
  · simp [History.initial]
  · intro k p hp ih
    have hstep := hp.lengthBudget_step (used k) (used_bound k) k.val.length ih
    rw [used_append, History.position_append]
    simpa only [History.append, List.length_append, List.length_singleton] using hstep

theorem requestSize_bound {N : Set ℕ} (h : Position.LegalHistory N) :
    ∀ p ∈ h.val, p.moveSize ≤ max (used h).card h.position.pendingSize := by
  apply History.induction
    (fun h => ∀ p ∈ h.val, p.moveSize ≤ max (used h).card h.position.pendingSize) ?_ ?_ h
  · simp [History.initial]
  · intro k p hp ih q hq
    have hq' : q ∈ k.val ∨ q = p := by simpa [History.append] using hq
    rw [used_append, History.position_append]
    rcases hq' with hq' | rfl
    · exact (ih q hq').trans (hp.requestBudget_mono (used k))
    · exact hp.moveSize_le_budget (used k)

theorem records_injective (N : Set ℕ) :
    Function.Injective (fun h : Position.LegalHistory N => h.val.map Position.lastMove) :=
  History.records_injective Position.lastMove fun _ _ _ hq ht heq => hq.deterministic ht heq

def requests (K : ℕ) : Finset Request :=
  (Finset.univ : Finset Bool).biUnion fun side =>
    insert ⟨side, .finish⟩ ((Finset.range (K + 1)).image fun d => ⟨side, .advance d⟩)

@[simp] theorem mem_requests (K : ℕ) (r : Request) : r ∈ requests K ↔ r.size ≤ K := by
  obtain ⟨side, cmd⟩ := r
  cases side <;> cases cmd <;> simp [requests, Request.size, Request.mk.injEq]

def alphabet (F : Finset ℕ) (K : ℕ) : Finset (Option Move) :=
  insert none
    ((((Finset.univ : Finset Bool).product (requests K)).image fun mr => some (.inl mr)) ∪
      (F.powerset.image fun u => some (.inr u)))

@[simp] theorem none_mem_alphabet (F : Finset ℕ) (K : ℕ) : none ∈ alphabet F K := by
  simp [alphabet]

@[simp] theorem request_mem_alphabet (F : Finset ℕ) (K : ℕ) (mode : Bool) (r : Request) :
    some (.inl (mode, r)) ∈ alphabet F K ↔ r.size ≤ K := by
  simp [alphabet]

@[simp] theorem reply_mem_alphabet (F : Finset ℕ) (K : ℕ) (u : Finset ℕ) :
    some (.inr u) ∈ alphabet F K ↔ u ⊆ F := by
  simp [alphabet]

theorem records_mem_alphabet {N : Set ℕ} (h : Position.LegalHistory N)
    (F : Finset ℕ) (q : ℕ) (hF : used h ⊆ F) (hq : h.position.pendingSize ≤ q) :
    ∀ m ∈ h.val.map Position.lastMove, m ∈ alphabet F (max F.card q) := by
  intro m hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  have hsize : p.moveSize ≤ max F.card q :=
    (requestSize_bound h p hp).trans (max_le_max (Finset.card_le_card hF) hq)
  cases hlast : p.lastMove with
  | none => exact none_mem_alphabet F _
  | some m =>
      cases m with
      | inl mr =>
          obtain ⟨mode, r⟩ := mr
          apply (request_mem_alphabet F _ mode r).2
          simpa [Position.moveSize, hlast] using hsize
      | inr u =>
          apply (reply_mem_alphabet F _ u).2
          have hi := (inputs_subset_used hp).trans hF
          simpa [Position.inputs, hlast] using hi

theorem records_length_bound {N : Set ℕ} (h : Position.LegalHistory N)
    (F : Finset ℕ) (hF : used h ⊆ F) :
    (h.val.map Position.lastMove).length ≤ 2 * F.card + 1 := by
  have hlen := length_bound h
  have hcard := Finset.card_le_card hF
  have hphase : h.position.phase ≤ 1 := by
    unfold Position.phase
    split <;> omega
  rw [List.length_map]
  omega

theorem finite_bounded_lists {A : Type*} (S : Finset A) (L : ℕ) :
    {xs : List A | xs.length ≤ L ∧ ∀ x ∈ xs, x ∈ S}.Finite := by
  classical
  have hf := (List.finite_length_le (↑S : Type _) L).image (List.map Subtype.val)
  apply hf.subset
  intro xs hxs
  let ys : List (↑S : Type _) := xs.attach.map fun x => ⟨x.val, hxs.2 x.val x.property⟩
  refine ⟨ys, ?_, ?_⟩
  · simpa [ys] using hxs.1
  · simp [ys, List.map_map]

/-- Legal histories over a finite numerical set are finite once the
current pending request size is bounded. All earlier request sizes and
the total history length have been proved bounded above. -/
theorem finite_histories (N : Set ℕ) (F : Finset ℕ) (q : ℕ) :
    {h : Position.LegalHistory N | used h ⊆ F ∧ h.position.pendingSize ≤ q}.Finite := by
  let A := alphabet F (max F.card q)
  let L := 2 * F.card + 1
  have hf := finite_bounded_lists A L
  have hp := hf.preimage (f := fun h : Position.LegalHistory N => h.val.map Position.lastMove)
    (fun _ _ _ _ heq => records_injective N heq)
  apply hp.subset
  intro h hh
  exact ⟨records_length_bound h F hh.1, records_mem_alphabet h F q hh.1 hh.2⟩

noncomputable def bound (N : Set ℕ) (b : Position.LegalHistory N → ℕ)
    (F : Finset ℕ) (q : ℕ) : ℕ :=
  max (F.sup id) ((finite_histories N F q).toFinset.sup b) + 1

theorem lt_bound_of_mem (N : Set ℕ) (b : Position.LegalHistory N → ℕ)
    (F : Finset ℕ) (q : ℕ) {x : ℕ} (hx : x ∈ F) : x < bound N b F q := by
  exact (Finset.le_sup (f := id) hx).trans_lt
    ((le_max_left _ _).trans_lt (Nat.lt_succ_self _))

theorem history_lt_bound (N : Set ℕ) (b : Position.LegalHistory N → ℕ)
    (F : Finset ℕ) (q : ℕ) (h : Position.LegalHistory N)
    (hF : used h ⊆ F) (hq : h.position.pendingSize ≤ q) : b h < bound N b F q := by
  have hh : h ∈ (finite_histories N F q).toFinset :=
    (finite_histories N F q).mem_toFinset.mpr ⟨hF, hq⟩
  exact (Finset.le_sup (f := b) hh).trans_lt
    ((le_max_right _ _).trans_lt (Nat.lt_succ_self _))

/-- This is the bound needed immediately before the first retained
input of a retrospectively replayed response. -/
theorem request_lt_bound (N : Set ℕ) (b : Position.LegalHistory N → ℕ)
    (F : Finset ℕ) (q : ℕ) (h : Position.LegalHistory N) (mode : Bool) (r : Request)
    (hr : Position.Next N (h.position.request mode r) h.position)
    (hF : used h ⊆ F) (hq : r.size ≤ q) :
    b (h.append (h.position.request mode r) hr) < bound N b F q := by
  apply history_lt_bound
  · simpa [Position.inputs, Position.request] using hF
  · simpa [Position.pendingSize, Position.request] using hq

#print axioms length_bound
#print axioms requestSize_bound
#print axioms request_lt_bound

end ReplayBudget

end Erdos591.Positive.Game

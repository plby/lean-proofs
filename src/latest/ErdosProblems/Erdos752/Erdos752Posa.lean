import ErdosProblems.Erdos752.Erdos752Moore

/-!
# A DFS long-path lemma for Erdős problem 752

The proof records the usual depth-first-search partition.  At every time the
vertices are partitioned into finished vertices, the active stack, and unseen
vertices; no edge joins a finished vertex to an unseen vertex.  At the first
time that exactly `m` vertices are finished, their external boundary is
therefore contained in the active stack.
-/

namespace Erdos752

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace DFS

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The three mutable pieces of a depth-first search.  The head of `stack` is
the active endpoint. -/
structure State (W : Type u) where
  done : Finset W
  stack : List W
  unseen : Finset W

namespace State

/-- The invariants of the standard depth-first-search stack. -/
structure Valid (s : State V) : Prop where
  stack_nodup : s.stack.Nodup
  done_not_stack : ∀ ⦃x⦄, x ∈ s.done → x ∉ s.stack
  done_not_unseen : ∀ ⦃x⦄, x ∈ s.done → x ∉ s.unseen
  stack_not_unseen : ∀ ⦃x⦄, x ∈ s.stack → x ∉ s.unseen
  cover : ∀ x, x ∈ s.done ∨ x ∈ s.stack ∨ x ∈ s.unseen
  stack_chain : s.stack.IsChain G.Adj
  done_not_adj_unseen : ∀ ⦃x⦄, x ∈ s.done → ∀ ⦃y⦄, y ∈ s.unseen → ¬G.Adj x y

/-- Initially every vertex is unseen. -/
def initial : State V where
  done := ∅
  stack := []
  unseen := Finset.univ

lemma initial_valid : (initial : State V).Valid G := by
  constructor <;> simp [initial]

/-- Move an unseen vertex to the head of the active stack. -/
def push (s : State V) (x : V) : State V where
  done := s.done
  stack := x :: s.stack
  unseen := s.unseen.erase x

/-- Finish the active vertex. -/
def pop (s : State V) (x : V) (tail : List V) : State V where
  done := insert x s.done
  stack := tail
  unseen := s.unseen

lemma push_valid {s : State V} (hs : s.Valid G) {x : V} (hx : x ∈ s.unseen)
    (hchain : (x :: s.stack).IsChain G.Adj) : (s.push x).Valid G := by
  constructor
  · simp only [push, List.nodup_cons]
    exact ⟨fun hxs ↦ hs.stack_not_unseen hxs hx, hs.stack_nodup⟩
  · intro y hy
    simp only [push, List.mem_cons]
    exact fun h ↦ h.elim (fun hxy ↦ hs.done_not_unseen hy (hxy ▸ hx))
      (hs.done_not_stack hy)
  · intro y hy
    simp only [push, Finset.mem_erase]
    exact fun h ↦ hs.done_not_unseen hy h.2
  · intro y hy
    change y ∈ x :: s.stack at hy
    intro hyerase
    have hyx : y ≠ x := (Finset.mem_erase.mp hyerase).1
    have hyu : y ∈ s.unseen := (Finset.mem_erase.mp hyerase).2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hyx rfl
    · exact hs.stack_not_unseen hy hyu
  · intro y
    rcases hs.cover y with hy | hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inl (by simp [push, hy]))
    · by_cases hxy : y = x
      · exact Or.inr (Or.inl (by simp [push, hxy]))
      · exact Or.inr (Or.inr (by simp [push, hxy, hy]))
  · exact hchain
  · intro y hy z hz
    apply hs.done_not_adj_unseen hy
    exact (Finset.mem_erase.mp hz).2

lemma pop_valid {s : State V} (hs : s.Valid G) {x : V} {tail : List V}
    (hstack : s.stack = x :: tail)
    (hclosed : ∀ y ∈ s.unseen, ¬G.Adj x y) : (s.pop x tail).Valid G := by
  have hx_stack : x ∈ s.stack := by simp [hstack]
  have hx_unseen : x ∉ s.unseen := hs.stack_not_unseen hx_stack
  have hn : (x :: tail).Nodup := by simpa [hstack] using hs.stack_nodup
  constructor
  · simpa [pop, hstack] using hs.stack_nodup.tail
  · intro y hy
    simp only [pop, Finset.mem_insert] at hy
    rcases hy with hyx | hy
    · exact hyx ▸ hn.notMem
    · have := hs.done_not_stack hy
      exact (by simpa [hstack] using this : y ≠ x ∧ y ∉ tail).2
  · intro y hy
    simp only [pop, Finset.mem_insert] at hy
    change y ∉ s.unseen
    rcases hy with rfl | hy
    · exact hx_unseen
    · exact hs.done_not_unseen hy
  · intro y hy
    change y ∈ tail at hy
    apply hs.stack_not_unseen
    rw [hstack]
    exact List.mem_cons_of_mem x hy
  · intro y
    rcases hs.cover y with hy | hy | hy
    · exact Or.inl (by simp [pop, hy])
    · rw [hstack] at hy
      simp only [List.mem_cons] at hy
      exact hy.elim (fun h ↦ Or.inl (by simp [pop, h]))
        (fun h ↦ Or.inr (Or.inl (by simpa [pop] using h)))
    · exact Or.inr (Or.inr (by simpa [pop] using hy))
  · simpa [hstack, pop] using hs.stack_chain.tail
  · intro y hy z hz
    simp only [pop, Finset.mem_insert] at hy
    exact hy.elim (fun h ↦ h ▸ hclosed z hz)
      (fun hy ↦ hs.done_not_adj_unseen hy hz)

/-- One deterministic DFS transition.  Choice is used only to select an
unseen neighbor (or a new component root). -/
noncomputable def next (s : State V) : State V := by
  classical
  match hstack : s.stack with
  | [] =>
      if h : s.unseen.Nonempty then
        exact s.push h.choose
      else
        exact s
  | x :: tail =>
      if h : ∃ y ∈ s.unseen, G.Adj x y then
        exact s.push h.choose
      else
        exact s.pop x tail

lemma next_valid {s : State V} (hs : s.Valid G) : (s.next G).Valid G := by
  classical
  unfold next
  split
  next hstack =>
    split
    next h =>
      apply push_valid G hs h.choose_spec
      simp [hstack]
    next => exact hs
  next x tail hstack =>
    split
    next h =>
      apply push_valid G hs h.choose_spec.1
      rw [hstack]
      exact .cons_cons h.choose_spec.2.symm (by rw [← hstack]; exact hs.stack_chain)
    next h =>
      apply pop_valid G hs hstack
      intro y hy hadj
      exact h ⟨y, hy, hadj⟩

/-- The number of remaining elementary DFS transitions. -/
def potential (s : State V) : ℕ := 2 * s.unseen.card + s.stack.length

lemma potential_next {s : State V} (hs : s.Valid G) (hpos : 0 < s.potential) :
    (s.next G).potential = s.potential - 1 := by
  classical
  simp only [potential] at hpos ⊢
  unfold next
  split
  next hstack =>
    split
    next h =>
      have hc := Finset.card_erase_of_mem h.choose_spec
      have hcardpos : 0 < s.unseen.card := Finset.card_pos.mpr ⟨h.choose, h.choose_spec⟩
      simp only [potential, push, List.length_cons]
      rw [hc]
      omega
    next h =>
      exfalso
      simp only [potential, hstack, List.length_nil, add_zero] at hpos
      have : s.unseen = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [this] at hpos
  next x tail hstack =>
    split
    next h =>
      have hc := Finset.card_erase_of_mem h.choose_spec.1
      have hcardpos : 0 < s.unseen.card :=
        Finset.card_pos.mpr ⟨h.choose, h.choose_spec.1⟩
      simp only [potential, push, List.length_cons]
      rw [hc]
      omega
    next =>
      simp only [potential, pop, hstack, List.length_cons]
      omega

lemma done_card_next_bounds (s : State V) :
    s.done.card ≤ (s.next G).done.card ∧ (s.next G).done.card ≤ s.done.card + 1 := by
  classical
  unfold next
  split <;> split
  · simp [push]
  · simp
  · simp [push]
  · constructor
    · exact Finset.card_le_card (Finset.subset_insert _ _)
    · exact Finset.card_insert_le _ _

lemma valid_iterate (s : State V) (hs : s.Valid G) (n : ℕ) :
    ((next G)^[n] s).Valid G := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact next_valid G ih

lemma potential_iterate_self_eq_zero (s : State V) (hs : s.Valid G) :
    (((next G)^[s.potential] s).potential) = 0 := by
  generalize hn : s.potential = n
  induction n generalizing s with
  | zero => simpa [hn]
  | succ n ih =>
      have hpos : 0 < s.potential := by omega
      have hp := potential_next G hs hpos
      have hs' := next_valid G hs
      rw [Function.iterate_succ_apply]
      apply ih (next G s) hs'
      omega

lemma card_done_of_potential_eq_zero {s : State V} (hs : s.Valid G)
    (hp : s.potential = 0) : s.done.card = Fintype.card V := by
  have hu : s.unseen = ∅ := by
    apply Finset.card_eq_zero.mp
    simp only [potential] at hp
    omega
  have hstack : s.stack = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simp only [potential] at hp
    omega
  have hdone : s.done = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rcases hs.cover x with hx | hx | hx
    · exact hx
    · simpa [hstack] using hx
    · simpa [hu] using hx
  simp [hdone]

lemma exists_iterate_done_card_eq (s : State V) (hs : s.Valid G) (m t : ℕ)
    (hsm : s.done.card ≤ m)
    (hfinal : m ≤ (((next G)^[t] s).done.card)) :
    ∃ j ≤ t, (((next G)^[j] s).done.card) = m := by
  induction t generalizing s with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      simpa using Nat.le_antisymm hsm hfinal
  | succ t ih =>
      by_cases hm : m ≤ s.done.card
      · exact ⟨0, Nat.zero_le _, Nat.le_antisymm hsm hm⟩
      · have hlt : s.done.card < m := Nat.lt_of_not_ge hm
        have hb := done_card_next_bounds G s
        have hsnext : (s.next G).done.card ≤ m := by omega
        have hfinal' : m ≤ (((next G)^[t] (s.next G)).done.card) := by
          simpa [Function.iterate_succ_apply] using hfinal
        obtain ⟨j, hjt, hj⟩ := ih (s.next G) (next_valid G hs) hsnext hfinal'
        exact ⟨j + 1, by omega, by simpa [Function.iterate_succ_apply] using hj⟩

lemma exists_valid_state_done_card_eq (m : ℕ) (hm : m ≤ Fintype.card V) :
    ∃ s : State V, s.Valid G ∧ s.done.card = m := by
  let s₀ : State V := initial
  let t := s₀.potential
  have hs₀ : s₀.Valid G := initial_valid G
  have hp : (((next G)^[t] s₀).potential) = 0 :=
    potential_iterate_self_eq_zero G s₀ hs₀
  have hvfinal := valid_iterate G s₀ hs₀ t
  have hcard : (((next G)^[t] s₀).done.card) = Fintype.card V :=
    card_done_of_potential_eq_zero G hvfinal hp
  obtain ⟨j, hjt, hj⟩ := exists_iterate_done_card_eq G s₀ hs₀ m t (by simp [s₀, initial])
    (by simpa [hcard] using hm)
  exact ⟨(next G)^[j] s₀, valid_iterate G s₀ hs₀ j, hj⟩

lemma externalBoundary_done_subset_stack {s : State V} (hs : s.Valid G) :
    externalBoundary G s.done ⊆ s.stack.toFinset := by
  intro y hy
  rw [mem_externalBoundary] at hy
  rcases hy with ⟨hy_done, x, hx, hxy⟩
  rcases hs.cover y with hy | hy | hy
  · exact (hy_done hy).elim
  · simpa using hy
  · exact (hs.done_not_adj_unseen hx hy hxy).elim

end State

end DFS

/-- **DFS long-path lemma.** If every `m`-vertex set has more than `2m`
external neighbors, then the graph contains a simple path with at least `2m`
edges. -/
theorem exists_long_path_of_externalBoundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : m ≤ Fintype.card V)
    (hexpand : ∀ X : Finset V, X.card = m → 2 * m < (externalBoundary G X).card) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ 2 * m ≤ p.length := by
  obtain ⟨s, hs, hcard⟩ := DFS.State.exists_valid_state_done_card_eq G m hm
  have hboundary : 2 * m < (externalBoundary G s.done).card := hexpand s.done hcard
  have hsubset := DFS.State.externalBoundary_done_subset_stack G hs
  have hstack : 2 * m < s.stack.length := by
    have hle := Finset.card_le_card hsubset
    simpa [List.toFinset_card_of_nodup hs.stack_nodup] using hboundary.trans_le hle
  have hne : s.stack ≠ [] := by
    intro h
    simp [h] at hstack
  let p := SimpleGraph.Walk.ofSupport s.stack hne hs.stack_chain
  refine ⟨s.stack.head hne, s.stack.getLast hne, p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simpa [p, SimpleGraph.Walk.support_ofSupport] using hs.stack_nodup
  · simp only [p, SimpleGraph.Walk.length_ofSupport]
    omega

end Erdos752

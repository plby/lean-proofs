/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.SafeLinkProposition

/-!
# Erdős Problem 599: the finite and countable extension step

This file formalizes the countable branch of the extension clause in
Aharoni--Berger, Theorem 9.2.  Starting with a linkage `F` of the sources
outside a countable set `A0`, we maintain a FIFO queue.  At every nontrivial
stage the head of the queue is linked by Theorem 6.1 in the web obtained by
deleting all paths chosen earlier.  The finitely many members of `F` met by
the new path have their initial vertices appended to the queue.  A FIFO
argument shows that every appended vertex is eventually processed.

The union of the safely chosen paths is therefore closed under displacement
of members of `F`.  It can be united with the members of `F` which avoid that
union, giving a linkage of the whole source.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- The precise input from Aharoni--Berger Theorem 6.1.  It is kept as a
named proposition so the queue construction can be checked independently
of the long proof of the safe-link theorem. -/
def SafeLinkRule (V : Type u) : Prop :=
  ∀ (G : DWeb V) (a : V), G.IsUnhindered → a ∈ G.source →
    G.HasSafeTargetPath a

/-- Proposition 6.3 supplies exactly the safe one-point linkage rule used
by the countable queue construction. -/
theorem safeLinkRule_of_proposition63
    (h63 : SafeLink.Proposition63 V) : SafeLinkRule V := by
  intro G a hG ha
  exact SafeLink.exists_safeTargetPath_of_boundaryWaves h63 G hG ha

namespace CountableExtension

variable (G : DWeb V)

/-- Members of the old linkage which meet a newly chosen finite path. -/
def displacedPaths (F : Set G.DPath)
    (p : DirectedPath.FinitePath G.graph) : Set G.DPath :=
  {q | q ∈ F ∧ (q.support ∩ p.support).Nonempty}

theorem displacedPaths_finite {F : Set G.DPath}
    (hF : G.IsWarp F) (p : DirectedPath.FinitePath G.graph) :
    (displacedPaths G F p).Finite := by
  apply FamilyTools.finite_of_pairwiseDisjoint_of_meets
    (I := displacedPaths G F p) (F := DirectedPath.Path.support)
    (S := p.support)
  · intro q hq r hr hqr
    exact hF hq.1 hr.1 hqr
  · exact p.support_finite
  · intro q hq
    obtain ⟨x, hxq, hxp⟩ := hq.2
    exact ⟨x, hxp, hxq⟩

/-- A finite FIFO payload containing the initial vertex of every displaced
member of `F`. -/
def displacedInitials (F : Set G.DPath) (hF : G.IsWarp F)
    (p : DirectedPath.FinitePath G.graph) : List V :=
  ((displacedPaths_finite G hF p).toFinset.toList.map
    DirectedPath.Path.initial)

theorem mem_displacedInitials_iff {F : Set G.DPath}
    (hF : G.IsWarp F) (p : DirectedPath.FinitePath G.graph) (a : V) :
    a ∈ displacedInitials G F hF p ↔
      ∃ q ∈ F, (q.support ∩ p.support).Nonempty ∧ q.initial = a := by
  classical
  simp only [displacedInitials, List.mem_map, Finset.mem_toList,
    Set.Finite.mem_toFinset, displacedPaths]
  constructor
  · rintro ⟨q, ⟨hqF, hqmeet⟩, rfl⟩
    exact ⟨q, hqF, hqmeet, rfl⟩
  · rintro ⟨q, hqF, hqmeet, rfl⟩
    exact ⟨q, ⟨hqF, hqmeet⟩, rfl⟩

/-- Exact endpoint data retained for every safely chosen path. -/
def IsChosenPath (p : G.DPath) : Prop :=
  ∃ q : DirectedPath.FinitePath G.graph,
    p = .inl q ∧ q.start ∈ G.source ∧ q.finish ∈ G.target ∧
      q.support ∩ G.source = {q.start} ∧
      q.support ∩ G.target = {q.finish}

/-- A finite stage of the fair safe-link recursion. -/
structure QueueState (F : Set G.DPath) where
  deleted : Set V
  queue : List V
  chosen : Set G.DPath
  unhindered : (G.delete deleted).IsUnhindered
  vertexSet_eq : G.vertexSet chosen = deleted
  warp : G.IsWarp chosen
  finiteCharacter : G.HasFiniteCharacter chosen
  chosen_spec : ∀ p ∈ chosen, IsChosenPath G p
  queue_source : ∀ a ∈ queue, a ∈ G.source
  old_pending : ∀ p ∈ F, (p.support ∩ deleted).Nonempty →
    p.initial ∈ deleted ∨ p.initial ∈ queue

/-- The concrete result of applying the safe-link theorem to the head of a
queue.  The path has already been lifted from the current deleted web to the
original web. -/
structure SafeChoice (F : Set G.DPath) (s : QueueState G F) (a : V) where
  path : DirectedPath.FinitePath G.graph
  start_eq : path.start = a
  start_source : path.start ∈ G.source
  finish_target : path.finish ∈ G.target
  source_pure : path.support ∩ G.source = {path.start}
  target_pure : path.support ∩ G.target = {path.finish}
  avoids : Disjoint path.support s.deleted
  next_unhindered :
    (G.delete (s.deleted ∪ path.support)).IsUnhindered

/-- Apply Theorem 6.1 in the normalized current deleted web, then lift the
resulting path to the original graph.  Normalization is used only to obtain
endpoint purity; safety is transported back by `SafeLink`'s normalization
lemma. -/
noncomputable def chooseSafe
    (safeLink : SafeLinkRule V) {F : Set G.DPath}
    (s : QueueState G F) {a : V} (haSource : a ∈ G.source)
    (haFresh : a ∉ s.deleted) : SafeChoice G F s a := by
  let H := G.delete s.deleted
  have haH : a ∈ H.source := ⟨haSource, haFresh⟩
  have haNorm : a ∈ H.normalized.source := haH
  have hsafeNorm : H.normalized.HasSafeTargetPath a :=
    safeLink H.normalized a s.unhindered.normalized haNorm
  let hex : ∃ q : DirectedPath.FinitePath H.graph,
      H.IsSafeTargetPath a q ∧
      q.support ∩ H.source ⊆ {q.start} ∧
      q.support ∩ H.target ⊆ {q.finish} :=
    Erdos599.SafeLink.exists_endpointPure_safeTargetPath_of_normalized H hsafeNorm
  let q : DirectedPath.FinitePath H.graph := Classical.choose hex
  have hq := Classical.choose_spec hex
  have hqSafe : H.IsSafeTargetPath a q := hq.1
  have hqSource : q.support ∩ H.source ⊆ {q.start} := hq.2.1
  have hqTarget : q.support ∩ H.target ⊆ {q.finish} := hq.2.2
  dsimp only [H] at q hqSafe hqSource hqTarget
  let p : DirectedPath.FinitePath G.graph :=
    q.lift (fun {_ _} h ↦ G.delete_adj_imp h)
  have hpSupport : p.support = q.support := by simp [p]
  have hpAvoid : Disjoint p.support s.deleted := by
    change Disjoint (G.liftDeletePath s.deleted (.inl q)).support s.deleted
    apply G.liftDeletePath_avoids s.deleted (.inl q)
    change q.start ∉ s.deleted
    rw [hqSafe.1]
    exact haFresh
  have hpSourcePure : p.support ∩ G.source = {p.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxA⟩
      have hxFresh : x ∉ s.deleted :=
        fun hx ↦ Set.disjoint_left.1 hpAvoid hxp hx
      have hxCurrent : x ∈ q.support ∩ H.source := by
        exact ⟨by simpa [hpSupport] using hxp, hxA, hxFresh⟩
      have hx := hqSource hxCurrent
      simpa only [p, DirectedPath.FinitePath.lift] using hx
    · rintro x hx
      have hxEq : x = p.start := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.start_mem_support, ?_⟩
      simpa only [p, DirectedPath.FinitePath.lift, hqSafe.1] using haSource
  have hpTargetPure : p.support ∩ G.target = {p.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxB⟩
      have hxFresh : x ∉ s.deleted :=
        fun hx ↦ Set.disjoint_left.1 hpAvoid hxp hx
      have hxCurrent : x ∈ q.support ∩ H.target := by
        exact ⟨by simpa [hpSupport] using hxp, hxB, hxFresh⟩
      have hx := hqTarget hxCurrent
      simpa only [p, DirectedPath.FinitePath.lift] using hx
    · rintro x hx
      have hxEq : x = p.finish := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨p.finish_mem_support, ?_⟩
      simpa only [p, DirectedPath.FinitePath.lift] using hqSafe.2.1.1
  refine
    { path := p
      start_eq := by simpa only [p, DirectedPath.FinitePath.lift] using hqSafe.1
      start_source := by
        simpa only [p, DirectedPath.FinitePath.lift, hqSafe.1] using haSource
      finish_target := by
        simpa only [p, DirectedPath.FinitePath.lift] using hqSafe.2.1.1
      source_pure := hpSourcePure
      target_pure := hpTargetPure
      avoids := hpAvoid
      next_unhindered := ?_ }
  rw [← G.delete_delete]
  simpa [H, hpSupport] using hqSafe.2.2

/-- A path chosen at one stage, viewed as a member of the ambient concrete
path type, satisfies the retained endpoint specification. -/
theorem chosenPath_of_safeChoice {F : Set G.DPath}
    {s : QueueState G F} {a : V} (c : SafeChoice G F s a) :
    IsChosenPath G (.inl c.path) := by
  exact ⟨c.path, rfl, c.start_source, c.finish_target,
    c.source_pure, c.target_pure⟩

/-- Every vertex already waiting in the queue is either the popped head or
remains in the tail. -/
private theorem mem_head_or_tail {a x : V} {tail : List V}
    (hx : x ∈ a :: tail) : x = a ∨ x ∈ tail := by
  simpa only [List.mem_cons] using hx

/-- Extend a state by the safe path chosen for its fresh queue head. -/
noncomputable def extendFresh
    (safeLink : SafeLinkRule V)
    {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (s : QueueState G F) (a : V) (tail : List V)
    (hqueue : s.queue = a :: tail) (base : V) (hbase : base ∈ G.source)
    (haFresh : a ∉ s.deleted) : QueueState G F := by
  classical
  have haSource : a ∈ G.source := s.queue_source a (hqueue.symm ▸ List.mem_cons_self)
  let c := chooseSafe G safeLink s haSource haFresh
  let r : G.DPath := .inl c.path
  let payload := displacedInitials G F hF.isWarp c.path ++ [base]
  refine
    { deleted := s.deleted ∪ c.path.support
      queue := tail ++ payload
      chosen := insert r s.chosen
      unhindered := c.next_unhindered
      vertexSet_eq := ?_
      warp := ?_
      finiteCharacter := ?_
      chosen_spec := ?_
      queue_source := ?_
      old_pending := ?_ }
  · ext x
    simp only [DWeb.vertexSet, Set.mem_setOf_eq, Set.mem_union,
      Set.mem_insert_iff]
    constructor
    · rintro ⟨p, rfl | hp, hxp⟩
      · exact Or.inr hxp
      · left
        rw [← s.vertexSet_eq]
        exact ⟨p, hp, hxp⟩
    · rintro (hx | hx)
      · rw [← s.vertexSet_eq] at hx
        obtain ⟨p, hp, hxp⟩ := hx
        exact ⟨p, Or.inr hp, hxp⟩
      · exact ⟨r, Or.inl rfl, hx⟩
  · intro p hp q hq hpq
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · exact (hpq rfl).elim
      · apply Set.disjoint_left.2
        intro x hxc hxq
        apply Set.disjoint_left.1 c.avoids hxc
        rw [← s.vertexSet_eq]
        exact ⟨q, hq, hxq⟩
    · rcases hq with rfl | hq
      · apply Set.disjoint_left.2
        intro x hxp hxc
        apply Set.disjoint_left.1 c.avoids hxc
        rw [← s.vertexSet_eq]
        exact ⟨p, hp, hxp⟩
      · exact s.warp hp hq hpq
  · intro p hp
    rcases hp with rfl | hp
    · exact ⟨c.path, rfl⟩
    · exact s.finiteCharacter hp
  · intro p hp
    rcases hp with rfl | hp
    · exact chosenPath_of_safeChoice G c
    · exact s.chosen_spec p hp
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hxTail | hxPayload
    · exact s.queue_source x (by
        rw [hqueue]
        exact List.mem_cons_of_mem a hxTail)
    · rw [List.mem_append] at hxPayload
      rcases hxPayload with hxDisplaced | hxBase
      · obtain ⟨q, hqF, _hqmeet, hqinit⟩ :=
          (mem_displacedInitials_iff G hF.isWarp c.path x).1 hxDisplaced
        have hxInit : q.initial ∈ G.initialSet F := ⟨q, hqF, rfl⟩
        rw [hF.initialSet_eq] at hxInit
        exact hqinit ▸ hxInit.1
      · have hxEq : x = base := by simpa only [List.mem_singleton] using hxBase
        exact hxEq ▸ hbase
  · intro p hpF hpMeet
    by_cases hpOld : (p.support ∩ s.deleted).Nonempty
    · rcases s.old_pending p hpF hpOld with hpDeleted | hpQueue
      · exact Or.inl (Or.inl hpDeleted)
      · have hpQueue' : p.initial ∈ a :: tail := by
          rw [← hqueue]
          exact hpQueue
        rcases mem_head_or_tail hpQueue' with hpHead | hpTail
        · left
          right
          have hpEq : p.initial = c.path.start := hpHead.trans c.start_eq.symm
          exact hpEq ▸ c.path.start_mem_support
        · right
          apply List.mem_append_left payload
          exact hpTail
    · have hpNew : (p.support ∩ c.path.support).Nonempty := by
        obtain ⟨x, hxp, hxOld | hxNew⟩ := hpMeet
        · exact False.elim (hpOld ⟨x, hxp, hxOld⟩)
        · exact ⟨x, hxp, hxNew⟩
      right
      apply List.mem_append_right tail
      apply List.mem_append_left [base]
      exact (mem_displacedInitials_iff G hF.isWarp c.path p.initial).2
        ⟨p, hpF, hpNew, rfl⟩

/-- When the queue is empty, append the next item of the fixed enumeration.
No graph data changes. -/
def enqueueEmpty {F : Set G.DPath} (s : QueueState G F)
    (hqueue : s.queue = []) (base : V) (hbase : base ∈ G.source) :
    QueueState G F where
  deleted := s.deleted
  queue := [base]
  chosen := s.chosen
  unhindered := s.unhindered
  vertexSet_eq := s.vertexSet_eq
  warp := s.warp
  finiteCharacter := s.finiteCharacter
  chosen_spec := s.chosen_spec
  queue_source := by
    intro x hx
    have hxEq : x = base := by simpa only [List.mem_singleton] using hx
    exact hxEq ▸ hbase
  old_pending := by
    intro p hpF hpMeet
    rcases s.old_pending p hpF hpMeet with hpDeleted | hpQueue
    · exact Or.inl hpDeleted
    · rw [hqueue] at hpQueue
      simp at hpQueue

/-- Pop a queue head which was already deleted.  It remains recorded as
processed, and all later queue elements retain their order. -/
def dropDeleted {F : Set G.DPath} (s : QueueState G F)
    (a : V) (tail : List V) (hqueue : s.queue = a :: tail)
    (haDeleted : a ∈ s.deleted) (base : V) (hbase : base ∈ G.source) :
    QueueState G F where
  deleted := s.deleted
  queue := tail ++ [base]
  chosen := s.chosen
  unhindered := s.unhindered
  vertexSet_eq := s.vertexSet_eq
  warp := s.warp
  finiteCharacter := s.finiteCharacter
  chosen_spec := s.chosen_spec
  queue_source := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hxTail | hxBase
    · apply s.queue_source x
      rw [hqueue]
      exact List.mem_cons_of_mem a hxTail
    · have hxEq : x = base := by simpa only [List.mem_singleton] using hxBase
      exact hxEq ▸ hbase
  old_pending := by
    intro p hpF hpMeet
    rcases s.old_pending p hpF hpMeet with hpDeleted | hpQueue
    · exact Or.inl hpDeleted
    · have hpQueue' : p.initial ∈ a :: tail := by
        rw [← hqueue]
        exact hpQueue
      rcases mem_head_or_tail hpQueue' with hpHead | hpTail
      · exact Or.inl (hpHead ▸ haDeleted)
      · exact Or.inr (List.mem_append_left [base] hpTail)

/-- The observable specification of one FIFO transition. -/
def SuccessorSpec {F : Set G.DPath} (s t : QueueState G F)
    (base : V) : Prop :=
  s.deleted ⊆ t.deleted ∧
    s.chosen ⊆ t.chosen ∧
    base ∈ t.queue ∧
    ∀ a tail, s.queue = a :: tail →
      ∃ added, t.queue = tail ++ added ∧ a ∈ t.deleted

/-- A stage satisfying the FIFO successor specification always exists. -/
theorem exists_successor
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (base : V) (hbase : base ∈ G.source) (s : QueueState G F) :
    ∃ t : QueueState G F, SuccessorSpec G s t base := by
  classical
  cases hqueue : s.queue with
  | nil =>
      let t := enqueueEmpty G s hqueue base hbase
      refine ⟨t, Set.Subset.rfl, Set.Subset.rfl, ?_, ?_⟩
      · change base ∈ [base]
        simp
      · intro a tail hcons
        rw [hqueue] at hcons
        simp at hcons
  | cons a tail =>
      by_cases ha : a ∈ s.deleted
      · let t := dropDeleted G s a tail hqueue ha base hbase
        refine ⟨t, Set.Subset.rfl, Set.Subset.rfl, ?_, ?_⟩
        · apply List.mem_append_right tail
          simp
        · intro b rest hb
          have heq : b = a ∧ rest = tail := List.cons.inj (hb.symm.trans hqueue)
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨[base], rfl, ha⟩
      · let t := extendFresh G safeLink hF s a tail hqueue base hbase ha
        let c := chooseSafe G safeLink s
          (s.queue_source a (hqueue.symm ▸ List.mem_cons_self)) ha
        refine ⟨t, Set.subset_union_left,
          Set.subset_insert (Sum.inl c.path) s.chosen, ?_, ?_⟩
        · apply List.mem_append_right tail
          apply List.mem_append_right (displacedInitials G F hF.isWarp c.path)
          simp
        · intro b rest hb
          have heq : b = a ∧ rest = tail := List.cons.inj (hb.symm.trans hqueue)
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨displacedInitials G F hF.isWarp c.path ++ [base], rfl, ?_⟩
          change b ∈ s.deleted ∪
            (chooseSafe G safeLink s
              (s.queue_source b (hqueue.symm ▸ List.mem_cons_self)) ha).path.support
          right
          let c' := chooseSafe G safeLink s
            (s.queue_source b (hqueue.symm ▸ List.mem_cons_self)) ha
          change b ∈ c'.path.support
          simpa only [c'.start_eq] using c'.path.start_mem_support

/-- One FIFO stage, selected from the proved nonempty class of valid
successors. -/
noncomputable def nextState
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (base : V) (hbase : base ∈ G.source) (s : QueueState G F) :
    QueueState G F :=
  Classical.choose (exists_successor G safeLink hF base hbase s)

theorem nextState_spec
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (base : V) (hbase : base ∈ G.source) (s : QueueState G F) :
    SuccessorSpec G s (nextState G safeLink hF base hbase s) base :=
  Classical.choose_spec (exists_successor G safeLink hF base hbase s)

theorem deleted_subset_nextState
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (base : V) (hbase : base ∈ G.source) (s : QueueState G F) :
    s.deleted ⊆ (nextState G safeLink hF base hbase s).deleted :=
  (nextState_spec G safeLink hF base hbase s).1

theorem chosen_subset_nextState
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (base : V) (hbase : base ∈ G.source) (s : QueueState G F) :
    s.chosen ⊆ (nextState G safeLink hF base hbase s).chosen :=
  (nextState_spec G safeLink hF base hbase s).2.1

/-- Every nonempty FIFO transition has exactly the form required by the
generic fairness lemma: remove the head, append a finite payload, and record
the head in the next deletion set. -/
theorem nextState_queue_of_cons
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (base : V) (hbase : base ∈ G.source) (s : QueueState G F)
    (a : V) (tail : List V) (hqueue : s.queue = a :: tail) :
    ∃ added,
      (nextState G safeLink hF base hbase s).queue = tail ++ added ∧
      a ∈ (nextState G safeLink hF base hbase s).deleted :=
  (nextState_spec G safeLink hF base hbase s).2.2.2 a tail hqueue

/-- The initial stage contains no chosen paths and an empty queue. -/
def initialState (F : Set G.DPath) (hG : G.IsUnhindered) :
    QueueState G F where
  deleted := ∅
  queue := []
  chosen := ∅
  unhindered := by simpa using hG
  vertexSet_eq := by ext x; simp [DWeb.vertexSet]
  warp := by intro p hp; exact hp.elim
  finiteCharacter := by intro p hp; exact hp.elim
  chosen_spec := by intro p hp; exact hp.elim
  queue_source := by intro a ha; simp at ha
  old_pending := by intro p hp hmeet; simpa using hmeet

/-! ## Fairness of the FIFO schedule -/

/-- In a FIFO process which removes the head at every nonempty step and
records it at the next stage, every queued item is eventually recorded.
The appended payload may vary with the stage, but is finite because it is
a list; newly appended items can therefore never overtake an old item. -/
theorem fifo_eventually_recorded
    {queue : ℕ → List V} {recorded : ℕ → Set V}
    (hstep : ∀ n a tail, queue n = a :: tail →
      ∃ added, queue (n + 1) = tail ++ added ∧
        a ∈ recorded (n + 1))
    {n : ℕ} {x : V} (hx : x ∈ queue n) :
    ∃ m, n ≤ m ∧ x ∈ recorded m := by
  obtain ⟨before, after, hqueue⟩ := List.mem_iff_append.1 hx
  induction before generalizing n after with
  | nil =>
      simp only [List.nil_append] at hqueue
      obtain ⟨added, _hnext, hxrec⟩ :=
        hstep n x after hqueue
      exact ⟨n + 1, Nat.le_succ n, hxrec⟩
  | cons a before ih =>
      rw [List.cons_append] at hqueue
      obtain ⟨added, hnext, _harec⟩ :=
        hstep n a (before ++ x :: after) hqueue
      have hnext' : queue (n + 1) =
          before ++ x :: (after ++ added) := by
        calc
          queue (n + 1) = (before ++ x :: after) ++ added := hnext
          _ = before ++ x :: (after ++ added) := by
            simp only [List.append_assoc, List.cons_append]
      have hxnext : x ∈ queue (n + 1) := by
        rw [hnext']
        simp
      obtain ⟨m, hm, hxrec⟩ := ih hxnext (after ++ added) hnext'
      exact ⟨m, (Nat.le_succ n).trans hm, hxrec⟩

/-! ## The countable recursion and its limit -/

/-- The states of the countable safe-link construction, driven by a fixed
source-valued enumeration. -/
noncomputable def stateSeq
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) : ℕ → QueueState G F
  | 0 => initialState G F hG
  | n + 1 => nextState G safeLink hF (e n) (he n)
      (stateSeq safeLink hF hG e he n)

@[simp] theorem stateSeq_zero
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    stateSeq G safeLink hF hG e he 0 = initialState G F hG := rfl

@[simp] theorem stateSeq_succ
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (n : ℕ) :
    stateSeq G safeLink hF hG e he (n + 1) =
      nextState G safeLink hF (e n) (he n)
        (stateSeq G safeLink hF hG e he n) := rfl

theorem stateSeq_deleted_mono
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    Monotone (fun n ↦ (stateSeq G safeLink hF hG e he n).deleted) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [stateSeq_succ]
  exact deleted_subset_nextState G safeLink hF (e n) (he n) _

theorem stateSeq_chosen_mono
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    Monotone (fun n ↦ (stateSeq G safeLink hF hG e he n).chosen) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [stateSeq_succ]
  exact chosen_subset_nextState G safeLink hF (e n) (he n) _

theorem stateSeq_queue_step
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (n : ℕ) (a : V)
    (tail : List V)
    (hq : (stateSeq G safeLink hF hG e he n).queue = a :: tail) :
    ∃ added,
      (stateSeq G safeLink hF hG e he (n + 1)).queue =
        tail ++ added ∧
      a ∈ (stateSeq G safeLink hF hG e he (n + 1)).deleted := by
  rw [stateSeq_succ]
  exact nextState_queue_of_cons G safeLink hF (e n) (he n) _ a tail hq

theorem stateSeq_base_queued
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (n : ℕ) :
    e n ∈ (stateSeq G safeLink hF hG e he (n + 1)).queue := by
  rw [stateSeq_succ]
  exact (nextState_spec G safeLink hF (e n) (he n) _).2.2.1

theorem stateSeq_queue_eventually_deleted
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) {n : ℕ} {a : V}
    (ha : a ∈ (stateSeq G safeLink hF hG e he n).queue) :
    ∃ m, n ≤ m ∧
      a ∈ (stateSeq G safeLink hF hG e he m).deleted := by
  apply fifo_eventually_recorded
    (stateSeq_queue_step G safeLink hF hG e he)
    ha

/-- All vertices and paths ever committed by the countable recursion. -/
def limitDeleted
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) : Set V :=
  ⋃ n, (stateSeq G safeLink hF hG e he n).deleted

def limitChosen
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) : Set G.DPath :=
  ⋃ n, (stateSeq G safeLink hF hG e he n).chosen

theorem vertexSet_limitChosen
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    G.vertexSet (limitChosen G safeLink hF hG e he) =
      limitDeleted G safeLink hF hG e he := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
    apply Set.mem_iUnion.2
    refine ⟨n, ?_⟩
    rw [← (stateSeq G safeLink hF hG e he n).vertexSet_eq]
    exact ⟨p, hpn, hxp⟩
  · intro hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    rw [← (stateSeq G safeLink hF hG e he n).vertexSet_eq] at hxn
    obtain ⟨p, hpn, hxp⟩ := hxn
    exact ⟨p, Set.mem_iUnion.2 ⟨n, hpn⟩, hxp⟩

theorem limitChosen_isWarp
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    G.IsWarp (limitChosen G safeLink hF hG e he) := by
  intro p hp q hq hpq
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
  obtain ⟨j, hqj⟩ := Set.mem_iUnion.1 hq
  rcases le_total i j with hij | hji
  · exact (stateSeq G safeLink hF hG e he j).warp
      ((stateSeq_chosen_mono G safeLink hF hG e he) hij hpi) hqj hpq
  · exact (stateSeq G safeLink hF hG e he i).warp hpi
      ((stateSeq_chosen_mono G safeLink hF hG e he) hji hqj) hpq

theorem limitChosen_finiteCharacter
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    G.HasFiniteCharacter (limitChosen G safeLink hF hG e he) := by
  intro p hp
  obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
  exact (stateSeq G safeLink hF hG e he n).finiteCharacter hpn

theorem limitChosen_spec
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) :
    ∀ p ∈ limitChosen G safeLink hF hG e he, IsChosenPath G p := by
  intro p hp
  obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
  exact (stateSeq G safeLink hF hG e he n).chosen_spec p hpn

theorem source_mem_initialSet_limitChosen_of_mem_limitDeleted
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) {a : V}
    (haSource : a ∈ G.source)
    (haDeleted : a ∈ limitDeleted G safeLink hF hG e he) :
    a ∈ G.initialSet (limitChosen G safeLink hF hG e he) := by
  have haVertex : a ∈ G.vertexSet (limitChosen G safeLink hF hG e he) := by
    rw [vertexSet_limitChosen G safeLink hF hG e he]
    exact haDeleted
  obtain ⟨p, hp, hap⟩ := haVertex
  obtain ⟨q, rfl, _hqStart, _hqFinish, hqSource, _hqTarget⟩ :=
    limitChosen_spec G safeLink hF hG e he p hp
  have haSingleton : a ∈ ({q.start} : Set V) := by
    rw [← hqSource]
    exact ⟨hap, haSource⟩
  have ha : a = q.start := Set.mem_singleton_iff.1 haSingleton
  exact ⟨Sum.inl q, hp, ha.symm⟩

theorem enumerated_mem_limitDeleted
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (n : ℕ) :
    e n ∈ limitDeleted G safeLink hF hG e he := by
  obtain ⟨m, _hm, hdel⟩ := stateSeq_queue_eventually_deleted
    G safeLink hF hG e he (stateSeq_base_queued G safeLink hF hG e he n)
  exact Set.mem_iUnion.2 ⟨m, hdel⟩

theorem old_initial_mem_limitDeleted_of_meets
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) {p : G.DPath} (hpF : p ∈ F)
    (hpMeet :
      (p.support ∩ limitDeleted G safeLink hF hG e he).Nonempty) :
    p.initial ∈ limitDeleted G safeLink hF hG e he := by
  obtain ⟨x, hxp, hxDeleted⟩ := hpMeet
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxDeleted
  have hpStageMeet :
      (p.support ∩ (stateSeq G safeLink hF hG e he n).deleted).Nonempty :=
    ⟨x, hxp, hxn⟩
  rcases (stateSeq G safeLink hF hG e he n).old_pending p hpF hpStageMeet with
    hpDeleted | hpQueue
  · exact Set.mem_iUnion.2 ⟨n, hpDeleted⟩
  · obtain ⟨m, _hnm, hpDeleted⟩ :=
      stateSeq_queue_eventually_deleted G safeLink hF hG e he hpQueue
    exact Set.mem_iUnion.2 ⟨m, hpDeleted⟩

/-- Old linkage paths untouched by the recursively chosen linkage. -/
def retainedOld
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) : Set G.DPath :=
  {p | p ∈ F ∧
    Disjoint p.support (limitDeleted G safeLink hF hG e he)}

/-- The final linkage: the paths selected by safe-link recursion, together
with exactly the old linkage paths which avoid all selected vertices. -/
def finalFamily
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) : Set G.DPath :=
  limitChosen G safeLink hF hG e he ∪
    retainedOld G safeLink hF hG e he

theorem designated_subset_limitDeleted
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (hcover : A₀ ⊆ Set.range e) :
    A₀ ⊆ limitDeleted G safeLink hF hG e he := by
  intro a ha
  obtain ⟨n, rfl⟩ := hcover ha
  exact enumerated_mem_limitDeleted G safeLink hF hG e he n

theorem limitChosen_isPathBetween
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) {p : G.DPath}
    (hp : p ∈ limitChosen G safeLink hF hG e he) :
    IsPathBetween G G.source G.target p := by
  obtain ⟨q, rfl, _hqSource, _hqTarget, hsource, htarget⟩ :=
    limitChosen_spec G safeLink hF hG e he p hp
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  simp only [Set.singleton_union]

theorem retainedOld_isPathBetween
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (hcover : A₀ ⊆ Set.range e)
    {p : G.DPath} (hp : p ∈ retainedOld G safeLink hF hG e he) :
    IsPathBetween G G.source G.target p := by
  have hA₀Deleted := designated_subset_limitDeleted
    G safeLink hF hG e he hcover
  have hdisA₀ : Disjoint p.support A₀ := hp.2.mono_right hA₀Deleted
  rcases hF.endpointPure p hp.1 with ⟨q, rfl, hends, hsource⟩
  refine ⟨q, rfl, ?_, ?_⟩
  · rw [← hends]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
    constructor
    · rintro ⟨hxs, hxsour | hxt⟩
      · exact ⟨hxs, Or.inl ⟨hxsour,
          fun hxA₀ ↦ Set.disjoint_left.1 hdisA₀ hxs hxA₀⟩⟩
      · exact ⟨hxs, Or.inr hxt⟩
    · rintro ⟨hxs, ⟨hxsour, -⟩ | hxt⟩
      · exact ⟨hxs, Or.inl hxsour⟩
      · exact ⟨hxs, Or.inr hxt⟩
  · rw [← hsource]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff]
    constructor
    · rintro ⟨hxs, hxsour⟩
      exact ⟨hxs, hxsour,
        fun hxA₀ ↦ Set.disjoint_left.1 hdisA₀ hxs hxA₀⟩
    · rintro ⟨hxs, hxsour, -⟩
      exact ⟨hxs, hxsour⟩

/-- The FIFO construction yields a full source--target linkage whenever
the designated source set is covered by its source-valued enumeration. -/
theorem isLinkable_of_safeLink_countableConstruction
    (safeLink : SafeLinkRule V) {A₀ : Set V} {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hG : G.IsUnhindered) (e : ℕ → V)
    (he : ∀ n, e n ∈ G.source) (hcover : A₀ ⊆ Set.range e) :
    IsLinkable G := by
  let D := limitDeleted G safeLink hF hG e he
  let W := limitChosen G safeLink hF hG e he
  let L := finalFamily G safeLink hF hG e he
  have hA₀D : A₀ ⊆ D :=
    designated_subset_limitDeleted G safeLink hF hG e he hcover
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpW | hpR
    · rcases hq with hqW | hqR
      · exact limitChosen_isWarp G safeLink hF hG e he hpW hqW hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        apply Set.disjoint_left.1 hqR.2 hxq
        rw [← vertexSet_limitChosen G safeLink hF hG e he]
        exact ⟨p, hpW, hxp⟩
    · rcases hq with hqW | hqR
      · apply Set.disjoint_left.2
        intro x hxp hxq
        apply Set.disjoint_left.1 hpR.2 hxp
        rw [← vertexSet_limitChosen G safeLink hF hG e he]
        exact ⟨q, hqW, hxq⟩
      · exact hF.isWarp hpR.1 hqR.1 hpq
  · intro p hp
    rcases hp with hpW | hpR
    · exact limitChosen_finiteCharacter G safeLink hF hG e he hpW
    · exact hF.finiteCharacter hpR.1
  · ext a
    constructor
    · rintro ⟨p, hpW | hpR, rfl⟩
      · obtain ⟨q, rfl, hqSource, -⟩ :=
          limitChosen_spec G safeLink hF hG e he p hpW
        exact hqSource
      · have ha : p.initial ∈ G.source \ A₀ := by
          rw [← hF.initialSet_eq]
          exact ⟨p, hpR.1, rfl⟩
        exact ha.1
    · intro haSource
      by_cases haA₀ : a ∈ A₀
      · have haW : a ∈ G.initialSet W :=
          source_mem_initialSet_limitChosen_of_mem_limitDeleted
            G safeLink hF hG e he haSource (hA₀D haA₀)
        obtain ⟨p, hpW, hpa⟩ := haW
        exact ⟨p, Or.inl hpW, hpa⟩
      · have haF : a ∈ G.initialSet F := by
          rw [hF.initialSet_eq]
          exact ⟨haSource, haA₀⟩
        obtain ⟨p, hpF, hpa⟩ := haF
        by_cases hpD : Disjoint p.support D
        · exact ⟨p, Or.inr ⟨hpF, hpD⟩, hpa⟩
        · have hpMeet : (p.support ∩ D).Nonempty := by
            obtain ⟨x, hxp, hxD⟩ := Set.not_disjoint_iff.1 hpD
            exact ⟨x, hxp, hxD⟩
          have hpInitD : p.initial ∈ D :=
            old_initial_mem_limitDeleted_of_meets
              G safeLink hF hG e he hpF hpMeet
          have hpInitSource : p.initial ∈ G.source := by
            have hpInit : p.initial ∈ G.source \ A₀ := by
              rw [← hF.initialSet_eq]
              exact ⟨p, hpF, rfl⟩
            exact hpInit.1
          have hpInitW : p.initial ∈ G.initialSet W :=
            source_mem_initialSet_limitChosen_of_mem_limitDeleted
              G safeLink hF hG e he hpInitSource hpInitD
          obtain ⟨q, hqW, hqp⟩ := hpInitW
          exact ⟨q, Or.inl hqW, hqp.trans hpa⟩
  · rintro x ⟨p, hpW | hpR, hpx⟩
    · obtain ⟨q, rfl, _hqSource, hqTarget, -⟩ :=
        limitChosen_spec G safeLink hF hG e he p hpW
      exact Option.some.inj hpx ▸ hqTarget
    · exact hF.terminalFrontier_subset ⟨p, hpR.1, hpx⟩
  · intro p hp
    rcases hp with hpW | hpR
    · exact limitChosen_isPathBetween G safeLink hF hG e he hpW
    · exact retainedOld_isPathBetween
        G safeLink hF hG e he hcover hpR

/-- The countable extension clause, isolated from the proof of the safe-link
rule.  This is the exact combinatorial consumer of Theorem 6.1. -/
theorem extensionClauseAt_countable_of_safeLink
    (safeLink : SafeLinkRule V) (G : DWeb V) (hG : G.IsUnhindered)
    {kappa : Cardinal.{u}} (hkappa : kappa ≤ ℵ₀) :
    ExtensionClauseAt G kappa := by
  intro A₀ hA₀Source hA₀Card hlink
  obtain ⟨F, hF⟩ := hlink
  by_cases hsource : G.source.Nonempty
  · obtain ⟨base, hbase⟩ := hsource
    have hA₀Countable : A₀.Countable := by
      apply Cardinal.le_aleph0_iff_set_countable.1
      rw [hA₀Card]
      exact hkappa
    let e : ℕ → V := Set.enumerateCountable hA₀Countable base
    have he : ∀ n, e n ∈ G.source := by
      intro n
      have hen : e n ∈ Set.range e := Set.mem_range_self n
      have hins : e n ∈ insert base A₀ :=
        Set.range_enumerateCountable_subset hA₀Countable base hen
      rcases hins with heq | hA₀
      · simpa only [heq] using hbase
      · exact hA₀Source hA₀
    have hcover : A₀ ⊆ Set.range e :=
      Set.subset_range_enumerate hA₀Countable base
    exact isLinkable_of_safeLink_countableConstruction
      G safeLink hF hG e he hcover
  · have hsourceEmpty : G.source = ∅ := Set.not_nonempty_iff_eq_empty.1 hsource
    refine ⟨∅, ?_⟩
    simpa only [hsourceEmpty] using empty_linkage G

/-- Countable extension, with the safe-link input discharged by
Proposition 6.3. -/
theorem extensionClauseAt_countable_of_proposition63
    (h63 : SafeLink.Proposition63 V)
    (G : DWeb V) (hG : G.IsUnhindered)
    {kappa : Cardinal.{u}} (hkappa : kappa ≤ ℵ₀) :
    ExtensionClauseAt G kappa :=
  extensionClauseAt_countable_of_safeLink
    (safeLinkRule_of_proposition63 h63) G hG hkappa

end CountableExtension

/-- Namespace-level form used by the cardinal-case dispatcher. -/
theorem extensionClauseAt_countable_of_proposition63
    (h63 : SafeLink.Proposition63 V)
    (G : DWeb V) (hG : G.IsUnhindered)
    {kappa : Cardinal.{u}} (hkappa : kappa ≤ ℵ₀) :
    ExtensionClauseAt G kappa :=
  CountableExtension.extensionClauseAt_countable_of_proposition63
    h63 G hG hkappa

end CardinalInduction
end Erdos599

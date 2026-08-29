/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingTraceOps

/-!
# From projected two-colour walks to alternating traces

This file isolates a useful representation bridge for the alternating-path
construction.  The construction itself naturally produces an injective walk
of *states*, whose projection to vertices has forward and backward runs.
The trace language, on the other hand, stores each maximal run as one finite
directed path.  `ProjectedRun` and the two assembly structures below record
exactly the information left after that run compression.

The principal theorems, `FiniteRunWalk.toFiniteTrace` and
`InfiniteRunWalk.toInfiniteTrace`, prove that projection-injectivity makes all
the collision clauses of Definition 4.2 automatic.  Subsequent theorems add
the warp labels and the safeness certificates used by the source dichotomy.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- A compressed monochromatic run of a projected edge walk.  Its support is
exactly the projection of the integer interval from `first` through `last`.
The ambient orientation is already incorporated into `link.path`; thus a
backward run has a path oriented from the projected last vertex to the first,
while `link.entry` and `link.exit` remain traversal endpoints. -/
structure ProjectedRun (D : Digraph V) (vertex : ℕ → V) where
  first : ℕ
  last : ℕ
  first_lt_last : first < last
  link : Link D
  entry_eq : link.entry = vertex first
  exit_eq : link.exit = vertex last
  support_eq : link.path.support = vertex '' Set.Icc first last

namespace ProjectedRun

variable {vertex : ℕ → V}

theorem entry_mem (r : ProjectedRun D vertex) :
    r.link.entry ∈ r.link.path.support :=
  r.link.entry_mem_support

theorem exit_mem (r : ProjectedRun D vertex) :
    r.link.exit ∈ r.link.path.support :=
  r.link.exit_mem_support

theorem mem_support_iff (r : ProjectedRun D vertex) {x : V} :
    x ∈ r.link.path.support ↔
      ∃ k, r.first ≤ k ∧ k ≤ r.last ∧ vertex k = x := by
  rw [r.support_eq]
  constructor
  · rintro ⟨k, ⟨hk₁, hk₂⟩, rfl⟩
    exact ⟨k, hk₁, hk₂, rfl⟩
  · rintro ⟨k, hk₁, hk₂, rfl⟩
    exact ⟨k, ⟨hk₁, hk₂⟩, rfl⟩

end ProjectedRun

/-- A finite sequence of compressed runs covering an initial segment of an
injective projected walk.  Adjacent integer intervals share one endpoint and
run directions alternate. -/
structure FiniteRunWalk (D : Digraph V) where
  lastIndex : ℕ
  vertex : ℕ → V
  run : Fin (lastIndex + 1) → ProjectedRun D vertex
  /-- Only the finite part of `vertex` used by the runs has to be
  injective.  Requiring the arbitrary extension `ℕ → V` to be globally
  injective would make this finite construction unusable when `V` is
  finite. -/
  vertex_injective_on : ∀ {i j : ℕ},
    i ≤ (run ⟨lastIndex, Nat.lt_succ_self _⟩).last →
    j ≤ (run ⟨lastIndex, Nat.lt_succ_self _⟩).last →
    vertex i = vertex j → i = j
  starts_zero : (run ⟨0, Nat.zero_lt_succ _⟩).first = 0
  consecutive : ∀ i : Fin lastIndex,
    (run i.castSucc).last = (run i.succ).first
  ordered : ∀ i j : Fin (lastIndex + 1), i < j →
    (run i).last ≤ (run j).first
  directions_alternate : ∀ i : Fin lastIndex,
    (run i.castSucc).link.direction ≠ (run i.succ).link.direction

namespace FiniteRunWalk

variable (W : FiniteRunWalk D)

/-- The number of nonempty monochromatic runs. -/
def runCount : ℕ := W.lastIndex + 1

@[simp] theorem runCount_eq : W.runCount = W.lastIndex + 1 := rfl

/-- Every run ends no later than the final run. -/
theorem run_last_le_final (i : Fin (W.lastIndex + 1)) :
    (W.run i).last ≤
      (W.run ⟨W.lastIndex, Nat.lt_succ_self _⟩).last := by
  by_cases hi : i.1 = W.lastIndex
  · have hi' : i = ⟨W.lastIndex, Nat.lt_succ_self _⟩ := Fin.ext hi
    subst i
    exact le_rfl
  · have hilast : i <
        (⟨W.lastIndex, Nat.lt_succ_self _⟩ : Fin (W.lastIndex + 1)) := by
      exact Fin.mk_lt_mk.2 (lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi)
    exact (W.ordered i ⟨W.lastIndex, Nat.lt_succ_self _⟩ hilast).trans
      (W.run ⟨W.lastIndex, Nat.lt_succ_self _⟩).first_lt_last.le

/-- Forget run endpoints and retain their alternating links. -/
def toFiniteTrace : FiniteTrace D where
  lastIndex := W.lastIndex
  link i := (W.run i).link
  joins := by
    intro i
    rw [(W.run i.castSucc).exit_eq, (W.run i.succ).entry_eq,
      W.consecutive i]
  alternates := by
    intro i
    exact W.directions_alternate i
  compatible := by
    intro i j hij
    have horder : (W.run i).last ≤ (W.run j).first := W.ordered i j hij
    have htouch :
        ∀ {x}, x ∈ (W.run i).link.path.support →
          x ∈ (W.run j).link.path.support →
          x = W.vertex (W.run i).last ∧
            (W.run i).last = (W.run j).first := by
      intro x hxi hxj
      rw [(W.run i).support_eq] at hxi
      rw [(W.run j).support_eq] at hxj
      rcases hxi with ⟨a, ⟨hai, hia⟩, rfl⟩
      rcases hxj with ⟨b, ⟨hjb, hbj⟩, hab⟩
      have haiFinal : a ≤
          (W.run ⟨W.lastIndex, Nat.lt_succ_self _⟩).last :=
        hia.trans (W.run_last_le_final i)
      have hbjFinal : b ≤
          (W.run ⟨W.lastIndex, Nat.lt_succ_self _⟩).last :=
        hbj.trans (W.run_last_le_final j)
      have hab' : a = b := W.vertex_injective_on haiFinal hbjFinal hab.symm
      subst b
      have hEq : a = (W.run i).last := Nat.le_antisymm hia (horder.trans hjb)
      subst a
      exact ⟨rfl, Nat.le_antisymm horder hjb⟩
    have hdisjoint :
        ¬ (j.1 = i.1 + 1) →
          Disjoint (W.run i).link.path.support (W.run j).link.path.support := by
      intro hnon
      rw [Set.disjoint_left]
      intro x hxi hxj
      obtain ⟨_hx, heq⟩ := htouch hxi hxj
      have hstrict : i.1 + 1 < j.1 := by omega
      let imid : Fin W.lastIndex := ⟨i.1, by omega⟩
      let inext : Fin (W.lastIndex + 1) := ⟨i.1 + 1, by omega⟩
      have hcast : imid.castSucc = i := by
        apply Fin.ext
        simp [imid]
      have hsucc : imid.succ = inext := by
        apply Fin.ext
        simp [imid, inext]
      have hchain : (W.run i).last = (W.run inext).first := by
        simpa [hcast, hsucc] using W.consecutive imid
      have hnextj : inext < j := by
        change i.1 + 1 < j.1
        exact hstrict
      have hfirstlt : (W.run i).last < (W.run j).first := by
        rw [hchain]
        exact (W.run inext).first_lt_last.trans_le (W.ordered inext j hnextj)
      exact (Nat.not_lt_of_ge heq.ge) hfirstlt
    cases hi : (W.run i).link.direction <;>
      cases hj : (W.run j).link.direction <;>
      simp only [CompatibleInOrder, hi, hj]
    · intro x hxi hxj
      obtain ⟨hx, heq⟩ := htouch hxi hxj
      right
      constructor
      · rw [(W.run i).exit_eq]
        exact hx
      · rw [(W.run j).entry_eq, ← heq]
        exact hx
    · constructor
      · intro _hadj
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨hxv, heq⟩ := htouch hx.1 hx.2
          rw [(W.run i).exit_eq, hxv]
          exact Set.mem_singleton _
        · intro x hx
          have hxv : x = (W.run i).link.exit := by simpa using hx
          subst x
          constructor
          · exact (W.run i).link.exit_mem_support
          · let imid : Fin W.lastIndex := ⟨i.1, by omega⟩
            have hcast : imid.castSucc = i := by
              apply Fin.ext
              simp [imid]
            have hsucc : imid.succ = j := by
              apply Fin.ext
              simpa [imid] using _hadj.symm
            have hjoin : (W.run i).link.exit = (W.run j).link.entry := by
              rw [(W.run i).exit_eq, (W.run j).entry_eq]
              exact congrArg W.vertex (by
                simpa [hcast, hsucc] using W.consecutive imid)
            rw [hjoin]
            exact (W.run j).link.entry_mem_support
      · exact hdisjoint
    · constructor
      · intro _hadj x hxi hxj
        left
        obtain ⟨hx, _heq⟩ := htouch hxi hxj
        rw [(W.run i).exit_eq]
        exact hx
      · intro hnon x hx
        exact False.elim (Set.disjoint_left.1 (hdisjoint hnon) hx.1 hx.2)
    · intro x hxi hxj
      obtain ⟨hx, heq⟩ := htouch hxi hxj
      right
      constructor
      · rw [(W.run i).exit_eq]
        exact hx
      · rw [(W.run j).entry_eq, ← heq]
        exact hx

@[simp]
theorem toFiniteTrace_initial :
    W.toFiniteTrace.initial = W.vertex 0 := by
  change (W.run ⟨0, Nat.zero_lt_succ _⟩).link.entry = W.vertex 0
  rw [(W.run _).entry_eq]
  rw [W.starts_zero]

/-- The last compressed run, indexed without making `runCount - 1`
definitionally equal to the trace's final index. -/
def lastRunIndex : Fin (W.lastIndex + 1) :=
  ⟨W.lastIndex, Nat.lt_succ_self _⟩

@[simp]
theorem lastRunIndex_val : W.lastRunIndex.1 = W.lastIndex :=
  rfl

@[simp]
theorem toFiniteTrace_terminal :
    W.toFiniteTrace.terminal = W.vertex (W.run W.lastRunIndex).last := by
  change (W.run ⟨W.lastIndex, Nat.lt_succ_self _⟩).link.exit = _
  rw [(W.run _).exit_eq]
  rfl

theorem toFiniteTrace_links :
    W.toFiniteTrace.links =
      Set.range (fun i : Fin (W.lastIndex + 1) ↦ (W.run i).link) :=
  rfl

theorem run_link_mem (i : Fin (W.lastIndex + 1)) :
    (W.run i).link ∈ W.toFiniteTrace.links := by
  rw [W.toFiniteTrace_links]
  exact ⟨i, rfl⟩

end FiniteRunWalk

/-- An omega-sequence of finite compressed runs.  It represents the result
of maximal-run compression of an infinite two-colour projected walk. -/
structure InfiniteRunWalk (D : Digraph V) where
  vertex : ℕ → V
  vertex_injective : Function.Injective vertex
  run : ℕ → ProjectedRun D vertex
  starts_zero : (run 0).first = 0
  consecutive : ∀ i, (run i).last = (run (i + 1)).first
  ordered : ∀ i j, i < j → (run i).last ≤ (run j).first
  directions_alternate : ∀ i,
    (run i).link.direction ≠ (run (i + 1)).link.direction

namespace InfiniteRunWalk

variable (W : InfiniteRunWalk D)

/-- The alternating trace represented by the compressed projected walk. -/
def toInfiniteTrace : InfiniteTrace D where
  link i := (W.run i).link
  joins i := by
    rw [(W.run i).exit_eq, (W.run (i + 1)).entry_eq,
      W.consecutive i]
  alternates := W.directions_alternate
  compatible := by
    intro i j hij
    have horder := W.ordered i j hij
    have htouch :
        ∀ {x}, x ∈ (W.run i).link.path.support →
          x ∈ (W.run j).link.path.support →
          x = W.vertex (W.run i).last ∧
            (W.run i).last = (W.run j).first := by
      intro x hxi hxj
      rw [(W.run i).support_eq] at hxi
      rw [(W.run j).support_eq] at hxj
      rcases hxi with ⟨a, ⟨hai, hia⟩, rfl⟩
      rcases hxj with ⟨b, ⟨hjb, hbj⟩, hab⟩
      have hab' : a = b := W.vertex_injective hab.symm
      subst b
      have hEq : a = (W.run i).last := Nat.le_antisymm hia (horder.trans hjb)
      subst a
      exact ⟨rfl, Nat.le_antisymm horder hjb⟩
    have hdisjoint :
        ¬ (j = i + 1) →
          Disjoint (W.run i).link.path.support (W.run j).link.path.support := by
      intro hnon
      rw [Set.disjoint_left]
      intro x hxi hxj
      obtain ⟨_hx, heq⟩ := htouch hxi hxj
      have hstrict : i + 1 < j := by omega
      have hfirstlt : (W.run i).last < (W.run j).first := by
        rw [W.consecutive i]
        exact (W.run (i + 1)).first_lt_last.trans_le
          (W.ordered (i + 1) j hstrict)
      exact (Nat.not_lt_of_ge heq.ge) hfirstlt
    cases hi : (W.run i).link.direction <;>
      cases hj : (W.run j).link.direction <;>
      simp only [CompatibleInOrder, hi, hj]
    · intro x hxi hxj
      obtain ⟨hx, heq⟩ := htouch hxi hxj
      right
      constructor
      · rw [(W.run i).exit_eq]
        exact hx
      · rw [(W.run j).entry_eq, ← heq]
        exact hx
    · constructor
      · intro _hadj
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨hxv, heq⟩ := htouch hx.1 hx.2
          rw [(W.run i).exit_eq, hxv]
          exact Set.mem_singleton _
        · intro x hx
          have hxv : x = (W.run i).link.exit := by simpa using hx
          subst x
          constructor
          · exact (W.run i).link.exit_mem_support
          · have hjoin : (W.run i).link.exit = (W.run j).link.entry := by
              rw [(W.run i).exit_eq, (W.run j).entry_eq,
                W.consecutive i, _hadj]
            rw [hjoin]
            exact (W.run j).link.entry_mem_support
      · exact hdisjoint
    · constructor
      · intro _hadj x hxi hxj
        left
        obtain ⟨hx, _heq⟩ := htouch hxi hxj
        rw [(W.run i).exit_eq]
        exact hx
      · intro hnon x hx
        exact False.elim (Set.disjoint_left.1 (hdisjoint hnon) hx.1 hx.2)
    · intro x hxi hxj
      obtain ⟨hx, heq⟩ := htouch hxi hxj
      right
      constructor
      · rw [(W.run i).exit_eq]
        exact hx
      · rw [(W.run j).entry_eq, ← heq]
        exact hx

@[simp]
theorem toInfiniteTrace_initial :
    W.toInfiniteTrace.initial = W.vertex 0 := by
  change (W.run 0).link.entry = W.vertex 0
  rw [(W.run 0).entry_eq, W.starts_zero]

theorem toInfiniteTrace_links :
    W.toInfiniteTrace.links = Set.range (fun i ↦ (W.run i).link) :=
  rfl

theorem run_link_mem (i : ℕ) :
    (W.run i).link ∈ W.toInfiniteTrace.links :=
  ⟨i, rfl⟩

end InfiniteRunWalk

/-! ## Warp-labelled compressed walks -/

variable {Γ : DWeb V}

/-- The local, run-indexed certificates needed to recognize an infinite
compressed walk as a bracket alternating path.  This is deliberately stated
per run, so a state-walk construction never has to reason through a union of
trace links. -/
structure InfiniteRunWalk.BracketLabels
    (W : InfiniteRunWalk Γ.graph) (U Y : Set Γ.DPath) : Prop where
  reference_isWarp : Γ.IsWarp Y
  backward_on : ∀ i, (W.run i).link.direction = .backward →
    IsFragmentOf (W.run i).link.path Y
  forward_off : ∀ i, (W.run i).link.direction = .forward →
    Disjoint (W.run i).link.path.edgeSet (familyEdges Y)
  forward_on : ∀ i, (W.run i).link.direction = .forward →
    IsFragmentOf (W.run i).link.path U
  initial_outside : (W.run 0).link.direction = .forward →
    W.vertex 0 ∉ Γ.vertexSet Y

namespace InfiniteRunWalk

theorem isBracketAlternating (W : InfiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (h : W.BracketLabels U Y) :
    IsBracketAlternating U Y (.infinite W.toInfiniteTrace) := by
  refine ⟨⟨h.reference_isWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hdir
    rcases hl with ⟨i, rfl⟩
    exact h.backward_on i hdir
  · intro hfirst
    rw [show (AltPath.infinite W.toInfiniteTrace).initial = W.vertex 0 from
      W.toInfiniteTrace_initial]
    apply h.initial_outside
    simpa [AltPath.firstDirection?, toInfiniteTrace] using hfirst
  · intro t ht
    simp [AltPath.terminal?] at ht
  · intro l hl hdir
    rcases hl with ⟨i, rfl⟩
    exact h.forward_on i hdir

/-- A run-indexed contact certificate.  It is exactly the useful form for a
maximal-contact construction: every reference-warp vertex on a forward run
also lies on some backward run. -/
def ContactsCovered (W : InfiniteRunWalk Γ.graph) (Y : Set Γ.DPath) : Prop :=
  ∀ i, (W.run i).link.direction = .forward →
    (W.run i).link.path.support ∩ Γ.vertexSet Y ⊆
      ⋃ j, ⋃ (_ : (W.run j).link.direction = .backward),
        (W.run j).link.path.support

theorem forwardVertexContactsCovered (W : InfiniteRunWalk Γ.graph)
    {Y : Set Γ.DPath} (h : W.ContactsCovered Y) :
    ForwardVertexContactsCovered Y (.infinite W.toInfiniteTrace) := by
  intro x hx
  change x ∈ (⋃ l ∈ W.toInfiniteTrace.links,
    ⋃ (_ : l.direction = .forward), l.path.support) ∩ Γ.vertexSet Y at hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion] at hx
  rcases hx.1 with ⟨l, ⟨i, rfl⟩, hdir, hxl⟩
  have hx' := h i hdir ⟨hxl, hx.2⟩
  change x ∈ ⋃ l ∈ W.toInfiniteTrace.links,
    ⋃ (_ : l.direction = .backward), l.path.support
  simp only [Set.mem_iUnion] at hx' ⊢
  rcases hx' with ⟨j, hback, hxj⟩
  exact ⟨(W.run j).link, ⟨j, rfl⟩, hback, hxj⟩

theorem isBracketSwitchingAlternating (W : InfiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (hlabels : W.BracketLabels U Y)
    (hcontacts : W.ContactsCovered Y) :
    IsBracketSwitchingAlternating U Y (.infinite W.toInfiniteTrace) := by
  refine ⟨W.isBracketAlternating hlabels, ?_,
    W.forwardVertexContactsCovered hcontacts⟩
  intro l hl hdir
  rcases hl with ⟨i, rfl⟩
  exact hlabels.forward_off i hdir

/-- The three global safeness clauses are kept as a separate certificate.
They concern unions of run edge sets, rather than the local construction of
the projected walk. -/
structure SafetyCertificate (W : InfiniteRunWalk Γ.graph)
    (Y : Set Γ.DPath) : Prop where
  intervals : ∀ p ∈ Y,
    IsEdgeInterval
      ((.infinite W.toInfiniteTrace : AltPath Γ.graph).directionEdges .backward ∩
        p.edgeSet) p
  no_ray : ¬ ContainsDirectedRay
    ((.infinite W.toInfiniteTrace : AltPath Γ.graph).edgeSet \ familyEdges Y)
  no_cycle : ¬ ContainsDirectedCycle
    ((.infinite W.toInfiniteTrace : AltPath Γ.graph).edgeSet \ familyEdges Y)

theorem isBracketSafe (W : InfiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (hlabels : W.BracketLabels U Y)
    (hsafe : W.SafetyCertificate Y) :
    IsBracketSafe U Y (.infinite W.toInfiniteTrace) := by
  have hbracket := W.isBracketAlternating hlabels
  exact ⟨⟨hbracket.1, hsafe.intervals, hsafe.no_ray, hsafe.no_cycle⟩,
    hbracket⟩

theorem isSwitchingSafe (W : InfiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (hlabels : W.BracketLabels U Y)
    (hsafe : W.SafetyCertificate Y) (hcontacts : W.ContactsCovered Y) :
    IsSwitchingSafe Y (.infinite W.toInfiniteTrace) := by
  refine ⟨(W.isBracketSafe hlabels hsafe).1, ?_,
    W.forwardVertexContactsCovered hcontacts⟩
  intro l hl hdir
  rcases hl with ⟨i, rfl⟩
  exact hlabels.forward_off i hdir

end InfiniteRunWalk

/-- Finite analogue of `InfiniteRunWalk.BracketLabels`, including the
exposed terminal condition when the final run is forward. -/
structure FiniteRunWalk.BracketLabels
    (W : FiniteRunWalk Γ.graph) (U Y : Set Γ.DPath) : Prop where
  reference_isWarp : Γ.IsWarp Y
  backward_on : ∀ i, (W.run i).link.direction = .backward →
    IsFragmentOf (W.run i).link.path Y
  forward_off : ∀ i, (W.run i).link.direction = .forward →
    Disjoint (W.run i).link.path.edgeSet (familyEdges Y)
  forward_on : ∀ i, (W.run i).link.direction = .forward →
    IsFragmentOf (W.run i).link.path U
  initial_outside :
    (W.run ⟨0, Nat.zero_lt_succ _⟩).link.direction = .forward →
    W.vertex 0 ∉ Γ.vertexSet Y
  terminal_outside : (W.run W.lastRunIndex).link.direction = .forward →
    W.vertex (W.run W.lastRunIndex).last ∉ Γ.vertexSet Y

namespace FiniteRunWalk

theorem isBracketAlternating (W : FiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (h : W.BracketLabels U Y) :
    IsBracketAlternating U Y (.finite W.toFiniteTrace) := by
  refine ⟨⟨h.reference_isWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hdir
    change l ∈ W.toFiniteTrace.links at hl
    rw [W.toFiniteTrace_links] at hl
    rcases hl with ⟨i, rfl⟩
    exact h.backward_on i hdir
  · intro hfirst
    rw [show (AltPath.finite W.toFiniteTrace).initial = W.vertex 0 from
      W.toFiniteTrace_initial]
    apply h.initial_outside
    simpa [AltPath.firstDirection?, FiniteTrace.firstLink, toFiniteTrace] using hfirst
  · intro t ht hlast
    have ht' : t = W.vertex (W.run W.lastRunIndex).last := by
      change some W.toFiniteTrace.terminal = some t at ht
      have heq : W.toFiniteTrace.terminal = t := Option.some.inj ht
      rw [W.toFiniteTrace_terminal] at heq
      exact heq.symm
    subst t
    apply h.terminal_outside
    simpa [AltPath.lastDirection?, FiniteTrace.lastLink, toFiniteTrace,
      lastRunIndex] using hlast
  · intro l hl hdir
    change l ∈ W.toFiniteTrace.links at hl
    rw [W.toFiniteTrace_links] at hl
    rcases hl with ⟨i, rfl⟩
    exact h.forward_on i hdir

/-- Contact coverage, stated per compressed forward run. -/
def ContactsCovered (W : FiniteRunWalk Γ.graph) (Y : Set Γ.DPath) : Prop :=
  ∀ i, (W.run i).link.direction = .forward →
    (W.run i).link.path.support ∩ Γ.vertexSet Y ⊆
      ⋃ j, ⋃ (_ : (W.run j).link.direction = .backward),
        (W.run j).link.path.support

theorem forwardVertexContactsCovered (W : FiniteRunWalk Γ.graph)
    {Y : Set Γ.DPath} (h : W.ContactsCovered Y) :
    ForwardVertexContactsCovered Y (.finite W.toFiniteTrace) := by
  intro x hx
  change x ∈ (⋃ l ∈ W.toFiniteTrace.links,
    ⋃ (_ : l.direction = .forward), l.path.support) ∩ Γ.vertexSet Y at hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion] at hx
  rcases hx.1 with ⟨l, ⟨i, hili⟩, hdir, hxl⟩
  subst l
  have hx' := h i hdir ⟨hxl, hx.2⟩
  change x ∈ ⋃ l ∈ W.toFiniteTrace.links,
    ⋃ (_ : l.direction = .backward), l.path.support
  simp only [Set.mem_iUnion] at hx' ⊢
  rcases hx' with ⟨j, hback, hxj⟩
  exact ⟨(W.run j).link, W.run_link_mem j, hback, hxj⟩

theorem isBracketSwitchingAlternating (W : FiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (hlabels : W.BracketLabels U Y)
    (hcontacts : W.ContactsCovered Y) :
    IsBracketSwitchingAlternating U Y (.finite W.toFiniteTrace) := by
  refine ⟨W.isBracketAlternating hlabels, ?_,
    W.forwardVertexContactsCovered hcontacts⟩
  intro l hl hdir
  change l ∈ W.toFiniteTrace.links at hl
  rw [W.toFiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact hlabels.forward_off i hdir

structure SafetyCertificate (W : FiniteRunWalk Γ.graph)
    (Y : Set Γ.DPath) : Prop where
  intervals : ∀ p ∈ Y,
    IsEdgeInterval
      ((.finite W.toFiniteTrace : AltPath Γ.graph).directionEdges .backward ∩
        p.edgeSet) p
  no_ray : ¬ ContainsDirectedRay
    ((.finite W.toFiniteTrace : AltPath Γ.graph).edgeSet \ familyEdges Y)
  no_cycle : ¬ ContainsDirectedCycle
    ((.finite W.toFiniteTrace : AltPath Γ.graph).edgeSet \ familyEdges Y)

theorem isBracketSafe (W : FiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (hlabels : W.BracketLabels U Y)
    (hsafe : W.SafetyCertificate Y) :
    IsBracketSafe U Y (.finite W.toFiniteTrace) := by
  have hbracket := W.isBracketAlternating hlabels
  exact ⟨⟨hbracket.1, hsafe.intervals, hsafe.no_ray, hsafe.no_cycle⟩,
    hbracket⟩

theorem isSwitchingSafe (W : FiniteRunWalk Γ.graph)
    {U Y : Set Γ.DPath} (hlabels : W.BracketLabels U Y)
    (hsafe : W.SafetyCertificate Y) (hcontacts : W.ContactsCovered Y) :
    IsSwitchingSafe Y (.finite W.toFiniteTrace) := by
  refine ⟨(W.isBracketSafe hlabels hsafe).1, ?_,
    W.forwardVertexContactsCovered hcontacts⟩
  intro l hl hdir
  change l ∈ W.toFiniteTrace.links at hl
  rw [W.toFiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact hlabels.forward_off i hdir

end FiniteRunWalk

end Erdos599.Alternating

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceResidualHallRoot

/-!
# Invariance of fixed-family safe words under ambient graph enlargement

All vertices and colours are unchanged. The actual forward and reference
families, not the ambient adjacency relation, determine the transitions.
Interval witnesses are copied back using their own edges. This avoids a
dependency on the later half-way engine's graph-copy constructions.
-/

namespace Erdos599.Alternating.ColouredSafeGraphLift

open Set DirectedPath ColouredSafeReverseReachability FiniteColouredOccurrenceWord

universe u

variable {V : Type u} {D E : Digraph V}

private theorem walk_edges_lift (h : ∀ {x y}, D.Adj x y → E.Adj x y) :
    ∀ {a b : V} (p : Walk D a b), (p.lift h).edgeSet = p.edgeSet
  | _, _, .nil => rfl
  | _, _, .cons _ p => by simp [Walk.lift, walk_edges_lift h p]

theorem path_edges_lift (h : ∀ {x y}, D.Adj x y → E.Adj x y) (p : Path D) :
    (p.lift h).edgeSet = p.edgeSet := by
  cases p with
  | inl p => exact walk_edges_lift h p.walk
  | inr r => rfl

private def copyWalk : ∀ {a b : V} (p : Walk D a b),
    (∀ e ∈ p.edgeSet, E.Adj e.1 e.2) → Walk E a b
  | _, _, .nil, _ => .nil
  | _, _, @Walk.cons _ _ a b c _ p, h =>
      .cons (h (a, b) (by simp)) (copyWalk p (fun e he ↦ h e (by simp [he])))

private theorem copyWalk_support : ∀ {a b : V} (p : Walk D a b)
    (h : ∀ e ∈ p.edgeSet, E.Adj e.1 e.2), (copyWalk p h).support = p.support
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, _ => by
      simp only [copyWalk, Walk.support_cons]
      exact congrArg (List.cons _) (copyWalk_support p _)

private theorem copyWalk_edges : ∀ {a b : V} (p : Walk D a b)
    (h : ∀ e ∈ p.edgeSet, E.Adj e.1 e.2), (copyWalk p h).edgeSet = p.edgeSet
  | _, _, .nil, _ => rfl
  | _, _, .cons _ p, _ => by
      simp only [copyWalk, Walk.edgeSet_cons]
      exact congrArg (fun F ↦ {_} ∪ F) (copyWalk_edges p _)

/-- Copy a path using only the adjacency of its actual edges. -/
def copyPath : (p : Path D) → (∀ e ∈ p.edgeSet, E.Adj e.1 e.2) → Path E
  | .inl p, h => .inl {
      start := p.start
      finish := p.finish
      walk := copyWalk p.walk (fun e he ↦ h e he)
      isPath := Eq.mpr
        (congrArg List.Nodup (copyWalk_support p.walk (fun e he ↦ h e he))) p.isPath }
  | .inr r, h => .inr {
      toFun := r.toFun
      adj_succ := fun n ↦ h (r n, r (n + 1)) ⟨n, rfl⟩
      injective := r.injective }

theorem copyPath_support (p : Path D) (h : ∀ e ∈ p.edgeSet, E.Adj e.1 e.2) :
    (copyPath p h).support = p.support := by
  cases p with
  | inl p =>
      change ∀ e ∈ p.walk.edgeSet, E.Adj e.1 e.2 at h
      ext x
      change x ∈ (copyWalk p.walk h).support ↔ x ∈ p.walk.support
      rw [copyWalk_support]
  | inr r => rfl

theorem copyPath_edges (p : Path D) (h : ∀ e ∈ p.edgeSet, E.Adj e.1 e.2) :
    (copyPath p h).edgeSet = p.edgeSet := by
  cases p with
  | inl p => exact copyWalk_edges p.walk h
  | inr r => rfl

variable {Gamma Delta : DWeb V}

def liftFamily (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    (W : Set Gamma.DPath) : Set Delta.DPath := Path.lift h '' W

theorem liftFamily_isWarp (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) : Delta.IsWarp (liftFamily h W) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
  change Disjoint (p.lift h).support (q.lift h).support
  rw [Path.support_lift, Path.support_lift]
  exact hW hp hq (fun he ↦ hne (congrArg (Path.lift h) he))

theorem liftFamily_finiteCharacter
    (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    {W : Set Gamma.DPath} (hW : Gamma.HasFiniteCharacter W) :
    Delta.HasFiniteCharacter (liftFamily h W) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, rfl⟩ := hW hp
  exact ⟨q.lift h, rfl⟩

@[simp] theorem liftFamily_vertexSet
    (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    (W : Set Gamma.DPath) : Delta.vertexSet (liftFamily h W) = Gamma.vertexSet W := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, by simpa only [Path.support_lift] using hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨p.lift h, ⟨p, hp, rfl⟩, by simpa only [Path.support_lift] using hx⟩

@[simp] theorem liftFamily_initialSet
    (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    (W : Set Gamma.DPath) : Delta.initialSet (liftFamily h W) = Gamma.initialSet W := by
  have hi : ∀ p : Gamma.DPath, (p.lift h).initial = p.initial := by
    intro p
    cases p <;> rfl
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, (hi p).symm.trans hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨p.lift h, ⟨p, hp, rfl⟩, (hi p).trans hx⟩

@[simp] theorem liftFamily_terminalFrontier
    (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    (W : Set Gamma.DPath) :
    Delta.terminalFrontier (liftFamily h W) = Gamma.terminalFrontier W := by
  have ht : ∀ p : Gamma.DPath, (p.lift h).terminal? = p.terminal? := by
    intro p
    cases p <;> rfl
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, (ht p).symm.trans hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨p.lift h, ⟨p, hp, rfl⟩, (ht p).trans hx⟩

@[simp] theorem liftFamily_edges
    (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
    (W : Set Gamma.DPath) : familyEdges (liftFamily h W) = familyEdges W := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, he⟩
    exact ⟨p, hp, by simpa only [path_edges_lift] using he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p.lift h, ⟨p, hp, rfl⟩, by simpa only [path_edges_lift] using he⟩

/-- Retype a word between possibly different ambient digraphs, retaining
the same vertex type, chronology, and actual coloured edges. -/
def retypeWord {W Y : Set Gamma.DPath} {W' Y' : Set Delta.DPath}
    (hW : familyEdges W ⊆ familyEdges W') (hY : familyEdges Y ⊆ familyEdges Y')
    (Q : FiniteColouredOccurrenceWord W Y) : FiniteColouredOccurrenceWord W' Y' where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => exact hW (by simpa only [hd] using Q.actualEdge_spec i)
    | backward => exact hY (by simpa only [hd] using Q.actualEdge_spec i)
  occurrence_injective := Q.occurrence_injective

variable (h : ∀ {x y}, Gamma.graph.Adj x y → Delta.graph.Adj x y)
variable {W Y : Set Gamma.DPath}

def liftWord (Q : FiniteColouredOccurrenceWord W Y) :
    FiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y) :=
  retypeWord (by rw [liftFamily_edges]) (by rw [liftFamily_edges]) Q

def lowerWord (Q : FiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y)) :
    FiniteColouredOccurrenceWord W Y :=
  retypeWord (by rw [liftFamily_edges]) (by rw [liftFamily_edges]) Q

theorem isEdgeInterval_lift_iff (R : Set (V × V)) (p : Gamma.DPath) :
    IsEdgeInterval R (p.lift h) ↔ IsEdgeInterval R p := by
  constructor
  · rintro (he | ⟨q, hqp, he⟩)
    · exact Or.inl he
    · have hqadj : ∀ e ∈ q.edgeSet, Gamma.graph.Adj e.1 e.2 := by
        intro e heq
        apply p.edgeSet_subset_adj
        simpa only [path_edges_lift] using hqp.2 heq
      refine Or.inr ⟨copyPath q hqadj, ⟨?_, ?_⟩, ?_⟩
      · simpa only [copyPath_support, Path.support_lift] using hqp.1
      · simpa only [copyPath_edges, path_edges_lift] using hqp.2
      · simpa only [copyPath_edges] using he
  · rintro (he | ⟨q, hqp, he⟩)
    · exact Or.inl he
    · refine Or.inr ⟨q.lift h, ⟨?_, ?_⟩, ?_⟩
      · simpa only [Path.support_lift] using hqp.1
      · simpa only [path_edges_lift] using hqp.2
      · simpa only [path_edges_lift] using he

theorem liftWord_isIntervalSafe {Q : FiniteColouredOccurrenceWord W Y}
    (hQ : Q.IsIntervalSafe) : (liftWord h Q).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b x ha hb
    apply hQ.incoming_removed ha
    simpa only [liftFamily_edges] using hb
  · intro x a b ha hb
    apply hQ.outgoing_removed ha
    simpa only [liftFamily_edges] using hb
  · rintro _ ⟨p, hp, rfl⟩
    change IsEdgeInterval (Q.backwardEdges ∩ (p.lift h).edgeSet) (p.lift h)
    rw [path_edges_lift]
    exact (isEdgeInterval_lift_iff h _ p).mpr (hQ.intervals p hp)
  · intro x y he
    simpa only [liftFamily_initialSet, liftFamily_terminalFrontier] using hQ.endpoint_pure he

theorem lowerWord_isIntervalSafe
    {Q : FiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y)}
    (hQ : Q.IsIntervalSafe) : (lowerWord h Q).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b x ha hb
    apply hQ.incoming_removed ha
    simpa only [liftFamily_edges] using hb
  · intro x a b ha hb
    apply hQ.outgoing_removed ha
    simpa only [liftFamily_edges] using hb
  · intro p hp
    have hi := hQ.intervals (p.lift h) ⟨p, hp, rfl⟩
    change IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
    apply (isEdgeInterval_lift_iff h _ p).mp
    simpa only [path_edges_lift] using hi
  · intro x y he
    simpa only [liftFamily_initialSet, liftFamily_terminalFrontier] using hQ.endpoint_pure he

/-- Infinite chronology also lowers without using any new ambient edge. -/
def lowerInfiniteWord
    (Q : InfiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y)) :
    InfiniteColouredOccurrenceWord W Y where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i <;>
      simpa only [hd, liftFamily_edges] using Q.actualEdge_spec i
  occurrence_injective := Q.occurrence_injective

theorem lowerInfiniteWord_isIntervalSafe
    {Q : InfiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y)}
    (hQ : Q.IsIntervalSafe) : (lowerInfiniteWord h Q).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b x ha hb
    apply hQ.incoming_removed ha
    simpa only [liftFamily_edges] using hb
  · intro x a b ha hb
    apply hQ.outgoing_removed ha
    simpa only [liftFamily_edges] using hb
  · intro p hp
    have hi := hQ.intervals (p.lift h) ⟨p, hp, rfl⟩
    change IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
    apply (isEdgeInterval_lift_iff h _ p).mp
    simpa only [path_edges_lift] using hi
  · intro x y he
    simpa only [liftFamily_initialSet, liftFamily_terminalFrontier] using hQ.endpoint_pure he

theorem no_safeInfinite_liftFamily {s : V}
    (hno : ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) :
    ¬ ∃ Q : InfiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y),
      Q.IsIntervalSafe ∧ Q.vertex 0 = s := by
  rintro ⟨Q, hQ, hs⟩
  exact hno ⟨lowerInfiniteWord h Q, lowerInfiniteWord_isIntervalSafe h hQ, hs⟩

/-- Enlarging the graph introduces no new terminal in a fixed safe row. -/
theorem safelyReachable_liftFamily (s : V) :
    safelyReachable (liftFamily h W) (liftFamily h Y) s = safelyReachable W Y s := by
  ext t
  constructor
  · rintro ⟨ht, Q, hQ, hs, hf⟩
    exact ⟨by simpa only [liftFamily_terminalFrontier, liftFamily_vertexSet] using ht,
      lowerWord h Q, lowerWord_isIntervalSafe h hQ, hs, hf⟩
  · rintro ⟨ht, Q, hQ, hs, hf⟩
    exact ⟨by simpa only [liftFamily_terminalFrontier, liftFamily_vertexSet] using ht,
      liftWord h Q, liftWord_isIntervalSafe h hQ, hs, hf⟩

def liftSource (s : ExposedInitial W Y) : ExposedInitial (liftFamily h W) (liftFamily h Y) :=
  ⟨s.1, by simpa only [liftFamily_initialSet, liftFamily_vertexSet] using s.2⟩

theorem liftSource_injective : Function.Injective (liftSource h (W := W) (Y := Y)) := by
  intro s t he
  apply Subtype.ext
  exact congrArg (fun r : ExposedInitial (liftFamily h W) (liftFamily h Y) ↦ r.1) he

theorem safeTerminalUnion_liftSource (J : Set (ExposedInitial W Y)) :
    safeTerminalUnion (liftSource h '' J) = safeTerminalUnion J := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨⟨r, hr, rfl⟩, hts⟩ := Set.mem_iUnion.mp hs
    apply mem_safeTerminalUnion_of_mem_safelyReachable hr
    exact (safelyReachable_liftFamily h r.1) ▸ hts
  · intro ht
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hsJ, hts⟩ := Set.mem_iUnion.mp hs
    apply mem_safeTerminalUnion_of_mem_safelyReachable
      (J := liftSource h '' J) (s := liftSource h s) ⟨s, hsJ, rfl⟩
    exact (safelyReachable_liftFamily h s.1).symm ▸ hts

#print axioms lowerWord_isIntervalSafe
#print axioms lowerInfiniteWord_isIntervalSafe
#print axioms no_safeInfinite_liftFamily
#print axioms safelyReachable_liftFamily
#print axioms safeTerminalUnion_liftSource

end Erdos599.Alternating.ColouredSafeGraphLift

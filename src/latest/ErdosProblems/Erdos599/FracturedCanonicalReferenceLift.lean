/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedCanonicalFiniteLift

/-!
# A canonical proper-edge lift of a finite reference warp

This is the honest-warp companion to `FracturedCanonicalFiniteLift`.  A
nontrivial finite reference member is lifted by the literal walk

`outgoing x -> incoming y -> plain y -> outgoing y -> ...`,

so every genuine reference edge `x -> y` occurs upstairs exactly as
`outgoing x -> incoming y`.  A singleton is represented explicitly by the
trivial path at `outgoing x`, preserving uniform outgoing initial copies.

No generic endpoint-purity assertion relative to a second fractured family
is made here: such a statement additionally needs the application-specific
fact that no fractured junction lies on the reference carrier.
-/

noncomputable section

namespace Erdos599.Alternating.FracturedCanonicalReferenceLift

open Set DirectedPath
open FracturedDuplication FracturedCanonicalFiniteLift

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The canonical proper lift of an original edge. -/
private theorem canonicalProperAdj (Z : FracturedWarp Gamma)
    {x y : V} (h : Gamma.graph.Adj x y) :
    (web Gamma Z).graph.Adj (outgoing x) (incoming y) := by
  exact graph_adj_swapVertex Z (adj_terminal_source_of_adj Z h)

/-- The first half of an internal canonical vertex block. -/
private theorem incomingPlainAdj (Z : FracturedWarp Gamma) (x : V) :
    (web Gamma Z).graph.Adj (incoming x) (plain x) := by
  exact Or.inr ⟨rfl, by simp [incoming, plain]⟩

/-- The second half of an internal canonical vertex block. -/
private theorem plainOutgoingAdj (Z : FracturedWarp Gamma) (x : V) :
    (web Gamma Z).graph.Adj (plain x) (outgoing x) := by
  exact Or.inr ⟨rfl, by simp [plain, outgoing]⟩

/-- Direct canonical lift of a nonempty original walk.  The first original
edge is supplied separately, so the result always has distinct endpoint
roles even when the tail is a nil walk. -/
def canonicalConsWalk (Z : FracturedWarp Gamma) :
    {x y z : V} → Gamma.graph.Adj x y → Walk Gamma.graph y z →
      Walk (web Gamma Z).graph (outgoing x) (incoming z)
  | _, y, _, h, .nil =>
      .cons (canonicalProperAdj Z h) .nil
  | _, y, _, h, .cons hnext q =>
      .cons (canonicalProperAdj Z h)
        (.cons (incomingPlainAdj Z y)
          (.cons (plainOutgoingAdj Z y) (canonicalConsWalk Z hnext q)))

/-- Its ordered support is exactly the full canonical block expansion with
the first incoming/plain and last plain/outgoing copies removed. -/
theorem canonicalConsWalk_support_expansion (Z : FracturedWarp Gamma) :
    ∀ {x y z : V} (h : Gamma.graph.Adj x y) (q : Walk Gamma.graph y z),
      [incoming x, plain x] ++ (canonicalConsWalk Z h q).support ++
          [plain z, outgoing z] =
        (x :: q.support).flatMap canonicalBlock := by
  intro x y z h q
  induction q generalizing x with
  | nil => simp [canonicalConsWalk, canonicalBlock]
  | @cons y w z hnext q ih =>
      simp only [canonicalConsWalk, Walk.support_cons, List.flatMap_cons]
      simpa [canonicalBlock, List.append_assoc] using
        congrArg (fun l ↦ canonicalBlock x ++ l) (ih hnext)

/-- Every original edge of a nonempty walk has its literal canonical proper
edge in the direct lift. -/
theorem canonicalProperEdge_mem_canonicalConsWalk (Z : FracturedWarp Gamma) :
    ∀ {x y z : V} (h : Gamma.graph.Adj x y) (q : Walk Gamma.graph y z)
      {a b : V}, (a, b) ∈ (Walk.cons h q).edgeSet →
        (outgoing a, incoming b) ∈ (canonicalConsWalk Z h q).edgeSet := by
  intro x y z h q
  induction q generalizing x with
  | nil =>
      intro a b hab
      simp only [Walk.edgeSet_cons, Walk.edgeSet_nil, Set.union_empty,
        Set.mem_singleton_iff] at hab ⊢
      cases hab
      simp [canonicalConsWalk]
  | @cons y w z hnext q ih =>
      intro a b hab
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hab ⊢
      rcases hab with hab | hab
      · cases hab
        exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (ih hnext hab)))

/-- Conversely, every nonconnector edge of the direct walk is one of those
canonical proper lifts and projects to a literal original edge. -/
theorem canonicalConsWalk_edge_roles_of_project_ne
    (Z : FracturedWarp Gamma) :
    ∀ {x y z : V} (h : Gamma.graph.Adj x y) (q : Walk Gamma.graph y z)
      {e : Vertex V × Vertex V},
      e ∈ (canonicalConsWalk Z h q).edgeSet →
      project e.1 ≠ project e.2 →
      e.1 = outgoing (project e.1) ∧
        e.2 = incoming (project e.2) ∧
        (project e.1, project e.2) ∈ (Walk.cons h q).edgeSet := by
  intro x y z h q
  induction q generalizing x with
  | nil =>
      intro e he hproper
      simp only [canonicalConsWalk, Walk.edgeSet_cons, Walk.edgeSet_nil,
        Set.union_empty, Set.mem_singleton_iff] at he
      subst e
      exact ⟨rfl, rfl, by simp⟩
  | @cons y w z hnext q ih =>
      intro e he hproper
      simp only [canonicalConsWalk, Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with he | he | he | he
      · subst e
        exact ⟨rfl, rfl, by simp⟩
      · subst e
        exact False.elim (hproper rfl)
      · subst e
        exact False.elim (hproper rfl)
      · obtain ⟨h₁, h₂, hedge⟩ := ih hnext he hproper
        exact ⟨h₁, h₂, Set.mem_union_right _ hedge⟩

/-- A first-edge decomposition of a nontrivial finite member. -/
structure FirstConsData (p : FinitePath Gamma.graph) where
  middle : V
  first : Gamma.graph.Adj p.start middle
  tail : Walk Gamma.graph middle p.finish
  walk_eq : p.walk = .cons first tail

theorem exists_firstConsData (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) : Nonempty (FirstConsData p) := by
  obtain ⟨y, hxy, q, hpwalk⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish Gamma.graph.Adj p.walk hne
  exact ⟨⟨y, hxy, q, hpwalk⟩⟩

/-- Canonical first-edge data. -/
def firstConsData (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) : FirstConsData p :=
  Classical.choice (exists_firstConsData p hne)

/-- The direct walk has the same ordered support as the previously verified
canonical interval lift. -/
theorem canonicalConsWalk_support_eq_lift (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    (canonicalConsWalk Z (firstConsData p hne).first
        (firstConsData p hne).tail).support =
      (lift Z p hne).walk.support := by
  let A := firstConsData p hne
  let D := canonicalOccurrenceData Z p hne
  have hpSupport : p.walk.support = p.start :: A.tail.support := by
    rw [A.walk_eq]
    rfl
  have hcanonical := canonicalConsWalk_support_expansion Z A.first A.tail
  have hfull : (swappedExpansion Z p).walk.support =
      [incoming p.start, plain p.start] ++
        (canonicalConsWalk Z A.first A.tail).support ++
          [plain p.finish, outgoing p.finish] := by
    rw [swappedExpansion_support, hpSupport]
    exact hcanonical.symm
  have hlift : (swappedExpansion Z p).walk.support =
      [incoming p.start, plain p.start] ++ (lift Z p hne).walk.support ++
        [plain p.finish, outgoing p.finish] := by
    rw [D.occurrence.support_eq, D.before_eq, D.after_eq]
    change [incoming p.start, plain p.start] ++
        outgoing p.start :: D.occurrence.middle ++
          incoming p.finish :: [plain p.finish, outgoing p.finish] =
      [incoming p.start, plain p.start] ++
        ((swappedExpansion Z p).between D.occurrence).walk.support ++
          [plain p.finish, outgoing p.finish]
    rw [(swappedExpansion Z p).between_support_eq D.occurrence]
    simp only [List.append_assoc, List.singleton_append]
  have hboth := hfull.symm.trans hlift
  have hright := List.append_cancel_right hboth
  exact List.append_cancel_left hright

/-- The direct nontrivial canonical finite path. -/
def activeLiftFinitePath (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    FinitePath (web Gamma Z).graph where
  start := outgoing p.start
  finish := incoming p.finish
  walk := canonicalConsWalk Z (firstConsData p hne).first
    (firstConsData p hne).tail
  isPath := by
    rw [Walk.IsPath, canonicalConsWalk_support_eq_lift Z p hne]
    exact (lift Z p hne).isPath

@[simp] theorem activeLiftFinitePath_start (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    (activeLiftFinitePath Z p hne).start = outgoing p.start := rfl

@[simp] theorem activeLiftFinitePath_finish (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    (activeLiftFinitePath Z p hne).finish = incoming p.finish := rfl

/-- Projection of the direct active lift has exactly the original support. -/
theorem project_image_activeLiftFinitePath_support
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) :
    project '' (activeLiftFinitePath Z p hne).support = p.support := by
  change project '' {z | z ∈
    (canonicalConsWalk Z (firstConsData p hne).first
      (firstConsData p hne).tail).support} = p.support
  rw [canonicalConsWalk_support_eq_lift Z p hne]
  exact project_image_lift_support Z p hne

/-- Every downstairs edge has its actual canonical occurrence in the direct
active lift. -/
theorem canonicalProperEdge_mem_activeLiftFinitePath
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) {a b : V} (hab : (a, b) ∈ p.edgeSet) :
    (outgoing a, incoming b) ∈ (activeLiftFinitePath Z p hne).edgeSet := by
  let A := firstConsData p hne
  have hab' : (a, b) ∈ (Walk.cons A.first A.tail).edgeSet := by
    rw [← A.walk_eq]
    exact hab
  exact canonicalProperEdge_mem_canonicalConsWalk Z A.first A.tail hab'

/-- Every proper upstairs edge of the direct active lift has the forced roles
and projects back to the original owner. -/
theorem activeLiftFinitePath_edge_roles_of_project_ne
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) {e : Vertex V × Vertex V}
    (he : e ∈ (activeLiftFinitePath Z p hne).edgeSet)
    (hproper : project e.1 ≠ project e.2) :
    e.1 = outgoing (project e.1) ∧
      e.2 = incoming (project e.2) ∧
      (project e.1, project e.2) ∈ p.edgeSet := by
  let A := firstConsData p hne
  have hclass := canonicalConsWalk_edge_roles_of_project_ne
    Z A.first A.tail he hproper
  refine ⟨hclass.1, hclass.2.1, ?_⟩
  change (project e.1, project e.2) ∈ p.walk.edgeSet
  rw [A.walk_eq]
  exact hclass.2.2

/-- Exact proper-edge image for a direct active owner. -/
theorem properEdge_image_activeLiftFinitePath
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) :
    (fun e : Vertex V × Vertex V ↦ (project e.1, project e.2)) ''
        {e | e ∈ (activeLiftFinitePath Z p hne).edgeSet ∧
          project e.1 ≠ project e.2} = p.edgeSet := by
  apply Set.Subset.antisymm
  · rintro e ⟨f, ⟨hf, hfproper⟩, rfl⟩
    exact (activeLiftFinitePath_edge_roles_of_project_ne
      Z p hne hf hfproper).2.2
  · rintro ⟨a, b⟩ hab
    refine ⟨(outgoing a, incoming b), ⟨
      canonicalProperEdge_mem_activeLiftFinitePath Z p hne hab, ?_⟩, rfl⟩
    intro habEq
    have hends := p.edgeSet_subset_support_prod hab
    have hwalkNodup : p.walk.support.Nodup := p.isPath
    have ha : a ≠ b := by
      obtain ⟨n, hn, hna, hnb⟩ :=
        Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hab
      intro heq
      have hn0 : n < p.walk.support.length := by omega
      have hget : p.walk.support[n]'hn0 = p.walk.support[n + 1]'hn :=
        hna.trans (heq.trans hnb.symm)
      exact Nat.ne_of_lt (Nat.lt_succ_self n) (hwalkNodup.getElem_inj_iff.mp hget)
    exact ha habEq

/-- Explicit singleton-aware canonical reference lift. -/
def referenceLiftFinitePath (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) : FinitePath (web Gamma Z).graph := by
  classical
  exact if h : p.start = p.finish then
    FinitePath.trivial (web Gamma Z).graph (outgoing p.start)
  else activeLiftFinitePath Z p h

/-- The exact initial copy used by the singleton-aware lift. -/
def referenceInitialCopy (p : FinitePath Gamma.graph) : Vertex V :=
  outgoing p.start

/-- The exact terminal copy used by the singleton-aware lift. -/
def referenceTerminalCopy (p : FinitePath Gamma.graph) : Vertex V := by
  classical
  exact if p.start = p.finish then outgoing p.finish else incoming p.finish

@[simp] theorem referenceLiftFinitePath_start (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) :
    (referenceLiftFinitePath Z p).start = referenceInitialCopy p := by
  by_cases h : p.start = p.finish
  · simp [referenceLiftFinitePath, referenceInitialCopy, h]
  · simp [referenceLiftFinitePath, referenceInitialCopy, h]

@[simp] theorem referenceLiftFinitePath_finish (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) :
    (referenceLiftFinitePath Z p).finish = referenceTerminalCopy p := by
  by_cases h : p.start = p.finish
  · simp [referenceLiftFinitePath, referenceTerminalCopy, h]
  · simp [referenceLiftFinitePath, referenceTerminalCopy, h]

private theorem finiteEdge_endpoints_ne (p : FinitePath Gamma.graph)
    {a b : V} (hab : (a, b) ∈ p.edgeSet) : a ≠ b := by
  obtain ⟨n, hn, hna, hnb⟩ :=
    Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hab
  intro heq
  have hn0 : n < p.walk.support.length := by omega
  have hget : p.walk.support[n]'hn0 = p.walk.support[n + 1]'hn :=
    hna.trans (heq.trans hnb.symm)
  exact Nat.ne_of_lt (Nat.lt_succ_self n) (p.isPath.getElem_inj_iff.mp hget)

private theorem finitePath_edgeSet_eq_empty_of_start_eq_finish
    (p : FinitePath Gamma.graph) (h : p.start = p.finish) :
    p.edgeSet = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he
  have hsupp : p.walk.support = [p.start] :=
    walk_support_eq_singleton_of_isPath_of_endpoints_eq p.walk p.isPath h
  have hends := p.edgeSet_subset_support_prod he
  change e.1 ∈ p.walk.support ∧ e.2 ∈ p.walk.support at hends
  rw [hsupp] at hends
  have hfirst : e.1 = p.start := by simpa using hends.1
  have hsecond : e.2 = p.start := by simpa using hends.2
  exact finiteEdge_endpoints_ne p he (hfirst.trans hsecond.symm)

/-- Projection of a singleton-aware canonical reference owner has exactly the
original support. -/
theorem project_image_referenceLiftFinitePath_support
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph) :
    project '' (referenceLiftFinitePath Z p).support = p.support := by
  by_cases h : p.start = p.finish
  · rw [referenceLiftFinitePath, dif_pos h, FinitePath.support_trivial]
    have hsupp : p.walk.support = [p.start] :=
      walk_support_eq_singleton_of_isPath_of_endpoints_eq p.walk p.isPath h
    change project '' ({outgoing p.start} : Set (Vertex V)) =
      {x | x ∈ p.walk.support}
    rw [hsupp]
    ext x
    simp
  · rw [referenceLiftFinitePath, dif_neg h]
    exact project_image_activeLiftFinitePath_support Z p h

/-- Every original reference edge has its actual canonical occurrence in the
singleton-aware lift. -/
theorem canonicalProperEdge_mem_referenceLiftFinitePath
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    {a b : V} (hab : (a, b) ∈ p.edgeSet) :
    (outgoing a, incoming b) ∈ (referenceLiftFinitePath Z p).edgeSet := by
  have hne : p.start ≠ p.finish := by
    intro h
    rw [finitePath_edgeSet_eq_empty_of_start_eq_finish p h] at hab
    exact hab
  rw [referenceLiftFinitePath, dif_neg hne]
  exact canonicalProperEdge_mem_activeLiftFinitePath Z p hne hab

/-- Every proper edge of the singleton-aware lift has canonical roles and
projects back to its original owner. -/
theorem referenceLiftFinitePath_edge_roles_of_project_ne
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    {e : Vertex V × Vertex V}
    (he : e ∈ (referenceLiftFinitePath Z p).edgeSet)
    (hproper : project e.1 ≠ project e.2) :
    e.1 = outgoing (project e.1) ∧
      e.2 = incoming (project e.2) ∧
      (project e.1, project e.2) ∈ p.edgeSet := by
  by_cases h : p.start = p.finish
  · rw [referenceLiftFinitePath, dif_pos h] at he
    simpa [FinitePath.edgeSet, FinitePath.trivial] using he
  · rw [referenceLiftFinitePath, dif_neg h] at he
    exact activeLiftFinitePath_edge_roles_of_project_ne Z p h he hproper

/-- Exact proper-edge image for every singleton-aware reference owner. -/
theorem properEdge_image_referenceLiftFinitePath
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph) :
    (fun e : Vertex V × Vertex V ↦ (project e.1, project e.2)) ''
        {e | e ∈ (referenceLiftFinitePath Z p).edgeSet ∧
          project e.1 ≠ project e.2} = p.edgeSet := by
  by_cases h : p.start = p.finish
  · rw [referenceLiftFinitePath, dif_pos h,
      finitePath_edgeSet_eq_empty_of_start_eq_finish p h]
    ext e
    simp [FinitePath.edgeSet, FinitePath.trivial]
  · rw [referenceLiftFinitePath, dif_neg h]
    exact properEdge_image_activeLiftFinitePath Z p h

/-- Canonical lifts of all finite members of the reference family. -/
def liftedReferencePaths (Z : FracturedWarp Gamma)
    (Y : Set Gamma.DPath) : Set (web Gamma Z).DPath :=
  {P | ∃ (p : FinitePath Gamma.graph),
    (.inl p : Gamma.DPath) ∈ Y ∧ P = .inl (referenceLiftFinitePath Z p)}

theorem referenceLiftFinitePath_mem_liftedReferencePaths
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    {p : FinitePath Gamma.graph} (hp : (.inl p : Gamma.DPath) ∈ Y) :
    (.inl (referenceLiftFinitePath Z p) : (web Gamma Z).DPath) ∈
      liftedReferencePaths Z Y :=
  ⟨p, hp, rfl⟩

theorem liftedReferencePaths_hasFiniteCharacter
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) :
    (web Gamma Z).HasFiniteCharacter (liftedReferencePaths Z Y) := by
  rintro P ⟨p, hp, rfl⟩
  exact ⟨referenceLiftFinitePath Z p, rfl⟩

/-- An honest finite-character reference warp remains an honest warp after
the canonical lift. -/
theorem liftedReferencePaths_isWarp (Z : FracturedWarp Gamma)
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y) :
    (web Gamma Z).IsWarp (liftedReferencePaths Z Y) := by
  rintro P ⟨p, hp, rfl⟩ Q ⟨q, hq, rfl⟩ hPQ
  have hpq : (.inl p : Gamma.DPath) ≠ .inl q := by
    intro hpq'
    have : p = q := Sum.inl.inj hpq'
    subst q
    exact hPQ rfl
  apply Set.disjoint_left.2
  intro z hzp hzq
  have hxp : project z ∈ p.support := by
    rw [← project_image_referenceLiftFinitePath_support Z p]
    exact ⟨z, hzp, rfl⟩
  have hxq : project z ∈ q.support := by
    rw [← project_image_referenceLiftFinitePath_support Z q]
    exact ⟨z, hzq, rfl⟩
  exact Set.disjoint_left.1 (hY hp hq hpq) hxp hxq

/-- Precise lifted initials.  Singleton and active owners both use the
outgoing copy. -/
theorem initialSet_liftedReferencePaths (Z : FracturedWarp Gamma)
    (Y : Set Gamma.DPath) :
    (web Gamma Z).initialSet (liftedReferencePaths Z Y) =
      {z | ∃ (p : FinitePath Gamma.graph),
        (.inl p : Gamma.DPath) ∈ Y ∧ z = referenceInitialCopy p} := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hz⟩
    exact ⟨p, hp, hz.symm.trans (referenceLiftFinitePath_start Z p)⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨.inl (referenceLiftFinitePath Z p), ⟨p, hp, rfl⟩,
      referenceLiftFinitePath_start Z p⟩

/-- Precise lifted finite terminals.  A singleton stays at its outgoing
initial copy; an active owner ends at the incoming copy. -/
theorem terminalFrontier_liftedReferencePaths (Z : FracturedWarp Gamma)
    (Y : Set Gamma.DPath) :
    (web Gamma Z).terminalFrontier (liftedReferencePaths Z Y) =
      {z | ∃ (p : FinitePath Gamma.graph),
        (.inl p : Gamma.DPath) ∈ Y ∧ z = referenceTerminalCopy p} := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hterm⟩
    have hz : referenceTerminalCopy p = z := by
      change some (referenceLiftFinitePath Z p).finish = some z at hterm
      rw [referenceLiftFinitePath_finish] at hterm
      exact Option.some.inj hterm
    exact ⟨p, hp, hz.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨.inl (referenceLiftFinitePath Z p), ⟨p, hp, rfl⟩, by simp⟩

/-- Every edge of a finite-character downstairs reference family has its
literal canonical proper occurrence in the lifted family. -/
theorem canonicalProperEdge_mem_familyEdges_liftedReferencePaths
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y) {a b : V}
    (hab : (a, b) ∈ familyEdges Y) :
    (outgoing a, incoming b) ∈ familyEdges (liftedReferencePaths Z Y) := by
  simp only [familyEdges, Set.mem_iUnion] at hab ⊢
  rcases hab with ⟨P, hp, hab⟩
  rcases hYfinite hp with ⟨p, rfl⟩
  exact ⟨.inl (referenceLiftFinitePath Z p),
    referenceLiftFinitePath_mem_liftedReferencePaths Z hp,
    canonicalProperEdge_mem_referenceLiftFinitePath Z p hab⟩

/-- Exact proper-edge image of the whole finite-character reference lift. -/
theorem properEdge_image_liftedReferencePaths
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hYfinite : Gamma.HasFiniteCharacter Y) :
    (fun e : Vertex V × Vertex V ↦ (project e.1, project e.2)) ''
        {e | e ∈ familyEdges (liftedReferencePaths Z Y) ∧
          project e.1 ≠ project e.2} = familyEdges Y := by
  apply Set.Subset.antisymm
  · rintro e ⟨f, ⟨hf, hfproper⟩, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hf ⊢
    rcases hf with ⟨P, ⟨p, hp, rfl⟩, hf⟩
    have hclass := referenceLiftFinitePath_edge_roles_of_project_ne
      Z p hf hfproper
    exact ⟨.inl p, hp, hclass.2.2⟩
  · intro e he
    simp only [familyEdges, Set.mem_iUnion] at he
    rcases he with ⟨P, hp, he⟩
    rcases hYfinite hp with ⟨p, rfl⟩
    have heImage : e ∈
        (fun f : Vertex V × Vertex V ↦ (project f.1, project f.2)) ''
          {f | f ∈ (referenceLiftFinitePath Z p).edgeSet ∧
            project f.1 ≠ project f.2} := by
      rw [properEdge_image_referenceLiftFinitePath Z p]
      exact he
    rcases heImage with ⟨f, ⟨hf, hfproper⟩, rfl⟩
    refine ⟨f, ⟨?_, hfproper⟩, rfl⟩
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl (referenceLiftFinitePath Z p),
      referenceLiftFinitePath_mem_liftedReferencePaths Z hp, hf⟩

/-- Projection is injective on all proper edges of the canonical lifted
reference family.  Together with the exact image theorem, this says every
downstairs edge has exactly one upstairs proper lift. -/
theorem projectEdge_injOn_proper_liftedReferencePaths
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) :
    Set.InjOn (fun e : Vertex V × Vertex V ↦
      (project e.1, project e.2))
      {e | e ∈ familyEdges (liftedReferencePaths Z Y) ∧
        project e.1 ≠ project e.2} := by
  intro e he f hf hproject
  have heFamily := he.1
  simp only [familyEdges, Set.mem_iUnion] at heFamily
  rcases heFamily with ⟨P, ⟨p, hp, rfl⟩, hep⟩
  have heClass := referenceLiftFinitePath_edge_roles_of_project_ne
    Z p hep he.2
  have hfFamily := hf.1
  simp only [familyEdges, Set.mem_iUnion] at hfFamily
  rcases hfFamily with ⟨Q, ⟨q, hq, rfl⟩, hfq⟩
  have hfClass := referenceLiftFinitePath_edge_roles_of_project_ne
    Z q hfq hf.2
  change (project e.1, project e.2) =
    (project f.1, project f.2) at hproject
  have hfirst : project e.1 = project f.1 :=
    congrArg (fun z : V × V ↦ z.1) hproject
  have hsecond : project e.2 = project f.2 :=
    congrArg (fun z : V × V ↦ z.2) hproject
  apply Prod.ext
  · rw [heClass.1, hfClass.1, hfirst]
  · rw [heClass.2.1, hfClass.2.1, hsecond]

#print axioms liftedReferencePaths_isWarp
#print axioms properEdge_image_liftedReferencePaths
#print axioms projectEdge_injOn_proper_liftedReferencePaths

end Erdos599.Alternating.FracturedCanonicalReferenceLift

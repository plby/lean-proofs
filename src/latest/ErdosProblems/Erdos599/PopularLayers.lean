/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Popular

/-!
# The popular-layer argument

This file proves the layer induction in Aharoni--Berger, Section 8.  The
one-edge extension below is deliberately stated for concrete paths: if the
new terminal set has already been met, the path is cut at its first hit;
otherwise the chosen last edge is appended.  This is the small normalization
step hidden by the phrase "adding edges" in Assertions 8.8 and 8.9.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u

variable {V : Type u}

/-! ## Normalized one-edge extension -/

/-- The result of sending a finite path one layer toward `T`.  Outside `T`
the new path is contained in the old path, and it meets `T` only at its new
terminal. -/
structure TowardExtension {Γ : DWeb V} (p : FinitePath Γ.graph) (T : Set V) where
  path : FinitePath Γ.graph
  start_eq : path.start = p.start
  finish_mem : path.finish ∈ T
  outside_support : path.support \ T ⊆ p.support
  join_only_at_end : path.support ∩ T ⊆ {path.finish}

/-- Cut at the first old `T`-vertex, or append a prescribed edge to `T` when
there was no old hit. -/
def extendToward {Γ : DWeb V} (p : FinitePath Γ.graph) (T : Set V)
    {w : V} (hw : w ∈ T) (e : Γ.graph.Adj p.finish w) :
    TowardExtension p T := by
  classical
  by_cases hmeet : p.walk.Meets T
  · let q := p.firstHit T hmeet
    refine
      { path := q
        start_eq := rfl
        finish_mem := p.firstHit_finish_mem T hmeet
        outside_support := ?_
        join_only_at_end := ?_ }
    · intro x hx
      exact p.firstHit_support_subset T hmeet hx.1
    · intro x hx
      apply Set.mem_singleton_iff.2
      by_contra hne
      have hxdrop : x ∈ q.walk.support.dropLast := by
        apply List.mem_dropLast_of_mem_of_ne_getLast hx.1
        simpa [q] using hne
      exact p.firstHit_no_mem_before T hmeet hxdrop hx.2
  · have hwold : w ∉ p.support := by
      intro hwp
      exact hmeet ⟨w, hwp, hw⟩
    let q : FinitePath Γ.graph :=
      { start := p.start
        finish := w
        walk := p.walk.concat e
        isPath := by
          rw [Walk.IsPath, Walk.support_concat]
          exact p.isPath.append (by simp) (by simpa [List.disjoint_singleton]) }
    refine
      { path := q
        start_eq := rfl
        finish_mem := hw
        outside_support := ?_
        join_only_at_end := ?_ }
    · intro x hx
      have hxsupp : x ∈ p.walk.support ++ [w] := by
        simpa [q, FinitePath.support] using hx.1
      simp only [List.mem_append, List.mem_singleton] at hxsupp
      exact hxsupp.elim id fun hxw ↦ (hx.2 (hxw ▸ hw)).elim
    · intro x hx
      apply Set.mem_singleton_iff.2
      have hxsupp : x ∈ p.walk.support ++ [w] := by
        simpa [q, FinitePath.support] using hx.1
      simp only [List.mem_append, List.mem_singleton] at hxsupp
      exact hxsupp.elim
        (fun hxp ↦ (hmeet ⟨x, hxp, hx.2⟩).elim)
        id

@[simp]
theorem extendToward_start {Γ : DWeb V} (p : FinitePath Γ.graph)
    (T : Set V) {w : V} (hw : w ∈ T) (e : Γ.graph.Adj p.finish w) :
    (extendToward p T hw e).path.start = p.start :=
  (extendToward p T hw e).start_eq

theorem extendToward_support_subset {Γ : DWeb V}
    (p : FinitePath Γ.graph) (T : Set V) {w : V} (hw : w ∈ T)
    (e : Γ.graph.Adj p.finish w) :
    (extendToward p T hw e).path.support ⊆ p.support ∪ T := by
  intro x hx
  by_cases hxT : x ∈ T
  · exact Or.inr hxT
  · exact Or.inl <| (extendToward p T hw e).outside_support ⟨hx, hxT⟩

/-- Select one outgoing edge toward `T` at every point of `S`. -/
def nextVertex {Γ : DWeb V} {S T : Set V}
    (hnext : S ⊆ inNeighbors Γ T) (u : S) : V :=
  Classical.choose (hnext u.2)

theorem nextVertex_mem {Γ : DWeb V} {S T : Set V}
    (hnext : S ⊆ inNeighbors Γ T) (u : S) : nextVertex hnext u ∈ T :=
  (Classical.choose_spec (hnext u.2)).1

theorem nextVertex_adj {Γ : DWeb V} {S T : Set V}
    (hnext : S ⊆ inNeighbors Γ T) (u : S) :
    Γ.graph.Adj u.1 (nextVertex hnext u) :=
  (Classical.choose_spec (hnext u.2)).2

/-! ## Pushing a disjoint warp to the preceding layer -/

/-- Pushing every path of a warp one step toward `T` produces a normalized
`T`-joined family.  Different pushed paths can acquire the same last vertex,
but all their other vertices remain in the disjoint old paths. -/
def XSWarp.pushToJoined {Γ : DWeb V} {S T : Set V} (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w) :
    JoinedFamily Γ T where
  paths := Set.range fun p : P.paths ↦ P.pushPath hstep p.1 p.2
  starts_in_source := by
    rintro q ⟨p, rfl⟩
    rw [P.pushPath_start hstep p.1 p.2]
    exact P.starts_in_source p.2
  ends_in_join := by
    rintro q ⟨p, rfl⟩
    exact P.pushPath_finish_mem hstep p.1 p.2
  join_only_at_end := by
    rintro q ⟨p, rfl⟩
    exact P.pushPath_join_only_at_end hstep p.1 p.2
  joined := by
    rintro q ⟨p, rfl⟩ r ⟨p', rfl⟩ hqr x hx
    by_contra hxT
    have hxold : x ∈ p.1.support :=
      (P.pushPath_support_subset hstep p.1 p.2 hx.1).resolve_right hxT
    have hxold' : x ∈ p'.1.support :=
      (P.pushPath_support_subset hstep p'.1 p'.2 hx.2).resolve_right hxT
    have hpp' : p.1 = p'.1 := by
      by_contra hne
      exact Set.disjoint_left.1 (P.disjoint p.2 p'.2 hne) hxold hxold'
    apply hqr
    have hpSub : p = p' := Subtype.ext hpp'
    exact congrArg (fun z : P.paths ↦ P.pushPath hstep z.1 z.2) hpSub

/-- Pushing preserves all initial indices. -/
theorem initialIndices_pushToJoined_subset {Γ : DWeb V}
    {κ : Cardinal.{u}} (U : KappaIndexed Γ κ) {S T : Set V}
    (P : XSWarp Γ S)
    (hstep : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w) :
    initialIndicesOf U P.paths P.starts_in_source ⊆
      initialIndicesOf U (P.pushToJoined hstep).paths
        (P.pushToJoined hstep).starts_in_source := by
  intro a ha
  obtain ⟨p, hp, ha⟩ := ha
  let q := P.pushPath hstep p hp
  refine ⟨q, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
  have hsource :
      (⟨q.start, (P.pushToJoined hstep).starts_in_source
        ⟨⟨p, hp⟩, rfl⟩⟩ : Γ.source) =
      ⟨p.start, P.starts_in_source hp⟩ := by
    apply Subtype.ext
    exact P.pushPath_start hstep p hp
  exact (congrArg U.f hsource).trans ha

/-! ## Terminal fibres of joined families -/

/-- Terminals at which a joined family has at least one path. -/
def activeTerminals {Γ : DWeb V} {S : Set V}
    (F : JoinedFamily Γ S) : Set S :=
  {y | ∃ p ∈ F.paths, p.finish = y.1}

/-- The initial-index fibre at an active terminal. -/
def terminalIndexFiber {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (y : activeTerminals F) : Set (Below κ) :=
  initialIndicesOf U (F.finishFiber y.1.1).paths
    (F.finishFiber y.1.1).starts_in_source

theorem terminalIndexFiber_nonempty {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (y : activeTerminals F) : (terminalIndexFiber U F y).Nonempty := by
  obtain ⟨p, hp, hpy⟩ := y.2
  refine ⟨U.f ⟨p.start, F.starts_in_source hp⟩, p, ⟨hp, hpy⟩, rfl⟩

/-- Splitting by the terminal loses no initial indices. -/
theorem initialIndices_eq_iUnion_terminalIndexFiber
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S : Set V} (F : JoinedFamily Γ S) :
    initialIndicesOf U F.paths F.starts_in_source =
      ⋃ y : activeTerminals F, terminalIndexFiber U F y := by
  ext a
  constructor
  · rintro ⟨p, hp, ha⟩
    let y : activeTerminals F :=
      ⟨⟨p.finish, F.ends_in_join hp⟩, p, hp, rfl⟩
    exact Set.mem_iUnion.2 ⟨y, ⟨p, ⟨hp, rfl⟩, ha⟩⟩
  · rintro ha
    obtain ⟨y, p, hp, ha⟩ := Set.mem_iUnion.1 ha
    exact ⟨p, hp.1, ha⟩

/-- A path realizing a prescribed initial index in one terminal fibre. -/
def chosenFiberPath {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y)
    (y : activeTerminals F) : FinitePath Γ.graph :=
  Classical.choose (hg y)

theorem chosenFiberPath_mem {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y)
    (y : activeTerminals F) :
    chosenFiberPath U F g hg y ∈ F.paths :=
  (Classical.choose_spec (hg y)).1.1

theorem chosenFiberPath_finish {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y)
    (y : activeTerminals F) :
    (chosenFiberPath U F g hg y).finish = y.1.1 :=
  (Classical.choose_spec (hg y)).1.2

theorem chosenFiberPath_index {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y)
    (y : activeTerminals F) :
    U.f ⟨(chosenFiberPath U F g hg y).start,
      F.starts_in_source (chosenFiberPath_mem U F g hg y)⟩ = g y :=
  (Classical.choose_spec (hg y)).2

/-- Choosing one path in every nonempty terminal fibre turns a joined family
into a genuinely disjoint warp. -/
def selectedFiberWarp {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {S : Set V} (F : JoinedFamily Γ S)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y) : XSWarp Γ S where
  paths := Set.range (chosenFiberPath U F g hg)
  disjoint := by
    rintro p ⟨y, rfl⟩ q ⟨z, rfl⟩ hpq
    apply Set.disjoint_left.2
    intro x hxp hxq
    have hxS : x ∈ S := F.joined
      (chosenFiberPath_mem U F g hg y)
      (chosenFiberPath_mem U F g hg z) hpq ⟨hxp, hxq⟩
    have hxy : x = (chosenFiberPath U F g hg y).finish :=
      Set.mem_singleton_iff.1 <| F.join_only_at_end
        (chosenFiberPath_mem U F g hg y) ⟨hxp, hxS⟩
    have hxz : x = (chosenFiberPath U F g hg z).finish :=
      Set.mem_singleton_iff.1 <| F.join_only_at_end
        (chosenFiberPath_mem U F g hg z) ⟨hxq, hxS⟩
    have hyz : y.1.1 = z.1.1 := by
      rw [← chosenFiberPath_finish U F g hg y,
        ← chosenFiberPath_finish U F g hg z]
      exact hxy.symm.trans hxz
    have : y = z := by
      apply Subtype.ext
      apply Subtype.ext
      exact hyz
    exact hpq (congrArg (chosenFiberPath U F g hg) this)
  starts_in_source := by
    rintro p ⟨y, rfl⟩
    exact F.starts_in_source (chosenFiberPath_mem U F g hg y)
  ends_in_target := by
    rintro p ⟨y, rfl⟩
    rw [chosenFiberPath_finish U F g hg y]
    exact y.1.2

/-- Every chosen ordinal is an initial index of the selected warp. -/
theorem range_subset_initialIndices_selectedFiberWarp
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S : Set V} (F : JoinedFamily Γ S)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y) :
    Set.range g ⊆ initialIndicesOf U (selectedFiberWarp U F g hg).paths
      (selectedFiberWarp U F g hg).starts_in_source := by
  rintro a ⟨y, rfl⟩
  let p := chosenFiberPath U F g hg y
  refine ⟨p, ⟨y, rfl⟩, ?_⟩
  have hsource :
      (⟨p.start, (selectedFiberWarp U F g hg).starts_in_source
        ⟨y, rfl⟩⟩ : Γ.source) =
      ⟨p.start, F.starts_in_source (chosenFiberPath_mem U F g hg y)⟩ := by
    rfl
  exact (congrArg U.f hsource).trans (chosenFiberPath_index U F g hg y)

/-- The constructive part of Assertion 8.8: once one initial index has been
selected from every terminal fibre with stationary range, the selected paths
are disjoint and can be pushed one layer, making the preceding layer popular. -/
theorem isPopular_of_stationary_terminal_selection
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S T : Set V} (F : JoinedFamily Γ S)
    (hstep : S ⊆ inNeighbors Γ T)
    (g : activeTerminals F → Below κ)
    (hg : ∀ y, g y ∈ terminalIndexFiber U F y)
    (hgstat : IsStationaryBelow κ (Set.range g)) :
    IsPopular U T := by
  let P := selectedFiberWarp U F g hg
  let hnext : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w :=
    fun _ hv ↦ hstep hv
  let H := P.pushToJoined hnext
  apply Or.inr
  refine ⟨H, hgstat.mono ?_⟩
  exact (range_subset_initialIndices_selectedFiberWarp U F g hg).trans
    (initialIndices_pushToJoined_subset U P hnext)

/-- Pushing a strongly popular warp one layer makes the preceding layer
popular.  This is the path operation used in Assertion 8.9. -/
theorem isPopular_of_stronglyPopular_of_step
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S T : Set V} (hstep : S ⊆ inNeighbors Γ T)
    (hstrong : IsStronglyPopular U S) : IsPopular U T := by
  obtain ⟨P, hstat⟩ := hstrong
  let hnext : ∀ ⦃v⦄, v ∈ S → ∃ w ∈ T, Γ.graph.Adj v w :=
    fun _ hv ↦ hstep hv
  exact Or.inr ⟨P.pushToJoined hnext,
    hstat.mono (initialIndices_pushToJoined_subset U P hnext)⟩

/-- A subset of a set which is not strongly popular is not strongly
popular. -/
theorem not_stronglyPopular_of_subset {Γ : DWeb V} {κ : Cardinal.{u}}
    {U : KappaIndexed Γ κ} {S T : Set V} (hST : S ⊆ T)
    (hT : ¬ IsStronglyPopular U T) : ¬ IsStronglyPopular U S :=
  fun hS ↦ hT (hS.mono hST)

/-! ## Restricting warps by their terminal layer -/

/-- Keep exactly the paths of a warp whose terminal lies in `T`. -/
def XSWarp.restrictTerminal {Γ : DWeb V} {S : Set V} (P : XSWarp Γ S)
    (T : Set V) : XSWarp Γ T where
  paths := {p | p ∈ P.paths ∧ p.finish ∈ T}
  disjoint := P.disjoint.subset fun _ hp ↦ hp.1
  starts_in_source hp := P.starts_in_source hp.1
  ends_in_target hp := hp.2

@[simp]
theorem XSWarp.mem_restrictTerminal {Γ : DWeb V} {S : Set V}
    (P : XSWarp Γ S) (T : Set V) (p : FinitePath Γ.graph) :
    p ∈ (P.restrictTerminal T).paths ↔ p ∈ P.paths ∧ p.finish ∈ T :=
  Iff.rfl

/-- The initial indices of a warp ending in a countable union are covered by
the initial-index sets of its terminal-layer restrictions. -/
theorem initialIndices_subset_iUnion_restrictTerminal
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {S : Set V} (P : XSWarp Γ S) (T : ℕ → Set V)
    (hcover : S ⊆ ⋃ n, T n) :
    initialIndicesOf U P.paths P.starts_in_source ⊆
      ⋃ n, initialIndicesOf U (P.restrictTerminal (T n)).paths
        (P.restrictTerminal (T n)).starts_in_source := by
  rintro a ⟨p, hp, ha⟩
  obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 (hcover (P.ends_in_target hp))
  exact Set.mem_iUnion.2 ⟨n, ⟨p, ⟨hp, hpn⟩, ha⟩⟩

/-! ## First-hit warps used to localize popularity -/

theorem firstHit_not_mem_of_finish_not_mem {Γ : DWeb V}
    (p : FinitePath Γ.graph) (T : Set V) (hmeet : p.walk.Meets T)
    (hfinish : p.finish ∉ T) : p.finish ∉ (p.firstHit T hmeet).support := by
  intro hmem
  let F := p.walk.firstHit T hmeet
  have hlast : p.walk.support.getLast p.walk.support_ne_nil ∈ F.walk.support := by
    rw [p.walk.getLast_support]
    exact hmem
  have heq : F.walk.support = p.walk.support :=
    List.Nodup.eq_of_getLast_mem_of_prefix F.support_prefix hlast p.isPath
  have hendpoint : F.endpoint = p.finish := by
    calc
      F.endpoint = F.walk.support.getLast F.walk.support_ne_nil :=
        F.walk.getLast_support.symm
      _ = p.walk.support.getLast p.walk.support_ne_nil :=
        List.getLast_congr F.walk.support_ne_nil p.walk.support_ne_nil heq
      _ = p.finish := p.walk.getLast_support
  exact hfinish (hendpoint ▸ F.endpoint_mem)

/-- Paths of `F` which meet `C` before their common terminal `s`. -/
def badPaths {Γ : DWeb V} (F : JoinedFamily Γ ({s} : Set V))
    (C : Set V) : Set (FinitePath Γ.graph) :=
  {p | p ∈ F.paths ∧ p.walk.Meets (C \ {s})}

/-- Truncate every bad path at its first earlier separator vertex.  The
common endpoint `s` disappears from every prefix, so the prefixes are a
genuine warp. -/
def badPrefixWarp {Γ : DWeb V} (F : JoinedFamily Γ ({s} : Set V))
    (C : Set V) : XSWarp Γ C where
  paths := Set.range fun p : badPaths F C ↦ p.1.firstHit (C \ {s}) p.2.2
  disjoint := by
    rintro p ⟨q, rfl⟩ r ⟨q', rfl⟩ hpr
    apply Set.disjoint_left.2
    intro x hxp hxr
    have hxq : x ∈ q.1.support :=
      q.1.firstHit_support_subset (C \ {s}) q.2.2 hxp
    have hxq' : x ∈ q'.1.support :=
      q'.1.firstHit_support_subset (C \ {s}) q'.2.2 hxr
    have hqq' : q.1 ≠ q'.1 := by
      intro heq
      apply hpr
      have hsub : q = q' := Subtype.ext heq
      exact congrArg
        (fun z : badPaths F C ↦ z.1.firstHit (C \ {s}) z.2.2) hsub
    have hxs : x = s := Set.mem_singleton_iff.1 <|
      F.joined q.2.1 q'.2.1 hqq' ⟨hxq, hxq'⟩
    subst x
    have hsfinish : q.1.finish = s :=
      Set.mem_singleton_iff.1 (F.ends_in_join q.2.1)
    apply firstHit_not_mem_of_finish_not_mem q.1 (C \ {s}) q.2.2
      (by simp [hsfinish])
    simpa only [hsfinish] using hxp
  starts_in_source := by
    rintro p ⟨q, rfl⟩
    change q.1.start ∈ Γ.source
    exact F.starts_in_source q.2.1
  ends_in_target := by
    rintro p ⟨q, rfl⟩
    exact (q.1.firstHit_finish_mem (C \ {s}) q.2.2).1

/-- Truncation at the first earlier `C`-hit preserves all bad-path initial
indices. -/
theorem initialIndices_badPaths_subset_badPrefixWarp
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {s : V} (F : JoinedFamily Γ ({s} : Set V)) (C : Set V) :
    initialIndicesOf U (badPaths F C)
        (fun hp ↦ F.starts_in_source hp.1) ⊆
      initialIndicesOf U (badPrefixWarp F C).paths
        (badPrefixWarp F C).starts_in_source := by
  rintro a ⟨p, hp, ha⟩
  let q : badPaths F C := ⟨p, hp⟩
  let r := p.firstHit (C \ {s}) hp.2
  refine ⟨r, ⟨q, rfl⟩, ?_⟩
  have hsource :
      (⟨r.start, (badPrefixWarp F C).starts_in_source ⟨q, rfl⟩⟩ : Γ.source) =
      ⟨p.start, F.starts_in_source hp.1⟩ := by
    rfl
  exact (congrArg U.f hsource).trans ha

/-- The paths of a singleton-joined family which meet `C` only at the
common terminal. -/
def goodPaths {Γ : DWeb V} (F : JoinedFamily Γ ({s} : Set V))
    (C : Set V) : Set (FinitePath Γ.graph) :=
  {p | p ∈ F.paths ∧ ¬ p.walk.Meets (C \ {s})}

/-- Restrict a singleton-joined family to the paths having no earlier
`C`-hit. -/
def goodJoinedFamily {Γ : DWeb V} (F : JoinedFamily Γ ({s} : Set V))
    (C : Set V) : JoinedFamily Γ {s} where
  paths := goodPaths F C
  starts_in_source hp := F.starts_in_source hp.1
  ends_in_join hp := F.ends_in_join hp.1
  join_only_at_end hp := F.join_only_at_end hp.1
  joined := by
    intro p hp q hq hpq
    exact F.joined hp.1 hq.1 hpq

/-- The good subfan is normalized against the whole ambient candidate set:
its only possible `C`-vertex is its common terminal.  This is exactly the
extra hypothesis in the Aharoni Lemma 2.5 application. -/
theorem goodJoinedFamily_normalized {Γ : DWeb V}
    (F : JoinedFamily Γ ({s} : Set V)) (C : Set V) :
    ∀ {p}, p ∈ (goodJoinedFamily F C).paths →
      p.support ∩ C ⊆ {s} := by
  intro p hp
  exact JoinedFamily.support_inter_subset_singleton_of_not_meets_sdiff
    p hp.2

/-! ## Aharoni's normalized fan-covering lemma -/

/-- Source Lemma 8.6, supplied by Aharoni's Lemma 2.5 after reversing all
paths.  More than `κ` normalized singleton in-fans toward a source of size
at most `κ` yield a disjoint source--`C` warp which covers the initial
vertices of one entire fan. -/
theorem lemma8_6_exists_warp_covering_one_joinedFamily
    {Γ : DWeb V} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    {C : Set V} (hCX : Disjoint C Γ.source) (hsource : #Γ.source ≤ κ)
    (hlarge : κ < #C) (F : (c : C) → JoinedFamily Γ {c.1})
    (hnorm : ∀ c {p}, p ∈ (F c).paths → p.support ∩ C ⊆ {c.1}) :
    ∃ (P : XSWarp Γ C) (c : C),
      ∀ {p}, p ∈ (F c).paths →
        ∃ q ∈ P.paths, q.start = p.start := by
  let H : (c : C) → Aharoni25.InFan (transpose Γ.graph) C Γ.source c.1 :=
    fun c ↦ (F c).reverseInFan c (hnorm c)
  obtain ⟨c, W, hW⟩ := Aharoni25.exists_warp_covering_one_fan
    hκ hCX hsource hlarge H
  let P : XSWarp Γ C :=
    JoinedFamily.unreverseWarp W.paths W.disjoint W.start_mem W.finish_mem
  refine ⟨P, c, ?_⟩
  intro p hp
  have hprev : p.reverse ∈ (H c).paths := by
    exact ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hfinish⟩ := hW p.reverse hprev
  refine ⟨JoinedFamily.unreverse q, ⟨q, hq, rfl⟩, ?_⟩
  change q.finish = p.start at hfinish
  simpa only [JoinedFamily.unreverse_start] using hfinish

/-- Every old initial index lies in the bad or good subfamily. -/
theorem initialIndices_subset_bad_union_good
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {s : V} (F : JoinedFamily Γ ({s} : Set V)) (C : Set V) :
    initialIndicesOf U F.paths F.starts_in_source ⊆
      initialIndicesOf U (badPaths F C) (fun hp ↦ F.starts_in_source hp.1) ∪
      initialIndicesOf U (goodPaths F C) (fun hp ↦ F.starts_in_source hp.1) := by
  rintro a ⟨p, hp, ha⟩
  by_cases hmeet : p.walk.Meets (C \ {s})
  · exact Or.inl ⟨p, ⟨hp, hmeet⟩, ha⟩
  · exact Or.inr ⟨p, ⟨hp, hmeet⟩, ha⟩

/-- If the whole singleton fan is stationary but `C` is not strongly
popular, then the subfan meeting `C` only at `s` is still stationary. -/
theorem goodJoinedFamily_stationary
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {s : V} (F : JoinedFamily Γ ({s} : Set V)) (C : Set V)
    (hF : IsStationaryBelow κ
      (initialIndicesOf U F.paths F.starts_in_source))
    (hC : ¬ IsStronglyPopular U C) :
    IsStationaryBelow κ
      (initialIndicesOf U (goodJoinedFamily F C).paths
        (goodJoinedFamily F C).starts_in_source) := by
  let Ibad := initialIndicesOf U (badPaths F C)
    (fun hp ↦ F.starts_in_source hp.1)
  let Igood := initialIndicesOf U (goodPaths F C)
    (fun hp ↦ F.starts_in_source hp.1)
  have hbad : ¬ IsStationaryBelow κ Ibad := by
    intro hstat
    apply hC
    exact ⟨badPrefixWarp F C,
      hstat.mono (initialIndices_badPaths_subset_badPrefixWarp U F C)⟩
  have hgood : IsStationaryBelow κ Igood := by
    by_contra hgood
    let J : Bool → Set (Below κ)
      | false => Ibad
      | true => Igood
    have hJ : ∀ b, ¬ IsStationaryBelow κ (J b) := by
      intro b
      cases b <;> assumption
    have hnunion : ¬ IsStationaryBelow κ (⋃ b, J b) :=
      not_isStationaryBelow_iUnion_of_countable
        U.regular U.uncountable hJ
    apply hnunion
    apply hF.mono
    intro a ha
    have ha' := initialIndices_subset_bad_union_good U F C ha
    rcases ha' with ha' | ha'
    · exact Set.mem_iUnion.2 ⟨false, ha'⟩
    · exact Set.mem_iUnion.2 ⟨true, ha'⟩
  exact hgood

/-- Source Theorem 8.4's local popularity clause. -/
def IsLocallyPopular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (C : Set V) (s : V) : Prop :=
  s ∈ Γ.source ∨
    ∃ F : JoinedFamily Γ {s},
      IsStationaryBelow κ (initialIndicesOf U F.paths F.starts_in_source) ∧
      ∀ ⦃p⦄, p ∈ F.paths → p.support ⊆ Γ.strictRoof C ∪ {s}

/-- A path which begins under the roof of `C`, ends at `s ∈ C`, and has no
other `C`-vertex lies in the strict roof together with `s`. -/
theorem support_subset_strictRoof_union_singleton
    {Γ : DWeb V} {C : Set V} {s : V} (hsC : s ∈ C)
    (p : FinitePath Γ.graph) (hinit : p.start ∈ Γ.roof C)
    (hfinish : p.finish = s) (hgood : ¬ p.walk.Meets (C \ {s})) :
    p.support ⊆ Γ.strictRoof C ∪ {s} := by
  have hinter : p.support ∩ C ⊆ ({p.finish} : Set V) := by
    intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxfinish
    apply hgood
    refine ⟨x, hx.1, hx.2, ?_⟩
    intro hxs
    exact hxfinish (hxs.trans hfinish.symm)
  have hroof : p.support ⊆ Γ.roof C := by
    have hterminal : ∀ t, Γ.terminal? (.inl p) = some t → t ∈ C := by
      intro t ht
      have hpt : p.finish = t := by simpa only [DWeb.terminal?_finite,
        Option.some.injEq] using ht
      simpa only [← hpt, hfinish] using hsC
    have hinter' :
        DirectedPath.Path.support (.inl p) ∩ C ⊆
          (match Γ.terminal? (.inl p) with
          | some t => ({t} : Set V)
          | none => ∅) := by
      change p.support ∩ C ⊆ ({p.finish} : Set V)
      exact hinter
    have hroof' := Γ.pathSupportRoof (.inl p) C hinit hterminal hinter'
    change p.support ⊆ Γ.roof C at hroof'
    exact hroof'
  intro x hxp
  by_cases hxs : x = s
  · exact Or.inr (Set.mem_singleton_iff.2 hxs)
  · apply Or.inl
    refine ⟨hroof hxp, ?_⟩
    intro hxess
    have hxC : x ∈ C := Γ.essential_subset C hxess
    exact hgood ⟨x, hxp, hxC, fun hxsing ↦ hxs (Set.mem_singleton_iff.1 hxsing)⟩

/-! ## The layer induction (Assertions 8.8 and 8.9) -/

/-- Aharoni--Berger Lemma 8.5, re-exported with the terminology used in
the popular-layer proof. -/
theorem lemma8_5_stationary_range_choice {κ : Cardinal.{u}}
    (hunc : ℵ₀ < κ) (hreg : κ.IsRegular)
    {ι : Type*} (Ξ : ι → Set (Below κ))
    (hne : ∀ i, (Ξ i).Nonempty)
    (hnon : ∀ i, ¬ IsStationaryBelow κ (Ξ i))
    (hunion : IsStationaryBelow κ (⋃ i, Ξ i)) :
    ∃ g : ι → Below κ,
      (∀ i, g i ∈ Ξ i) ∧ IsStationaryBelow κ (Set.range g) :=
  InfiniteKonig.stationary_range_choice hunc hreg Ξ hne hnon hunion

/-- Assertion 8.8: every unpopular layer is itself unpopular. -/
theorem unpopularLayer_not_popular {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ) :
    ∀ n : ℕ, ¬ IsPopular U.toKappaIndexed
      (unpopularLayer U.toKappaIndexed n) := by
  intro n
  induction n with
  | zero => exact unpopularLayer_zero_not_popular U
  | succ n ih =>
      intro hpopular
      rcases hpopular with hsource | ⟨F, hstat⟩
      · obtain ⟨x, hxlayer, hxsource⟩ := hsource
        exact (unpopularLayer_subset_unpopular U.toKappaIndexed
          (n + 1) hxlayer)
          (popularVertex_of_mem_source U.toKappaIndexed hxsource)
      · have hstrong : IsStronglyPopular U.toKappaIndexed
            (unpopularLayer U.toKappaIndexed (n + 1)) :=
          stronglyPopular_of_joined_of_unpopular_terminals
            U.toKappaIndexed F hstat <| by
            intro v hv
            exact unpopularLayer_subset_unpopular U.toKappaIndexed (n + 1) hv
        apply ih
        exact popular_of_stronglyPopular_of_step U.toKappaIndexed
          (hS := hstrong) fun _ hv ↦ hv.1

/-- Assertion 8.9: no popular layer is strongly popular. -/
theorem popularLayer_not_stronglyPopular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ) :
    ∀ n : ℕ, ¬ IsStronglyPopular U.toKappaIndexed
      (popularLayer U.toKappaIndexed n) := by
  intro n
  cases n with
  | zero => exact popularLayer_zero_not_stronglyPopular U
  | succ n =>
      exact popularLayer_succ_not_stronglyPopular_of_not_popular
        U.toKappaIndexed n
        (unpopularLayer_not_popular U n)

/-! ## Canonical fans at non-source popular vertices -/

/-- Choose the stationary singleton-joined family witnessing popularity at
a popular vertex outside the source. -/
def nonSourcePopularFan {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) {v : V} (hv : IsPopularVertex U v)
    (hvX : v ∉ Γ.source) : JoinedFamily Γ {v} := by
  have hnotSource : ¬ (({v} : Set V) ∩ Γ.source).Nonempty := by
    rintro ⟨x, hxv, hxX⟩
    exact hvX ((Set.mem_singleton_iff.1 hxv) ▸ hxX)
  exact Classical.choose (hv.resolve_left hnotSource)

/-- The chosen fan at a non-source popular vertex has stationary initial
index set. -/
theorem nonSourcePopularFan_stationary
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    {v : V} (hv : IsPopularVertex U v) (hvX : v ∉ Γ.source) :
    IsStationaryBelow κ
      (initialIndicesOf U (nonSourcePopularFan U hv hvX).paths
        (nonSourcePopularFan U hv hvX).starts_in_source) := by
  have hnotSource : ¬ (({v} : Set V) ∩ Γ.source).Nonempty := by
    rintro ⟨x, hxv, hxX⟩
    exact hvX ((Set.mem_singleton_iff.1 hxv) ▸ hxX)
  exact Classical.choose_spec (hv.resolve_left hnotSource)

/-- The normalized stationary fan used at a non-source point of a fixed
popular layer.  Its paths avoid every other point of that layer's
non-source part. -/
def popularLayerGoodFan {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaIndexed Γ κ) (n : ℕ)
    (c : (popularLayer U n \ Γ.source : Set V)) : JoinedFamily Γ {c.1} :=
  goodJoinedFamily
    (nonSourcePopularFan U (popularLayer_subset_popular U n c.2.1) c.2.2)
    (popularLayer U n \ Γ.source)

/-- Every canonical normalized fan in a popular layer still carries a
stationary set of source indices. -/
theorem popularLayerGoodFan_stationary
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ) (n : ℕ)
    (c : (popularLayer U.toKappaIndexed n \ Γ.source : Set V)) :
    IsStationaryBelow κ
      (initialIndicesOf U.toKappaIndexed
        (popularLayerGoodFan U.toKappaIndexed n c).paths
        (popularLayerGoodFan U.toKappaIndexed n c).starts_in_source) := by
  apply goodJoinedFamily_stationary U.toKappaIndexed
    (nonSourcePopularFan U.toKappaIndexed
      (popularLayer_subset_popular U.toKappaIndexed n c.2.1) c.2.2)
    (popularLayer U.toKappaIndexed n \ Γ.source)
  · exact nonSourcePopularFan_stationary U.toKappaIndexed
      (popularLayer_subset_popular U.toKappaIndexed n c.2.1) c.2.2
  · exact not_stronglyPopular_of_subset Set.sdiff_subset
      (popularLayer_not_stronglyPopular U n)

/-- The canonical fan at `c` has no other vertex in the non-source part of
the layer. -/
theorem popularLayerGoodFan_normalized
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ) (n : ℕ)
    (c : (popularLayer U n \ Γ.source : Set V)) :
    ∀ {p}, p ∈ (popularLayerGoodFan U n c).paths →
      p.support ∩ (popularLayer U n \ Γ.source) ⊆ {c.1} := by
  exact goodJoinedFamily_normalized
    (nonSourcePopularFan U (popularLayer_subset_popular U n c.2.1) c.2.2)
    (popularLayer U n \ Γ.source)

/-- The non-source part of every popular layer has cardinality at most
`κ`.  Otherwise its canonical normalized stationary fans feed Aharoni's
Lemma 2.5 and produce a strongly popular warp to that layer, contradicting
Assertion 8.9. -/
theorem popularLayer_diff_source_card_le
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ)
    (hU : U.toKappaIndexed.SourceBounded) (n : ℕ) :
    #(popularLayer U.toKappaIndexed n \ Γ.source : Set V) ≤ κ := by
  apply le_of_not_gt
  intro hlarge
  have hdisjoint :
      Disjoint (popularLayer U.toKappaIndexed n \ Γ.source : Set V)
        Γ.source :=
    Set.disjoint_sdiff_left
  have hstrong :
      IsStronglyPopular U.toKappaIndexed
        (popularLayer U.toKappaIndexed n \ Γ.source) :=
    stronglyPopular_of_large_normalized_fans U.toKappaIndexed hU
      hdisjoint hlarge
      (popularLayerGoodFan U.toKappaIndexed n)
      (popularLayerGoodFan_normalized U.toKappaIndexed n)
      (popularLayerGoodFan_stationary U n)
  exact popularLayer_not_stronglyPopular U n
    (hstrong.mono Set.sdiff_subset)

/-! ## The countable union and the locality clauses -/

/-- A countable union of sets of cardinality at most an infinite cardinal
still has cardinality at most that cardinal. -/
theorem mk_iUnion_nat_le {κ : Cardinal.{u}} (F : ℕ → Set V)
    (hκ : ℵ₀ ≤ κ) (hF : ∀ n, #(F n) ≤ κ) :
    #(⋃ n, F n) ≤ κ := by
  calc
    #(⋃ n, F n) ≤ Cardinal.sum (fun n : ℕ ↦ #(F n)) :=
      by simpa using Cardinal.mk_iUnion_le_sum_mk_lift (f := F)
    _ ≤ Cardinal.sum (fun _ : ℕ ↦ κ) :=
      Cardinal.sum_le_sum _ _ hF
    _ = ℵ₀ * κ := by simp
    _ = κ := Cardinal.aleph0_mul_eq hκ

/-- Once the non-source part of each popular layer has size at most `κ`,
the same is true of their countable union. -/
theorem layerSeparator_diff_source_card_le_of_layers
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaIndexed Γ κ)
    (hlayer : ∀ n : ℕ, #(popularLayer U n \ Γ.source : Set V) ≤ κ) :
    #(layerSeparator U \ Γ.source : Set V) ≤ κ := by
  have hsubset : layerSeparator U \ Γ.source ⊆
      ⋃ n : ℕ, popularLayer U n \ Γ.source := by
    rintro x ⟨hxS, hxX⟩
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxS
    exact Set.mem_iUnion.2 ⟨n, hxn, hxX⟩
  exact (Cardinal.mk_le_mk_of_subset hsubset).trans
    (mk_iUnion_nat_le (fun n ↦ popularLayer U n \ Γ.source)
      U.uncountable.le hlayer)

/-- The non-source part of the canonical popular separator has cardinality
at most `κ`. -/
theorem layerSeparator_diff_source_card_le
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ)
    (hU : U.toKappaIndexed.SourceBounded) :
    #(layerSeparator U.toKappaIndexed \ Γ.source : Set V) ≤ κ :=
  layerSeparator_diff_source_card_le_of_layers U.toKappaIndexed
    (popularLayer_diff_source_card_le U hU)

/-- The union of the popular layers cannot be strongly popular: restricting
a hypothetical stationary warp by its terminal layer leaves one stationary
part. -/
theorem layerSeparator_not_stronglyPopular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ) :
    ¬ IsStronglyPopular U.toKappaIndexed
      (layerSeparator U.toKappaIndexed) := by
  rintro ⟨P, hP⟩
  have hcover : layerSeparator U.toKappaIndexed ⊆
      ⋃ n : ℕ, popularLayer U.toKappaIndexed n := by
    intro x hx
    exact hx
  have hindices :
      initialIndicesOf U.toKappaIndexed P.paths P.starts_in_source ⊆
        ⋃ n : ℕ, initialIndicesOf U.toKappaIndexed
          (P.restrictTerminal (popularLayer U.toKappaIndexed n)).paths
          (P.restrictTerminal
            (popularLayer U.toKappaIndexed n)).starts_in_source :=
    initialIndices_subset_iUnion_restrictTerminal U.toKappaIndexed P
      (popularLayer U.toKappaIndexed) hcover
  obtain ⟨n, hn⟩ := exists_stationary_of_subset_iUnion
    U.regular U.uncountable hP hindices
  exact popularLayer_not_stronglyPopular U n
    ⟨P.restrictTerminal (popularLayer U.toKappaIndexed n), hn⟩

/-- Every point of the canonical separator has its stationary in-fan
localized to the strict roof of that separator (unless it is itself a source
vertex).  This is the first clause of Theorem 8.4. -/
theorem layerSeparator_locallyPopular
    {Γ : DWeb V} {κ : Cardinal.{u}} (U : KappaUnbalanced Γ κ) :
    ∀ s ∈ layerSeparator U.toKappaIndexed,
      IsLocallyPopularAt U.toKappaIndexed
        (layerSeparator U.toKappaIndexed) s := by
  intro s hs
  have hspop : IsPopularVertex U.toKappaIndexed s :=
    layerSeparator_subset_popular U.toKappaIndexed hs
  rcases hspop with hsource | ⟨F, hF⟩
  · obtain ⟨x, hxs, hxsource⟩ := hsource
    exact Or.inl ((Set.mem_singleton_iff.1 hxs) ▸ hxsource)
  · apply Or.inr
    let G := goodJoinedFamily F (layerSeparator U.toKappaIndexed)
    have hG : IsStationaryBelow κ
        (initialIndicesOf U.toKappaIndexed G.paths G.starts_in_source) :=
      goodJoinedFamily_stationary U.toKappaIndexed F
        (layerSeparator U.toKappaIndexed) hF
        (layerSeparator_not_stronglyPopular U)
    refine ⟨G, hG, ?_⟩
    intro p hp
    have hpF : p ∈ F.paths := hp.1
    have hstartRoof : p.start ∈
        Γ.roof (layerSeparator U.toKappaIndexed) := by
      intro q hq
      exact layerSeparator_isSeparator U.toKappaIndexed q
        (by simpa [hq.1] using F.starts_in_source hpF) hq.2
    have hfinish : p.finish = s :=
      Set.mem_singleton_iff.1 (F.ends_in_join hpF)
    exact support_subset_strictRoof_union_singleton hs p hstartRoof hfinish hp.2

/-! ## The popular-separator theorem -/

/-- Aharoni--Berger Theorem 8.4, in the source-bounded form required by
its application of Lemma 8.6.  The separator is the union of the canonical
popular layers. -/
noncomputable def theorem8_4 {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ)
    (hU : U.toKappaIndexed.SourceBounded) :
    PopularSeparator U.toKappaIndexed where
  cut := layerSeparator U.toKappaIndexed
  separates := layerSeparator_isSeparator U.toKappaIndexed
  locally_popular := layerSeparator_locallyPopular U
  card_diff_source := by
    exact Cardinal.lift_le.2 (layerSeparator_diff_source_card_le U hU)
  not_strongly_popular := layerSeparator_not_stronglyPopular U

/-- Convenient Theorem 8.4 interface for the actual Section 8 auxiliary
web, whose source is injectively indexed below `κ`. -/
noncomputable def theorem8_4_of_sourceIndexed {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ)
    (hU : U.toKappaIndexed.SourceIndexed) :
    PopularSeparator U.toKappaIndexed :=
  theorem8_4 U (U.sourceBounded_of_sourceIndexed hU)

/-- Propositional existence form of Theorem 8.4. -/
theorem exists_popularSeparator {Γ : DWeb V} {κ : Cardinal.{u}}
    (U : KappaUnbalanced Γ κ)
    (hU : U.toKappaIndexed.SourceBounded) :
    Nonempty (PopularSeparator U.toKappaIndexed) :=
  ⟨theorem8_4 U hU⟩

end Popular
end Erdos599

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Countable simultaneous safe assignments

This file proves the countable recursive core of Aharoni--Berger
Theorem 4.12.  We enumerate the uncovered initial vertices without
repetitions.  At a finite alternative, the reducing switch removes exactly
the current source and terminal; at an infinite alternative the current
warp is retained.  The set of finite terminals already used is kept
disjoint from the terminal frontier of the current warp.  This is the
invariant that gives endpoint injectivity.
-/

namespace Erdos599
namespace Alternating

open Set
open DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-! ## Normalization at source vertices -/

/-- In a normalized web, a source vertex occurring on a finite directed
path is its initial vertex. -/
theorem walk_eq_start_of_mem_support_of_mem_source
    (hΓ : Γ.IsNormalized) {a b x : V} (p : Walk Γ.graph a b)
    (hx : x ∈ p.support) (hxA : x ∈ Γ.source) : x = a := by
  induction p with
  | nil => simpa using hx
  | @cons a c b hac p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · have hxc : x = c := ih hx
        subst x
        exact (hΓ hac).1 hxA |>.elim

/-- In a normalized web, a source vertex occurring on a finite path is its
initial vertex. -/
theorem finitePath_eq_start_of_mem_support_of_mem_source
    (hΓ : Γ.IsNormalized) (p : FinitePath Γ.graph) {x : V}
    (hx : x ∈ p.support) (hxA : x ∈ Γ.source) : x = p.start :=
  walk_eq_start_of_mem_support_of_mem_source hΓ p.walk hx hxA

/-- In a normalized web, a source vertex occurring on a ray is its initial
vertex. -/
theorem ray_eq_initial_of_mem_support_of_mem_source
    (hΓ : Γ.IsNormalized) (r : Ray Γ.graph) {x : V}
    (hx : x ∈ r.support) (hxA : x ∈ Γ.source) : x = r.initial := by
  rcases hx with ⟨n, rfl⟩
  cases n with
  | zero => rfl
  | succ n =>
      exact (hΓ (r.adj_succ n)).1 hxA |>.elim

/-- In a normalized web, a source vertex occurring on any warp path is its
initial vertex. -/
theorem path_eq_initial_of_mem_support_of_mem_source
    (hΓ : Γ.IsNormalized) (p : Γ.DPath) {x : V}
    (hx : x ∈ p.support) (hxA : x ∈ Γ.source) : x = p.initial := by
  rcases p with p | r
  · exact finitePath_eq_start_of_mem_support_of_mem_source hΓ p hx hxA
  · exact ray_eq_initial_of_mem_support_of_mem_source hΓ r hx hxA

/-- On the source side of a normalized web, membership in the vertex set of
a family is the same as membership in its initial set (in the direction
needed below). -/
theorem mem_initialSet_of_mem_vertexSet_of_mem_source
    (hΓ : Γ.IsNormalized) {W : Set Γ.DPath} {x : V}
    (hxW : x ∈ Γ.vertexSet W) (hxA : x ∈ Γ.source) :
    x ∈ Γ.initialSet W := by
  rcases hxW with ⟨p, hpW, hxp⟩
  exact ⟨p, hpW, (path_eq_initial_of_mem_support_of_mem_source hΓ p hxp hxA).symm⟩

/-! ## Vertex confinement of bracket-alternating paths -/

theorem AltPath.vertexSet_subset_initial_union_links {D : Digraph V}
    (Q : AltPath D) :
    Q.vertexSet ⊆ {Q.initial} ∪ ⋃ l ∈ Q.links, l.path.support := by
  intro x hx
  cases Q with
  | trivial v => exact Or.inl hx
  | finite Q =>
      right
      simp only [AltPath.vertexSet, FiniteTrace.vertexSet, Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2
        ⟨Q.link i, Set.mem_iUnion.2 ⟨⟨i, rfl⟩, hxi⟩⟩
  | infinite Q =>
      right
      simp only [AltPath.vertexSet, InfiniteTrace.vertexSet, Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2
        ⟨Q.link i, Set.mem_iUnion.2 ⟨⟨i, rfl⟩, hxi⟩⟩

theorem IsFragmentOf.support_subset_vertexSet
    {W : Set Γ.DPath} {p : FinitePath Γ.graph}
    (hp : IsFragmentOf p W) : p.support ⊆ Γ.vertexSet W := by
  rcases hp with ⟨q, hqW, hpq⟩
  intro x hx
  exact ⟨q, hqW, hpq.1 hx⟩

/-- Every vertex of a bracket-alternating path lies either on the forward
warp or on its reference warp, provided its initial vertex does. -/
theorem IsBracketAlternating.vertexSet_subset_union
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hQ : IsBracketAlternating Z Y Q)
    (hinit : Q.initial ∈ Γ.vertexSet Z) :
    Q.vertexSet ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y := by
  intro x hx
  rcases Q.vertexSet_subset_initial_union_links hx with hx | hx
  · have hxi : x = Q.initial := by simpa using hx
    subst x
    exact Or.inl hinit
  · simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨l, hl, hxl⟩
    cases hdir : l.direction with
    | forward =>
        exact Or.inl ((hQ.2 l hl hdir).support_subset_vertexSet hxl)
    | backward =>
        exact Or.inr ((hQ.1.2.1 l hl hdir).support_subset_vertexSet hxl)

/-! ## The exact reducing-switch interface used by the recursion -/

/-- The part of the reducing-switch theorem needed by the countable
successive-switch construction.  `ReducingSwitch.exists_reducingSwitch`
supplies this rule. -/
def ReducingSwitchRule (Γ : DWeb V) : Prop :=
  ∀ (Z Y : Set Γ.DPath) (u v : V) (T : AltPath Γ.graph),
    Γ.IsWarp Z → Γ.HasFiniteCharacter Z →
    Γ.IsWarp Y → Γ.HasFiniteCharacter Y →
    u ∈ Γ.initialSet Z → u ∉ Γ.vertexSet Y →
    v ∈ Γ.terminalFrontier Z → v ∉ Γ.vertexSet Y →
    IsBracketAlternating Y Z T → T.initial = v →
    T.terminal? = some u → T.IsFinite →
    ∃ Z' : Set Γ.DPath,
      Γ.IsWarp Z' ∧ Γ.HasFiniteCharacter Z' ∧
      Γ.initialSet Z' = Γ.initialSet Z \ {u} ∧
      Γ.terminalFrontier Z' = Γ.terminalFrontier Z \ {v} ∧
      Γ.vertexSet Z' ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y

section Recursion

variable (Γ)
variable (Z Y : Set Γ.DPath)

private abbrev Uncovered :=
  {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y}

/-- The path assigned to one uncovered source, with all properties that do
not mention assignments at other sources. -/
private structure AssignedData (z : Uncovered Γ Z Y) where
  path : AltPath Γ.graph
  starts_at : path.initial = z.1
  safe : IsSafe Y path
  leaving : IsLeaving Y path
  maximal : path.IsInfinite ∨
    ∃ v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y,
      path.terminal? = some v
  confined : path.vertexSet ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y

/-- State after all codes below `n` have been inspected.  `used` consists
of the finite terminals selected so far. -/
private structure AssignmentState
    (code : Uncovered Γ Z Y → ℕ) (n : ℕ) where
  current : Set Γ.DPath
  current_isWarp : Γ.IsWarp current
  current_finite : Γ.HasFiniteCharacter current
  current_initial_source : Γ.initialSet current ⊆ Γ.source
  current_terminal_target : Γ.terminalFrontier current ⊆ Γ.target
  current_vertex_subset : Γ.vertexSet current ⊆
    Γ.vertexSet Z ∪ Γ.vertexSet Y
  initialY_subset : Γ.initialSet Y ⊆ Γ.initialSet current
  unprocessed_initial : ∀ z, n ≤ code z → z.1 ∈ Γ.initialSet current
  terminal_subset : Γ.terminalFrontier current ⊆ Γ.terminalFrontier Z
  used : Set V
  used_disjoint : Disjoint used (Γ.terminalFrontier current)

namespace AssignmentState

variable {Γ Z Y}
variable {code : Uncovered Γ Z Y → ℕ}

/-- Initial state of the successive-switch recursion. -/
private def initial (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z) :
    AssignmentState Γ Z Y code 0 where
  current := Z
  current_isWarp := hZ
  current_finite := hZfin
  current_initial_source := hZsource
  current_terminal_target := hZtarget
  current_vertex_subset := fun _ hx ↦ Or.inl hx
  initialY_subset := hYZ
  unprocessed_initial := by
    intro z _
    exact z.property.1
  terminal_subset := Subset.rfl
  used := ∅
  used_disjoint := by simp

/-- Output of one recursive stage.  There is output for the (necessarily
unique) uncovered source whose code is the current stage. -/
private structure StepResult (n : ℕ) (s : AssignmentState Γ Z Y code n) where
  next : AssignmentState Γ Z Y code (n + 1)
  used_mono : s.used ⊆ next.used
  output : ∀ z, code z = n → AssignedData Γ Z Y z
  finite_terminal_mem_current : ∀ z (hz : code z = n) v,
    (output z hz).path.terminal? = some v →
      v ∈ Γ.terminalFrontier s.current
  finite_terminal_mem_next_used : ∀ z (hz : code z = n) v,
    (output z hz).path.terminal? = some v → v ∈ next.used

/-- A data-valued form of the two alternatives.  We first prove this type
nonempty in `Prop`, and only then use classical choice; this avoids any
large elimination from the propositional dichotomy. -/
private inductive ChosenAlternative
    (current : Set Γ.DPath) (z : Uncovered Γ Z Y) : Type u
  | infinite (Q : AltPath Γ.graph)
      (safe : IsBracketSafe current Y Q)
      (initial : Q.initial = z.1) (isInfinite : Q.IsInfinite)
  | finite (v : V)
      (terminal_mem : v ∈ Γ.terminalFrontier current \ Γ.vertexSet Y)
      (Q : AltPath Γ.graph) (safe : IsBracketSafe current Y Q)
      (initial : Q.initial = z.1) (terminal : Q.terminal? = some v)
      (T : AltPath Γ.graph) (reducing : IsBracketAlternating Y current T)
      (reducing_initial : T.initial = v)
      (reducing_terminal : T.terminal? = some z.1)

/-- One stage of the recursion.  The use of `code` rather than a surjective
enumeration means that holes cause a genuine no-op and no source can be
visited twice. -/
private noncomputable def step
    (hΓ : Γ.IsNormalized)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ)
    (hcode : Function.Injective code)
    (n : ℕ) (s : AssignmentState Γ Z Y code n) :
    StepResult n s := by
  classical
  by_cases hn : ∃ z, code z = n
  · let z : Uncovered Γ Z Y := Classical.choose hn
    have hzcode : code z = n := Classical.choose_spec hn
    have hzuCurrent : z.1 ∈ Γ.initialSet s.current :=
      s.unprocessed_initial z (by omega)
    have hzuVertex : z.1 ∈ Γ.vertexSet s.current := by
      rcases hzuCurrent with ⟨p, hp, hpinit⟩
      exact ⟨p, hp, hpinit ▸ p.initial_mem_support⟩
    have hzuSource : z.1 ∈ Γ.source := hZsource z.property.1
    have hzuY : z.1 ∉ Γ.vertexSet Y := by
      intro hvertex
      exact z.property.2
        (mem_initialSet_of_mem_vertexSet_of_mem_source hΓ hvertex hzuSource)
    have hAlt : SafeAlternatingDichotomy s.current Y z.1 :=
      hDichotomy hΓ s.current Y s.current_initial_source
        s.current_terminal_target s.current_isWarp hY s.current_finite hYfin
        s.initialY_subset z.1 ⟨hzuCurrent, hzuY⟩
    have hChosen : Nonempty (ChosenAlternative s.current z) := by
      rcases hAlt with hInfinite | hFinite
      · rcases hInfinite with ⟨Q, hQsafe, hQinitial, hQinfinite⟩
        exact ⟨.infinite Q hQsafe hQinitial hQinfinite⟩
      · rcases hFinite with
          ⟨v, hvCurrent, Q, hQsafe, hQinitial, hQterminal,
            T, hTalt, hTinitial, hTterminal⟩
        exact ⟨.finite v hvCurrent Q hQsafe hQinitial hQterminal T hTalt
          hTinitial hTterminal⟩
    let chosen := Classical.choice hChosen
    cases chosen with
    | infinite Q hQsafe hQinitial hQinfinite =>
      have hQinitVertex : Q.initial ∈ Γ.vertexSet s.current :=
        hQinitial.symm ▸ hzuVertex
      have hQconfined :
          Q.vertexSet ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y := by
        intro x hx
        rcases hQsafe.isBracketAlternating.vertexSet_subset_union hQinitVertex hx with
          hxCurrent | hxY
        · exact s.current_vertex_subset hxCurrent
        · exact Or.inr hxY
      let data : AssignedData Γ Z Y z :=
        { path := Q
          starts_at := hQinitial
          safe := hQsafe.isSafe
          leaving := Or.inl hQinfinite
          maximal := Or.inl hQinfinite
          confined := hQconfined }
      exact
        { next :=
            { current := s.current
              current_isWarp := s.current_isWarp
              current_finite := s.current_finite
              current_initial_source := s.current_initial_source
              current_terminal_target := s.current_terminal_target
              current_vertex_subset := s.current_vertex_subset
              initialY_subset := s.initialY_subset
              unprocessed_initial := by
                intro w hw
                exact s.unprocessed_initial w (by omega)
              terminal_subset := s.terminal_subset
              used := s.used
              used_disjoint := s.used_disjoint }
          used_mono := Subset.rfl
          output := by
            intro w hw
            have hwz : w = z := hcode (hw.trans hzcode.symm)
            subst w
            exact data
          finite_terminal_mem_current := by
            intro w hw v hv
            have hwz : w = z := hcode (hw.trans hzcode.symm)
            subst w
            change Q.terminal? = some v at hv
            rw [Q.isInfinite_iff_terminal?_eq_none.1 hQinfinite] at hv
            simp at hv
          finite_terminal_mem_next_used := by
            intro w hw v hv
            have hwz : w = z := hcode (hw.trans hzcode.symm)
            subst w
            change Q.terminal? = some v at hv
            rw [Q.isInfinite_iff_terminal?_eq_none.1 hQinfinite] at hv
            simp at hv }
    | finite v hvCurrent Q hQsafe hQinitial hQterminal T hTalt hTinitial hTterminal =>
      have hTfinite : T.IsFinite :=
        T.isFinite_iff_exists_terminal.2 ⟨z.1, hTterminal⟩
      have hSwitchExists :=
        hSwitch s.current Y z.1 v T s.current_isWarp s.current_finite
          hY hYfin hzuCurrent hzuY hvCurrent.1 hvCurrent.2 hTalt
          hTinitial hTterminal hTfinite
      let Z' : Set Γ.DPath := Classical.choose hSwitchExists
      have hZ' := Classical.choose_spec hSwitchExists
      have hZ'warp : Γ.IsWarp Z' := hZ'.1
      have hZ'finite : Γ.HasFiniteCharacter Z' := hZ'.2.1
      have hZ'initial :
          Γ.initialSet Z' = Γ.initialSet s.current \ {z.1} := hZ'.2.2.1
      have hZ'terminal :
          Γ.terminalFrontier Z' = Γ.terminalFrontier s.current \ {v} :=
        hZ'.2.2.2.1
      have hZ'vertex :
          Γ.vertexSet Z' ⊆ Γ.vertexSet s.current ∪ Γ.vertexSet Y :=
        hZ'.2.2.2.2
      have hvOriginal : v ∈ Γ.terminalFrontier Z :=
        s.terminal_subset hvCurrent.1
      have hQinitVertex : Q.initial ∈ Γ.vertexSet s.current :=
        hQinitial.symm ▸ hzuVertex
      have hQconfined :
          Q.vertexSet ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y := by
        intro x hx
        rcases hQsafe.isBracketAlternating.vertexSet_subset_union hQinitVertex hx with
          hxCurrent | hxY
        · exact s.current_vertex_subset hxCurrent
        · exact Or.inr hxY
      let data : AssignedData Γ Z Y z :=
        { path := Q
          starts_at := hQinitial
          safe := hQsafe.isSafe
          leaving := Or.inr ⟨v, hQterminal, hvCurrent.2⟩
          maximal := Or.inr
            ⟨v, ⟨hvOriginal, hvCurrent.2⟩, hQterminal⟩
          confined := hQconfined }
      exact
        { next :=
            { current := Z'
              current_isWarp := hZ'warp
              current_finite := hZ'finite
              current_initial_source := by
                rw [hZ'initial]
                exact Set.sdiff_subset.trans s.current_initial_source
              current_terminal_target := by
                rw [hZ'terminal]
                exact Set.sdiff_subset.trans s.current_terminal_target
              current_vertex_subset := by
                intro x hx
                rcases hZ'vertex hx with hxCurrent | hxY
                · exact s.current_vertex_subset hxCurrent
                · exact Or.inr hxY
              initialY_subset := by
                rw [hZ'initial]
                intro x hxY
                refine ⟨s.initialY_subset hxY, ?_⟩
                simp only [Set.mem_singleton_iff]
                intro hxz
                subst x
                exact z.property.2 hxY
              unprocessed_initial := by
                intro w hw
                rw [hZ'initial]
                refine ⟨s.unprocessed_initial w (by omega), ?_⟩
                simp only [Set.mem_singleton_iff]
                intro hwzval
                have hwz : w = z := Subtype.ext hwzval
                subst w
                omega
              terminal_subset := by
                rw [hZ'terminal]
                exact Set.sdiff_subset.trans s.terminal_subset
              used := insert v s.used
              used_disjoint := by
                rw [Set.disjoint_left]
                intro x hxUsed hxTerminal
                rw [hZ'terminal] at hxTerminal
                rcases hxUsed with rfl | hxUsed
                · exact hxTerminal.2 rfl
                · exact Set.disjoint_left.1 s.used_disjoint hxUsed hxTerminal.1 }
          used_mono := subset_insert v s.used
          output := by
            intro w hw
            have hwz : w = z := hcode (hw.trans hzcode.symm)
            subst w
            exact data
          finite_terminal_mem_current := by
            intro w hw x hx
            have hwz : w = z := hcode (hw.trans hzcode.symm)
            subst w
            change Q.terminal? = some x at hx
            have hxv : x = v := Option.some.inj (hx.symm.trans hQterminal)
            exact hxv ▸ hvCurrent.1
          finite_terminal_mem_next_used := by
            intro w hw x hx
            have hwz : w = z := hcode (hw.trans hzcode.symm)
            subst w
            change Q.terminal? = some x at hx
            have hxv : x = v := Option.some.inj (hx.symm.trans hQterminal)
            exact hxv ▸ Set.mem_insert v s.used }
  · exact
      { next :=
          { current := s.current
            current_isWarp := s.current_isWarp
            current_finite := s.current_finite
            current_initial_source := s.current_initial_source
            current_terminal_target := s.current_terminal_target
            current_vertex_subset := s.current_vertex_subset
            initialY_subset := s.initialY_subset
            unprocessed_initial := by
              intro z hz
              exact s.unprocessed_initial z (by omega)
            terminal_subset := s.terminal_subset
            used := s.used
            used_disjoint := s.used_disjoint }
        used_mono := Subset.rfl
        output := by
          intro z hz
          exact (hn ⟨z, hz⟩).elim
        finite_terminal_mem_current := by
          intro z hz
          exact (hn ⟨z, hz⟩).elim
        finite_terminal_mem_next_used := by
          intro z hz
          exact (hn ⟨z, hz⟩).elim }

end AssignmentState

open AssignmentState

/-- The recursively produced state sequence. -/
private noncomputable def assignmentStates
    (hΓ : Γ.IsNormalized)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ)
    (code : Uncovered Γ Z Y → ℕ) (hcode : Function.Injective code) :
    ∀ n, AssignmentState Γ Z Y code n
  | 0 => AssignmentState.initial hZ hZfin hZsource hZtarget hYZ
  | n + 1 =>
      (AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch hcode n
        (assignmentStates hΓ hZ hZfin hY hYfin hYZ hZsource hZtarget hDichotomy
          hSwitch code hcode n)).next

private theorem assignmentStates_used_mono
    (hΓ : Γ.IsNormalized)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ)
    (code : Uncovered Γ Z Y → ℕ) (hcode : Function.Injective code)
    {n m : ℕ} (hnm : n ≤ m) :
    (assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource hZtarget hDichotomy
      hSwitch code hcode n).used ⊆
    (assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource hZtarget hDichotomy
      hSwitch code hcode m).used := by
  intro x hx
  induction m, hnm using Nat.le_induction with
  | base => exact hx
  | succ m hnm ih =>
      exact
        (AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch hcode m
          (assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource hZtarget hDichotomy
            hSwitch code hcode m)).used_mono ih

/-- The assigned datum at the unique stage equal to the source's code. -/
private noncomputable def assignmentData
    (hΓ : Γ.IsNormalized)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ)
    (code : Uncovered Γ Z Y → ℕ) (hcode : Function.Injective code)
    (z : Uncovered Γ Z Y) : AssignedData Γ Z Y z :=
  (AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch hcode (code z)
    (assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource hZtarget hDichotomy
      hSwitch code hcode (code z))).output z rfl

private theorem assignmentData_finite_terminals_injective
    (hΓ : Γ.IsNormalized)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ)
    (code : Uncovered Γ Z Y → ℕ) (hcode : Function.Injective code)
    ⦃z₁ z₂ : Uncovered Γ Z Y⦄ ⦃v : V⦄
    (hz₁ : (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
      hZtarget hDichotomy hSwitch code hcode z₁).path.terminal? = some v)
    (hz₂ : (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
      hZtarget hDichotomy hSwitch code hcode z₂).path.terminal? = some v) :
    z₁ = z₂ := by
  rcases lt_trichotomy (code z₁) (code z₂) with hlt | heq | hgt
  · let s₁ := assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
      hZtarget hDichotomy hSwitch code hcode (code z₁)
    let r₁ := AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch
      hcode (code z₁) s₁
    let s₂ := assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
      hZtarget hDichotomy hSwitch code hcode (code z₂)
    let r₂ := AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch
      hcode (code z₂) s₂
    have hvUsedNext : v ∈ r₁.next.used := by
      apply r₁.finite_terminal_mem_next_used z₁ rfl v
      exact hz₁
    have hvUsed : v ∈ s₂.used :=
      assignmentStates_used_mono Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
        hZtarget hDichotomy hSwitch code hcode (Nat.succ_le_iff.2 hlt) hvUsedNext
    have hvTerminal : v ∈ Γ.terminalFrontier s₂.current := by
      apply r₂.finite_terminal_mem_current z₂ rfl v
      exact hz₂
    exact (Set.disjoint_left.1 s₂.used_disjoint hvUsed hvTerminal).elim
  · exact hcode heq
  · let s₂ := assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
      hZtarget hDichotomy hSwitch code hcode (code z₂)
    let r₂ := AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch
      hcode (code z₂) s₂
    let s₁ := assignmentStates Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
      hZtarget hDichotomy hSwitch code hcode (code z₁)
    let r₁ := AssignmentState.step hΓ hY hYfin hZsource hDichotomy hSwitch
      hcode (code z₁) s₁
    have hvUsedNext : v ∈ r₂.next.used := by
      apply r₂.finite_terminal_mem_next_used z₂ rfl v
      exact hz₂
    have hvUsed : v ∈ s₁.used :=
      assignmentStates_used_mono Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
        hZtarget hDichotomy hSwitch code hcode (Nat.succ_le_iff.2 hgt) hvUsedNext
    have hvTerminal : v ∈ Γ.terminalFrontier s₁.current := by
      apply r₁.finite_terminal_mem_current z₁ rfl v
      exact hz₁
    exact (Set.disjoint_left.1 s₁.used_disjoint hvUsed hvTerminal).elim

private noncomputable def simultaneousAssignmentOfCode
    (hΓ : Γ.IsNormalized)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ)
    (code : Uncovered Γ Z Y → ℕ) (hcode : Function.Injective code) :
    SimultaneousAssignment Z Y where
  assigned z := (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
    hZtarget hDichotomy hSwitch code hcode z).path
  starts_at z := (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
    hZtarget hDichotomy hSwitch code hcode z).starts_at
  safe z := (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
    hZtarget hDichotomy hSwitch code hcode z).safe
  leaving z := (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
    hZtarget hDichotomy hSwitch code hcode z).leaving
  maximal z := (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
    hZtarget hDichotomy hSwitch code hcode z).maximal
  finite_terminals_injective := assignmentData_finite_terminals_injective Γ Z Y
    hΓ hZ hZfin hY hYfin hYZ hZsource hZtarget hDichotomy hSwitch code hcode

/-- Countable recursive core of Theorem 4.12.  The only two substantive
inputs are Lemma 4.13 (`hDichotomy`) and the exact reducing-switch lemma.
Normalization turns “not an initial vertex of `Y`” into “not on `Y`”, which
is the hypothesis required by Lemma 4.13. -/
theorem exists_simultaneousAssignment_of_countable_with_confinement
    (hΓ : Γ.IsNormalized)
    {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hcount : (Γ.initialSet Z \ Γ.initialSet Y).Countable)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ) :
    ∃ A : SimultaneousAssignment Z Y,
      ∀ z, (A.assigned z).vertexSet ⊆
        Γ.vertexSet Z ∪ Γ.vertexSet Y := by
  classical
  rcases Set.countable_iff_exists_injective.1 hcount with ⟨code, hcode⟩
  let A := simultaneousAssignmentOfCode Γ Z Y hΓ hZ hZfin hY hYfin hYZ
    hZsource hZtarget hDichotomy hSwitch code hcode
  refine ⟨A, ?_⟩
  intro z
  exact (assignmentData Γ Z Y hΓ hZ hZfin hY hYfin hYZ hZsource
    hZtarget hDichotomy hSwitch code hcode z).confined

/-- The confinement-forgetting form of the countable recursive theorem. -/
theorem exists_simultaneousAssignment_of_countable
    (hΓ : Γ.IsNormalized)
    {Z Y : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hcount : (Γ.initialSet Z \ Γ.initialSet Y).Countable)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ) :
    Nonempty (SimultaneousAssignment Z Y) := by
  rcases exists_simultaneousAssignment_of_countable_with_confinement Γ hΓ hZ hZfin
      hY hYfin hYZ hZsource hZtarget hcount hDichotomy hSwitch with
    ⟨A, _⟩
  exact ⟨A⟩

/-- Fixed-region form used when the global theorem is assembled one
component at a time. -/
theorem exists_simultaneousAssignment_of_countable_inside
    (hΓ : Γ.IsNormalized)
    {Z Y : Set Γ.DPath} {C : Set V}
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hY : Γ.IsWarp Y) (hYfin : Γ.HasFiniteCharacter Y)
    (hYZ : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (hZsource : Γ.initialSet Z ⊆ Γ.source)
    (hZtarget : Γ.terminalFrontier Z ⊆ Γ.target)
    (hcount : (Γ.initialSet Z \ Γ.initialSet Y).Countable)
    (hZC : Γ.vertexSet Z ⊆ C) (hYC : Γ.vertexSet Y ⊆ C)
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ) :
    ∃ A : SimultaneousAssignment Z Y,
      ∀ z, (A.assigned z).vertexSet ⊆ C := by
  rcases exists_simultaneousAssignment_of_countable_with_confinement Γ hΓ hZ
      hZfin hY hYfin hYZ hZsource hZtarget hcount hDichotomy hSwitch with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro z x hx
  rcases hA z hx with hxZ | hxY
  · exact hZC hxZ
  · exact hYC hxY

end Recursion

end Alternating
end Erdos599

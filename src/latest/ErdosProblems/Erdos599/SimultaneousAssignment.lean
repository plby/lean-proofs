/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingDichotomy
import ErdosProblems.Erdos599.AlternatingComponents
import ErdosProblems.Erdos599.CountableAssignment
import ErdosProblems.Erdos599.FracturedDuplication
import ErdosProblems.Erdos599.SimultaneousAssignmentGlobal

/-!
# Simultaneous safe alternating-path assignments

This file formalizes Aharoni--Berger Theorem 4.12 and its fractured-warp
extension, Remark 4.20.  The elementary lemma below isolates the final
endpoint-injectivity argument used by the successive-switching construction.
-/

namespace Erdos599
namespace Alternating

open Set
open DirectedPath
open AlternatingComponents

universe u v

variable {V : Type u} {D : Digraph V}

/-- If later members of a linearly ordered family never reuse an earlier
finite terminal, equality of finite terminals forces equality of indices. -/
theorem finiteTerminalsInjective_of_fresh {I : Type v} [LinearOrder I]
    (Q : I → AltPath D)
    (fresh : ∀ {i j : I}, i < j → ∀ {x : V},
      (Q i).terminal? = some x → (Q j).terminal? ≠ some x)
    {i j : I} {x : V}
    (hi : (Q i).terminal? = some x)
    (hj : (Q j).terminal? = some x) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (fresh hij hi hj).elim
  · exact hij
  · exact (fresh hij hj hi).elim

/-! ## Restriction to one alternating component -/

variable {Γ : DWeb V}

/-- Members of `W` whose initial vertex lies in the component of `root`
for the original pair `Z,Y`. -/
def pathsInComponent (Z Y W : Set Γ.DPath) (root : V) : Set Γ.DPath :=
  {p | p ∈ W ∧ p.initial ∈ component Z Y root}

@[simp]
theorem mem_pathsInComponent {Z Y W : Set Γ.DPath} {root : V}
    {p : Γ.DPath} :
    p ∈ pathsInComponent Z Y W root ↔
      p ∈ W ∧ p.initial ∈ component Z Y root :=
  Iff.rfl

theorem isWarp_pathsInComponent {Z Y W : Set Γ.DPath} {root : V}
    (hW : Γ.IsWarp W) :
    Γ.IsWarp (pathsInComponent Z Y W root) := by
  intro p hp q hq hpq
  exact DWeb.IsWarp.disjoint Γ hW hp.1 hq.1 hpq

theorem hasFiniteCharacter_pathsInComponent
    {Z Y W : Set Γ.DPath} {root : V}
    (hW : Γ.HasFiniteCharacter W) :
    Γ.HasFiniteCharacter (pathsInComponent Z Y W root) := by
  intro p hp
  exact hW hp.1

theorem initialSet_pathsInComponent (Z Y W : Set Γ.DPath) (root : V) :
    Γ.initialSet (pathsInComponent Z Y W root) =
      Γ.initialSet W ∩ component Z Y root := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨⟨p, hpW, hp⟩, hxC⟩
    refine ⟨p, ⟨hpW, ?_⟩, hp⟩
    exact hp.symm ▸ hxC

theorem terminalFrontier_pathsInComponent_subset
    (Z Y W : Set Γ.DPath) (root : V) :
    Γ.terminalFrontier (pathsInComponent Z Y W root) ⊆
      Γ.terminalFrontier W := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp.1, hpx⟩

theorem initialSet_pathsInComponent_mono
    {Z Y : Set Γ.DPath} {root : V}
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z) :
    Γ.initialSet (pathsInComponent Z Y Y root) ⊆
      Γ.initialSet (pathsInComponent Z Y Z root) := by
  rw [initialSet_pathsInComponent, initialSet_pathsInComponent]
  exact Set.inter_subset_inter hinit Set.Subset.rfl

theorem vertexSet_pathsInComponent_left_subset
    {Z Y : Set Γ.DPath} {root : V}
    (hZfinite : Γ.HasFiniteCharacter Z) :
    Γ.vertexSet (pathsInComponent Z Y Z root) ⊆ component Z Y root := by
  rintro x ⟨p, hp, hxp⟩
  obtain ⟨q, rfl⟩ := hZfinite hp.1
  exact finitePath_support_subset_component_of_touches_left
    hp.2 hp.1 q.start_mem_support hxp

theorem vertexSet_pathsInComponent_right_subset
    {Z Y : Set Γ.DPath} {root : V}
    (hYfinite : Γ.HasFiniteCharacter Y) :
    Γ.vertexSet (pathsInComponent Z Y Y root) ⊆ component Z Y root := by
  rintro x ⟨p, hp, hxp⟩
  obtain ⟨q, rfl⟩ := hYfinite hp.1
  exact finitePath_support_subset_component_of_touches_right
    hp.2 hp.1 q.start_mem_support hxp

/-! ## The quotient of vertices by alternating components -/

/-- Connectedness in `E[Z] \cup E[Y]` is the equivalence relation whose
classes index the independent countable constructions. -/
def componentSetoid (Z Y : Set Γ.DPath) : Setoid V where
  r x y := y ∈ component Z Y x
  iseqv :=
    { refl := fun x ↦ mem_component_self Z Y x
      symm := @fun _ _ h ↦ component_symm h
      trans := @fun _ _ _ hxy hyz ↦ component_trans hxy hyz }

/-- The set of alternating components of the pair `Z,Y`. -/
abbrev ComponentClass (Z Y : Set Γ.DPath) := Quotient (componentSetoid Z Y)

/-- The component containing `x`. -/
def componentClass (Z Y : Set Γ.DPath) (x : V) : ComponentClass Z Y :=
  Quotient.mk (componentSetoid Z Y) x

/-- A fixed representative of an alternating component. -/
noncomputable def componentRepresentative (Z Y : Set Γ.DPath)
    (c : ComponentClass Z Y) : V :=
  Quotient.out c

theorem componentClass_eq_iff {Z Y : Set Γ.DPath} {x y : V} :
    componentClass Z Y x = componentClass Z Y y ↔
      y ∈ component Z Y x := by
  constructor
  · exact @Quotient.exact V (componentSetoid Z Y) x y
  · exact @Quotient.sound V (componentSetoid Z Y) x y

theorem mem_component_representative {Z Y : Set Γ.DPath} (x : V) :
    x ∈ component Z Y
      (componentRepresentative Z Y (componentClass Z Y x)) := by
  apply componentClass_eq_iff.mp
  exact Quotient.out_eq (componentClass Z Y x)

theorem component_eq_of_mem {Z Y : Set Γ.DPath} {x y : V}
    (hy : y ∈ component Z Y x) :
    component Z Y y = component Z Y x := by
  ext z
  constructor
  · intro hz
    exact component_trans hy hz
  · intro hz
    exact component_trans (component_symm hy) hz

theorem component_representative_eq {Z Y : Set Γ.DPath} (x : V) :
    component Z Y (componentRepresentative Z Y (componentClass Z Y x)) =
      component Z Y x :=
  (component_eq_of_mem
    (mem_component_representative (Z := Z) (Y := Y) x)).symm

/-! ## Exact carrier identities for component restrictions -/

theorem vertexSet_pathsInComponent_left
    {Z Y : Set Γ.DPath} {root : V}
    (hZfinite : Γ.HasFiniteCharacter Z) :
    Γ.vertexSet (pathsInComponent Z Y Z root) =
      Γ.vertexSet Z ∩ component Z Y root := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩,
      vertexSet_pathsInComponent_left_subset hZfinite hx⟩
  · rintro x ⟨⟨p, hpZ, hxp⟩, hxC⟩
    obtain ⟨q, rfl⟩ := hZfinite hpZ
    refine ⟨.inl q, ⟨hpZ, ?_⟩, hxp⟩
    exact finitePath_support_subset_component_of_touches_left
      hxC hpZ hxp q.start_mem_support

theorem vertexSet_pathsInComponent_right
    {Z Y : Set Γ.DPath} {root : V}
    (hYfinite : Γ.HasFiniteCharacter Y) :
    Γ.vertexSet (pathsInComponent Z Y Y root) =
      Γ.vertexSet Y ∩ component Z Y root := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩,
      vertexSet_pathsInComponent_right_subset hYfinite hx⟩
  · rintro x ⟨⟨p, hpY, hxp⟩, hxC⟩
    obtain ⟨q, rfl⟩ := hYfinite hpY
    refine ⟨.inl q, ⟨hpY, ?_⟩, hxp⟩
    exact finitePath_support_subset_component_of_touches_right
      hxC hpY hxp q.start_mem_support

theorem initialDifference_pathsInComponent
    (Z Y : Set Γ.DPath) (root : V) :
    Γ.initialSet (pathsInComponent Z Y Z root) \
        Γ.initialSet (pathsInComponent Z Y Y root) =
      (Γ.initialSet Z \ Γ.initialSet Y) ∩ component Z Y root := by
  rw [initialSet_pathsInComponent, initialSet_pathsInComponent]
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

theorem terminalFrontier_pathsInComponent
    {Z Y W : Set Γ.DPath} {root : V}
    (hWfinite : Γ.HasFiniteCharacter W)
    (hside : ∀ {p : FinitePath Γ.graph},
      (.inl p : Γ.DPath) ∈ W →
      p.support ⊆ component Z Y p.start) :
    Γ.terminalFrontier (pathsInComponent Z Y W root) =
      Γ.terminalFrontier W ∩ component Z Y root := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨terminalFrontier_pathsInComponent_subset Z Y W root hx, ?_⟩
    rcases hx with ⟨p, hp, hfinish⟩
    obtain ⟨q, rfl⟩ := hWfinite hp.1
    change some q.finish = some x at hfinish
    have hx : q.finish = x := Option.some.inj hfinish
    exact hx ▸ component_trans hp.2 (hside hp.1 q.finish_mem_support)
  · rintro x ⟨⟨p, hpW, hfinish⟩, hxC⟩
    obtain ⟨q, rfl⟩ := hWfinite hpW
    refine ⟨.inl q, ⟨hpW, ?_⟩, hfinish⟩
    change some q.finish = some x at hfinish
    have hx : q.finish = x := Option.some.inj hfinish
    have hfinishC : q.finish ∈ component Z Y root := hx ▸ hxC
    exact component_trans hfinishC
      (component_symm (hside hpW q.finish_mem_support))

/-! ## Promoting componentwise safety -/

theorem AltPath.link_support_subset_vertexSet {Q : AltPath Γ.graph}
    {l : Link Γ.graph} (hl : l ∈ Q.links) :
    l.path.support ⊆ Q.vertexSet := by
  cases Q with
  | trivial v => simp at hl
  | finite Q =>
      simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, hx⟩
  | infinite Q =>
      simp only [AltPath.links, InfiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, hx⟩

theorem AltPath.edgeSet_subset_vertexSet_prod (Q : AltPath Γ.graph) :
    Q.edgeSet ⊆ {e | e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet} := by
  intro e he
  rw [Q.edgeSet_eq_iUnion_links] at he
  simp only [Set.mem_iUnion] at he
  rcases he with ⟨l, hl, hel⟩
  have hs := l.path.edgeSet_subset_support_prod hel
  exact ⟨Q.link_support_subset_vertexSet hl hs.1,
    Q.link_support_subset_vertexSet hl hs.2⟩

theorem AltPath.mem_vertexSet_of_terminal_eq {Q : AltPath Γ.graph} {x : V}
    (hx : Q.terminal? = some x) : x ∈ Q.vertexSet := by
  cases Q with
  | trivial v => simpa using Option.some.inj hx.symm
  | finite Q =>
      have heq : Q.terminal = x := Option.some.inj hx
      exact heq ▸ Q.terminal_mem_vertexSet
  | infinite Q => simp at hx

theorem mem_familyEdges_pathsInComponent_right_of_mem
    {Z Y : Set Γ.DPath} {root : V} {e : V × V}
    (hYfinite : Γ.HasFiniteCharacter Y)
    (heY : e ∈ familyEdges Y) (heC : e.1 ∈ component Z Y root) :
    e ∈ familyEdges (pathsInComponent Z Y Y root) := by
  simp only [familyEdges, Set.mem_iUnion] at heY ⊢
  rcases heY with ⟨p, hpY, hep⟩
  obtain ⟨q, rfl⟩ := hYfinite hpY
  refine ⟨.inl q, ⟨hpY, ?_⟩, hep⟩
  have heSupport := q.edgeSet_subset_support_prod hep
  exact finitePath_support_subset_component_of_touches_right
    heC hpY heSupport.1 q.start_mem_support

/-- Safety proved after restricting the reference warp to one alternating
component is genuine safety for the whole reference warp, as soon as the
alternating path itself stays in that component. -/
theorem IsSafe.of_pathsInComponent
    {Z Y : Set Γ.DPath} {root : V} {Q : AltPath Γ.graph}
    (hY : Γ.IsWarp Y) (hYfinite : Γ.HasFiniteCharacter Y)
    (hQ : IsSafe (pathsInComponent Z Y Y root) Q)
    (hQC : Q.vertexSet ⊆ component Z Y root) :
    IsSafe Y Q := by
  let Yc := pathsInComponent Z Y Y root
  have hvertex : ∀ {x : V}, x ∈ Γ.vertexSet Y →
      x ∈ component Z Y root → x ∈ Γ.vertexSet Yc := by
    intro x hxY hxC
    rw [vertexSet_pathsInComponent_right hYfinite]
    exact ⟨hxY, hxC⟩
  have hfamily : familyEdges Yc ⊆ familyEdges Y := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion] at he ⊢
    rcases he with ⟨p, hp, hep⟩
    exact ⟨p, hp.1, hep⟩
  rcases hQ with
    ⟨⟨_hYc, hback, hinitial, hterminal⟩,
      hinterval, hnray, hncycle⟩
  refine ⟨⟨hY, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro l hl hdir
    rcases hback l hl hdir with ⟨p, hpYc, hlp⟩
    exact ⟨p, hpYc.1, hlp⟩
  · intro hfirst hxY
    exact hinitial hfirst (hvertex hxY (hQC Q.initial_mem_vertexSet))
  · intro t hterm hlast htY
    exact hterminal t hterm hlast
      (hvertex htY (hQC (Q.mem_vertexSet_of_terminal_eq hterm)))
  · intro p hpY
    by_cases hpC : p.initial ∈ component Z Y root
    · exact hinterval p ⟨hpY, hpC⟩
    · left
      apply Set.Subset.antisymm
      · intro e he
        exfalso
        rcases he with ⟨heQ, hep⟩
        have heQ' : e ∈ Q.edgeSet := by
          rw [Q.edgeSet_eq_directionEdges_union]
          exact Or.inr heQ
        have heQC : e.1 ∈ component Z Y root :=
          hQC (Q.edgeSet_subset_vertexSet_prod heQ').1
        obtain ⟨q, rfl⟩ := hYfinite hpY
        have hes := q.edgeSet_subset_support_prod hep
        exact hpC (finitePath_support_subset_component_of_touches_right
          heQC hpY hes.1 q.start_mem_support)
      · intro e he
        exact he.elim
  · intro hray
    apply hnray
    rcases hray with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro e he
    have he' := hR he
    exact ⟨he'.1, fun heYc ↦ he'.2 (hfamily heYc)⟩
  · intro hcycle
    apply hncycle
    rcases hcycle with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro e he
    have he' := hC he
    exact ⟨he'.1, fun heYc ↦ he'.2 (hfamily heYc)⟩

theorem terminalFrontier_pathsInComponent_left
    {Z Y : Set Γ.DPath} {root : V}
    (hZfinite : Γ.HasFiniteCharacter Z) :
    Γ.terminalFrontier (pathsInComponent Z Y Z root) =
      Γ.terminalFrontier Z ∩ component Z Y root := by
  apply terminalFrontier_pathsInComponent hZfinite
  intro p hp
  exact finitePath_support_subset_component_left hp p.start_mem_support

theorem IsLeaving.of_pathsInComponent
    {Z Y : Set Γ.DPath} {root : V} {Q : AltPath Γ.graph}
    (hYfinite : Γ.HasFiniteCharacter Y)
    (hQ : IsLeaving (pathsInComponent Z Y Y root) Q)
    (hQC : Q.vertexSet ⊆ component Z Y root) :
    IsLeaving Y Q := by
  rcases hQ with hinfinite | ⟨t, hterm, ht⟩
  · exact Or.inl hinfinite
  · refine Or.inr ⟨t, hterm, ?_⟩
    intro htY
    apply ht
    rw [vertexSet_pathsInComponent_right hYfinite]
    exact ⟨htY, hQC (Q.mem_vertexSet_of_terminal_eq hterm)⟩

/-! ## Assembly of the countable component assignments -/

/-- The componentwise assembly of Theorem 4.12.  The hypotheses are exactly
the already-separated Lemma 4.13 and reducing-switch theorem; the public
theorem below discharges both with their concrete implementations. -/
theorem simultaneousAssignment_of_components
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ) :
    SimultaneousAssignmentStatement Γ := by
  intro hΓ Z Y hZsource hZtarget hZ hY hZfinite hYfinite hYZ
  classical
  let K := ComponentClass Z Y
  let root : K → V := fun c ↦ componentRepresentative Z Y c
  let Zc : K → Set Γ.DPath := fun c ↦ pathsInComponent Z Y Z (root c)
  let Yc : K → Set Γ.DPath := fun c ↦ pathsInComponent Z Y Y (root c)
  have hlocal : ∀ c : K,
      ∃ A : SimultaneousAssignment (Zc c) (Yc c),
        ∀ z, (A.assigned z).vertexSet ⊆ component Z Y (root c) := by
    intro c
    apply exists_simultaneousAssignment_of_countable_inside Γ hΓ
    · exact isWarp_pathsInComponent hZ
    · exact hasFiniteCharacter_pathsInComponent hZfinite
    · exact isWarp_pathsInComponent hY
    · exact hasFiniteCharacter_pathsInComponent hYfinite
    · exact initialSet_pathsInComponent_mono hYZ
    · intro x hx
      rw [initialSet_pathsInComponent] at hx
      exact hZsource hx.1
    · exact (terminalFrontier_pathsInComponent_subset Z Y Z (root c)).trans hZtarget
    · rw [initialDifference_pathsInComponent]
      exact component_initial_difference_countable hZ hY hZfinite hYfinite (root c)
    · exact vertexSet_pathsInComponent_left_subset hZfinite
    · exact vertexSet_pathsInComponent_right_subset hYfinite
    · exact hDichotomy
    · exact hSwitch
  choose A hAconfined using hlocal
  let localSource (z : {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y}) :
      {x : V // x ∈ Γ.initialSet (Zc (componentClass Z Y z.1)) \
        Γ.initialSet (Yc (componentClass Z Y z.1))} :=
    ⟨z.1, by
      rw [initialDifference_pathsInComponent]
      exact ⟨z.property,
        mem_component_representative (Z := Z) (Y := Y) z.1⟩⟩
  refine ⟨
    { assigned := fun z ↦
        (A (componentClass Z Y z.1)).assigned (localSource z)
      starts_at := fun z ↦
        (A (componentClass Z Y z.1)).starts_at (localSource z)
      safe := ?_
      leaving := ?_
      maximal := ?_
      finite_terminals_injective := ?_ }⟩
  · intro z
    apply IsSafe.of_pathsInComponent hY hYfinite
    · exact (A (componentClass Z Y z.1)).safe (localSource z)
    · exact hAconfined (componentClass Z Y z.1) (localSource z)
  · intro z
    apply IsLeaving.of_pathsInComponent hYfinite
    · exact (A (componentClass Z Y z.1)).leaving (localSource z)
    · exact hAconfined (componentClass Z Y z.1) (localSource z)
  · intro z
    let c := componentClass Z Y z.1
    rcases (A c).maximal (localSource z) with hinfinite | ⟨v, hv, hterm⟩
    · exact Or.inl hinfinite
    · refine Or.inr ⟨v, ⟨?_, ?_⟩, hterm⟩
      · exact terminalFrontier_pathsInComponent_subset Z Y Z (root c) hv.1
      · intro hvY
        apply hv.2
        rw [vertexSet_pathsInComponent_right hYfinite]
        have hvZc : v ∈ Γ.terminalFrontier
            (pathsInComponent Z Y Z (root c)) := by
          simpa [Zc] using hv.1
        rw [terminalFrontier_pathsInComponent_left
          (Γ := Γ) (Z := Z) (Y := Y) (root := root c) hZfinite] at hvZc
        exact ⟨hvY, hvZc.2⟩
  · intro z₁ z₂ v hz₁ hz₂
    let c₁ := componentClass Z Y z₁.1
    let c₂ := componentClass Z Y z₂.1
    have hv₁ := (A c₁).finite_terminal_mem (localSource z₁) hz₁
    have hv₂ := (A c₂).finite_terminal_mem (localSource z₂) hz₂
    have hvZc₁ : v ∈ Γ.terminalFrontier
        (pathsInComponent Z Y Z (root c₁)) := by
      simpa [Zc] using hv₁.1
    have hvZc₂ : v ∈ Γ.terminalFrontier
        (pathsInComponent Z Y Z (root c₂)) := by
      simpa [Zc] using hv₂.1
    rw [terminalFrontier_pathsInComponent_left
      (Γ := Γ) (Z := Z) (Y := Y) (root := root c₁) hZfinite] at hvZc₁
    rw [terminalFrontier_pathsInComponent_left
      (Γ := Γ) (Z := Z) (Y := Y) (root := root c₂) hZfinite] at hvZc₂
    have hvC₁ : v ∈ component Z Y (root c₁) := hvZc₁.2
    have hvC₂ : v ∈ component Z Y (root c₂) := hvZc₂.2
    have hroot : root c₂ ∈ component Z Y (root c₁) :=
      component_trans hvC₁ (component_symm hvC₂)
    have hc : c₁ = c₂ := by
      calc
        c₁ = componentClass Z Y (root c₁) :=
          (Quotient.out_eq c₁).symm
        _ = componentClass Z Y (root c₂) :=
          componentClass_eq_iff.mpr hroot
        _ = c₂ := Quotient.out_eq c₂
    have hc' : componentClass Z Y z₁.1 = componentClass Z Y z₂.1 := by
      simpa [c₁, c₂] using hc
    have hsame : ∀ (d₁ d₂ : K)
        (w₁ : {x : V // x ∈ Γ.initialSet (Zc d₁) \ Γ.initialSet (Yc d₁)})
        (w₂ : {x : V // x ∈ Γ.initialSet (Zc d₂) \ Γ.initialSet (Yc d₂)})
        (x : V), d₁ = d₂ →
        ((A d₁).assigned w₁).terminal? = some x →
        ((A d₂).assigned w₂).terminal? = some x → w₁.1 = w₂.1 := by
      intro d₁ d₂ w₁ w₂ x hd h₁ h₂
      subst d₂
      exact congrArg Subtype.val
        ((A d₁).finite_terminals_injective h₁ h₂)
    have hzlocal : (localSource z₁).1 = (localSource z₂).1 :=
      hsame _ _ (localSource z₁) (localSource z₂) v hc' hz₁ hz₂
    apply Subtype.ext
    exact hzlocal

/-- Componentwise Theorem 4.12 also gives the fractured conclusion of
Remark 4.20.  Under the normalized endpoint hypotheses, the fractured
family is already a warp. -/
theorem fracturedSimultaneousAssignment_of_components
    (hDichotomy : SafeAlternatingDichotomyStatement Γ)
    (hSwitch : ReducingSwitchRule Γ) :
    FracturedSimultaneousAssignmentStatement Γ :=
  FracturedDuplication.fracturedSimultaneousAssignment_of_ordinary
    (simultaneousAssignment_of_components hDichotomy hSwitch)

/-- Theorem 4.12 follows globally from Lemma 4.13.  The proof uses the
disjoint endpoint-macro orbits of the uncovered sources; it does not use the
false one-pair reducing-switch rule. -/
theorem simultaneousAssignment_of_safeAlternatingDichotomy
    (hDichotomy : SafeAlternatingDichotomyStatement Γ) :
    SimultaneousAssignmentStatement Γ :=
  simultaneousAssignment_of_safeAlternatingDichotomy_global hDichotomy

/-- Fractured form with the same sole input, Lemma 4.13. -/
theorem fracturedSimultaneousAssignment_of_safeAlternatingDichotomy
    (hDichotomy : SafeAlternatingDichotomyStatement Γ) :
    FracturedSimultaneousAssignmentStatement Γ :=
  FracturedDuplication.fracturedSimultaneousAssignment_of_ordinary
    (simultaneousAssignment_of_safeAlternatingDichotomy hDichotomy)

end Alternating
end Erdos599

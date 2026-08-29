/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Order.Zorn

/-!
# Erdős Problem 599: the abstract wave calculus

This file isolates the order-theoretic part of the Aharoni--Berger wave
argument from the eventual concrete implementation of directed paths.  The
interface is deliberately honest: the two graph-theoretic facts about roofs
which are used below are fields of `RoofedPathSystem`, and therefore have to
be proved when the interface is instantiated by a directed graph.

The principal definitions are `IsWave`, `IsHindrance`, `IsLoose`, `RoofLE`,
and `ForwardExtension`.  We prove self-roofing, essential trimming, an
explicit-hypothesis splice theorem, and the Zorn maximal-wave step.
-/

namespace Erdos599.WaveCore

universe u v

/-- The path data used by the abstract wave calculus.

`Extends p q` means that `q` is a forward extension of `p`.  Only its
preorder laws and the elementary facts that an extension has the same
initial vertex and contains the old support are built into the interface.
Unlike the public undirected problem, this source-faithful directed layer
also admits rays: they are exactly the paths whose terminal is `none`.
-/
structure DirectedPathSystem (V : Type u) (Path : Type v) where
  support : Path → Set V
  initial : Path → V
  /-- `some t` for a finite path ending at `t`, and `none` for a ray. -/
  terminal : Path → Option V
  initial_mem : ∀ p, initial p ∈ support p
  terminal_mem : ∀ p t, terminal p = some t → t ∈ support p
  trivial : V → Path
  support_trivial : ∀ x, support (trivial x) = {x}
  initial_trivial : ∀ x, initial (trivial x) = x
  terminal_trivial : ∀ x, terminal (trivial x) = some x
  Extends : Path → Path → Prop
  extends_refl : ∀ p, Extends p p
  extends_trans : ∀ {p q r}, Extends p q → Extends q r → Extends p r
  extends_initial : ∀ {p q}, Extends p q → initial p = initial q
  support_mono_of_extends : ∀ {p q}, Extends p q → support p ⊆ support q

variable {V : Type u} {Path : Type v}

namespace DirectedPathSystem

variable (D : DirectedPathSystem V Path)

/-- All vertices used by a family of paths. -/
def vertexSet (W : Set Path) : Set V :=
  {x | ∃ p ∈ W, x ∈ D.support p}

/-- The initial vertices of a path family. -/
def initialSet (W : Set Path) : Set V :=
  D.initial '' W

/-- The terminal vertices of the finite members of a path family.  Rays do
not contribute a terminal vertex. -/
def terminalSet (W : Set Path) : Set V :=
  {x | ∃ p ∈ W, D.terminal p = some x}

/-- A path is finite when it has a terminal vertex. -/
def IsFinite (p : Path) : Prop :=
  ∃ x, D.terminal p = some x

/-- A path is a ray when it has no terminal vertex. -/
def IsRay (p : Path) : Prop :=
  D.terminal p = none

/-- The singleton containing the terminal of a finite path, and the empty
set for a ray. -/
def terminalSingleton (p : Path) : Set V :=
  match D.terminal p with
  | some x => {x}
  | none => ∅

/-- The family of all length-zero paths based at a set of vertices. -/
def trivialWarp (A : Set V) : Set Path :=
  D.trivial '' A

/-- A warp is a pairwise vertex-disjoint family of paths. -/
def IsWarp (W : Set Path) : Prop :=
  W.PairwiseDisjoint D.support

@[simp]
theorem mem_vertexSet {W : Set Path} {x : V} :
    x ∈ D.vertexSet W ↔ ∃ p ∈ W, x ∈ D.support p :=
  Iff.rfl

@[simp]
theorem mem_initialSet {W : Set Path} {x : V} :
    x ∈ D.initialSet W ↔ ∃ p ∈ W, D.initial p = x :=
  Set.mem_image _ _ _

@[simp]
theorem mem_terminalSet {W : Set Path} {x : V} :
    x ∈ D.terminalSet W ↔ ∃ p ∈ W, D.terminal p = some x :=
  Iff.rfl

theorem terminal_trivial_isFinite (x : V) : D.IsFinite (D.trivial x) :=
  ⟨x, D.terminal_trivial x⟩

theorem terminal_trivial_not_isRay (x : V) : ¬D.IsRay (D.trivial x) := by
  simp only [IsRay, D.terminal_trivial, reduceCtorEq, not_false_eq_true]

theorem initialSet_trivialWarp (A : Set V) :
    D.initialSet (D.trivialWarp A) = A := by
  ext x
  constructor
  · rintro ⟨p, ⟨a, ha, rfl⟩, hx⟩
    have hax : a = x := by simpa [D.initial_trivial] using hx
    exact hax ▸ ha
  · intro hx
    exact ⟨D.trivial x, ⟨x, hx, rfl⟩, D.initial_trivial x⟩

theorem terminalSet_trivialWarp (A : Set V) :
    D.terminalSet (D.trivialWarp A) = A := by
  ext x
  constructor
  · rintro ⟨p, ⟨a, ha, rfl⟩, hx⟩
    have hax : a = x := by simpa [D.terminal_trivial] using hx
    exact hax ▸ ha
  · intro hx
    exact ⟨D.trivial x, ⟨x, hx, rfl⟩, D.terminal_trivial x⟩

theorem trivial_injective : Function.Injective D.trivial := by
  intro x y h
  have := congrArg D.initial h
  simpa [D.initial_trivial] using this

theorem isWarp_trivialWarp (A : Set V) : D.IsWarp (D.trivialWarp A) := by
  rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hpq
  change Disjoint (D.support (D.trivial x)) (D.support (D.trivial y))
  rw [D.support_trivial, D.support_trivial]
  simpa only [Set.disjoint_singleton] using
    (fun hxy : x = y ↦ hpq (congrArg D.trivial hxy))

end DirectedPathSystem

/-- A roof operator for paths aimed at one fixed target set.

For a concrete web, `roof S` is the set of vertices from which every path
to the target meets `S`.  `path_support_roof` is the elementary
prefix-splicing argument used by self-roofing.  Its intersection hypothesis
records the point which is sometimes implicit in prose: the path has not
already met a different member of `S`.  For a ray the permitted terminal
singleton is empty, recording that a disjoint ray member misses the whole
terminal frontier.  `roof_essential` is the last-point argument on a finite
path to the target (Aharoni--Berger, Lemma 2.14).
-/
structure RoofedPathSystem (V : Type u) (Path : Type v)
    extends DirectedPathSystem V Path where
  roof : Set V → Set V
  subset_roof : ∀ S, S ⊆ roof S
  roof_mono : Monotone roof
  roof_cut : ∀ {X S}, X ⊆ roof S → roof X ⊆ roof S
  path_support_roof : ∀ (p : Path) (S : Set V),
    initial p ∈ roof S →
      (∀ t, terminal p = some t → t ∈ S) →
      support p ∩ S ⊆ toDirectedPathSystem.terminalSingleton p →
      support p ⊆ roof S
  roof_essential : ∀ S,
    roof {s | s ∈ S ∧ s ∉ roof (S \ {s})} = roof S

namespace RoofedPathSystem

variable (D : RoofedPathSystem V Path)

/-- A point of `S` is essential when it can still see the target while
avoiding all other points of `S`.  This is the complement-of-roof form of
the usual definition. -/
def Essential (S : Set V) : Set V :=
  {s | s ∈ S ∧ s ∉ D.roof (S \ {s})}

/-- The inessential points of a frontier. -/
def inessential (S : Set V) : Set V :=
  S \ D.Essential S

/-- The strict roof is the roof with its essential frontier removed. -/
def strictRoof (S : Set V) : Set V :=
  D.roof S \ D.Essential S

theorem essential_subset (S : Set V) : D.Essential S ⊆ S :=
  fun _ hx ↦ hx.1

theorem roof_essential_eq (S : Set V) :
    D.roof (D.Essential S) = D.roof S := by
  exact D.roof_essential S

/-- `S` separates `X` from the fixed target encoded by `D`. -/
def Separates (X S : Set V) : Prop :=
  X ⊆ D.roof S

/-- A wave is a disjoint, `A`-starting family whose terminal frontier
separates `A` from the target. -/
def IsWave (A : Set V) (W : Set Path) : Prop :=
  D.toDirectedPathSystem.IsWarp W ∧
    D.toDirectedPathSystem.initialSet W ⊆ A ∧
    D.Separates A (D.toDirectedPathSystem.terminalSet W)

/-- A hindrance is a wave which misses at least one source as an initial
vertex. -/
def IsHindrance (A : Set V) (W : Set Path) : Prop :=
  D.IsWave A W ∧ D.toDirectedPathSystem.initialSet W ≠ A

/-- A web is unhindered when it has no hindrance. -/
def IsUnhindered (A : Set V) : Prop :=
  ¬ ∃ W : Set Path, D.IsHindrance A W

/-- A web is loose when its only wave is the trivial singleton warp. -/
def IsLoose (A : Set V) : Prop :=
  ∀ W : Set Path, D.IsWave A W →
    W = D.toDirectedPathSystem.trivialWarp A

/-- Keep exactly the finite paths ending at essential points of the terminal
frontier.  In particular, every ray is discarded. -/
def essentialTrim (W : Set Path) : Set Path :=
  {p ∈ W | ∃ t,
    D.terminal p = some t ∧
      t ∈ D.Essential (D.toDirectedPathSystem.terminalSet W)}

theorem separates_essential {X S : Set V} (h : D.Separates X S) :
    D.Separates X (D.Essential S) := by
  rw [Separates, D.roof_essential_eq]
  exact h

theorem terminalSet_essentialTrim (W : Set Path) :
    D.toDirectedPathSystem.terminalSet (D.essentialTrim W) =
      D.Essential (D.toDirectedPathSystem.terminalSet W) := by
  ext x
  constructor
  · rintro ⟨p, ⟨hp, t, hpt, ht⟩, hpx⟩
    have htx : t = x := Option.some.inj (hpt.symm.trans hpx)
    simpa [htx] using ht
  · intro hx
    obtain ⟨p, hp, hpx⟩ := hx.1
    exact ⟨p, ⟨hp, x, hpx, hx⟩, hpx⟩

theorem essentialTrim_isFinite {W : Set Path} {p : Path}
    (hp : p ∈ D.essentialTrim W) : D.toDirectedPathSystem.IsFinite p := by
  obtain ⟨t, hpt, ht⟩ := hp.2
  exact ⟨t, hpt⟩

theorem ray_not_mem_essentialTrim {W : Set Path} {p : Path}
    (hp : D.toDirectedPathSystem.IsRay p) : p ∉ D.essentialTrim W := by
  intro hpW
  obtain ⟨t, hpt, ht⟩ := hpW.2
  unfold DirectedPathSystem.IsRay at hp
  rw [hp] at hpt
  cases hpt

theorem isWarp_essentialTrim {W : Set Path}
    (hW : D.toDirectedPathSystem.IsWarp W) :
    D.toDirectedPathSystem.IsWarp (D.essentialTrim W) := by
  intro p hp q hq hpq
  exact hW hp.1 hq.1 hpq

/-- Essential trimming preserves a wave.  The only substantive separator
step is `roof_essential`, exposed by the abstract interface above. -/
theorem isWave_essentialTrim {A : Set V} {W : Set Path}
    (hW : D.IsWave A W) : D.IsWave A (D.essentialTrim W) := by
  refine ⟨D.isWarp_essentialTrim hW.1, ?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    exact hW.2.1 ⟨p, hp.1, rfl⟩
  · rw [D.terminalSet_essentialTrim]
    exact D.separates_essential hW.2.2

/-- A member of a warp cannot contain the terminal vertex of a different
member.  Consequently it meets the warp's terminal frontier only at its own
terminal when finite, and does not meet that frontier at all when it is a
ray. -/
theorem support_inter_terminalSet_subset {W : Set Path}
    (hW : D.toDirectedPathSystem.IsWarp W) {p : Path} (hp : p ∈ W) :
    D.support p ∩ D.toDirectedPathSystem.terminalSet W ⊆
      D.toDirectedPathSystem.terminalSingleton p := by
  intro x hx
  obtain ⟨q, hq, hqx⟩ := hx.2
  have hxq : x ∈ D.support q := by
    exact D.terminal_mem q x hqx
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW hp hq hpq) hx.1 hxq
  subst q
  unfold DirectedPathSystem.terminalSingleton
  split <;> rename_i hterminal
  · simp only [Set.mem_singleton_iff]
    have := hterminal.symm.trans hqx
    exact (Option.some.inj this).symm
  · have : (none : Option V) = some x := hterminal.symm.trans hqx
    simp at this

/-- Every wave lies inside the roof of its own terminal frontier
(Aharoni--Berger, Lemma 3.7). -/
theorem IsWave.self_roofing {A : Set V} {W : Set Path}
    (hW : D.IsWave A W) :
    D.toDirectedPathSystem.vertexSet W ⊆
      D.roof (D.toDirectedPathSystem.terminalSet W) := by
  rintro x ⟨p, hp, hxp⟩
  have hiA : D.initial p ∈ A := hW.2.1 ⟨p, hp, rfl⟩
  have hiRoof : D.initial p ∈
      D.roof (D.toDirectedPathSystem.terminalSet W) := hW.2.2 hiA
  have ht : ∀ t, D.terminal p = some t →
      t ∈ D.toDirectedPathSystem.terminalSet W :=
    fun t hpt ↦ ⟨p, hp, hpt⟩
  exact D.path_support_roof p _ hiRoof ht
    (D.support_inter_terminalSet_subset hW.1 hp) hxp

/-- The ray case of self-roofing, stated separately for downstream proofs
which distinguish finite and unending members of a warp. -/
theorem IsWave.ray_support_subset_roof {A : Set V} {W : Set Path}
    (hW : D.IsWave A W) {p : Path} (hp : p ∈ W)
    (_hpRay : D.toDirectedPathSystem.IsRay p) :
    D.support p ⊆ D.roof (D.toDirectedPathSystem.terminalSet W) := by
  intro x hx
  exact IsWave.self_roofing D hW ⟨p, hp, hx⟩

theorem isWave_trivialWarp (A : Set V) :
    D.IsWave A (D.toDirectedPathSystem.trivialWarp A) := by
  refine ⟨D.toDirectedPathSystem.isWarp_trivialWarp A, ?_, ?_⟩
  · rw [D.toDirectedPathSystem.initialSet_trivialWarp]
  · rw [Separates, D.toDirectedPathSystem.terminalSet_trivialWarp]
    exact D.subset_roof A

theorem isLoose_iff (A : Set V) :
    D.IsLoose A ↔
      ∀ W : Set Path, D.IsWave A W ↔
        W = D.toDirectedPathSystem.trivialWarp A := by
  constructor
  · intro h W
    constructor
    · exact h W
    · rintro rfl
      exact D.isWave_trivialWarp A
  · intro h W hW
    exact (h W).1 hW

theorem isUnhindered_iff (A : Set V) :
    D.IsUnhindered A ↔
      ∀ W : Set Path, D.IsWave A W →
        D.toDirectedPathSystem.initialSet W = A := by
  simp only [IsUnhindered, IsHindrance, not_exists, not_and, Decidable.not_not]

/-- Roof order on path families.  This is distinct from forward extension. -/
def RoofLE (U W : Set Path) : Prop :=
  D.roof (D.toDirectedPathSystem.terminalSet U) ⊆
    D.roof (D.toDirectedPathSystem.terminalSet W)

theorem roofLE_refl (W : Set Path) : D.RoofLE W W :=
  Set.Subset.rfl

theorem roofLE_trans {U W Z : Set Path}
    (hUW : D.RoofLE U W) (hWZ : D.RoofLE W Z) : D.RoofLE U Z :=
  hUW.trans hWZ

/-- Equality modulo the essential terminal frontier. -/
def RoofEquivalent (U W : Set Path) : Prop :=
  D.Essential (D.toDirectedPathSystem.terminalSet U) =
    D.Essential (D.toDirectedPathSystem.terminalSet W)

theorem roofs_eq_of_roofEquivalent {U W : Set Path}
    (h : D.RoofEquivalent U W) :
    D.roof (D.toDirectedPathSystem.terminalSet U) =
      D.roof (D.toDirectedPathSystem.terminalSet W) := by
  calc
    D.roof (D.toDirectedPathSystem.terminalSet U) =
        D.roof (D.Essential (D.toDirectedPathSystem.terminalSet U)) :=
      (D.roof_essential_eq _).symm
    _ = D.roof (D.Essential (D.toDirectedPathSystem.terminalSet W)) :=
      congrArg D.roof h
    _ = D.roof (D.toDirectedPathSystem.terminalSet W) :=
      D.roof_essential_eq _

/-- Forward extension, lifted from individual paths to whole warps.  Both
directions of matching are required: extensions neither lose nor introduce
an initial thread. -/
def ForwardExtension (U W : Set Path) : Prop :=
  (∀ p ∈ U, ∃ q ∈ W, D.Extends p q) ∧
    (∀ q ∈ W, ∃ p ∈ U, D.Extends p q)

theorem forwardExtension_refl (W : Set Path) : D.ForwardExtension W W := by
  exact ⟨fun p hp ↦ ⟨p, hp, D.extends_refl p⟩,
    fun p hp ↦ ⟨p, hp, D.extends_refl p⟩⟩

theorem forwardExtension_trans {U W Z : Set Path}
    (hUW : D.ForwardExtension U W) (hWZ : D.ForwardExtension W Z) :
    D.ForwardExtension U Z := by
  constructor
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := hUW.1 p hp
    obtain ⟨r, hr, hqr⟩ := hWZ.1 q hq
    exact ⟨r, hr, D.extends_trans hpq hqr⟩
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := hWZ.2 r hr
    obtain ⟨p, hp, hpq⟩ := hUW.2 q hq
    exact ⟨p, hp, D.extends_trans hpq hqr⟩

theorem initialSet_eq_of_forwardExtension {U W : Set Path}
    (h : D.ForwardExtension U W) :
    D.toDirectedPathSystem.initialSet U =
      D.toDirectedPathSystem.initialSet W := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := h.1 p hp
    exact ⟨q, hq, (D.extends_initial hpq).symm⟩
  · rintro x ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := h.2 q hq
    exact ⟨p, hp, D.extends_initial hpq⟩

/-- The explicit structural obligations which a concrete path-splicing
operation must discharge. -/
def IsSpliceResult (U W R : Set Path) : Prop :=
  D.toDirectedPathSystem.IsWarp R ∧
    D.toDirectedPathSystem.initialSet R ⊆
      D.toDirectedPathSystem.initialSet U ∧
    D.toDirectedPathSystem.terminalSet R =
      D.toDirectedPathSystem.terminalSet W

/-- Splicing a wave from `A` with a wave from the first wave's terminal
frontier again gives a wave from `A`, provided the concrete splice has the
advertised disjointness, initial-set, and terminal-set properties. -/
theorem isWave_splice {A : Set V} {U W R : Set Path}
    (hU : D.IsWave A U)
    (hW : D.IsWave (D.toDirectedPathSystem.terminalSet U) W)
    (hR : D.IsSpliceResult U W R) : D.IsWave A R := by
  refine ⟨hR.1, hR.2.1.trans hU.2.1, ?_⟩
  intro a ha
  have haU : a ∈ D.roof (D.toDirectedPathSystem.terminalSet U) := hU.2.2 ha
  have hcut : D.roof (D.toDirectedPathSystem.terminalSet U) ⊆
      D.roof (D.toDirectedPathSystem.terminalSet W) :=
    D.roof_cut hW.2.2
  rw [hR.2.2]
  exact hcut haU

/-- Waves packaged as a type, for the Zorn argument. -/
abbrev AbstractWave (A : Set V) :=
  {W : Set Path // D.IsWave A W}

instance abstractWaveLE (A : Set V) : LE (D.AbstractWave A) where
  le U W := D.ForwardExtension U.1 W.1

instance abstractWavePreorder (A : Set V) : Preorder (D.AbstractWave A) where
  le U W := D.ForwardExtension U.1 W.1
  lt U W := D.ForwardExtension U.1 W.1 ∧ ¬D.ForwardExtension W.1 U.1
  le_refl _ := D.forwardExtension_refl _
  le_trans _ _ _ h₁ h₂ := D.forwardExtension_trans h₁ h₂
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Zorn's lemma for waves.  The chain-upper-bound theorem is an explicit
argument: this abstract result does not claim that arbitrary path systems
have such upper bounds.  In the concrete Aharoni--Berger development the
iterated-arrow lemma supplies `hchain`.
-/
theorem exists_maximal_forward_extension (A : Set V)
    (W₀ : D.AbstractWave A)
    (hchain : ∀ c : Set (D.AbstractWave A),
      IsChain (· ≤ ·) c → c.Nonempty →
        ∃ ub : D.AbstractWave A, ∀ W ∈ c, W ≤ ub) :
    ∃ M : D.AbstractWave A, W₀ ≤ M ∧ IsMax M := by
  apply zorn_le_nonempty_Ici₀ W₀
  · intro c hcIci hc y hy
    obtain ⟨ub, hub⟩ := hchain c hc ⟨y, hy⟩
    exact ⟨ub, hub⟩
  · exact le_rfl

end RoofedPathSystem

end Erdos599.WaveCore

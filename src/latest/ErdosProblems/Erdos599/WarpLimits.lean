/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Erdős Problem 599: eventual set limits and forward chains

The limits of warps in the Aharoni--Berger proof are not topological
limits.  A vertex or edge survives a limit stage precisely when it belongs
to every sufficiently late stage.  This file isolates that set-theoretic
notion and the small amount of order theory needed to form upper bounds of
forward-extension chains.

The definitions are independent of the eventual concrete representation of
paths and warps.  Once `Web.lean` supplies a warp type, its vertex set and
edge set can be used as the observables of `ForwardChain.observableLimit`.
-/

namespace Erdos599
namespace WarpLimits

open Filter Set

universe u v w

/-! ## Liminf along an arbitrary filter -/

/-- The set of points which belong to `s i` eventually along `l`.

This is the set-theoretic liminf used for both the vertex and edge sets of a
limit warp. -/
def filterSetLiminf {ι : Type u} {α : Type v} (l : Filter ι)
    (s : ι → Set α) : Set α :=
  {x | ∀ᶠ i in l, x ∈ s i}

@[simp]
theorem mem_filterSetLiminf {ι : Type u} {α : Type v} (l : Filter ι)
    (s : ι → Set α) (x : α) :
    x ∈ filterSetLiminf l s ↔ ∀ᶠ i in l, x ∈ s i :=
  Iff.rfl

/-- Eventual pointwise inclusion induces inclusion of liminfs. -/
theorem filterSetLiminf_mono {ι : Type u} {α : Type v} {l : Filter ι}
    {s t : ι → Set α} (h : ∀ᶠ i in l, s i ⊆ t i) :
    filterSetLiminf l s ⊆ filterSetLiminf l t := by
  intro x hx
  filter_upwards [hx, h] with i hxi hi
  exact hi hxi

/-- A set eventually contained in every stage is contained in the liminf. -/
theorem subset_filterSetLiminf_of_eventually_subset {ι : Type u} {α : Type v}
    {l : Filter ι} {S : Set α} {s : ι → Set α}
    (h : ∀ᶠ i in l, S ⊆ s i) :
    S ⊆ filterSetLiminf l s := by
  intro x hx
  exact h.mono fun _ hi ↦ hi hx

/-- An eventual common upper bound also bounds the liminf. -/
theorem filterSetLiminf_subset_of_eventually_subset {ι : Type u} {α : Type v}
    {l : Filter ι} [l.NeBot] {S : Set α} {s : ι → Set α}
    (h : ∀ᶠ i in l, s i ⊆ S) :
    filterSetLiminf l s ⊆ S := by
  intro x hx
  simpa only [Filter.eventually_const] using
    ((hx.and h).mono fun _ hi ↦ hi.2 hi.1)

@[simp]
theorem filterSetLiminf_inter {ι : Type u} {α : Type v} (l : Filter ι)
    (s t : ι → Set α) :
    filterSetLiminf l (fun i ↦ s i ∩ t i) =
      filterSetLiminf l s ∩ filterSetLiminf l t := by
  ext x
  simp only [mem_filterSetLiminf, Set.mem_inter_iff, Filter.eventually_and]

@[simp]
theorem filterSetLiminf_univ {ι : Type u} {α : Type v} (l : Filter ι) :
    filterSetLiminf l (fun _ ↦ (Set.univ : Set α)) = Set.univ := by
  ext x
  simp

@[simp]
theorem filterSetLiminf_const {ι : Type u} {α : Type v} (l : Filter ι)
    [l.NeBot] (S : Set α) :
    filterSetLiminf l (fun _ ↦ S) = S := by
  ext x
  simp [filterSetLiminf]

/-- Eventually equal families have the same liminf. -/
theorem filterSetLiminf_congr {ι : Type u} {α : Type v} {l : Filter ι}
    {s t : ι → Set α} (h : s =ᶠ[l] t) :
    filterSetLiminf l s = filterSetLiminf l t := by
  apply Set.Subset.antisymm
  · apply filterSetLiminf_mono
    exact h.mono fun _ hi ↦ hi ▸ Set.Subset.rfl
  · apply filterSetLiminf_mono
    exact h.mono fun _ hi ↦ hi.symm ▸ Set.Subset.rfl

/-- Pointwise eventual stability at a prescribed set. -/
def EventuallyPointwiseStable {ι : Type u} {α : Type v} (l : Filter ι)
    (s : ι → Set α) (S : Set α) : Prop :=
  ∀ x, ∀ᶠ i in l, (x ∈ s i ↔ x ∈ S)

/-- A pointwise eventually stable family has the prescribed liminf. -/
theorem filterSetLiminf_eq_of_eventuallyPointwiseStable
    {ι : Type u} {α : Type v} {l : Filter ι} [l.NeBot]
    {s : ι → Set α} {S : Set α}
    (h : EventuallyPointwiseStable l s S) :
    filterSetLiminf l s = S := by
  ext x
  constructor
  · intro hx
    simpa only [Filter.eventually_const] using
      ((hx.and (h x)).mono fun _ hi ↦ hi.2.mp hi.1)
  · intro hx
    exact (h x).mono fun _ hi ↦ hi.mpr hx

/-! ## Tail liminf on a directed preorder -/

section AtTop

variable {ι : Type u} {α : Type v}
variable [Preorder ι]

/-- The liminf of an order-indexed family: membership at every sufficiently
late stage. -/
def setLiminf (s : ι → Set α) : Set α :=
  filterSetLiminf atTop s

/-- Tail liminf is monotone under pointwise inclusion. -/
theorem setLiminf_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) :
    setLiminf s ⊆ setLiminf t :=
  filterSetLiminf_mono (Filter.Eventually.of_forall h)

variable [IsDirectedOrder ι] [Nonempty ι]

@[simp]
theorem mem_setLiminf (s : ι → Set α) (x : α) :
    x ∈ setLiminf s ↔ ∃ i, ∀ j, i ≤ j → x ∈ s j := by
  simp only [setLiminf, mem_filterSetLiminf, Filter.eventually_atTop]

/-- The explicit union-of-tail-intersections formula from the
Aharoni--Berger construction. -/
theorem setLiminf_eq_iUnion_iInter (s : ι → Set α) :
    setLiminf s = ⋃ i, ⋂ j, ⋂ (_ : i ≤ j), s j := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (mem_setLiminf s x).mp hx
    simp only [Set.mem_iUnion, Set.mem_iInter]
    exact ⟨i, fun j hij ↦ hi j hij⟩
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_iInter] at hx
    obtain ⟨i, hi⟩ := hx
    exact (mem_setLiminf s x).mpr ⟨i, fun j hij ↦ hi j hij⟩

/-- For an increasing family, liminf is simply its union.  This lemma is
safe precisely because monotonicity prevents vertices or edges from being
lost at later stages. -/
theorem setLiminf_eq_iUnion_of_monotone {s : ι → Set α} (hs : Monotone s) :
    setLiminf s = ⋃ i, s i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (mem_setLiminf s x).mp hx
    exact Set.mem_iUnion.2 ⟨i, hi i le_rfl⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (mem_setLiminf s x).mpr
      ⟨i, fun j hij ↦ hs hij hxi⟩

/-- At `atTop`, pointwise eventual stability computes the tail liminf. -/
theorem setLiminf_eq_of_eventuallyPointwiseStable {s : ι → Set α} {S : Set α}
    (h : EventuallyPointwiseStable atTop s S) :
    setLiminf s = S :=
  filterSetLiminf_eq_of_eventuallyPointwiseStable h

end AtTop

/-! ## Abstract forward-extension chains -/

/-- A reflexive and transitive notion of forward extension.  Antisymmetry is
not required: two warp presentations can be mutually extending without
being definitionally equal. -/
structure ForwardSystem (σ : Type u) where
  Extends : σ → σ → Prop
  refl : ∀ x, Extends x x
  trans : ∀ {x y z}, Extends x y → Extends y z → Extends x z

namespace ForwardSystem

variable {σ : Type u}

/-- An element above every member of a family in the forward relation. -/
def IsUpperBound (F : ForwardSystem σ) {ι : Type v} (s : ι → σ) (u : σ) : Prop :=
  ∀ i, F.Extends (s i) u

/-- An observable set respects forward extension if it can only grow. -/
def Respects {α : Type v} (F : ForwardSystem σ) (observe : σ → Set α) : Prop :=
  ∀ ⦃x y⦄, F.Extends x y → observe x ⊆ observe y

/-- Forward extension by literal inclusion. -/
def inclusion (α : Type v) : ForwardSystem (Set α) where
  Extends := (· ⊆ ·)
  refl := fun _ ↦ Set.Subset.rfl
  trans := fun hxy hyz ↦ hxy.trans hyz

end ForwardSystem

/-- A chain whose later stages are forward extensions of earlier stages. -/
structure ForwardChain (F : ForwardSystem (σ : Type u)) (ι : Type v)
    [Preorder ι] where
  stage : ι → σ
  forward : ∀ ⦃i j⦄, i ≤ j → F.Extends (stage i) (stage j)

namespace ForwardChain

variable {σ : Type u} {ι : Type v} {α : Type w}
variable {F : ForwardSystem σ} [Preorder ι]

/-- Every stage is below itself, stated in the chain API. -/
theorem forward_refl (c : ForwardChain F ι) (i : ι) :
    F.Extends (c.stage i) (c.stage i) :=
  F.refl _

/-- The stages of a chain form a family bounded by `u` exactly when `u` is
an upper bound in the forward system. -/
theorem isUpperBound_iff (c : ForwardChain F ι) (u : σ) :
    F.IsUpperBound c.stage u ↔ ∀ i, F.Extends (c.stage i) u :=
  Iff.rfl

/-- An observable which respects forward extension is monotone along a
forward chain. -/
theorem observable_monotone (c : ForwardChain F ι) (observe : σ → Set α)
    (hobserve : F.Respects observe) :
    Monotone (fun i ↦ observe (c.stage i)) := by
  intro i j hij
  exact hobserve (c.forward hij)

section Directed

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The eventual observable of a forward chain.  For a concrete warp chain,
`observe` will be either the vertex set or the edge set. -/
def observableLimit (c : ForwardChain F ι) (observe : σ → Set α) : Set α :=
  setLiminf (fun i ↦ observe (c.stage i))

@[simp]
theorem mem_observableLimit (c : ForwardChain F ι) (observe : σ → Set α)
    (x : α) :
    x ∈ c.observableLimit observe ↔
      ∃ i, ∀ j, i ≤ j → x ∈ observe (c.stage j) :=
  mem_setLiminf _ _

/-- Under a forward-respecting observable, every stage is contained in the
eventual observable.  Thus the liminf is a set-level upper bound. -/
theorem stage_subset_observableLimit (c : ForwardChain F ι)
    (observe : σ → Set α) (hobserve : F.Respects observe) (i : ι) :
    observe (c.stage i) ⊆ c.observableLimit observe := by
  intro x hx
  exact (c.mem_observableLimit observe x).mpr
    ⟨i, fun j hij ↦ hobserve (c.forward hij) hx⟩

/-- For forward-respecting observables the eventual limit is the union of
the stages. -/
theorem observableLimit_eq_iUnion (c : ForwardChain F ι)
    (observe : σ → Set α) (hobserve : F.Respects observe) :
    c.observableLimit observe = ⋃ i, observe (c.stage i) :=
  setLiminf_eq_iUnion_of_monotone (c.observable_monotone observe hobserve)

/-- The observable liminf is the least set-level upper bound of the chain. -/
theorem observableLimit_subset_of_upperBound (c : ForwardChain F ι)
    (observe : σ → Set α) (hobserve : F.Respects observe) {S : Set α}
    (hS : ∀ i, observe (c.stage i) ⊆ S) :
    c.observableLimit observe ⊆ S := by
  rw [c.observableLimit_eq_iUnion observe hobserve]
  exact Set.iUnion_subset hS

/-- A prescribed pointwise stable observable is the observable limit. -/
theorem observableLimit_eq_of_eventuallyPointwiseStable
    (c : ForwardChain F ι) (observe : σ → Set α) {S : Set α}
    (h : EventuallyPointwiseStable atTop (fun i ↦ observe (c.stage i)) S) :
    c.observableLimit observe = S :=
  setLiminf_eq_of_eventuallyPointwiseStable h

end Directed

end ForwardChain

end WarpLimits
end Erdos599

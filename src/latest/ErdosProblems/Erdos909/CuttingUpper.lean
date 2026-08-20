/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.SmallInductiveDimension

/-!
# The cutting-tree upper bound in the Anderson--Keisler construction

This file isolates the part of the proof of Erdős Problem 909 which only uses
the recursive definition of small inductive dimension.

A set `R` in a space `X` is an obstruction of order `n` if every subspace
disjoint from `R` has small inductive dimension strictly less than `n`.
The main theorem `isSmallInductiveDimensionObstruction_iUnion_frontier`
says that, given a topological basis, obstructions of order `n` in all basis
frontiers combine to an obstruction of order `n + 1` in `X`.

Iterating this theorem is precisely the induction back up the sphere-cutting
tree of Anderson and Keisler.  At the leaves the obstruction is the whole
terminal sphere; avoiding all terminal spheres makes the leaf intersections
empty.  Each cut supplies a basis on its parent sphere, and the final rational
sphere family supplies a basis of the Euclidean ambient space.
-/

open Set Topology TopologicalSpace

namespace Erdos909.CuttingUpper

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The strict small-inductive-dimension bound pulls back along an inducing
map.  Kept local to this standalone file so that the main Erdős file can
import the cutting argument without an import cycle. -/
theorem inducing_hasSmallInductiveDimensionLT {f : X → Y} (hf : IsInducing f)
    {n : ℕ} (h : HasSmallInductiveDimensionLT Y n) :
    HasSmallInductiveDimensionLT X n := by
  induction h generalizing X with
  | zero =>
      have := Function.isEmpty f
      exact HasSmallInductiveDimensionLT.zero
  | succ n s hs h ih =>
      refine .succ n _ (hs.isInducing hf) ?_
      rintro _ ⟨U, hU, rfl⟩
      apply ih U hU
      apply (hf.restrictPreimage (frontier U)).comp
      exact (IsEmbedding.inclusion (hf.continuous.frontier_preimage_subset U)).isInducing

/-- The two ways of presenting the intersection of subspaces `s` and `t`
are canonically homeomorphic. -/
def interSwapHomeomorph (s t : Set X) :
    (Subtype.val ⁻¹' t : Set s) ≃ₜ (Subtype.val ⁻¹' s : Set t) where
  toEquiv :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A subset of `X` whose avoidance forces a strict small-inductive-dimension
bound.  In the Anderson--Keisler application `R` is a union of terminal
spheres. -/
def IsSmallInductiveDimensionObstruction (R : Set X) (n : ℕ) : Prop :=
  ∀ T : Set X, Disjoint T R → HasSmallInductiveDimensionLT T n

/-- The whole space is the order-zero obstruction: a subspace avoiding it is
empty. -/
theorem isSmallInductiveDimensionObstruction_univ :
    IsSmallInductiveDimensionObstruction (Set.univ : Set X) 0 := by
  intro T hT
  have hTempty : T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact Set.disjoint_left.1 hT hx (Set.mem_univ x)
  subst T
  exact HasSmallInductiveDimensionLT.zero

/-- Enlarging an obstruction preserves its obstruction property. -/
theorem IsSmallInductiveDimensionObstruction.mono
    {R R' : Set X} {n : ℕ} (hR : IsSmallInductiveDimensionObstruction R n)
    (hsub : R ⊆ R') : IsSmallInductiveDimensionObstruction R' n := by
  intro T hT
  exact hR T (hT.mono_right hsub)

/-- General cutting-tree induction step, allowing a basis frontier to be only
contained in the designated cut carrier.

For every `U ∈ b`, `C U hU` is the carrier of the chosen cut and
`R U hU` is an obstruction in the relative space `C U hU`.  The images of
all these relative obstructions form the next obstruction in `X`.

This containment form is the interface used by geometric cutting systems:
one only needs to show that the relative frontier of a chosen complementary
domain is contained in the corresponding cut sphere. -/
theorem isSmallInductiveDimensionObstruction_iUnion_cut
    (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (C : ∀ (U : Set X), U ∈ b → Set X)
    (hfrontier : ∀ (U : Set X) (hU : U ∈ b), frontier U ⊆ C U hU)
    (R : ∀ (U : Set X) (hU : U ∈ b), Set (C U hU))
    (hR : ∀ (U : Set X) (hU : U ∈ b),
      IsSmallInductiveDimensionObstruction (R U hU) n) :
    IsSmallInductiveDimensionObstruction
      (⋃ (U : Set X), ⋃ (hU : U ∈ b),
        Subtype.val '' R U hU) (n + 1) := by
  intro T hT
  refine .succ n _ (hb.isInducing IsInducing.subtypeVal) ?_
  rintro _ ⟨U, hU, rfl⟩
  let TC : Set (C U hU) := Subtype.val ⁻¹' T
  have hdis : Disjoint TC (R U hU) := by
    rw [Set.disjoint_left]
    intro x hxT hxR
    apply Set.disjoint_left.1 hT hxT
    exact Set.mem_iUnion_of_mem U <|
      Set.mem_iUnion_of_mem hU ⟨x, hxR, rfl⟩
  have hdimTC : HasSmallInductiveDimensionLT TC n := hR U hU TC hdis
  have hdimPreimage :
      HasSmallInductiveDimensionLT (Subtype.val ⁻¹' C U hU : Set T) n :=
    inducing_hasSmallInductiveDimensionLT
      (interSwapHomeomorph T (C U hU)).isInducing hdimTC
  apply inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion _).isInducing hdimPreimage
  exact (continuous_subtype_val.frontier_preimage_subset U).trans <|
    preimage_mono (hfrontier U hU)

/-- The cutting-tree induction step.

For each member `U` of a basis `b`, let `R U hU` be an order-`n`
obstruction in the relative space `frontier U`.  Their images in `X`, unioned
over the basis, form an order-`n+1` obstruction in `X`.

No separation, metrizability, or Euclidean hypothesis is used here.  Those
hypotheses enter only when constructing the sphere bases and arranging the
terminal spheres in general position. -/
theorem isSmallInductiveDimensionObstruction_iUnion_frontier
    (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (R : ∀ (U : Set X), U ∈ b → Set (frontier U))
    (hR : ∀ (U : Set X) (hU : U ∈ b),
      IsSmallInductiveDimensionObstruction (R U hU) n) :
    IsSmallInductiveDimensionObstruction
      (⋃ (U : Set X), ⋃ (hU : U ∈ b),
        Subtype.val '' R U hU) (n + 1) := by
  intro T hT
  refine .succ n _ (hb.isInducing IsInducing.subtypeVal) ?_
  rintro _ ⟨U, hU, rfl⟩
  let TU : Set (frontier U) := Subtype.val ⁻¹' T
  have hdis : Disjoint TU (R U hU) := by
    rw [Set.disjoint_left]
    intro x hxT hxR
    apply Set.disjoint_left.1 hT hxT
    exact Set.mem_iUnion_of_mem U <|
      Set.mem_iUnion_of_mem hU ⟨x, hxR, rfl⟩
  have hdimTU : HasSmallInductiveDimensionLT TU n := hR U hU TU hdis
  have hdimPreimage :
      HasSmallInductiveDimensionLT (Subtype.val ⁻¹' frontier U : Set T) n :=
    inducing_hasSmallInductiveDimensionLT
      (interSwapHomeomorph T (frontier U)).isInducing hdimTU
  exact inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion
      (continuous_subtype_val.frontier_preimage_subset U)).isInducing
    hdimPreimage

/-- A convenient one-level specialization: if every basis frontier itself is
an order-`n` obstruction in its relative topology, their union is an
order-`n+1` obstruction. -/
theorem isSmallInductiveDimensionObstruction_iUnion_frontier_univ
    (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (hfrontier : ∀ U ∈ b,
      IsSmallInductiveDimensionObstruction
        (Set.univ : Set (frontier U)) n) :
    IsSmallInductiveDimensionObstruction
      (⋃ (U : Set X), ⋃ (_ : U ∈ b), frontier U) (n + 1) := by
  let R : ∀ (U : Set X), U ∈ b → Set (frontier U) :=
    fun _ _ => Set.univ
  have h := isSmallInductiveDimensionObstruction_iUnion_frontier n b hb R
    (fun U hU => hfrontier U hU)
  simpa only [R, Set.image_univ, Subtype.range_coe_subtype,
    Set.ofPred_mem_eq] using h

/-- Avoiding an obstruction gives the corresponding non-strict numerical
bound on small inductive dimension. -/
theorem smallInductiveDimension_le_of_disjoint_obstruction
    {R T : Set X} {n : ℕ}
    (hR : IsSmallInductiveDimensionObstruction R (n + 1))
    (hT : Disjoint T R) : smallInductiveDimension T ≤ n :=
  smallInductiveDimension_le_iff.2 (hR T hT)

universe u

/-- A countably indexed presentation of an obstruction.  The carriers are
the terminal cuts; keeping their index type explicit makes the countability
argument needed by the transfinite construction reusable. -/
structure CountableObstructionFamily (X : Type u) [TopologicalSpace X]
    (n : ℕ) where
  index : Type u
  index_countable : Countable index
  carrier : index → Set X
  forces : IsSmallInductiveDimensionObstruction (⋃ i, carrier i) n

/-- The one-member terminal family in a space: avoiding its sole carrier,
the whole space, forces dimension strictly below zero. -/
def CountableObstructionFamily.terminal (X : Type*) [TopologicalSpace X] :
    CountableObstructionFamily X 0 where
  index := PUnit
  index_countable := inferInstance
  carrier := fun _ => Set.univ
  forces := by
    simpa only [iUnion_const] using
      (isSmallInductiveDimensionObstruction_univ (X := X))

/-- Combine countable obstruction families on all cuts of a countable basis.

The resulting terminal index is the dependent sum of a basis member and a
terminal index below that member.  Thus finite iteration retains a countable
family of terminal spheres, rather than merely retaining their union. -/
noncomputable def CountableObstructionFamily.cut
    (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (hb_countable : b.Countable)
    (C : ∀ (U : Set X), U ∈ b → Set X)
    (hfrontier : ∀ (U : Set X) (hU : U ∈ b), frontier U ⊆ C U hU)
    (next : ∀ U : b, CountableObstructionFamily (C U.1 U.2) n) :
    CountableObstructionFamily X (n + 1) := by
  let I : Type _ := Σ U : b, (next U).index
  let _ : Countable b := hb_countable.to_subtype
  let _ : ∀ U : b, Countable (next U).index := fun U =>
    (next U).index_countable
  let hI : Countable I := inferInstance
  let S : I → Set X := fun i =>
    Subtype.val '' (next i.1).carrier i.2
  refine
    { index := I
      index_countable := hI
      carrier := S
      forces := ?_ }
  let R : ∀ (U : Set X) (hU : U ∈ b), Set (C U hU) :=
    fun U hU => ⋃ i, (next ⟨U, hU⟩).carrier i
  have hR : ∀ (U : Set X) (hU : U ∈ b),
      IsSmallInductiveDimensionObstruction (R U hU) n := by
    intro U hU
    exact (next ⟨U, hU⟩).forces
  have h := isSmallInductiveDimensionObstruction_iUnion_cut
    n b hb C hfrontier R hR
  convert h using 1
  ext x
  simp only [S, R, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, y, hy, rfl⟩
    exact ⟨i.1.1, i.1.2, y, ⟨i.2, hy⟩, rfl⟩
  · rintro ⟨U, hU, y, ⟨i, hi⟩, rfl⟩
    exact ⟨⟨⟨U, hU⟩, i⟩, y, hi, rfl⟩

section CountableMetricBallBasis

variable {Z : Type*} [PseudoMetricSpace Z]

/-- Indices for the standard countable metric basis attached to a countable
dense set of centers. -/
abbrev InvNatBallIndex (D : Set Z) := D × ℕ

/-- The positive radius `1 / (k + 1)` associated to a natural index. -/
noncomputable def invNatRadius (k : ℕ) : ℝ := 1 / (k + 1 : ℝ)

theorem invNatRadius_pos (k : ℕ) : 0 < invNatRadius k := by
  exact one_div_pos.mpr (by positivity)

/-- A ball centered in `D` with inverse-natural radius. -/
noncomputable def invNatBall (D : Set Z) (i : InvNatBallIndex D) : Set Z :=
  Metric.ball i.1 (invNatRadius i.2)

/-- The sphere bounding `invNatBall D i`. -/
noncomputable def invNatSphere (D : Set Z) (i : InvNatBallIndex D) : Set Z :=
  Metric.sphere i.1 (invNatRadius i.2)

/-- The family of all inverse-natural balls centered in `D`. -/
noncomputable def invNatBallBasis (D : Set Z) : Set (Set Z) :=
  Set.range (invNatBall D)

/-- A dense set of centers gives a topological basis of inverse-natural
balls. -/
theorem isTopologicalBasis_invNatBallBasis {D : Set Z} (hD : Dense D) :
    IsTopologicalBasis (invNatBallBasis D) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨i, rfl⟩
    exact Metric.isOpen_ball
  · intro x U hxU hU
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    have hr : 0 < invNatRadius k := invNatRadius_pos k
    obtain ⟨c, hcball, hcD⟩ :=
      (Metric.dense_iff.1 hD x (invNatRadius k) hr)
    let i : InvNatBallIndex D := (⟨c, hcD⟩, k)
    refine ⟨invNatBall D i, ⟨i, rfl⟩, ?_, ?_⟩
    · simpa [invNatBall, i, Metric.mem_ball, dist_comm] using hcball
    · intro z hz
      apply hεU
      have hzc : dist z c < invNatRadius k := by
        simpa [invNatBall, i, Metric.mem_ball] using hz
      have hcx : dist c x < invNatRadius k := by
        simpa [Metric.mem_ball] using hcball
      calc
        dist z x ≤ dist z c + dist c x := dist_triangle _ _ _
        _ < invNatRadius k + invNatRadius k := add_lt_add hzc hcx
        _ < ε := by
          dsimp [invNatRadius] at hk ⊢
          linarith

/-- If the chosen dense set is countable, the inverse-natural ball basis is
countable. -/
theorem invNatBallBasis_countable {D : Set Z} (hD : D.Countable) :
    (invNatBallBasis D).Countable := by
  let _ : Countable D := hD.to_subtype
  exact Set.countable_range (invNatBall D)

/-- The frontier of every ball in the chosen metric basis is contained in its
designated sphere.  In finite-dimensional real normed spaces this containment
is an equality, but containment is all the cutting-tree theorem needs. -/
theorem frontier_invNatBall_subset_sphere (D : Set Z)
    (i : InvNatBallIndex D) :
    frontier (invNatBall D i) ⊆ invNatSphere D i := by
  exact Metric.frontier_ball_subset_sphere

end CountableMetricBallBasis

section CountableTerminalFamily

variable {ι X₀ : Type*}

/-- A countable family of terminal cuts, each meeting a fixed pattern plane
in a finite set, has countable total intersection with that plane.  This is
the cardinal estimate used at every stage of the Anderson--Keisler recursion. -/
theorem countable_inter_iUnion_of_finite [Countable ι]
    (P : Set X₀) (S : ι → Set X₀) (hfinite : ∀ i, (P ∩ S i).Finite) :
    (P ∩ ⋃ i, S i).Countable := by
  rw [inter_iUnion]
  exact countable_iUnion fun i => (hfinite i).countable

/-- The trace of a countable obstruction family on a set is countable as
soon as every terminal carrier has finite trace. -/
theorem CountableObstructionFamily.countable_inter
    {X₁ : Type u} [TopologicalSpace X₁] {n : ℕ}
    (F : CountableObstructionFamily X₁ n) (P : Set X₁)
    (hfinite : ∀ i, (P ∩ F.carrier i).Finite) :
    (P ∩ ⋃ i, F.carrier i).Countable := by
  let _ : Countable F.index := F.index_countable
  exact countable_inter_iUnion_of_finite P F.carrier hfinite

/-- Avoidance of a union is equivalent to avoidance of every member of the
family. -/
theorem disjoint_iUnion_right_iff (T : Set X₀) (S : ι → Set X₀) :
    Disjoint T (⋃ i, S i) ↔ ∀ i, Disjoint T (S i) := by
  simp only [Set.disjoint_left, Set.mem_iUnion]
  aesop

end CountableTerminalFamily

end Erdos909.CuttingUpper

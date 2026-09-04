/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4VolumeIteration
import ErdosProblems.Erdos186.CFP.Bilu.Section5EpsilonInduction
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bilu Sections 9.2--9.3: kernel and affine-span reductions

Section 9.2 detects failure of injectivity by a nonzero difference in the
kernel and projects along such a difference.  Iterating the projection is
legitimate because the ambient rank is a natural number.  Section 9.3 then
translates the finite preimage set into the direction of its affine span;
this loses neither points nor pair sums and replaces the ambient rank by
the affine dimension.

This file proves those algebraic and termination steps independently of
the analytic volume estimate for the projected convex body.
-/

namespace Erdos186.CFP.Bilu.Section9KernelAffineReduction

open Set Module Submodule
open scoped Pointwise

section Kernel

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  [DecidableEq G] [DecidableEq H]

/-- Injectivity of an additive map on a finite set is exactly the absence
of a nonzero kernel vector in its difference set.  This is the algebraic
test used in Bilu Section 9.2 before quotienting by a primitive direction.
-/
theorem injOn_iff_sub_ker_eq_zero (f : G →+ H) (S : Finset G) :
    Set.InjOn f S ↔
      ∀ z ∈ S - S, f z = 0 → z = 0 := by
  constructor
  · intro hinj z hz hfz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    have hxy : f x = f y := by
      rw [map_sub, sub_eq_zero] at hfz
      exact hfz
    exact sub_eq_zero.mpr (hinj hx hy hxy)
  · intro hker x hx y hy hxy
    apply sub_eq_zero.mp
    apply hker (x - y)
    · exact Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩
    · rw [map_sub, hxy, sub_self]

/-- Failure of enlarged-body injectivity supplies the literal short
nonzero kernel difference along which Section 9.2 projects. -/
theorem exists_nonzero_mem_sub_ker_of_not_injOn
    (f : G →+ H) (S : Finset G)
    (h : ¬ Set.InjOn f S) :
    ∃ z ∈ S - S, z ≠ 0 ∧ f z = 0 := by
  rw [injOn_iff_sub_ker_eq_zero] at h
  push Not at h
  obtain ⟨z, hz, hfz, hz0⟩ := h
  exact ⟨z, hz, hz0, hfz⟩

end Kernel

/-! ## The concrete one-dimensional kernel quotient -/

section LinearKernelQuotient

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- The literal quotient direction selected when a linear realization is
not injective on its enlarged finite test set. -/
structure KernelQuotientStep (f : V →ₗ[ℝ] W) (S : Finset V) where
  collision : V
  collision_mem : collision ∈ S - S
  collision_ne_zero : collision ≠ 0
  collision_mem_ker : f collision = 0

namespace KernelQuotientStep

variable {f : V →ₗ[ℝ] W} {S : Finset V} (Q : KernelQuotientStep f S)

/-- Projection along the selected one-dimensional kernel direction. -/
def quotientMap : V →ₗ[ℝ] (V ⧸ (ℝ ∙ Q.collision)) :=
  (ℝ ∙ Q.collision).mkQ

/-- Since the collision direction lies in the kernel, the original map
factors through the quotient. -/
def factoredMap : (V ⧸ (ℝ ∙ Q.collision)) →ₗ[ℝ] W :=
  Submodule.liftQSpanSingleton Q.collision f Q.collision_mem_ker

@[simp]
theorem factoredMap_quotientMap (x : V) :
    Q.factoredMap (Q.quotientMap x) = f x := rfl

/-- Quotienting by the nonzero collision direction strictly lowers the
ambient dimension. -/
theorem finrank_quotient_lt :
    finrank ℝ (V ⧸ (ℝ ∙ Q.collision)) < finrank ℝ V := by
  have hdim := (ℝ ∙ Q.collision).finrank_quotient_add_finrank
  rw [finrank_span_singleton Q.collision_ne_zero] at hdim
  omega

/-- The finite image represented by the realization is unchanged after
the quotient and factorization. -/
theorem image_factoredMap_image_quotientMap :
    Q.factoredMap '' (Q.quotientMap '' (S : Set V)) = f '' (S : Set V) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, Q.factoredMap_quotientMap x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Q.quotientMap x, ⟨x, hx, rfl⟩, Q.factoredMap_quotientMap x⟩

end KernelQuotientStep

/-- A failed injectivity test constructs the concrete lower-dimensional
quotient through which the realization factors. -/
theorem exists_kernelQuotientStep_of_not_injOn
    (f : V →ₗ[ℝ] W) (S : Finset V)
    (h : ¬ Set.InjOn f S) :
    Nonempty (KernelQuotientStep f S) := by
  simp only [Set.InjOn] at h
  push Not at h
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := h
  refine ⟨⟨x - y, Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩, ?_, ?_⟩⟩
  · exact sub_ne_zero.mpr hne
  · rw [map_sub, hxy, sub_self]

end LinearKernelQuotient

/-! ## Minimal-rank termination -/

/-- A heterogeneous family of presentations, indexed by its ambient rank.
The payload may contain a body, lattice map, finite lifts, and all the
analytic admissibility data. -/
abbrev Ranked (P : ℕ → Type*) := Σ n, P n

/-- A presentation has minimal rank in a given class. -/
def IsRankMinimal {P : ℕ → Type*}
    (admissible : Ranked P → Prop) (x : Ranked P) : Prop :=
  admissible x ∧ ∀ y, admissible y → x.1 ≤ y.1

/-- Every nonempty class of rank-indexed presentations has a member of
minimal rank.  This is the well-founded choice made in Section 9.2. -/
theorem exists_rankMinimal {P : ℕ → Type*}
    (admissible : Ranked P → Prop)
    (hne : ∃ x, admissible x) :
    ∃ x, IsRankMinimal admissible x := by
  let ranks : Set ℕ := {n | ∃ x : P n, admissible ⟨n, x⟩}
  have hranks : ranks.Nonempty := by
    obtain ⟨⟨n, x⟩, hx⟩ := hne
    exact ⟨n, x, hx⟩
  let n := sInf ranks
  have hn : n ∈ ranks := Nat.sInf_mem hranks
  obtain ⟨x, hx⟩ := hn
  refine ⟨⟨n, x⟩, hx, ?_⟩
  intro y hy
  exact Nat.sInf_le ⟨y.2, hy⟩

/-- If every bad presentation can be repaired in strictly smaller rank,
a minimal-rank presentation is good.  The theorem performs the Section
9.2 descent rather than assuming injectivity of the selected object. -/
theorem exists_good_of_rank_reduction {P : ℕ → Type*}
    (admissible good : Ranked P → Prop)
    (hne : ∃ x, admissible x)
    (reduce : ∀ x, admissible x → ¬ good x →
      ∃ y, admissible y ∧ y.1 < x.1) :
    ∃ x, admissible x ∧ good x := by
  obtain ⟨x, hx, hxmin⟩ := exists_rankMinimal admissible hne
  refine ⟨x, hx, ?_⟩
  by_contra hbad
  obtain ⟨y, hy, hyrank⟩ := reduce x hx hbad
  exact (not_lt_of_ge (hxmin y hy)) hyrank

/-! ## Restriction to the affine span -/

section AffineSpan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- The direction of the affine span of a finite set. -/
def affineDirection (S : Finset V) : Submodule ℝ V :=
  (affineSpan ℝ (S : Set V)).direction

/-- Translate a member of `S` by a fixed base point into the direction of
the affine span. -/
def toAffineDirection (S : Finset V) (a : V) (ha : a ∈ S)
    (x : {x // x ∈ S}) : affineDirection S :=
  ⟨(x : V) - a, by
    change (x : V) -ᵥ a ∈ (affineSpan ℝ (S : Set V)).direction
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ (S : Set V) x.property)
      (subset_affineSpan ℝ (S : Set V) ha)⟩

/-- The finite set after translation into its intrinsic affine direction.
-/
def affineRestriction (S : Finset V) (a : V) (ha : a ∈ S) :
    Finset (affineDirection S) :=
  S.attach.image (toAffineDirection S a ha)

@[simp]
theorem coe_toAffineDirection (S : Finset V) (a : V) (ha : a ∈ S)
    (x : {x // x ∈ S}) :
    (toAffineDirection S a ha x : V) = (x : V) - a := rfl

/-- Translation into the affine direction is injective. -/
theorem toAffineDirection_injective (S : Finset V) (a : V) (ha : a ∈ S) :
    Function.Injective (toAffineDirection S a ha) := by
  intro x y hxy
  apply Subtype.ext
  have hxy' := congrArg ((↑) : affineDirection S → V) hxy
  exact sub_left_inj.mp hxy'

/-- Affine-span restriction loses no points. -/
@[simp]
theorem card_affineRestriction (S : Finset V) (a : V) (ha : a ∈ S) :
    (affineRestriction S a ha).card = S.card := by
  rw [affineRestriction, Finset.card_image_of_injective _
    (toAffineDirection_injective S a ha)]
  exact Finset.card_attach

/-- Pair sums are translated by the fixed vector `2a`, so equality of pair
sums is reflected exactly by affine-span restriction. -/
theorem add_toAffineDirection_eq_iff
    (S : Finset V) (a : V) (ha : a ∈ S)
    (x y u v : {x // x ∈ S}) :
    toAffineDirection S a ha x + toAffineDirection S a ha y =
        toAffineDirection S a ha u + toAffineDirection S a ha v ↔
      (x : V) + y = u + v := by
  rw [Subtype.ext_iff]
  simp only [Submodule.coe_add, coe_toAffineDirection]
  constructor
  · intro h
    calc
      (x : V) + y = ((x : V) - a + (y - a)) + (a + a) := by abel
      _ = ((u : V) - a + (v - a)) + (a + a) := by rw [h]
      _ = (u : V) + v := by abel
  · intro h
    calc
      (x : V) - a + (y - a) = ((x : V) + y) - (a + a) := by abel
      _ = ((u : V) + v) - (a + a) := by rw [h]
      _ = (u : V) - a + (v - a) := by abel

/-- The restriction map induces a bijection between the original pair
sumset and the intrinsic pair sumset. -/
theorem card_pairSumset_affineRestriction
    (S : Finset V) (a : V) (ha : a ∈ S) :
    (Section7FreimanMap.pairSumset (affineRestriction S a ha)).card =
      (Section7FreimanMap.pairSumset S).card := by
  classical
  let f := toAffineDirection S a ha
  let pairs := S.attach.product S.attach
  let sourceAdd : ({x // x ∈ S} × {x // x ∈ S}) → V :=
    fun p ↦ (p.1 : V) + p.2
  let targetAdd : ({x // x ∈ S} × {x // x ∈ S}) →
      affineDirection S := fun p ↦ f p.1 + f p.2
  let : Inhabited {x // x ∈ S} := ⟨⟨a, ha⟩⟩
  have hsource :
      Section7FreimanMap.pairSumset S = pairs.image sourceAdd := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ :=
        (Section7FreimanMap.mem_pairSumset S z).mp hz
      apply Finset.mem_image.mpr
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩),
        Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩,
        rfl⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact (Section7FreimanMap.mem_pairSumset _ _).mpr
        ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩
  have htarget :
      Section7FreimanMap.pairSumset (affineRestriction S a ha) =
        pairs.image targetAdd := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ :=
        (Section7FreimanMap.mem_pairSumset _ _).mp hz
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      exact ⟨(x', y'), Finset.mem_product.mpr ⟨hx', hy'⟩, rfl⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      have hp' := Finset.mem_product.mp hp
      exact (Section7FreimanMap.mem_pairSumset _ _).mpr
        ⟨f p.1, Finset.mem_image.mpr ⟨p.1, hp'.1, rfl⟩,
        f p.2, Finset.mem_image.mpr ⟨p.2, hp'.2, rfl⟩, rfl⟩
  rw [hsource, htarget]
  symm
  apply Section7FreimanMap.card_image_eq_card_image_of_eq_iff
  intro x _hx y _hy
  change ((x.1 : V) + x.2 = (y.1 : V) + y.2) ↔
    f x.1 + f x.2 = f y.1 + f y.2
  exact (add_toAffineDirection_eq_iff S a ha x.1 x.2 y.1 y.2).symm

/-- The intrinsic ambient rank is exactly the affine dimension of `S`. -/
@[simp]
theorem finrank_affineDirection (S : Finset V) :
    finrank ℝ (affineDirection S) =
      finrank ℝ (affineSpan ℝ (S : Set V)).direction := rfl

/-- Source-facing existential form: every nonempty finite set has a
cardinality- and doubling-preserving realization in a vector space whose
rank is its affine dimension. -/
theorem exists_affineRestriction (S : Finset V) (hS : S.Nonempty) :
    ∃ a, ∃ ha : a ∈ S,
      (affineRestriction S a ha).card = S.card ∧
      (Section7FreimanMap.pairSumset
          (affineRestriction S a ha)).card =
        (Section7FreimanMap.pairSumset S).card := by
  obtain ⟨a, ha⟩ := hS
  exact ⟨a, ha, card_affineRestriction S a ha,
    card_pairSumset_affineRestriction S a ha⟩

end AffineSpan

end Erdos186.CFP.Bilu.Section9KernelAffineReduction

#print axioms Erdos186.CFP.Bilu.Section9KernelAffineReduction.injOn_iff_sub_ker_eq_zero
#print axioms Erdos186.CFP.Bilu.Section9KernelAffineReduction.exists_kernelQuotientStep_of_not_injOn
#print axioms Erdos186.CFP.Bilu.Section9KernelAffineReduction.exists_good_of_rank_reduction
#print axioms Erdos186.CFP.Bilu.Section9KernelAffineReduction.card_pairSumset_affineRestriction
#print axioms Erdos186.CFP.Bilu.Section9KernelAffineReduction.exists_affineRestriction

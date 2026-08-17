/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic
import ErdosProblems.Erdos171.Density
import ErdosProblems.Erdos171.SubspaceOps

/-!
# Density inside combinatorial subspaces

This file connects the combinatorial `Subspace` API with the uniform-density
API used in the density Hales--Jewett argument.  Pullback density is the density
of the parameter words whose images belong to the ambient family.  Since every
proper subspace is injective in its parameter word, this is exactly relative
density inside the image of the subspace.

The second half gives two exact counting identities used repeatedly later:

* averaging the pullback densities of all fixed-suffix extensions is the
  pullback density on the corresponding sum-coordinate subspace;
* the fraction of internal lines contained in a family is both a finite
  density and the average of the corresponding containment indicator.
-/

open scoped BigOperators

namespace Erdos171

open Set

attribute [local instance 1] Classical.dec

variable {η ζ α ι κ : Type*}

/-! ## Pullback and relative density -/

/-- Pull an ambient finset back to the parameter cube of a subspace. -/
noncomputable def pullbackFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) (x : η → α) :
    x ∈ pullbackFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackFinset]

/-- Pull an ambient set back to the parameter cube, represented as a finset. -/
noncomputable def pullbackSetFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackSetFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) (x : η → α) :
    x ∈ pullbackSetFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackSetFinset]

@[simp] theorem pullback_setFinset [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    pullbackFinset U (setFinset A) = pullbackSetFinset U A := by
  classical
  ext x
  simp

/-- Density of an ambient finset when viewed in the coordinates of a subspace. -/
noncomputable def subspaceDensityFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  density (pullbackFinset U A)

/-- Density of an ambient set when viewed in the coordinates of a subspace. -/
noncomputable def subspaceDensity [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) : ℝ :=
  density (pullbackSetFinset U A)

@[simp] theorem subspaceDensity_setFinset [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    subspaceDensityFinset U (setFinset A) = subspaceDensity U A := by
  rw [subspaceDensityFinset, subspaceDensity, pullback_setFinset]

/-- The finite image of a subspace. -/
noncomputable def subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) : Finset (ι → α) := by
  classical
  exact Finset.univ.image U

@[simp] theorem mem_subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (y : ι → α) :
    y ∈ subspaceImageFinset U ↔ y ∈ Set.range U := by
  classical
  simp [subspaceImageFinset]

theorem card_subspaceImageFinset [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) :
    (subspaceImageFinset U).card = Fintype.card (η → α) := by
  classical
  simp [subspaceImageFinset, Finset.card_image_of_injective _ U.parameter_injective]

/-- Relative density of `A` inside the finite reference family `S`. -/
noncomputable def relativeDensityFinset {γ : Type*} [DecidableEq γ]
    (A S : Finset γ) : ℝ :=
  ((A ∩ S).card : ℝ) / S.card

/-- Relative density of `A` inside `S`, for sets in a finite ambient type. -/
noncomputable def relativeDensity [Fintype α] [DecidableEq α]
    (A S : Set α) : ℝ :=
  relativeDensityFinset (setFinset A) (setFinset S)

theorem card_pullback_eq_inter_image [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    (pullbackFinset U A).card = (A ∩ subspaceImageFinset U).card := by
  classical
  refine Finset.card_bij (fun x _ ↦ U x) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_inter.2 ⟨(mem_pullbackFinset U A x).1 hx,
      (mem_subspaceImageFinset U (U x)).2 ⟨x, rfl⟩⟩
  · intro x hx y hy hxy
    exact U.parameter_injective hxy
  · intro y hy
    obtain ⟨hyA, hyU⟩ := Finset.mem_inter.1 hy
    obtain ⟨x, rfl⟩ := (mem_subspaceImageFinset U y).1 hyU
    exact ⟨x, (mem_pullbackFinset U A x).2 hyA, rfl⟩

/-- Pullback density is relative density inside the subspace image. -/
theorem subspaceDensityFinset_eq_relative [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    subspaceDensityFinset U A = relativeDensityFinset A (subspaceImageFinset U) := by
  rw [subspaceDensityFinset, density_eq_card_div_card, relativeDensityFinset,
    card_pullback_eq_inter_image, card_subspaceImageFinset]

theorem setFinset_range_subspace [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) :
    setFinset (Set.range U) = subspaceImageFinset U := by
  classical
  ext y
  simp

/-- Set-valued form of pullback density as relative density in the image. -/
theorem subspaceDensity_eq_relative [Fintype (η → α)] [Fintype (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A : Set (ι → α)) :
    subspaceDensity U A = relativeDensity A (Set.range U) := by
  rw [← subspaceDensity_setFinset, subspaceDensityFinset_eq_relative,
    relativeDensity, setFinset_range_subspace]

@[simp] theorem pullbackFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    pullbackFinset (U.comp V) A = pullbackFinset V (pullbackFinset U A) := by
  classical
  ext x
  simp [Combinatorics.Subspace.comp_apply]

@[simp] theorem pullbackSetFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Set (ι → α)) :
    pullbackSetFinset (U.comp V) A = pullbackSetFinset V (U ⁻¹' A) := by
  classical
  ext x
  simp [Combinatorics.Subspace.comp_apply]

@[simp] theorem subspaceDensityFinset_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    subspaceDensityFinset (U.comp V) A =
      subspaceDensityFinset V (pullbackFinset U A) := by
  simp [subspaceDensityFinset]

@[simp] theorem subspaceDensity_comp [Fintype (η → α)] [Fintype (ζ → α)]
    (U : Combinatorics.Subspace η α ι) (V : Combinatorics.Subspace ζ α η)
    (A : Set (ι → α)) :
    subspaceDensity (U.comp V) A = subspaceDensity V (U ⁻¹' A) := by
  simp [subspaceDensity]

/-! ## Exact average over fixed-suffix extensions -/

end Erdos171

namespace Combinatorics

namespace Subspace

/-- The identity combinatorial subspace. -/
def coordinateIdentity (α η : Type*) : Subspace η α η where
  idxFun := Sum.inr
  proper e := ⟨e, rfl⟩

@[simp] theorem coordinateIdentity_apply (x : η → α) :
    coordinateIdentity α η x = x := by
  funext e
  rfl

end Subspace

end Combinatorics

namespace Erdos171

open Set

attribute [local instance 1] Classical.dec

variable {η ζ α ι κ : Type*}

/-- The set of pairs `(suffix, parameter)` whose extended word lies in `A`. -/
noncomputable def extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    Finset ((κ → α) × (η → α)) := by
  classical
  exact Finset.univ.filter fun p ↦
    Combinatorics.Subspace.sumWord (U p.2) p.1 ∈ A

@[simp] theorem mem_extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (p : (κ → α) × (η → α)) :
    p ∈ extensionPullback U A ↔
      Combinatorics.Subspace.sumWord (U p.2) p.1 ∈ A := by
  classical
  simp [extensionPullback]

theorem fiber_extensionPullback [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (y : κ → α) :
    fiber (extensionPullback U A) y = pullbackFinset (U.extendRightWord y) A := by
  classical
  ext x
  simp [Combinatorics.Subspace.extendRightWord_apply]

/-- Fubini's identity for all fixed-suffix extensions of a subspace. -/
theorem density_extensionPullback_eq_average
    [Fintype (η → α)] [Fintype (κ → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    density (extensionPullback U A) =
      average fun y : κ → α ↦ subspaceDensityFinset (U.extendRightWord y) A := by
  rw [density_eq_average_fiber]
  apply congrArg average
  funext y
  rw [fiber_extensionPullback]
  rfl

/-- Rebracket a pair `(suffix, parameter)` as a word on a sum of coordinate
types. -/
def extensionWordEquiv : ((κ → α) × (η → α)) ≃ (η ⊕ κ → α) where
  toFun p := Combinatorics.Subspace.sumWord p.2 p.1
  invFun z := (z ∘ Sum.inr, z ∘ Sum.inl)
  left_inv p := by
    ext q
    · rfl
    · rfl
  right_inv z := by
    funext q
    cases q <;> rfl

theorem extensionWord_mem_sumPullback
    [Fintype (η ⊕ κ → α)] [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α))
    (p : (κ → α) × (η → α)) :
    extensionWordEquiv p ∈
        pullbackFinset (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A ↔
      p ∈ extensionPullback U A := by
  classical
  simp [extensionWordEquiv, Combinatorics.Subspace.sum_apply_sumWord]

theorem card_extensionPullback_eq_sumPullback
    [Fintype (η ⊕ κ → α)] [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    (extensionPullback U A).card =
      (pullbackFinset
        (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A).card := by
  classical
  refine Finset.card_bij (fun p _ ↦ extensionWordEquiv p) ?_ ?_ ?_
  · intro p hp
    exact (extensionWord_mem_sumPullback U A p).2 hp
  · intro p hp q hq hpq
    exact extensionWordEquiv.injective hpq
  · intro z hz
    refine ⟨extensionWordEquiv.symm z, ?_, extensionWordEquiv.apply_symm_apply z⟩
    apply (extensionWord_mem_sumPullback U A (extensionWordEquiv.symm z)).1
    rw [extensionWordEquiv.apply_symm_apply]
    exact hz

/-- The pair-model extension pullback and the sum-subspace pullback have the
same density, including their ambient denominators. -/
theorem density_extensionPullback_eq_sumSubspaceDensity
    [Fintype (η ⊕ κ → α)] [Fintype (κ → α)] [Fintype (η → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    density (extensionPullback U A) =
      subspaceDensityFinset
        (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A := by
  unfold subspaceDensityFinset density
  rw [card_extensionPullback_eq_sumPullback]
  congr 1
  norm_cast
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact Nat.card_congr
    (extensionWordEquiv : ((κ → α) × (η → α)) ≃ (η ⊕ κ → α))

/-- Exact average of the densities on all fixed-suffix extensions. -/
theorem average_subspaceDensity_extendRightWord
    [Fintype (η ⊕ κ → α)] [Fintype (η → α)] [Fintype (κ → α)]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) :
    average (fun y : κ → α ↦ subspaceDensityFinset (U.extendRightWord y) A) =
      subspaceDensityFinset
        (U.sum (Combinatorics.Subspace.coordinateIdentity α κ)) A := by
  rw [← density_extensionPullback_eq_average,
    density_extensionPullback_eq_sumSubspaceDensity]

/-! ## Counting internal lines -/

/-- Internal parameter lines all of whose points map into `A`. -/
noncomputable def internalLines [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (Combinatorics.Line α η) := by
  classical
  exact Finset.univ.filter fun l ↦ ∀ a, U (l a) ∈ A

@[simp] theorem mem_internalLines [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α))
    (l : Combinatorics.Line α η) :
    l ∈ internalLines U A ↔ ∀ a, U (l a) ∈ A := by
  classical
  simp [internalLines]

/-- Fraction of the internal lines of `U` that are contained in `A`. -/
noncomputable def internalLineFraction [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  density (internalLines U A)

theorem internalLineFraction_eq_card [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A =
      ((internalLines U A).card : ℝ) / Fintype.card (Combinatorics.Line α η) := by
  rfl

theorem internalLineFraction_nonneg [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    0 ≤ internalLineFraction U A :=
  density_nonneg _

theorem internalLineFraction_le_one [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A ≤ 1 :=
  density_le_one _

/-- Internal-line fraction as an exact average of containment indicators. -/
theorem internalLineFraction_eq_average_indicator [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A =
      average fun l : Combinatorics.Line α η ↦
        if ∀ a, U (l a) ∈ A then (1 : ℝ) else 0 := by
  classical
  rw [internalLineFraction, ← average_indicator]
  apply congrArg average
  funext l
  simp

/-- Equivalent product form of the internal-line containment indicator. -/
theorem internalLineFraction_eq_average_prod [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    internalLineFraction U A =
      average fun l : Combinatorics.Line α η ↦
        ∏ a, if U (l a) ∈ A then (1 : ℝ) else 0 := by
  rw [internalLineFraction_eq_average_indicator]
  apply congrArg average
  funext l
  classical
  by_cases h : ∀ a, U (l a) ∈ A
  · simp [h]
  · push Not at h
    obtain ⟨a, ha⟩ := h
    have hn : ¬ ∀ b, U (l b) ∈ A := fun hall ↦ ha (hall a)
    simp only [hn, if_false]
    exact (Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])).symm

end Erdos171

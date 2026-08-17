/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Density
import ErdosProblems.Erdos171.Basic
import ErdosProblems.Erdos171.Insensitive
import ErdosProblems.Erdos171.SubspaceOps

/-!
# Finite tilings by combinatorial subspaces

This file contains the bookkeeping common to the insensitive-set tiling
argument.  A tile is represented by the finite range of a proper Mathlib
`Combinatorics.Subspace`; a tiling is a finite, pairwise-disjoint family of
such ranges.  The density lemmas below are deliberately stated for arbitrary
finite families, so that the final intersection argument can sum a relative
error estimate over all of its large tiles.
-/

open scoped BigOperators

namespace Erdos171

open Combinatorics

@[simp] theorem mem_finsetMap_equiv {A B : Type*} [DecidableEq A]
    [DecidableEq B] (e : A ≃ B) (D : Finset A) (x : B) :
    x ∈ D.map e.toEmbedding ↔ e.symm x ∈ D := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_map.mpr ⟨e.symm x, hx, by simp⟩

section SubspacePoints

variable {eta alpha iota : Type*}

/-- The finite set of points parametrized by a combinatorial subspace. -/
noncomputable def subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota) :
    Finset (iota → alpha) :=
  Finset.univ.image U

@[simp] theorem mem_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (x : iota → alpha) :
    x ∈ subspacePoints U ↔ x ∈ Set.range U := by
  simp [subspacePoints]

@[simp] theorem card_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota) :
    (subspacePoints U).card = Fintype.card (eta → alpha) := by
  rw [subspacePoints, Finset.card_image_of_injective _ U.parameter_injective,
    Finset.card_univ]

@[simp] theorem card_subspacePoints_fin {m q : ℕ}
    [DecidableEq (iota → Fin q)] (U : Subspace (Fin m) (Fin q) iota) :
    (subspacePoints U).card = q ^ m := by
  rw [card_subspacePoints, Fintype.card_fun]
  simp

theorem subspacePoints_nonempty [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [DecidableEq (iota → alpha)]
    (U : Subspace eta alpha iota) : (subspacePoints U).Nonempty := by
  inhabit eta → alpha
  exact ⟨U default, by simp⟩

end SubspacePoints

section Pullback

variable {eta zeta alpha iota : Type*}

/-- Pull a finite set in the ambient cube back to the parameter cube of a
subspace.  Its density is the usual relative density inside that subspace. -/
noncomputable def subspacePullback [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    Finset (eta → alpha) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ D

@[simp] theorem mem_subspacePullback [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha))
    (x : eta → alpha) :
    x ∈ subspacePullback U D ↔ U x ∈ D := by
  classical
  simp [subspacePullback]

theorem image_subspacePullback [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    (subspacePullback U D).image U = subspacePoints U ∩ D := by
  classical
  ext x
  constructor
  · simp only [Finset.mem_image, mem_subspacePullback, Finset.mem_inter,
      mem_subspacePoints]
    rintro ⟨y, hyD, rfl⟩
    exact ⟨⟨y, rfl⟩, hyD⟩
  · simp only [Finset.mem_inter, mem_subspacePoints, Finset.mem_image,
      mem_subspacePullback]
    rintro ⟨⟨y, rfl⟩, hyD⟩
    exact ⟨y, hyD, rfl⟩

theorem card_inter_subspacePoints [Fintype (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    (subspacePoints U ∩ D).card = (subspacePullback U D).card := by
  rw [← image_subspacePullback U D,
    Finset.card_image_of_injective _ U.parameter_injective]

/-- Ambient density factors as the density of the large tile times relative
density in its parameter cube. -/
theorem density_inter_subspacePoints [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [Fintype (iota → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (D : Finset (iota → alpha)) :
    density (subspacePoints U ∩ D) =
      density (subspacePoints U) * density (subspacePullback U D) := by
  simp only [density_eq_card_div_card, card_inter_subspacePoints]
  rw [card_subspacePoints]
  have heta : (Fintype.card (eta → alpha) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Density scaling for an arbitrary finite subset of a subspace's parameter
cube. -/
theorem density_image_subspace [Fintype (eta → alpha)]
    [Nonempty (eta → alpha)] [Fintype (iota → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (B : Finset (eta → alpha)) :
    density (B.image U) = density (subspacePoints U) * density B := by
  simp only [density_eq_card_div_card,
    Finset.card_image_of_injective _ U.parameter_injective, card_subspacePoints]
  have heta : (Fintype.card (eta → alpha) : ℝ) ≠ 0 := by positivity
  field_simp

theorem subspacePoints_comp [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) :
    subspacePoints (U.comp V) = (subspacePoints V).image U := by
  classical
  ext x
  simp only [mem_subspacePoints, Finset.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨V z, ⟨z, rfl⟩, (Subspace.comp_apply U V z).symm⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, Subspace.comp_apply U V z⟩

theorem subspacePoints_comp_subset_iff [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) (D : Finset (iota → alpha)) :
    subspacePoints (U.comp V) ⊆ D ↔
      subspacePoints V ⊆ subspacePullback U D := by
  constructor
  · intro h x hx
    rw [mem_subspacePullback]
    rw [mem_subspacePoints] at hx
    obtain ⟨z, rfl⟩ := hx
    apply h
    rw [mem_subspacePoints]
    exact ⟨z, Subspace.comp_apply U V z⟩
  · intro h x hx
    rw [mem_subspacePoints] at hx
    obtain ⟨z, rfl⟩ := hx
    have hz : U (V z) ∈ D := by
      rw [← mem_subspacePullback]
      apply h
      rw [mem_subspacePoints]
      exact ⟨z, rfl⟩
    simpa only [Subspace.comp_apply] using hz

theorem subspacePoints_comp_subset [Fintype (zeta → alpha)]
    [Fintype (eta → alpha)] [DecidableEq (eta → alpha)]
    [DecidableEq (iota → alpha)] (U : Subspace eta alpha iota)
    (V : Subspace zeta alpha eta) :
    subspacePoints (U.comp V) ⊆ subspacePoints U := by
  rw [subspacePoints_comp]
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  simp

end Pullback

section InsensitivePullback

variable {k m n : ℕ}

/-- Subspaces preserve `(i,last)`-equivalence of parameter words. -/
theorem lastEquivalent_subspace (i : Fin k)
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    {x y : Word (k + 1) m} (hxy : LastEquivalent i x y) :
    LastEquivalent i (U x) (U y) := by
  rw [LastEquivalent] at hxy ⊢
  funext r
  cases hr : U.idxFun r with
  | inl a => simp [replaceLast, Subspace.coe_apply, hr]
  | inr e =>
      simpa [replaceLast, Subspace.coe_apply, hr] using congrFun hxy e

/-- Pulling an insensitive set back through a combinatorial subspace again
gives an insensitive set in the parameter cube. -/
theorem IsLastInsensitive.subspacePullback (i : Fin k)
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Finset (Word (k + 1) n))
    (hD : IsLastInsensitive i (D : Set (Word (k + 1) n))) :
    IsLastInsensitive i (subspacePullback U D : Set (Word (k + 1) m)) := by
  intro x y hxy
  simp only [Finset.mem_coe, mem_subspacePullback]
  exact hD (U x) (U y) (lastEquivalent_subspace i U hxy)

end InsensitivePullback

section Families

variable {eta alpha iota : Type*} [Fintype (eta → alpha)]
  [DecidableEq (iota → alpha)]

/-- A finite pairwise-disjoint family of equal-dimensional combinatorial
subspaces.  Containment in a target set is kept separate, since the same
family is used with several successive remainders in the greedy argument. -/
structure SubspaceTiling (eta alpha iota : Type*)
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)] where
  tiles : Finset (Subspace eta alpha iota)
  pairwiseDisjoint : (tiles : Set (Subspace eta alpha iota)).PairwiseDisjoint
    subspacePoints

namespace SubspaceTiling

variable {zeta : Type*} [Fintype (zeta → alpha)]
  [DecidableEq (eta → alpha)]

/-- The empty tiling. -/
noncomputable def empty : SubspaceTiling eta alpha iota := by
  classical
  exact ⟨∅, by simp⟩

@[simp] theorem tiles_empty : (empty : SubspaceTiling eta alpha iota).tiles = ∅ := rfl

/-- The union of all points in all tiles. -/
noncomputable def covered (T : SubspaceTiling eta alpha iota) :
    Finset (iota → alpha) :=
  T.tiles.biUnion subspacePoints

@[simp] theorem covered_empty : (empty : SubspaceTiling eta alpha iota).covered = ∅ := by
  classical
  simp [covered, empty]

/-- Join two tilings whose covered point sets are disjoint. -/
noncomputable def disjointUnion (T S : SubspaceTiling eta alpha iota)
    (h : Disjoint T.covered S.covered) :
    SubspaceTiling eta alpha iota := by
  classical
  exact
    { tiles := T.tiles ∪ S.tiles
      pairwiseDisjoint := by
        intro U hU V hV hUV
        change U ∈ T.tiles ∪ S.tiles at hU
        change V ∈ T.tiles ∪ S.tiles at hV
        rw [Finset.mem_union] at hU hV
        rcases hU with hUT | hUS <;> rcases hV with hVT | hVS
        · exact T.pairwiseDisjoint hUT hVT hUV
        · exact h.mono
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨U, hUT, hx⟩)
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨V, hVS, hx⟩)
        · exact h.symm.mono
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨U, hUS, hx⟩)
            (fun x hx ↦ Finset.mem_biUnion.mpr ⟨V, hVT, hx⟩)
        · exact S.pairwiseDisjoint hUS hVS hUV }

theorem covered_disjointUnion (T S : SubspaceTiling eta alpha iota)
    (h : Disjoint T.covered S.covered) :
    (T.disjointUnion S h).covered = T.covered ∪ S.covered := by
  classical
  exact Finset.union_biUnion

@[simp] theorem mem_covered (T : SubspaceTiling eta alpha iota)
    (x : iota → alpha) :
    x ∈ T.covered ↔ ∃ U ∈ T.tiles, x ∈ subspacePoints U := by
  classical
  simp [covered]

theorem tile_subset_covered (T : SubspaceTiling eta alpha iota)
    {U : Subspace eta alpha iota} (hU : U ∈ T.tiles) :
    subspacePoints U ⊆ T.covered := by
  classical
  intro x hx
  exact (T.mem_covered x).2 ⟨U, hU, hx⟩

section AmbientReindex

variable {kappa : Type*} [DecidableEq (kappa → alpha)]

/-- The word equivalence induced by reindexing ambient coordinates. -/
def ambientWordEquiv (e : iota ≃ kappa) :
    (iota → alpha) ≃ (kappa → alpha) :=
  e.arrowCongr (Equiv.refl alpha)

theorem ambientWordEquiv_symm (e : iota ≃ kappa) :
    (ambientWordEquiv (alpha := alpha) e).symm = ambientWordEquiv e.symm := by
  ext x j
  rfl

@[simp] theorem mem_map_ambientWordEquiv (e : iota ≃ kappa)
    (D : Finset (iota → alpha)) (x : kappa → alpha) :
    x ∈ D.map (ambientWordEquiv e).toEmbedding ↔
      (ambientWordEquiv e).symm x ∈ D := by
  exact mem_finsetMap_equiv (ambientWordEquiv e) D x

theorem ambientReindex_injective (e : iota ≃ kappa) :
    Function.Injective (fun U : Subspace eta alpha iota ↦
      U.reindex (Equiv.refl eta) (Equiv.refl alpha) e) := by
  intro U V hUV
  apply Subspace.ext
  funext i
  have hi := congrArg
    (fun W : Subspace eta alpha kappa ↦ W.idxFun (e i)) hUV
  simpa [Subspace.reindex] using hi

noncomputable def ambientReindexEmbedding (e : iota ≃ kappa) :
    Subspace eta alpha iota ↪ Subspace eta alpha kappa :=
  ⟨fun U ↦ U.reindex (Equiv.refl eta) (Equiv.refl alpha) e,
    ambientReindex_injective e⟩

theorem subspacePoints_ambientReindex (e : iota ≃ kappa)
    (U : Subspace eta alpha iota) :
    subspacePoints (U.reindex (Equiv.refl eta) (Equiv.refl alpha) e) =
      (subspacePoints U).map (ambientWordEquiv e).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_subspacePoints] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Finset.mem_map.mpr
    refine ⟨U a, by simp, ?_⟩
    funext j
    simp [ambientWordEquiv, Function.comp_def]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [mem_subspacePoints] at hy ⊢
    obtain ⟨a, rfl⟩ := hy
    refine ⟨a, ?_⟩
    funext j
    simp [ambientWordEquiv, Function.comp_def]

/-- Transport every tile through an equivalence of ambient coordinate types. -/
noncomputable def ambientReindex (T : SubspaceTiling eta alpha iota)
    (e : iota ≃ kappa) : SubspaceTiling eta alpha kappa := by
  classical
  exact
    { tiles := T.tiles.map (ambientReindexEmbedding e)
      pairwiseDisjoint := by
        intro U hU V hV hUV
        obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
        obtain ⟨V₀, hV₀, rfl⟩ := Finset.mem_map.mp hV
        have hUV₀ : U₀ ≠ V₀ := fun h ↦
          hUV (congrArg (fun W ↦
            W.reindex (Equiv.refl eta) (Equiv.refl alpha) e) h)
        change Disjoint
          (subspacePoints
            (U₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e))
          (subspacePoints
            (V₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e))
        rw [subspacePoints_ambientReindex, subspacePoints_ambientReindex,
          Finset.disjoint_map]
        exact T.pairwiseDisjoint hU₀ hV₀ hUV₀ }

theorem covered_ambientReindex (T : SubspaceTiling eta alpha iota)
    (e : iota ≃ kappa) :
    (T.ambientReindex e).covered =
      T.covered.map (ambientWordEquiv e).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨U, hU, hxU⟩ := ((T.ambientReindex e).mem_covered x).mp hx
    change U ∈ T.tiles.map (ambientReindexEmbedding e) at hU
    obtain ⟨U₀, hU₀, rfl⟩ := Finset.mem_map.mp hU
    change x ∈ subspacePoints
      (U₀.reindex (Equiv.refl eta) (Equiv.refl alpha) e) at hxU
    rw [subspacePoints_ambientReindex] at hxU
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxU
    exact Finset.mem_map.mpr ⟨y, T.tile_subset_covered hU₀ hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨U, hU, hyU⟩ := (T.mem_covered y).mp hy
    apply ((T.ambientReindex e).mem_covered _).mpr
    refine ⟨U.reindex (Equiv.refl eta) (Equiv.refl alpha) e, ?_, ?_⟩
    · change U.reindex (Equiv.refl eta) (Equiv.refl alpha) e ∈
        T.tiles.map (ambientReindexEmbedding e)
      exact Finset.mem_map.mpr ⟨U, hU, rfl⟩
    · rw [subspacePoints_ambientReindex]
      exact Finset.mem_map.mpr ⟨y, hyU, rfl⟩

end AmbientReindex

/-- Every tile in `T` is contained in `D`. -/
def IsContainedIn (T : SubspaceTiling eta alpha iota)
    (D : Finset (iota → alpha)) : Prop :=
  ∀ U ∈ T.tiles, subspacePoints U ⊆ D

theorem covered_subset_iff (T : SubspaceTiling eta alpha iota)
    (D : Finset (iota → alpha)) :
    T.covered ⊆ D ↔ T.IsContainedIn D := by
  classical
  constructor
  · intro h U hU
    exact (T.tile_subset_covered hU).trans h
  · intro h x hx
    obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hx
    exact h U hU hxU

section AmbientReindexContainment

variable {kappa : Type*} [DecidableEq (kappa → alpha)]

/-- Containment after an ambient reindex is equivalent to containment in the
pullback of the target finset. -/
theorem ambientReindex_isContainedIn_iff
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    (T.ambientReindex e).IsContainedIn D ↔
      T.IsContainedIn
        (D.map (ambientWordEquiv e).symm.toEmbedding) := by
  rw [← (T.ambientReindex e).covered_subset_iff D,
    ← T.covered_subset_iff, covered_ambientReindex]
  constructor
  · intro h x hx
    apply Finset.mem_map.mpr
    refine ⟨ambientWordEquiv e x, h ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · simp
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' := h hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hy'
    simpa [← hzy] using hz

/-- Exact residual-set transport under an ambient coordinate equivalence. -/
theorem sdiff_covered_ambientReindex
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    D \ (T.ambientReindex e).covered =
      ((D.map (ambientWordEquiv e).symm.toEmbedding) \ T.covered).map
        (ambientWordEquiv e).toEmbedding := by
  classical
  rw [covered_ambientReindex]
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    apply Finset.mem_map.mpr
    refine ⟨(ambientWordEquiv e).symm x, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, by simp⟩
    · exact Finset.mem_map.mpr ⟨x, hx'.1, by simp⟩
    · intro hcover
      apply hx'.2
      exact Finset.mem_map.mpr
        ⟨(ambientWordEquiv e).symm x, hcover, by simp⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hy' := Finset.mem_sdiff.mp hy
    obtain ⟨z, hzD, hzy⟩ := Finset.mem_map.mp hy'.1
    apply Finset.mem_sdiff.mpr
    constructor
    · have hzx : z = x := by
        rw [← hyx, ← hzy]
        simp
      simpa [hzx] using hzD
    · intro hxcover
      obtain ⟨w, hwcover, hwx⟩ := Finset.mem_map.mp hxcover
      apply hy'.2
      have hwy : w = y := by
        apply (ambientWordEquiv e).injective
        exact hwx.trans hyx.symm
      simpa [hwy] using hwcover

theorem density_sdiff_covered_ambientReindex
    [Fintype (iota → alpha)] [Fintype (kappa → alpha)]
    (T : SubspaceTiling eta alpha iota) (e : iota ≃ kappa)
    (D : Finset (kappa → alpha)) :
    density (D \ (T.ambientReindex e).covered) =
      density (D.map (ambientWordEquiv e).symm.toEmbedding \ T.covered) := by
  rw [sdiff_covered_ambientReindex,
    density_map_equiv (ambientWordEquiv e)]

end AmbientReindexContainment

theorem card_covered (T : SubspaceTiling eta alpha iota) :
    T.covered.card = ∑ U ∈ T.tiles, (subspacePoints U).card := by
  classical
  exact Finset.card_biUnion T.pairwiseDisjoint

theorem comp_left_injective (U : Subspace eta alpha iota) :
    Function.Injective (U.comp : Subspace zeta alpha eta → Subspace zeta alpha iota) := by
  intro V W hVW
  apply Subspace.ext
  funext e
  obtain ⟨i, hi⟩ := U.proper e
  have hcoord := congrArg (fun X : Subspace zeta alpha iota ↦ X.idxFun i) hVW
  simpa [Subspace.comp, hi] using hcoord

noncomputable def compEmbedding (U : Subspace eta alpha iota) :
    Subspace zeta alpha eta ↪ Subspace zeta alpha iota :=
  ⟨U.comp, comp_left_injective U⟩

/-- Map every tile in a parameter cube into an outer combinatorial subspace. -/
noncomputable def comp (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) : SubspaceTiling zeta alpha iota := by
  classical
  exact
    { tiles := T.tiles.map (compEmbedding U)
      pairwiseDisjoint := by
        intro V hV W hW hne
        obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
        obtain ⟨W₀, hW₀, hWeq⟩ := Finset.mem_map.1 hW
        subst V
        subst W
        have hne₀ : V₀ ≠ W₀ := fun h ↦ hne (congrArg U.comp h)
        change Disjoint (subspacePoints (U.comp V₀)) (subspacePoints (U.comp W₀))
        rw [subspacePoints_comp, subspacePoints_comp,
          Finset.disjoint_image U.parameter_injective]
        exact T.pairwiseDisjoint hV₀ hW₀ hne₀ }

theorem covered_comp (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) :
    (T.comp U).covered = T.covered.image U := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨V, hV, hxV⟩ := ((T.comp U).mem_covered x).1 hx
    change V ∈ T.tiles.map (compEmbedding U) at hV
    obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
    subst V
    change x ∈ subspacePoints (U.comp V₀) at hxV
    rw [subspacePoints_comp] at hxV
    simp only [Finset.mem_image] at hxV ⊢
    obtain ⟨y, hy, rfl⟩ := hxV
    exact ⟨y, T.tile_subset_covered hV₀ hy, rfl⟩
  · intro hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨V, hV, hyV⟩ := (T.mem_covered y).1 hy
    apply ((T.comp U).mem_covered (U y)).2
    refine ⟨U.comp V, ?_, ?_⟩
    · change U.comp V ∈ T.tiles.map (compEmbedding U)
      exact Finset.mem_map.2 ⟨V, hV, rfl⟩
    · rw [subspacePoints_comp]
      exact Finset.mem_image_of_mem U hyV

theorem covered_comp_subset_subspacePoints
    (T : SubspaceTiling zeta alpha eta) (U : Subspace eta alpha iota) :
    (T.comp U).covered ⊆ subspacePoints U := by
  rw [covered_comp]
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  simp

theorem comp_isContainedIn_iff (T : SubspaceTiling zeta alpha eta)
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    (T.comp U).IsContainedIn D ↔ T.IsContainedIn (subspacePullback U D) := by
  classical
  constructor
  · intro h V hV
    rw [← subspacePoints_comp_subset_iff U V D]
    apply h (U.comp V)
    change U.comp V ∈ T.tiles.map (compEmbedding U)
    exact Finset.mem_map.2 ⟨V, hV, rfl⟩
  · intro h V hV
    change V ∈ T.tiles.map (compEmbedding U) at hV
    obtain ⟨V₀, hV₀, hVeq⟩ := Finset.mem_map.1 hV
    subst V
    change subspacePoints (U.comp V₀) ⊆ D
    rw [subspacePoints_comp_subset_iff]
    exact h V₀ hV₀

/-- Refine every tile of `T` by an inner tiling in its parameter cube and
flatten all the resulting composed subspaces into one tiling. -/
noncomputable def bind (T : SubspaceTiling eta alpha iota)
    (R : Subspace eta alpha iota → SubspaceTiling zeta alpha eta) :
    SubspaceTiling zeta alpha iota := by
  classical
  exact
    { tiles := T.tiles.biUnion fun U ↦ (R U).comp U |>.tiles
      pairwiseDisjoint := by
        intro A hA B hB hAB
        change A ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hA
        change B ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hB
        obtain ⟨U, hU, hAU⟩ := Finset.mem_biUnion.mp hA
        obtain ⟨V, hV, hBV⟩ := Finset.mem_biUnion.mp hB
        by_cases hUV : U = V
        · subst V
          exact ((R U).comp U).pairwiseDisjoint hAU hBV hAB
        · exact (T.pairwiseDisjoint hU hV hUV).mono
            (((R U).comp U).tile_subset_covered hAU |>.trans
              ((R U).covered_comp_subset_subspacePoints U))
            (((R V).comp V).tile_subset_covered hBV |>.trans
              ((R V).covered_comp_subset_subspacePoints V)) }

theorem covered_bind (T : SubspaceTiling eta alpha iota)
    (R : Subspace eta alpha iota → SubspaceTiling zeta alpha eta) :
    (T.bind R).covered =
      T.tiles.biUnion fun U ↦ ((R U).comp U).covered := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA, hxA⟩ := ((T.bind R).mem_covered x).1 hx
    change A ∈ T.tiles.biUnion (fun U ↦ ((R U).comp U).tiles) at hA
    obtain ⟨U, hU, hAU⟩ := Finset.mem_biUnion.mp hA
    apply Finset.mem_biUnion.mpr
    exact ⟨U, hU, (((R U).comp U).mem_covered x).2 ⟨A, hAU, hxA⟩⟩
  · intro hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨A, hAU, hxA⟩ := (((R U).comp U).mem_covered x).1 hxU
    apply ((T.bind R).mem_covered x).2
    refine ⟨A, ?_, hxA⟩
    change A ∈ T.tiles.biUnion (fun V ↦ ((R V).comp V).tiles)
    exact Finset.mem_biUnion.mpr ⟨U, hU, hAU⟩

theorem density_covered [Fintype (iota → alpha)]
    (T : SubspaceTiling eta alpha iota) :
    density T.covered = ∑ U ∈ T.tiles, density (subspacePoints U) := by
  classical
  simp only [density]
  rw [T.card_covered]
  push_cast
  rw [Finset.sum_div]

end SubspaceTiling

/-- A set is tiled by `eta`-dimensional combinatorial subspaces if it is the
covered set of a pairwise-disjoint finite subspace family. -/
def IsSubspaceTiled (E : Finset (iota → alpha)) : Prop :=
  ∃ T : SubspaceTiling eta alpha iota, T.covered = E

end Families

section DensityOfDisjointUnions

variable {A I : Type*} [Fintype A] [DecidableEq A]

/-- Density is additive on a finite pairwise-disjoint union. -/
theorem density_biUnion {s : Finset I} {f : I → Finset A}
    (h : (s : Set I).PairwiseDisjoint f) :
    density (s.biUnion f) = ∑ i ∈ s, density (f i) := by
  classical
  simp only [density]
  rw [Finset.card_biUnion h]
  push_cast
  rw [Finset.sum_div]

/-- Sum a uniform relative-density bound over pairwise-disjoint ambient
pieces.  This is the quantitative bookkeeping used in the induction from one
insensitive factor to an intersection of insensitive factors. -/
theorem density_biUnion_le_mul_density_biUnion
    {s : Finset I} {p q : I → Finset A}
    (hp : (s : Set I).PairwiseDisjoint p)
    (hq : ∀ i ∈ s, q i ⊆ p i) {c : ℝ}
    (hlocal : ∀ i ∈ s, density (q i) ≤ c * density (p i)) :
    density (s.biUnion q) ≤ c * density (s.biUnion p) := by
  classical
  have hqdisj : (s : Set I).PairwiseDisjoint q := by
    intro i hi j hj hij
    exact (hp hi hj hij).mono (hq i hi) (hq j hj)
  rw [density_biUnion hqdisj, density_biUnion hp, Finset.mul_sum]
  gcongr with i hi
  exact hlocal i hi

/-- A convenient cardinality form of the preceding lemma. -/
theorem density_biUnion_le_mul_of_card
    {s : Finset I} {p q : I → Finset A}
    (hp : (s : Set I).PairwiseDisjoint p)
    (hq : ∀ i ∈ s, q i ⊆ p i) {c : ℝ}
    (hcard : ∀ i ∈ s, (q i).card ≤ c * (p i).card) :
    density (s.biUnion q) ≤ c * density (s.biUnion p) := by
  apply density_biUnion_le_mul_density_biUnion hp hq
  intro i hi
  simp only [density_eq_card_div_card]
  have hA : 0 ≤ (Fintype.card A : ℝ) := by positivity
  calc
    (q i).card / (Fintype.card A : ℝ) ≤
        (c * (p i).card) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right (hcard i hi) hA
    _ = c * ((p i).card / (Fintype.card A : ℝ)) := by ring

end DensityOfDisjointUnions

section TilingStatements

/-- Intersection of a finite family of finsets, taken inside the full finite
ambient type. -/
noncomputable def familyInter {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ ∀ j, x ∈ D j

@[simp] theorem mem_familyInter {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) (x : X) :
    x ∈ familyInter D ↔ ∀ j, x ∈ D j := by
  classical
  simp [familyInter]

theorem familyInter_subset {X : Type*} [Fintype X] {r : ℕ}
    (D : Fin r → Finset X) (j : Fin r) : familyInter D ⊆ D j := by
  intro x hx
  exact (mem_familyInter D x).1 hx j

@[simp] theorem familyInter_one {X : Type*} [Fintype X]
    (D : Fin 1 → Finset X) : familyInter D = D 0 := by
  ext x
  simp only [mem_familyInter]
  constructor
  · exact fun h ↦ h 0
  · intro hx j
    simpa only [Subsingleton.elim j 0] using hx

theorem familyInter_succ {X : Type*} [Fintype X] [DecidableEq X] {r : ℕ}
    (D : Fin (r + 1) → Finset X) :
    familyInter D =
      familyInter (fun j : Fin r ↦ D j.castSucc) ∩ D (Fin.last r) := by
  ext x
  simp only [mem_familyInter, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun j ↦ h j.castSucc, h (Fin.last r)⟩
  · rintro ⟨hinit, hlast⟩ j
    exact Fin.lastCases hlast hinit j

/-- Exact-dimension form of DKT Lemma 12. -/
def OneInsensitiveTilingAt (k m n : ℕ) (beta : ℝ) : Prop :=
  ∀ (i : Fin k) (D : Finset (Word (k + 1) n)),
    IsLastInsensitive i (D : Set (Word (k + 1) n)) →
    2 * beta < density D →
    ∃ T : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n),
      T.IsContainedIn D ∧ density (D \ T.covered) < 2 * beta

/-- Exact-dimension form of DKT Corollary 13.  `label` records which old
letter each insensitive factor is paired with; the proof does not require
these labels to be distinct. -/
def InsensitiveIntersectionTilingAt (k r m n : ℕ) (beta : ℝ) : Prop :=
  ∀ (label : Fin r → Fin k) (D : Fin r → Finset (Word (k + 1) n)),
    (∀ j, IsLastInsensitive (label j) (D j : Set (Word (k + 1) n))) →
    2 * (r : ℝ) * beta < density (familyInter D) →
    ∃ T : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n),
      T.IsContainedIn (familyInter D) ∧
        density (familyInter D \ T.covered) < 2 * (r : ℝ) * beta

/-- Inductive step in DKT Corollary 13: first tile the intersection of the
first `r` factors by `F`-dimensional subspaces, then use the one-factor tiling
inside every retained large tile. -/
theorem InsensitiveIntersectionTilingAt.succ {k r F m n : ℕ} {beta : ℝ}
    (hbeta : 0 < beta) (hrpos : 0 < r)
    (hprev : InsensitiveIntersectionTilingAt k r F n beta)
    (hone : OneInsensitiveTilingAt k m F beta) :
    InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  classical
  intro label D hD hden
  let Dpre : Fin r → Finset (Word (k + 1) n) := fun j ↦ D j.castSucc
  let labelPre : Fin r → Fin k := fun j ↦ label j.castSucc
  let jlast : Fin (r + 1) := Fin.last r
  let Dlast : Finset (Word (k + 1) n) := D jlast
  have hsplit : familyInter D = familyInter Dpre ∩ Dlast := by
    simpa [Dpre, Dlast, jlast] using familyInter_succ D
  have hall_sub_pre : familyInter D ⊆ familyInter Dpre := by
    rw [hsplit]
    exact Finset.inter_subset_left
  have hmono : density (familyInter D) ≤ density (familyInter Dpre) :=
    density_mono hall_sub_pre
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hpreDen : 2 * (r : ℝ) * beta < density (familyInter Dpre) := by
    have hden' : 2 * ((r : ℝ) + 1) * beta < density (familyInter D) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hden
    nlinarith
  obtain ⟨T, hTsub, hTloss⟩ :=
    hprev labelPre Dpre (fun j ↦ hD j.castSucc) hpreDen
  have hlastInsensitive :
      IsLastInsensitive (label jlast) (Dlast : Set (Word (k + 1) n)) := by
    simpa [Dlast] using hD jlast
  have hinner : ∀ U : Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n),
      ∃ R : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin F),
        R.IsContainedIn (subspacePullback U Dlast) ∧
          density (subspacePullback U Dlast \ R.covered) ≤ 2 * beta := by
    intro U
    have hins := hlastInsensitive.subspacePullback (label jlast) U Dlast
    by_cases hdense : 2 * beta < density (subspacePullback U Dlast)
    · obtain ⟨R, hRsub, hRloss⟩ :=
        hone (label jlast) (subspacePullback U Dlast) hins hdense
      exact ⟨R, hRsub, hRloss.le⟩
    · refine ⟨SubspaceTiling.empty, ?_, ?_⟩
      · intro V hV
        simp at hV
      · simpa using le_of_not_gt hdense
  choose R hRsub hRloss using hinner
  let S : SubspaceTiling (Fin m) (Fin (k + 1)) (Fin n) := T.bind R
  have hSpre : S.covered ⊆ familyInter Dpre := by
    intro x hx
    rw [show S.covered = T.tiles.biUnion (fun U ↦ ((R U).comp U).covered) by
      exact T.covered_bind R] at hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    exact hTsub U hU (((R U).covered_comp_subset_subspacePoints U) hxU)
  have hSlast : S.covered ⊆ Dlast := by
    intro x hx
    rw [show S.covered = T.tiles.biUnion (fun U ↦ ((R U).comp U).covered) by
      exact T.covered_bind R] at hx
    obtain ⟨U, _hU, hxU⟩ := Finset.mem_biUnion.mp hx
    have hcomp : ((R U).comp U).IsContainedIn Dlast :=
      (((R U).comp_isContainedIn_iff U Dlast)).2 (hRsub U)
    exact (((R U).comp U).covered_subset_iff Dlast).2 hcomp hxU
  have hSsub : S.IsContainedIn (familyInter D) := by
    rw [← S.covered_subset_iff]
    rw [hsplit]
    exact fun _ hx ↦ Finset.mem_inter.mpr ⟨hSpre hx, hSlast hx⟩
  let q := fun U : Combinatorics.Subspace (Fin F) (Fin (k + 1)) (Fin n) ↦
    (subspacePullback U Dlast \ (R U).covered).image U
  have hqsub : ∀ U ∈ T.tiles, q U ⊆ subspacePoints U := by
    intro U _hU x hx
    simp only [q, Finset.mem_image] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    simp
  have hqlocal : ∀ U ∈ T.tiles,
      density (q U) ≤ (2 * beta) * density (subspacePoints U) := by
    intro U _hU
    rw [show density (q U) = density (subspacePoints U) *
        density (subspacePullback U Dlast \ (R U).covered) by
      exact density_image_subspace U _]
    have hpnonneg := density_nonneg (subspacePoints U)
    have := mul_le_mul_of_nonneg_left (hRloss U) hpnonneg
    nlinarith
  have hqUnion :
      density (T.tiles.biUnion q) ≤ 2 * beta := by
    have hsum := density_biUnion_le_mul_density_biUnion
      T.pairwiseDisjoint hqsub hqlocal
    have hcover : T.tiles.biUnion subspacePoints = T.covered := rfl
    rw [hcover] at hsum
    have hTle := density_le_one T.covered
    have hbnonneg : 0 ≤ 2 * beta := by positivity
    nlinarith
  have hresSub : familyInter D \ S.covered ⊆
      (familyInter Dpre \ T.covered) ∪ T.tiles.biUnion q := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxall := hx'.1
    have hxnotS := hx'.2
    have hxpre : x ∈ familyInter Dpre := hall_sub_pre hxall
    have hxlast : x ∈ Dlast := by
      rw [hsplit] at hxall
      exact (Finset.mem_inter.mp hxall).2
    by_cases hxT : x ∈ T.covered
    · apply Finset.mem_union.mpr
      apply Or.inr
      obtain ⟨U, hU, hxU⟩ := (T.mem_covered x).1 hxT
      apply Finset.mem_biUnion.mpr
      refine ⟨U, hU, ?_⟩
      rw [show q U =
          (subspacePullback U Dlast \ (R U).covered).image U by rfl]
      rw [mem_subspacePoints] at hxU
      obtain ⟨y, hy⟩ := hxU
      subst x
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (mem_subspacePullback U Dlast y).2 hxlast
      · intro hycover
        apply hxnotS
        rw [show S.covered = T.tiles.biUnion
            (fun V ↦ ((R V).comp V).covered) by exact T.covered_bind R]
        apply Finset.mem_biUnion.mpr
        refine ⟨U, hU, ?_⟩
        rw [(R U).covered_comp U]
        exact Finset.mem_image_of_mem U hycover
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxpre, hxT⟩))
  refine ⟨S, hSsub, ?_⟩
  have hresDen := density_mono hresSub
  have hunion := density_union_le_add
    (familyInter Dpre \ T.covered) (T.tiles.biUnion q)
  have htarget' :
      density (familyInter D \ S.covered) < 2 * (r : ℝ) * beta + 2 * beta := by
    linarith
  have hcast : (r + 1 : ℕ) = r + 1 := rfl
  push_cast
  nlinarith

/-- Qualitative form of DKT Corollary 13.  If the one-insensitive-set tiling
lemma is available in some dimension for every requested tile dimension,
then the same is true for every nonempty finite intersection of insensitive
sets. -/
theorem exists_insensitiveIntersectionTilingAt {k : ℕ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hone : ∀ m, ∃ n, OneInsensitiveTilingAt k m n beta) :
    ∀ r m, ∃ n, InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  intro r
  induction r with
  | zero =>
      intro m
      obtain ⟨n, hn⟩ := hone m
      refine ⟨n, ?_⟩
      intro label D hD hden
      have hden₀ : 2 * beta < density (D 0) := by
        simpa [familyInter_one] using hden
      obtain ⟨T, hTsub, hTloss⟩ := hn (label 0) (D 0) (hD 0) hden₀
      refine ⟨T, ?_, ?_⟩
      · simpa [familyInter_one] using hTsub
      · simpa [familyInter_one] using hTloss
  | succ r ihr =>
      intro m
      obtain ⟨F, hF⟩ := hone m
      obtain ⟨n, hn⟩ := ihr F
      exact ⟨n, hn.succ hbeta (Nat.succ_pos r) hF⟩

/-- Lower-bound-preserving form of the qualitative intersection tiling
theorem.  Only the outermost recursive tiling needs to meet the requested
ambient-dimension bound; dimensions used for the inner tilings may be chosen
freely. -/
theorem exists_insensitiveIntersectionTilingAt_ge {k : ℕ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hone : ∀ m N, ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k m n beta) :
    ∀ r m N, ∃ n, N ≤ n ∧
      InsensitiveIntersectionTilingAt k (r + 1) m n beta := by
  intro r
  induction r with
  | zero =>
      intro m N
      obtain ⟨n, hNn, hn⟩ := hone m N
      refine ⟨n, hNn, ?_⟩
      intro label D hD hden
      have hden₀ : 2 * beta < density (D 0) := by
        simpa [familyInter_one] using hden
      obtain ⟨T, hTsub, hTloss⟩ := hn (label 0) (D 0) (hD 0) hden₀
      refine ⟨T, ?_, ?_⟩
      · simpa [familyInter_one] using hTsub
      · simpa [familyInter_one] using hTloss
  | succ r ihr =>
      intro m N
      obtain ⟨F, _hzeroF, hF⟩ := hone m 0
      obtain ⟨n, hNn, hn⟩ := ihr F N
      exact ⟨n, hNn, hn.succ hbeta (Nat.succ_pos r) hF⟩

end TilingStatements

end Erdos171

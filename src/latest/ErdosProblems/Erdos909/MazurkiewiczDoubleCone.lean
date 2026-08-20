/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Topology.ShrinkingLemma
import ErdosProblems.Erdos909.AndersonKeislerAssembly
import ErdosProblems.Erdos909.DoubleCone
import ErdosProblems.Erdos909.FiniteCoverRefinement
import ErdosProblems.Erdos909.LebesguePartition
import ErdosProblems.Erdos909.MazurkiewiczComponents

/-!
# Mazurkiewicz avoidance in a cubical double cone

This file packages the cover-multiplicity part of Mazurkiewicz's theorem.
The double cone is the quotient of an `(n+1)`-cube obtained by collapsing one
pair of opposite faces to two vertices.  A separator of the vertices therefore
pulls back to a separator of those faces.  The generalized Lebesgue covering
theorem then contradicts an open refinement of multiplicity at most `n`.
-/

open Set Topology TopologicalSpace

namespace Erdos909.MazurkiewiczDoubleCone

open AndersonKeislerAssembly ContinuumLower CubeSeparators DoubleCone
  FiniteCoverRefinement LebesguePartition MazurkiewiczComponents

noncomputable section

/-- The exact finite-cover input needed for the double-cone proof.  Such a
cover is constructed explicitly from the cubical coordinates away from the
two collapsed faces. -/
def HasGoodFaceCover (n : ℕ) : Prop :=
  ∃ k, ∃ U : Fin k → Set (DoubleCone n),
    (∀ a, IsOpen (U a)) ∧
    ({lowerEndpoint n, upperEndpoint n}ᶜ ⊆ ⋃ a, U a) ∧
    (∀ a, lowerEndpoint n ∉ U a ∧ upperEndpoint n ∉ U a) ∧
    ∀ a i,
      ¬ (((quotientMap ⁻¹' U a) ∩ lowerFace i).Nonempty ∧
         ((quotientMap ⁻¹' U a) ∩ upperFace i).Nonempty)

theorem hasGoodFaceCover (n : ℕ) : HasGoodFaceCover n :=
  exists_good_open_cover n

theorem lowerEndpoint_ne_upperEndpoint (n : ℕ) :
    lowerEndpoint n ≠ upperEndpoint n := by
  intro h
  have h' := congrArg (fun p : DoubleCone n ↦ p.1.1) h
  norm_num [lowerEndpoint, upperEndpoint] at h'

/-- The cover-multiplicity proof of Mazurkiewicz avoidance, separated from
the elementary construction of the good cubical cover. -/
theorem hasMazurkiewiczBetween_of_hasGoodFaceCover
    (n : ℕ) (hgood : HasGoodFaceCover n) :
    ContinuumLower.HasMazurkiewiczBetween (DoubleCone n) n
      (lowerEndpoint n) (upperEndpoint n) := by
  intro M hM hloM hhiM hlohi
  rcases hgood with ⟨k, U, hUopen, hUcover, hUend, hUfaces⟩
  have hMU : M ⊆ ⋃ a, U a := by
    intro x hxM
    apply hUcover
    have hxl : x ≠ lowerEndpoint n := by
      intro h
      exact hloM (h.symm ▸ hxM)
    have hxu : x ≠ upperEndpoint n := by
      intro h
      exact hhiM (h.symm ▸ hxM)
    simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
      ⟨hxl, hxu⟩
  obtain ⟨V, hVopen, hMV, hVU, hVmult⟩ :=
    exists_open_refinement_natCard_le M hM U hUopen hMU
  have hloV : lowerEndpoint n ∉ ⋃ j, V j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact (hUend j.2).1 (hVU j hj)
  have hhiV : upperEndpoint n ∉ ⋃ j, V j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact (hUend j.2).2 (hVU j hj)

  by_contra hcontra
  push Not at hcontra
  have hno : ¬ ∃ K : Set (DoubleCone n),
      IsCompact K ∧ IsConnected K ∧ K ⊆ (⋃ j, V j)ᶜ ∧
        lowerEndpoint n ∈ K ∧ upperEndpoint n ∈ K := by
    rintro ⟨K, hKcompact, hKconnected, hKG, hloK, hhiK⟩
    have hKnondeg : IsNondegenerateContinuum K := by
      refine ⟨hKcompact, hKconnected, ?_⟩
      intro hKsub
      exact hlohi (hKsub hloK hhiK)
    have hKM : Disjoint K M := by
      rw [Set.disjoint_left]
      intro x hxK hxM
      exact hKG hxK (hMV hxM)
    exact hcontra K hKnondeg hKM

  obtain ⟨S, P, Q, hSclosed, hPopen, hQopen, hPQ, hSc,
      hloP, hhiQ, hSV⟩ :=
    exists_closed_separator_decomposition_subset_iUnion_of_no_continuum
      hVopen hloV hhiV hno
  obtain ⟨C, hSC, hCclosed, hCV⟩ :=
    exists_subset_iUnion_closed_subset hSclosed hVopen
      (fun _ _ ↦ Set.toFinite _) hSV

  let C' : Fin n × Fin k → Set (Cube (n + 1)) :=
    fun j ↦ quotientMap ⁻¹' C j
  have hC'closed (j : Fin n × Fin k) : IsClosed (C' j) :=
    (hCclosed j).preimage continuous_quotientMap
  let L : Set (Cube (n + 1)) := quotientMap ⁻¹' S
  have hLsep : SeparatesFaces (0 : Fin (n + 1)) L := by
    exact separatesFaces_preimage_of_decomposition hSclosed hPopen hQopen hPQ
      hSc hloP hhiQ
  have hLC : L ⊆ ⋃ j, C' j := by
    intro x hxL
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hSC hxL)
    exact mem_iUnion.mpr ⟨j, hj⟩
  have hC'faces (j : Fin n × Fin k) (i : Fin (n + 1)) :
      ¬ ((C' j ∩ lowerFace i).Nonempty ∧
         (C' j ∩ upperFace i).Nonempty) := by
    rintro ⟨⟨x, hxC, hxl⟩, ⟨y, hyC, hyu⟩⟩
    apply hUfaces j.2 i
    constructor
    · exact ⟨x, hVU j (hCV j hxC), hxl⟩
    · exact ⟨y, hVU j (hCV j hyC), hyu⟩

  obtain ⟨x, hxlarge⟩ :=
    finite_closed_cover_separator_multiplicity
      C' hC'closed L hLsep hLC hC'faces
  let f : {j : Fin n × Fin k // x ∈ C' j} →
      {j : Fin n × Fin k // quotientMap x ∈ V j} :=
    fun j ↦ ⟨j.1, hCV j.1 j.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg
      (fun z : {j : Fin n × Fin k // quotientMap x ∈ V j} ↦ z.1) hab
  have hsmall : Nat.card {j : Fin n × Fin k // x ∈ C' j} ≤ n :=
    (Nat.card_le_card_of_injective f hf).trans (hVmult (quotientMap x))
  omega

/-- The form used by the square-specialized Anderson--Keisler assembly. -/
theorem assembly_hasMazurkiewiczBetween_of_hasGoodFaceCover
    (n : ℕ) (hgood : HasGoodFaceCover n) :
    AndersonKeislerAssembly.HasMazurkiewiczBetween (DoubleCone n) n
      (lowerEndpoint n) (upperEndpoint n) := by
  intro M hM hlo hhi
  exact hasMazurkiewiczBetween_of_hasGoodFaceCover n hgood M hM hlo hhi
    (lowerEndpoint_ne_upperEndpoint n)

/-- Mazurkiewicz's prescribed-endpoint theorem for the cubical double cone. -/
theorem hasMazurkiewiczBetween (n : ℕ) :
    ContinuumLower.HasMazurkiewiczBetween (DoubleCone n) n
      (lowerEndpoint n) (upperEndpoint n) :=
  hasMazurkiewiczBetween_of_hasGoodFaceCover n (hasGoodFaceCover n)

/-- The same theorem in the interface expected by the Anderson--Keisler
selector assembly. -/
theorem assembly_hasMazurkiewiczBetween (n : ℕ) :
    AndersonKeislerAssembly.HasMazurkiewiczBetween (DoubleCone n) n
      (lowerEndpoint n) (upperEndpoint n) :=
  assembly_hasMazurkiewiczBetween_of_hasGoodFaceCover n (hasGoodFaceCover n)

/-! ### Passage to Euclidean space -/

/-- Splitting off coordinate zero identifies `(n+1)`-dimensional Euclidean
space with the ambient product used for the double cone. -/
def euclideanConeAmbientHomeomorph (n : ℕ) :
    EuclideanObstruction.LetterSpace (n + 1) ≃ₜ ConeAmbient n where
  toFun x := (x 0, fun i ↦ x i.succ)
  invFun p := WithLp.toLp 2
    (fun j : Fin (n + 1) ↦ @Fin.cases n (fun _ ↦ ℝ) p.1 p.2 j)
  left_inv x := by
    ext j
    exact Fin.cases rfl (fun _ ↦ rfl) j
  right_inv p := by
    ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hraw : Continuous
        (fun p : ConeAmbient n ↦
          (fun j : Fin (n + 1) ↦ @Fin.cases n (fun _ ↦ ℝ) p.1 p.2 j)) := by
      rw [continuous_pi_iff]
      intro j
      refine Fin.cases continuous_fst (fun i ↦ ?_) j
      exact (continuous_apply i).comp continuous_snd
    exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) ↦ ℝ)).comp hraw

/-- The canonical embedding of the double cone into the Euclidean letter
space used by the transfinite construction. -/
def doubleConeEmbedding (n : ℕ) :
    DoubleCone n → EuclideanObstruction.LetterSpace (n + 1) :=
  (euclideanConeAmbientHomeomorph n).symm ∘ Subtype.val

theorem doubleConeEmbedding_isEmbedding (n : ℕ) :
    IsEmbedding (doubleConeEmbedding n) :=
  (euclideanConeAmbientHomeomorph n).symm.isEmbedding.comp IsEmbedding.subtypeVal

/-- A prescribed-point Mazurkiewicz theorem in an embedded compact region
implies the corresponding theorem in the ambient Euclidean space: intersect
the exceptional set with the region and map the avoiding continuum back. -/
theorem euclidean_assembly_hasMazurkiewiczBetween (n : ℕ) :
    AndersonKeislerAssembly.HasMazurkiewiczBetween
      (EuclideanObstruction.LetterSpace (n + 1)) n
      (doubleConeEmbedding n (lowerEndpoint n))
      (doubleConeEmbedding n (upperEndpoint n)) := by
  intro M hM hloM hhiM
  let f := doubleConeEmbedding n
  let N : Set (DoubleCone n) := f ⁻¹' M
  have hf : IsEmbedding f := doubleConeEmbedding_isEmbedding n
  have hN : HasSmallInductiveDimensionLT N n := by
    exact ContinuumLower.inducing_hasSmallInductiveDimensionLT
      (hf.restrictPreimage M).isInducing hM
  have hloN : lowerEndpoint n ∉ N := hloM
  have hhiN : upperEndpoint n ∉ N := hhiM
  obtain ⟨C, hC, hCN⟩ :=
    assembly_hasMazurkiewiczBetween n N hN hloN hhiN
  refine ⟨f '' C, ?_, ?_⟩
  · refine ⟨hC.1.image hf.continuous, hC.2.1.image f hf.continuous.continuousOn, ?_⟩
    intro hsub
    apply hC.2.2
    intro x hx y hy
    exact hf.injective (hsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hxC, rfl⟩ hfxM
    exact Set.disjoint_left.1 hCN hxC hfxM

end

end Erdos909.MazurkiewiczDoubleCone

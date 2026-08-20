/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ShrinkingLemma
import ErdosProblems.Erdos909.ContinuumLower
import ErdosProblems.Erdos909.DoubleCone
import ErdosProblems.Erdos909.FiniteCoverRefinement
import ErdosProblems.Erdos909.LebesguePartition
import ErdosProblems.Erdos909.MazurkiewiczComponents

/-!
# Mazurkiewicz avoidance in finite-dimensional Euclidean space

This file combines the countable closed-sum/coincidence theorem, the compact
component separator, the cubical double-cone quotient, and the generalized
Lebesgue covering theorem.  The result is the prescribed-endpoint form of
Mazurkiewicz's theorem needed in the Anderson--Keisler construction.
-/

open Set Topology TopologicalSpace

namespace Erdos909.MazurkiewiczLower

open ContinuumLower CubeSeparators DoubleCone FiniteCoverRefinement
  LebesguePartition MazurkiewiczComponents

noncomputable section

/-- Mazurkiewicz avoidance inside the compact double cone. -/
theorem doubleCone_hasMazurkiewiczBetween (n : ℕ) :
    HasMazurkiewiczBetween (DoubleCone n) n
      (lowerEndpoint n) (upperEndpoint n) := by
  intro M hM hloM hhiM hends
  classical
  let I := Fin n → Bool
  let k := Fintype.card I
  let sign : Fin k → I := (Fintype.equivFin I).symm
  let U : Fin k → Set (DoubleCone n) := fun i ↦ goodOpenPatch (sign i)
  have hUopen (i : Fin k) : IsOpen (U i) := isOpen_goodOpenPatch (sign i)
  have hUcover : M ⊆ ⋃ i, U i := by
    intro x hxM
    have hxends : x ≠ lowerEndpoint n ∧ x ≠ upperEndpoint n :=
      ⟨fun h ↦ hloM (h ▸ hxM), fun h ↦ hhiM (h ▸ hxM)⟩
    obtain ⟨s, hxs⟩ := nonendpoint_mem_goodOpenPatch_some hxends
    let i : Fin k := Fintype.equivFin I s
    exact mem_iUnion.mpr ⟨i, by simpa [U, sign, i] using hxs⟩
  obtain ⟨V, hVopen, hVcover, hVsub, hVmult⟩ :=
    exists_open_refinement_natCard_le M hM U hUopen hUcover
  let G : Set (DoubleCone n) := ⋃ j, V j
  have hGopen : IsOpen G := isOpen_iUnion hVopen
  have hloG : lowerEndpoint n ∉ G := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact (goodOpenPatch_subset_nonendpoints (sign j.2) (hVsub j hj)).1 rfl
  have hhiG : upperEndpoint n ∉ G := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact (goodOpenPatch_subset_nonendpoints (sign j.2) (hVsub j hj)).2 rfl
  by_contra havoid
  have hno : ¬ ∃ K : Set (DoubleCone n),
      IsCompact K ∧ IsConnected K ∧ K ⊆ Gᶜ ∧
        lowerEndpoint n ∈ K ∧ upperEndpoint n ∈ K := by
    rintro ⟨K, hKc, hKconn, hKG, hloK, hhiK⟩
    apply havoid
    refine ⟨K, ⟨hKc, hKconn, ?_⟩, ?_⟩
    · intro hKsub
      exact hends (hKsub hloK hhiK)
    · rw [Set.disjoint_left]
      intro x hxK hxM
      exact hKG hxK (hVcover hxM)
  obtain ⟨S, P, Q, hSclosed, hPopen, hQopen, hPQ, hSPQ,
      hloP, hhiQ, hSG⟩ :=
    exists_closed_separator_decomposition_of_no_continuum
      hGopen hloG hhiG hno
  obtain ⟨C, hSC, hCclosed, hCV⟩ :=
    exists_subset_iUnion_closed_subset hSclosed hVopen
      (fun _ _ ↦ Set.toFinite _) hSG
  let C' : (Fin n × Fin k) → Set (Cube (n + 1)) :=
    fun j ↦ quotientMap ⁻¹' C j
  have hC'closed (j : Fin n × Fin k) : IsClosed (C' j) :=
    (hCclosed j).preimage continuous_quotientMap
  let L : Set (Cube (n + 1)) := quotientMap ⁻¹' S
  have hLsep : SeparatesFaces (0 : Fin (n + 1)) L :=
    separatesFaces_preimage_of_decomposition hSclosed hPopen hQopen hPQ
      hSPQ hloP hhiQ
  have hLC : L ⊆ ⋃ j, C' j := by
    intro x hxL
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hSC hxL)
    exact mem_iUnion.mpr ⟨j, hj⟩
  have hC'avoid (j : Fin n × Fin k) (i : Fin (n + 1)) :
      ¬ ((C' j ∩ lowerFace i).Nonempty ∧
        (C' j ∩ upperFace i).Nonempty) := by
    intro hboth
    apply goodOpenPatch_preimage_not_meets_both_faces (sign j.2) i
    constructor
    · rcases hboth.1 with ⟨x, hxC, hxf⟩
      exact ⟨x, hVsub j (hCV j hxC), hxf⟩
    · rcases hboth.2 with ⟨x, hxC, hxf⟩
      exact ⟨x, hVsub j (hCV j hxC), hxf⟩
  obtain ⟨x, hxlower⟩ := finite_closed_cover_separator_multiplicity
    C' hC'closed L hLsep hLC hC'avoid
  have hxupper : Nat.card {j : Fin n × Fin k // x ∈ C' j} ≤ n := by
    let f : {j : Fin n × Fin k // x ∈ C' j} →
        {j : Fin n × Fin k // quotientMap x ∈ V j} :=
      fun j ↦ ⟨j.1, hCV j.1 j.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg
        (fun z : {j : Fin n × Fin k // quotientMap x ∈ V j} ↦ z.1) hab
    exact (Nat.card_le_card_of_injective f hf).trans (hVmult (quotientMap x))
  omega

/-- Ambient version: the two cone vertices are prescribed points of the
finite-dimensional product vector space. -/
theorem coneAmbient_hasMazurkiewiczBetween (n : ℕ) :
    HasMazurkiewiczBetween (ConeAmbient n) n
      (lowerEndpoint n : ConeAmbient n) (upperEndpoint n : ConeAmbient n) := by
  intro M hM hloM hhiM hends
  let N : Set (DoubleCone n) := Subtype.val ⁻¹' M
  let f : N → M := fun x ↦ ⟨x.1.1, x.2⟩
  have hf : IsEmbedding f := by
    exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _
      (fun x ↦ x.2)
  have hN : HasSmallInductiveDimensionLT N n :=
    inducing_hasSmallInductiveDimensionLT hf.isInducing hM
  have hloN : lowerEndpoint n ∉ N := hloM
  have hhiN : upperEndpoint n ∉ N := hhiM
  have hendsN : lowerEndpoint n ≠ upperEndpoint n := by
    intro h
    apply hends
    exact congrArg Subtype.val h
  obtain ⟨C, ⟨hCc, hCconn, hCnt⟩, hCN⟩ :=
    doubleCone_hasMazurkiewiczBetween n N hN hloN hhiN hendsN
  let D : Set (ConeAmbient n) := Subtype.val '' C
  have hDnt : ¬ D.Subsingleton := by
    intro hDsub
    apply hCnt
    intro x hx y hy
    apply Subtype.val_injective
    exact hDsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  refine ⟨D, ⟨hCc.image continuous_subtype_val,
    hCconn.image Subtype.val continuous_subtype_val.continuousOn,
    hDnt⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro x ⟨y, hyC, rfl⟩ hxM
  exact Set.disjoint_left.mp hCN hyC hxM

/-! ### Transfer to Mathlib's Euclidean-space model -/

/-- The canonical linear homeomorphism splitting the first coordinate from
the remaining `n` coordinates. -/
def euclideanConeEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] ConeAmbient n := by
  let e1 : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    (EuclideanSpace.equiv (Fin 1) ℝ).trans
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ))
  let en : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  exact (EuclideanSpace.finAddEquivProd (n := n) (m := 1) (𝕜 := ℝ)).trans
    ((en.prodCongr e1).trans
      (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ))

/-- The Euclidean point corresponding to the lower cone vertex. -/
def euclideanLowerEndpoint (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (euclideanConeEquiv n).symm (lowerEndpoint n : ConeAmbient n)

/-- The Euclidean point corresponding to the upper cone vertex. -/
def euclideanUpperEndpoint (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (euclideanConeEquiv n).symm (upperEndpoint n : ConeAmbient n)

/-- The concrete prescribed-endpoint Mazurkiewicz theorem in Mathlib's
Euclidean-space model. -/
theorem euclidean_hasMazurkiewiczBetween (n : ℕ) :
    HasMazurkiewiczBetween (EuclideanSpace ℝ (Fin (n + 1))) n
      (euclideanLowerEndpoint n) (euclideanUpperEndpoint n) := by
  apply hasMazurkiewiczBetween_of_homeomorph (euclideanConeEquiv n).toHomeomorph
  simpa [euclideanLowerEndpoint, euclideanUpperEndpoint] using
    coneAmbient_hasMazurkiewiczBetween n

/-- The two fixed Euclidean endpoints are distinct. -/
theorem euclideanLowerEndpoint_ne_euclideanUpperEndpoint (n : ℕ) :
    euclideanLowerEndpoint n ≠ euclideanUpperEndpoint n := by
  intro h
  have h' := congrArg (fun z ↦ ((euclideanConeEquiv n) z).1) h
  norm_num [euclideanLowerEndpoint, euclideanUpperEndpoint,
    lowerEndpoint, upperEndpoint] at h'

/-- The Anderson--Keisler lower bound in the precise form needed after the
selector has been arranged to omit the two fixed points. -/
theorem smallInductiveDimension_ge_of_meetsEveryNondegenerateContinuum
    (n : ℕ) {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hK : MeetsEveryNondegenerateContinuum K)
    (hlow : euclideanLowerEndpoint n ∉ K)
    (hupp : euclideanUpperEndpoint n ∉ K) :
    (n : WithBot ℕ∞) ≤ smallInductiveDimension K :=
  smallInductiveDimension_ge_of_hitter_of_mazurkiewiczBetween
    hK hlow hupp (euclideanLowerEndpoint_ne_euclideanUpperEndpoint n)
      (euclidean_hasMazurkiewiczBetween n)

/-- Endpoint-existential form convenient for downstream selector
constructions.  The selected points are genuinely distinct. -/
theorem exists_euclidean_endpoints_hasMazurkiewiczBetween (n : ℕ) :
    ∃ p q : EuclideanSpace ℝ (Fin (n + 1)),
      p ≠ q ∧ HasMazurkiewiczBetween
        (EuclideanSpace ℝ (Fin (n + 1))) n p q := by
  refine ⟨euclideanLowerEndpoint n, euclideanUpperEndpoint n, ?_,
    euclidean_hasMazurkiewiczBetween n⟩
  exact euclideanLowerEndpoint_ne_euclideanUpperEndpoint n

end

end Erdos909.MazurkiewiczLower

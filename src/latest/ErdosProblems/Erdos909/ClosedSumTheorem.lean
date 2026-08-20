/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos909.ClosedSum
import Mathlib.Data.Nat.Pairing

/-!
# The countable closed-sum theorem for small inductive dimension

This file completes the mutual dimension induction begun in `ClosedSum`.  It
proves that a second-countable pseudometric space covered by countably many
closed subspaces of dimension at most `n` itself has dimension at most `n`.
-/

open Set Topology TopologicalSpace

namespace Erdos909.ClosedSum

universe u

private theorem inducing_dimLT
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : IsInducing f) {n : ℕ}
    (h : HasSmallInductiveDimensionLT B n) :
    HasSmallInductiveDimensionLT A n := by
  induction h generalizing A with
  | zero =>
      have := Function.isEmpty f
      exact .zero
  | succ n b hb hd ih =>
      refine .succ n _ (hb.isInducing hf) ?_
      rintro _ ⟨U, hU, rfl⟩
      apply ih U hU
      apply (hf.restrictPreimage (frontier U)).comp
      exact (IsEmbedding.inclusion
        (hf.continuous.frontier_preimage_subset U)).isInducing

private theorem inducing_dimLE
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : IsInducing f) {n : ℕ}
    (h : HasSmallInductiveDimensionLE B n) :
    HasSmallInductiveDimensionLE A n := inducing_dimLT hf h

private theorem subtype_dimLT_of_basis
    {A : Type*} [TopologicalSpace A]
    (s : Set A) (n : ℕ) (b : Set (Set A)) (hb : IsTopologicalBasis b)
    (hdim : ∀ U ∈ b,
      HasSmallInductiveDimensionLT (Subtype.val ⁻¹' frontier U : Set s) n) :
    HasSmallInductiveDimensionLT s (n + 1) := by
  refine .succ n _ (hb.isInducing IsInducing.subtypeVal) ?_
  rintro _ ⟨U, hU, rfl⟩
  exact inducing_dimLT
    (IsEmbedding.inclusion
      (continuous_subtype_val.frontier_preimage_subset U)).isInducing
    (hdim U hU)

/-- The universe-polymorphic countable closed-sum property at dimension
`n`. -/
def CountableClosedSumProperty (n : ℕ) : Prop :=
  ∀ (X : Type u) [PseudoMetricSpace X] [SecondCountableTopology X]
    (F : ℕ → Set X),
    (∀ i, IsClosed (F i)) →
    (⋃ i, F i) = univ →
    (∀ i, HasSmallInductiveDimensionLE (F i) n) →
    HasSmallInductiveDimensionLE X n

theorem countableClosedSumProperty_zero :
    CountableClosedSumProperty.{u} 0 := by
  intro X _ _ F hFc hFcov hFdim
  exact hasSmallInductiveDimensionLT_one_of_closed_iUnion F hFc hFdim hFcov

theorem countableClosedSumProperty_succ
    (n : ℕ) (ih : CountableClosedSumProperty.{u} n) :
    CountableClosedSumProperty.{u} (n + 1) := by
  classical
  intro X _ _ F hFc hFcov hFdim
  have hex_basis (i : ℕ) :
      ∃ b : Set (Set (F i)), IsTopologicalBasis b ∧
        ∀ U ∈ b, HasSmallInductiveDimensionLT (frontier U) (n + 1) := by
    have hi := hFdim i
    change HasSmallInductiveDimensionLT (F i) ((n + 1) + 1) at hi
    cases hi with
    | succ _ b hb hd => exact ⟨b, hb, hd⟩
  choose b hb hbdim using hex_basis
  have hex_countable (i : ℕ) :
      ∃ c : Set (Set (F i)), c ⊆ b i ∧ c.Countable ∧ IsTopologicalBasis c :=
    (hb i).exists_countable
  choose c hcsub hcc hcb using hex_countable
  let c' (i : ℕ) : Set (Set (F i)) := insert ∅ (c i)
  have hc'count (i : ℕ) : (c' i).Countable := (hcc i).insert ∅
  have hc'basis (i : ℕ) : IsTopologicalBasis (c' i) := (hcb i).insert_empty
  let q (i k : ℕ) : Set (F i) := Set.enumerateCountable (hc'count i) ∅ k
  have hqmem (i k : ℕ) : q i k ∈ c' i :=
    Set.enumerateCountable_mem (hc'count i) (mem_insert ∅ (c i)) k
  have hqrange (i : ℕ) : range (q i) = c' i :=
    Set.range_enumerateCountable_of_mem (hc'count i) (mem_insert ∅ (c i))
  let R (i k : ℕ) : Set X := Subtype.val '' frontier (q i k)
  have hRclosed (i k : ℕ) : IsClosed (R i k) :=
    (hFc i).isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_frontier
  have hRdim (i k : ℕ) : HasSmallInductiveDimensionLE (R i k) n := by
    rcases hqmem i k with hqempty | hqc
    · have heq : q i k = ∅ := hqempty
      have : IsEmpty (R i k) := by
        rw [isEmpty_coe_sort]
        simp [R, heq]
      exact HasSmallInductiveDimensionLT.mono zero_le HasSmallInductiveDimensionLT.zero
    · have hfront : HasSmallInductiveDimensionLT (frontier (q i k)) (n + 1) :=
        hbdim i (q i k) (hcsub i hqc)
      let e := IsEmbedding.subtypeVal.homeomorphImage (frontier (q i k))
      exact inducing_dimLT e.symm.isInducing hfront
  let Y : Set X := ⋃ i : ℕ, ⋃ k : ℕ, R i k
  let G (m : ℕ) : Set Y :=
    Subtype.val ⁻¹' R (Nat.unpair m).1 (Nat.unpair m).2
  have hGclosed (m : ℕ) : IsClosed (G m) :=
    (hRclosed (Nat.unpair m).1 (Nat.unpair m).2).preimage continuous_subtype_val
  have hGdim (m : ℕ) : HasSmallInductiveDimensionLE (G m) n := by
    let e : G m → R (Nat.unpair m).1 (Nat.unpair m).2 :=
      fun x ↦ ⟨x.1.1, x.2⟩
    have he : IsEmbedding e := by
      exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _
        (fun x ↦ x.2)
    exact inducing_dimLE he.isInducing
      (hRdim (Nat.unpair m).1 (Nat.unpair m).2)
  have hGcov : (⋃ m, G m) = univ := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ m, (y : X) ∈ R (Nat.unpair m).1 (Nat.unpair m).2
    have hy := y.2
    change (y : X) ∈ ⋃ i : ℕ, ⋃ k : ℕ, R i k at hy
    simp only [mem_iUnion] at hy
    rcases hy with ⟨i, hi⟩
    rcases hi with ⟨k, hik⟩
    exact ⟨Nat.pair i k, by simpa [Nat.unpair_pair] using hik⟩
  have hYdim : HasSmallInductiveDimensionLE Y n :=
    ih Y G hGclosed hGcov hGdim
  let Z : Set X := Yᶜ
  let S (i : ℕ) : Set (F i) := Subtype.val ⁻¹' Z
  have hSzero (i : ℕ) : HasSmallInductiveDimensionLE (S i) 0 := by
    apply subtype_dimLT_of_basis (S i) 0 (c' i) (hc'basis i)
    intro U hU
    rw [hasSmallInductiveDimensionLT_zero_iff, isEmpty_coe_sort]
    apply Set.Subset.antisymm
    · intro x hx
      exfalso
      rcases (show U ∈ range (q i) by rwa [hqrange i]) with ⟨k, rfl⟩
      apply x.2
      change (x.1.1 : X) ∈ Y
      apply mem_iUnion_of_mem i
      apply mem_iUnion_of_mem k
      change (x.1.1 : X) ∈ R i k
      let y : F i := x.val
      exact ⟨y, hx, rfl⟩
    · exact empty_subset _
  let T (i : ℕ) : Set Z := Subtype.val ⁻¹' F i
  have hTclosed (i : ℕ) : IsClosed (T i) :=
    (hFc i).preimage continuous_subtype_val
  have hTcov : (⋃ i, T i) = univ := by
    ext z
    simpa only [T, mem_iUnion, mem_preimage, mem_univ, iff_true] using
      (show (z : X) ∈ ⋃ i, F i by rw [hFcov]; exact mem_univ _)
  have hTzero (i : ℕ) : HasSmallInductiveDimensionLE (T i) 0 := by
    let e₀ : T i → F i := fun x ↦ ⟨x.1.1, x.2⟩
    have he₀ : IsEmbedding e₀ := by
      exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _
        (fun x ↦ x.2)
    let e : T i → S i := fun x ↦ ⟨e₀ x, x.1.2⟩
    have he : IsEmbedding e := he₀.codRestrict _ (fun x ↦ x.1.2)
    exact inducing_dimLE he.isInducing (hSzero i)
  have hZdim : HasSmallInductiveDimensionLE Z 0 :=
    hasSmallInductiveDimensionLT_one_of_closed_iUnion T hTclosed hTzero hTcov
  have hUnion :
      HasSmallInductiveDimensionLT (↑(Y ∪ Z : Set X)) ((n + 1) + 1) :=
    hasSmallInductiveDimensionLT_union_zeroDimensional Y Z hYdim hZdim
  let e : X → (Y ∪ Z : Set X) := fun x ↦ ⟨x, by simp [Z]⟩
  have he : IsEmbedding e := IsEmbedding.id.codRestrict _ (fun x ↦ by simp [Z])
  exact inducing_dimLT he.isInducing hUnion

/-- **Countable closed-sum theorem.** A second-countable pseudometric space
covered by countably many closed subspaces of dimension at most `n` has
dimension at most `n`. -/
theorem hasSmallInductiveDimensionLE_of_countable_closed_cover
    (n : ℕ) : CountableClosedSumProperty.{u} n := by
  induction n with
  | zero => exact countableClosedSumProperty_zero
  | succ n ih =>
      simpa [Nat.succ_eq_add_one] using countableClosedSumProperty_succ n ih

end Erdos909.ClosedSum

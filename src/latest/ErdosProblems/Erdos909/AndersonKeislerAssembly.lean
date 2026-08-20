/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos909.ContinuumLower
import ErdosProblems.Erdos909.ContinuumSchedule
import ErdosProblems.Erdos909.EuclideanObstruction

/-!
# Assembly of the Anderson--Keisler witness

This file connects the three independent parts of the construction:

* the continuum-length independent selector;
* the unary and binary dimension obstructions;
* the Mazurkiewicz lower bound for continuum-hitting subsets of Euclidean
  space.

The only hypotheses of the main theorem below are the two concrete geometric
packages which are developed separately.  All cardinal and product bookkeeping
is discharged here.
-/

open Set Topology TopologicalSpace

namespace Erdos909.AndersonKeislerAssembly

open ContinuumLower CuttingUpper EuclideanObstruction

noncomputable section

/-- The precise form of Mazurkiewicz's theorem needed after the selector has
been required to omit two fixed points.  Recording the points explicitly
avoids a separate Euclidean full-dimension argument merely to find points in
the complement of the selected set. -/
def HasMazurkiewiczBetween (X : Type*) [TopologicalSpace X]
    (n : ℕ) (p q : X) : Prop :=
  ∀ M : Set X, HasSmallInductiveDimensionLT M n → p ∉ M → q ∉ M →
    ∃ C : Set X, IsNondegenerateContinuum C ∧ Disjoint C M

/-- The two-point Mazurkiewicz property is invariant under homeomorphism. -/
theorem Homeomorph.hasMazurkiewiczBetween
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {n : ℕ} {p q : X}
    (hY : HasMazurkiewiczBetween Y n (e p) (e q)) :
    HasMazurkiewiczBetween X n p q := by
  intro M hM hp hq
  let N : Set Y := e '' M
  have hN : HasSmallInductiveDimensionLT N n :=
    ContinuumLower.inducing_hasSmallInductiveDimensionLT
      (e.image M).symm.isInducing hM
  have hep : e p ∉ N := by
    rintro ⟨x, hxM, hxp⟩
    exact hp ((e.injective hxp).symm ▸ hxM)
  have heq : e q ∉ N := by
    rintro ⟨x, hxM, hxq⟩
    exact hq ((e.injective hxq).symm ▸ hxM)
  obtain ⟨C, hC, hCN⟩ := hY N hN hep heq
  refine ⟨e.symm '' C, ?_, ?_⟩
  · refine ⟨hC.1.image e.symm.continuous, hC.2.1.image e.symm ?_, ?_⟩
    · exact e.symm.continuous.continuousOn
    · intro hsub
      apply hC.2.2
      intro x hx y hy
      apply e.symm.injective
      exact hsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · rw [Set.disjoint_left]
    rintro x ⟨y, hyC, rfl⟩ hxM
    apply Set.disjoint_left.1 hCN hyC
    exact ⟨e.symm y, hxM, e.apply_symm_apply y⟩

/-- The product of two copies of a subspace is canonically homeomorphic to the
subspace cut out by the set-theoretic Cartesian product. -/
def prodSubtypeHomeomorph {X : Type*} [TopologicalSpace X] (K : Set X) :
    K × K ≃ₜ (K ×ˢ K : Set (X × X)) where
  toEquiv :=
    { toFun := fun z => ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
      invFun := fun z => (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Countability of every binary-pattern trace gives exactly the three kinds
of countable sections required by the independent-selector recursion. -/
theorem BinaryTerminalFamily.countable_diagonal_and_sections
    {m : ℕ} (F : BinaryTerminalFamily m) :
    {x | (x, x) ∈ F.obstruction}.Countable ∧
      (∀ y, {x | (x, y) ∈ F.obstruction}.Countable) ∧
      ∀ y, {x | (y, x) ∈ F.obstruction}.Countable := by
  have diagonalInjective : Function.Injective
      (fun x : LetterSpace m => (x, x)) := fun _ _ h =>
    congrArg Prod.fst h
  have leftInjective (y : LetterSpace m) : Function.Injective
      (fun x : LetterSpace m => (x, y)) := fun _ _ h =>
    congrArg Prod.fst h
  have rightInjective (y : LetterSpace m) : Function.Injective
      (fun x : LetterSpace m => (y, x)) := fun _ _ h =>
    congrArg Prod.snd h
  refine ⟨?_, ?_, ?_⟩
  · have h := F.countable_pattern_inter BinaryPatternKind.diagonal 0
    have h' := h.preimage diagonalInjective
    convert h' using 1
    ext x
    simp [binaryPatternPlane]
  · intro y
    have h := F.countable_pattern_inter BinaryPatternKind.left y
    have h' := h.preimage (leftInjective y)
    convert h' using 1
    ext x
    simp [binaryPatternPlane]
  · intro y
    have h := F.countable_pattern_inter BinaryPatternKind.right y
    have h' := h.preimage (rightInjective y)
    convert h' using 1
    ext x
    simp [binaryPatternPlane]

/-- Once the Euclidean upper and lower geometric packages are available, the
transfinite selector gives a subspace whose dimension and square dimension
are both exactly `n`. -/
theorem exists_andersonKeisler_witness
    (n : ℕ) (O : UnaryBinaryObstructions (n + 1))
    (p q : LetterSpace (n + 1))
    (hMaz : HasMazurkiewiczBetween (LetterSpace (n + 1)) n p q) :
    ∃ K : Set (LetterSpace (n + 1)),
      smallInductiveDimension K = n ∧
      smallInductiveDimension (K × K) = n := by
  have hm : 0 < n + 1 := Nat.succ_pos n
  obtain ⟨hdiag, hleft, hright⟩ :=
    BinaryTerminalFamily.countable_diagonal_and_sections O.binary
  let avoid : Set (LetterSpace (n + 1)) :=
    O.unary.obstruction ∪ {p, q}
  have hAvoidCountable : avoid.Countable :=
    O.unary.countable.union (Set.toFinite {p, q}).countable
  obtain ⟨K, hKmeet, hKunary, hKbinary⟩ :=
    exists_set_meeting_indexed_continua_avoiding
      (n + 1) hm avoid O.binary.obstruction
      hAvoidCountable hdiag hleft hright

  have hMeet : MeetsEveryNondegenerateContinuum K := by
    intro C hC
    exact hKmeet C hC
  have hKunary' : Disjoint K O.unary.obstruction :=
    hKunary.mono_right subset_union_left
  have hpK : p ∉ K := fun hp =>
    Set.disjoint_left.1 hKunary hp (Or.inr (Set.mem_insert p {q}))
  have hqK : q ∉ K := fun hq =>
    Set.disjoint_left.1 hKunary hq (Or.inr (Set.mem_insert_of_mem p rfl))
  have hKnotLT : ¬ HasSmallInductiveDimensionLT K n := by
    intro hKdim
    obtain ⟨C, hC, hCK⟩ := hMaz K hKdim hpK hqK
    obtain ⟨x, hxK, hxC⟩ := hMeet C hC
    exact Set.disjoint_left.1 hCK hxC hxK
  have hKlower : (n : WithBot ℕ∞) ≤ smallInductiveDimension K := by
    rw [← not_lt, smallInductiveDimension_lt_iff]
    exact hKnotLT
  have hKupper : smallInductiveDimension K ≤ n :=
    smallInductiveDimension_le_iff.2 (O.unary.forces K hKunary')
  have hKdim : smallInductiveDimension K = n :=
    le_antisymm hKupper hKlower

  have hSqSubtype : HasSmallInductiveDimensionLT
      (K ×ˢ K : Set (LetterSpace (n + 1) × LetterSpace (n + 1))) (n + 1) :=
    O.binary.forces _ hKbinary
  have hSqUpperLT : HasSmallInductiveDimensionLT (K × K) (n + 1) :=
    ContinuumLower.inducing_hasSmallInductiveDimensionLT
      (prodSubtypeHomeomorph K).isInducing hSqSubtype
  have hSqUpper : smallInductiveDimension (K × K) ≤ n :=
    smallInductiveDimension_le_iff.2 hSqUpperLT

  have hKnonempty : Nonempty K := by
    have hFallback := hKmeet (fallbackContinuum (n + 1))
      (fallbackContinuum_isNondegenerateContinuum (n + 1) hm)
    obtain ⟨x, hxK, -⟩ := hFallback
    exact ⟨⟨x, hxK⟩⟩
  let x0 : K := Classical.choice hKnonempty
  let slice : K → K × K := fun x => (x, x0)
  have hSlice : IsInducing slice :=
    (isEmbedding_prodMkLeft x0).isInducing
  have hSqLower : (n : WithBot ℕ∞) ≤
      smallInductiveDimension (K × K) := by
    rw [← hasSmallInductiveDimensionGE_iff_smallInductiveDimension_ge]
    exact hasSmallInductiveDimensionGE_of_inducing hSlice
      ((hasSmallInductiveDimensionGE_iff_smallInductiveDimension_ge n).2
        hKlower)
  exact ⟨K, hKdim, le_antisymm hSqUpper hSqLower⟩

end

end Erdos909.AndersonKeislerAssembly

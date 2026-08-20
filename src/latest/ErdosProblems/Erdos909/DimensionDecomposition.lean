/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos909.ClosedSum
import ErdosProblems.Erdos909.ContinuumLower

/-!
# Finite zero-dimensional decomposition

The countable closed-sum theorem implies the classical decomposition of a
second-countable metric space of dimension at most `n` into `n+1`
zero-dimensional subspaces.  This is the form used to turn small inductive
dimension bounds into finite-cover multiplicity bounds.
-/

open Set Topology TopologicalSpace

namespace Erdos909.DimensionDecomposition

open ClosedSum ContinuumLower

universe u

/-- The binary decomposition assertion used in the finite-layer induction. -/
def BinaryZeroDimensionalDecomposition : Prop :=
  ∀ (Z : Type u) [PseudoMetricSpace Z] [SecondCountableTopology Z] (r : ℕ),
    HasSmallInductiveDimensionLE Z (r + 1) →
      ∃ A B : Set Z, A ∪ B = univ ∧ Disjoint A B ∧
        HasSmallInductiveDimensionLE A r ∧
        HasSmallInductiveDimensionLE B 0

private theorem countableClosedSumAt_of_full (r : ℕ) :
    CountableClosedSumAt.{u} (r + 1) := by
  induction r with
  | zero => exact countableClosedSumAt_one
  | succ r ih =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using countableClosedSumAt_succ ih

/-- The closed-sum theorem supplies the binary decomposition. -/
theorem binaryZeroDimensionalDecomposition :
    BinaryZeroDimensionalDecomposition.{u} := by
  intro Z _ _ r hZ
  simpa [HasSmallInductiveDimensionLE] using
    (exists_disjoint_decomposition_of_countableClosedSumAt
      (X := Z) (n := r + 1) (countableClosedSumAt_of_full r) hZ)

/-- An embedded image of a zero-dimensional subspace is zero-dimensional. -/
theorem hasSmallInductiveDimensionLE_zero_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) (s : Set X)
    (hs : HasSmallInductiveDimensionLE s 0) :
    HasSmallInductiveDimensionLE (f '' s) 0 := by
  exact inducing_hasSmallInductiveDimensionLT
    (hf.homeomorphImage s).symm.isInducing hs

/-- The decomposition induction as a finite coloring. -/
theorem exists_fin_zeroDimensional_coloring
    (hsplit : BinaryZeroDimensionalDecomposition.{u})
    (X : Type u) [PseudoMetricSpace X] [SecondCountableTopology X]
    (n : ℕ) (hX : HasSmallInductiveDimensionLE X n) :
    ∃ c : X → Fin (n + 1),
      ∀ i, HasSmallInductiveDimensionLE {x : X | c x = i} 0 := by
  classical
  induction n generalizing X with
  | zero =>
      let c : X → Fin 1 := fun _ ↦ 0
      refine ⟨c, fun i ↦ ?_⟩
      exact inducing_hasSmallInductiveDimensionLT IsInducing.subtypeVal hX
  | succ n ih =>
      obtain ⟨A, B, hcover, hdisj, hA, hB⟩ := hsplit X n hX
      obtain ⟨cA, hcA⟩ := ih A hA
      let c : X → Fin (n + 2) := fun x ↦
        if hx : x ∈ A then (cA ⟨x, hx⟩).castSucc else Fin.last (n + 1)
      refine ⟨c, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · apply inducing_hasSmallInductiveDimensionLT
          (IsEmbedding.inclusion (t := B) ?_).isInducing hB
        intro x hx
        have hxA : x ∉ A := by
          intro hxA
          have hcA' : c x = (cA ⟨x, hxA⟩).castSucc := by simp [c, hxA]
          have hlast : c x = Fin.last (n + 1) := hx
          exact Fin.castSucc_ne_last _ (hcA'.symm.trans hlast)
        have hxAB : x ∈ A ∪ B := by simpa [hcover]
        exact hxAB.resolve_left hxA
      · let D : Set A := {a | cA a = j}
        have hD : HasSmallInductiveDimensionLE D 0 := hcA j
        have himage : HasSmallInductiveDimensionLE (Subtype.val '' D : Set X) 0 :=
          hasSmallInductiveDimensionLE_zero_image IsEmbedding.subtypeVal D hD
        apply inducing_hasSmallInductiveDimensionLT
          (IsEmbedding.inclusion (t := Subtype.val '' D) ?_).isInducing himage
        intro x hx
        have hxA : x ∈ A := by
          by_contra hxA
          have hlast : c x = Fin.last (n + 1) := by simp [c, hxA]
          have hcast : c x = j.castSucc := hx
          exact Fin.castSucc_ne_last j (hcast.symm.trans hlast)
        refine ⟨⟨x, hxA⟩, ?_, rfl⟩
        have hc : c x = (cA ⟨x, hxA⟩).castSucc := by simp [c, hxA]
        exact Fin.castSucc_inj.mp (hc.symm.trans hx)

/-- A space of dimension at most `n` is a union of `n+1` pairwise-disjoint
zero-dimensional subspaces. -/
theorem exists_fin_zeroDimensional_partition
    (X : Type u) [PseudoMetricSpace X] [SecondCountableTopology X]
    (n : ℕ) (hX : HasSmallInductiveDimensionLE X n) :
    ∃ P : Fin (n + 1) → Set X,
      (⋃ i, P i) = univ ∧
      (∀ {i j}, i ≠ j → Disjoint (P i) (P j)) ∧
      ∀ i, HasSmallInductiveDimensionLE (P i) 0 := by
  obtain ⟨c, hc⟩ := exists_fin_zeroDimensional_coloring
    binaryZeroDimensionalDecomposition X n hX
  refine ⟨fun i ↦ {x | c x = i}, ?_, ?_, hc⟩
  · apply iUnion_eq_univ_iff.2
    exact fun x ↦ ⟨c x, rfl⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact hij (hxi.symm.trans hxj)

end Erdos909.DimensionDecomposition

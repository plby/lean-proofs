/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos909.DimensionDecomposition
import ErdosProblems.Erdos909.ZeroDimensionalRefinement

/-!
# Low-multiplicity refinements from small inductive dimension

This is the finite-cover form of the coincidence theorem `ind = dim` for
second-countable metric spaces needed in Mazurkiewicz's theorem.  It is
derived from the finite zero-dimensional decomposition and the disjoint
ambient refinement theorem for each layer.
-/

open Set Topology TopologicalSpace

namespace Erdos909.FiniteCoverRefinement

open ContinuumLower DimensionDecomposition ZeroDimensionalRefinement

universe u

/-- A finite ambient-open cover of a subspace of strict dimension `< n` has
an ambient-open subordinate refinement of multiplicity at most `n`.

The fixed product index `Fin n × Fin k` records the zero-dimensional layer
and the original cover member. -/
theorem exists_open_refinement_natCard_le
    {X : Type u} [PseudoMetricSpace X] [SecondCountableTopology X]
    (M : Set X) {n k : ℕ}
    (hM : HasSmallInductiveDimensionLT M n)
    (U : Fin k → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : M ⊆ ⋃ i, U i) :
    ∃ V : Fin n × Fin k → Set X,
      (∀ j, IsOpen (V j)) ∧ M ⊆ ⋃ j, V j ∧
      (∀ j, V j ⊆ U j.2) ∧
      ∀ x, Nat.card {j : Fin n × Fin k // x ∈ V j} ≤ n := by
  classical
  cases n with
  | zero =>
      have hMe : IsEmpty M := hasSmallInductiveDimensionLT_zero_iff.mp hM
      let : IsEmpty M := hMe
      let V : Fin 0 × Fin k → Set X := fun j ↦ Fin.elim0 j.1
      refine ⟨V, ?_, ?_, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j.1
      · intro x hx
        exact isEmptyElim (⟨x, hx⟩ : M)
      · intro j
        exact Fin.elim0 j.1
      · intro x
        simp
  | succ r =>
      obtain ⟨P, hPcover, -, hPzero⟩ :=
        exists_fin_zeroDimensional_partition M r hM
      let A : Fin (r + 1) → Set X := fun i ↦ Subtype.val '' P i
      have hAzero (i : Fin (r + 1)) :
          HasSmallInductiveDimensionLT (A i) 1 := by
        exact hasSmallInductiveDimensionLE_zero_image IsEmbedding.subtypeVal
          (P i) (hPzero i)
      have hAcover : M ⊆ ⋃ i, A i := by
        intro x hx
        let y : M := ⟨x, hx⟩
        have hy : y ∈ ⋃ i, P i := by rw [hPcover]; exact mem_univ y
        obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨i, ⟨y, hyi, rfl⟩⟩
      have hAUcover (i : Fin (r + 1)) : A i ⊆ ⋃ j, U j := by
        intro x hx
        obtain ⟨y, -, rfl⟩ := hx
        exact hUcover y.property
      choose W hWopen hWdisj hWcover hWsub using fun i ↦
        exists_ambient_disjoint_open_refinement (A i) (hAzero i)
          U hUopen (hAUcover i)
      let V : Fin (r + 1) × Fin k → Set X := fun j ↦ W j.1 j.2
      refine ⟨V, fun j ↦ hWopen j.1 j.2, ?_, fun j ↦ hWsub j.1 j.2, ?_⟩
      · intro x hxM
        obtain ⟨i, hxi⟩ := mem_iUnion.mp (hAcover hxM)
        obtain ⟨j, hxj⟩ := mem_iUnion.mp (hWcover i hxi)
        exact mem_iUnion.mpr ⟨(i, j), hxj⟩
      · intro x
        let f : {j : Fin (r + 1) × Fin k // x ∈ V j} → Fin (r + 1) :=
          fun j ↦ j.1.1
        have hf : Function.Injective f := by
          intro p q hpq
          apply Subtype.ext
          apply Prod.ext hpq
          by_contra hne
          have hp : x ∈ W p.1.1 p.1.2 := p.2
          have hq : x ∈ W q.1.1 q.1.2 := q.2
          have hpq' : p.1.1 = q.1.1 := hpq
          have hq' : x ∈ W p.1.1 q.1.2 := by
            rw [hpq']
            exact hq
          exact Set.disjoint_left.mp (hWdisj p.1.1 hne) hp
            hq'
        simpa [f] using Nat.card_le_card_of_injective f hf

end Erdos909.FiniteCoverRefinement

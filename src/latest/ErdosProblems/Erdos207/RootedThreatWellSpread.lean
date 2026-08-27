/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedThreatFourBound

/-!
# Full rooted-threat well-spreadness

This file recombines the indexed order-at-least-five witnesses and the
explicit order-four witnesses into the extension bound used by the KSSS
moment argument.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

theorem extensionWeight_rootedThreat_eq_indexed_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {u v : V}
    (p : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : RootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v ↦
          rootedThreatRemainder z)
        p A =
      extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        p A +
      extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        p A := by
  classical
  unfold extensionWeight
  symm
  simpa using Fintype.sum_subtype_add_sum_subtype
    (IsIndexedRootedThreatWitness q B u v)
    (fun z ↦ if A ⊆ rootedThreatRemainder z then
      setWeight p (rootedThreatRemainder z \ A) else 0)

/-- The exact natural-number coefficient in the full rooted extension
bound. -/
noncomputable def rootedThreatExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) : ℕ :=
  (q + 1) * refinedIndexedAbsorberBudget q M H X B + 4

/-- Absorber localization implies the complete rooted well-spreadness bound
at every distinct pair. -/
theorem absorberRootedThreatRemainder_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {u v : V}
    (hA2 : HasAbsorberLocalization q M H X B) (huv : u ≠ v) :
    HasExtensionBound
      (fun z : RootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v ↦
        rootedThreatRemainder z)
      (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
      ((Fintype.card V *
        rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0) := by
  intro A
  rw [extensionWeight_rootedThreat_eq_indexed_add_four]
  calc
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A +
      extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ((Fintype.card V * (q + 1) *
          refinedIndexedAbsorberBudget q M H X B : ℕ) : ℝ≥0) +
        ((Fintype.card V * 4 : ℕ) : ℝ≥0) :=
      add_le_add (extensionWeight_indexedRootedThreat_le hA2 huv A)
        (extensionWeight_fourRootedThreat_le huv A)
    _ = ((Fintype.card V *
        rootedThreatExtensionCoefficient q M H X B : ℕ) : ℝ≥0) := by
      simp only [rootedThreatExtensionCoefficient, Nat.cast_add,
        Nat.cast_mul]
      ring

end Erdos207

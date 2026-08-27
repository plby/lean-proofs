/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedThreatWeight
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.Powerset

/-!
# Finite cardinal and baseline extension bounds for rooted threats

These estimates are deliberately independent of the geometric information
in absorber property A2.  They identify the exact finite multiplicities
which the sharper well-spread argument must improve.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

/-- There are exactly `choose |V| 3` triples on a finite vertex type. -/
theorem card_tripleOn_eq_choose
    (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (TripleOn V) = Nat.choose (Fintype.card V) 3 := by
  simpa only [TripleOn] using
    (Fintype.card_finset_len (α := V) 3)

/-- The convenient cubic upper bound for the number of triples. -/
theorem card_tripleOn_le_cube_crude
    (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (TripleOn V) ≤ Fintype.card V ^ 3 := by
  rw [card_tripleOn_eq_choose]
  exact Nat.choose_le_pow _ _

/-- The finite type of all triple systems is a powerset of the triple type. -/
theorem card_tripleSystemOn_eq_two_pow
    (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (TripleSystemOn V) =
      2 ^ Nat.choose (Fintype.card V) 3 := by
  rw [Fintype.card_finset, card_tripleOn_eq_choose]

/-- Forgetting the distinguished root pair embeds rooted threat witnesses
into a forbidden member together with one of its triangles. -/
def rootedThreatWitnessEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (u v : V) :
    RootedThreatWitness V F u v ↪ Σ S : F, S.1 :=
  { toFun := fun z ↦ ⟨⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2.1⟩⟩
    inj' := by
      intro z w hzw
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x ↦ x.1.1) hzw)
        (congrArg (fun x ↦ x.2.1) hzw) }

/-- If every forbidden member has at most `k` triangles, there are at most
`k |F|` rooted witnesses at any ordered vertex pair. -/
theorem card_rootedThreatWitness_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (u v : V) (k : ℕ)
    (hcard : ∀ S ∈ F, S.card ≤ k) :
    Fintype.card (RootedThreatWitness V F u v) ≤ F.card * k := by
  calc
    Fintype.card (RootedThreatWitness V F u v) ≤
        Fintype.card (Σ S : F, S.1) :=
      Fintype.card_le_of_embedding (rootedThreatWitnessEmbedding F u v)
    _ = ∑ S : F, S.1.card := by simp
    _ ≤ ∑ _S : F, k := by
      apply sum_le_sum
      intro S _hS
      exact hcard S.1 S.2
    _ = F.card * k := by simp

/-- A product of point weights bounded by one is bounded by one. -/
lemma setWeight_le_one
    {W : Type*} [DecidableEq W] (π : W → ℝ≥0)
    (hπ : ∀ x, π x ≤ 1) (S : Finset W) : setWeight π S ≤ 1 := by
  unfold setWeight
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      rw [prod_insert hx]
      calc
        π x * ∏ y ∈ S, π y ≤ (1 : ℝ≥0) * 1 := by
          exact mul_le_mul (hπ x) ih zero_le zero_le
        _ = 1 := by simp

/-- Baseline extension bound obtained only from the number of witnesses.
The A2/well-spread argument improves this bound by powers of the ambient
order, but this theorem makes the purely finite part explicit. -/
theorem rootedThreatRemainder_hasExtensionBound_crude
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (u v : V) (π : TripleOn V → ℝ≥0)
    (k : ℕ) (hcard : ∀ S ∈ F, S.card ≤ k)
    (hπ : ∀ T, π T ≤ 1) :
    HasExtensionBound
      (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
      π (F.card * k) := by
  intro H
  unfold extensionWeight
  calc
    ∑ z : RootedThreatWitness V F u v,
        (if H ⊆ rootedThreatRemainder z then
          setWeight π (rootedThreatRemainder z \ H) else 0) ≤
        ∑ _z : RootedThreatWitness V F u v, (1 : ℝ≥0) := by
      apply sum_le_sum
      intro z _hz
      split_ifs
      · exact setWeight_le_one π hπ _
      · exact zero_le
    _ = (Fintype.card (RootedThreatWitness V F u v) : ℝ≥0) := by simp
    _ ≤ (F.card * k : ℝ≥0) := by
      exact_mod_cast card_rootedThreatWitness_le F u v k hcard

/-- The same baseline estimate for the absorber-induced family. -/
theorem absorberRootedThreatRemainder_hasExtensionBound_crude
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (u v : V)
    (π : TripleOn V → ℝ≥0) (hπ : ∀ T, π T ≤ 1) :
    HasExtensionBound
      (fun z : RootedThreatWitness V
        (absorberErdosForbiddenConfigurationsOn q B) u v ↦
          rootedThreatRemainder z)
      π ((absorberErdosForbiddenConfigurationsOn q B).card * q) := by
  apply rootedThreatRemainder_hasExtensionBound_crude _ u v π q
  · exact fun S hS ↦ card_le_cutoff_of_mem_absorberErdosForbidden hS
  · exact hπ

end Erdos207

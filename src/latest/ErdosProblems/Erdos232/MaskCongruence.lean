/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CombinatorialData
import ErdosProblems.Erdos232.RigidCongruence

namespace Erdos232

open scoped ComplexConjugate

/-- Vertices selected by a natural-number mask. -/
def selectedVertices (m : Nat) : Finset (Fin 23) :=
  Finset.univ.filter fun i ↦ m.testBit i

/-- Two masks select congruent subconfigurations, witnessed by a bijection preserving every
entry of the exact squared-distance label matrix. -/
def MaskCongruent (m n : Nat) : Prop :=
  (selectedVertices m).Nonempty ∧
    ∃ e : (↥(selectedVertices m)) ≃ (↥(selectedVertices n)),
      ∀ i j, configurationDistanceLabel i.1 j.1 =
        configurationDistanceLabel (e i).1 (e j).1

/-- Decode the image of vertex `i` from the base-23 digits of `code`. -/
def decodedVertex (code : Nat) (i : Fin 23) : Fin 23 :=
  ⟨code / 23 ^ i.val % 23, Nat.mod_lt _ (by norm_num)⟩

/-- A directly checkable certificate that the base-23 map encoded by `code` restricts to a
distance-preserving bijection between the two selected configurations. -/
def MaskMapValid (m n code : Nat) : Prop :=
  (selectedVertices m).Nonempty ∧
  (∀ i, i ∈ selectedVertices m → decodedVertex code i ∈ selectedVertices n) ∧
  (∀ i, i ∈ selectedVertices m → ∀ j, j ∈ selectedVertices m →
    decodedVertex code i = decodedVertex code j → i = j) ∧
  (∀ j, j ∈ selectedVertices n →
    ∃ i, i ∈ selectedVertices m ∧ decodedVertex code i = j) ∧
  (∀ i, i ∈ selectedVertices m → ∀ j, j ∈ selectedVertices m →
    configurationDistanceLabel i j =
      configurationDistanceLabel (decodedVertex code i) (decodedVertex code j))

instance (m n code : Nat) : Decidable (MaskMapValid m n code) := by
  unfold MaskMapValid
  infer_instance

/-- A valid base-23 map certificate produces the required subtype equivalence. -/
theorem MaskMapValid.maskCongruent {m n code : Nat} (h : MaskMapValid m n code) :
    MaskCongruent m n := by
  rcases h with ⟨hne, hmaps, hinjective, hsurjective, hlabels⟩
  let f : (↥(selectedVertices m)) → (↥(selectedVertices n)) := fun i ↦
    ⟨decodedVertex code i.1, hmaps i.1 i.2⟩
  have hf_injective : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hinjective i.1 i.2 j.1 j.2 (Subtype.ext_iff.mp hij)
  have hf_surjective : Function.Surjective f := by
    intro j
    obtain ⟨i, hi, hij⟩ := hsurjective j.1 j.2
    refine ⟨⟨i, hi⟩, ?_⟩
    exact Subtype.ext hij
  let e : (↥(selectedVertices m)) ≃ (↥(selectedVertices n)) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  refine ⟨hne, e, ?_⟩
  intro i j
  change configurationDistanceLabel i.1 j.1 =
    configurationDistanceLabel (f i).1 (f j).1
  exact hlabels i.1 i.2 j.1 j.2

/-- A distance-label congruence is an actual Euclidean congruence of the selected points. -/
theorem MaskCongruent.exists_rigid {m n : Nat} (h : MaskCongruent m n) :
    ∃ e : (↥(selectedVertices m)) ≃ (↥(selectedVertices n)),
      ∃ reflected : Bool, ∃ u c : ℂ, Complex.normSq u = 1 ∧
        ∀ i, configurationPoint (e i).1 =
          u * (if reflected then conj (configurationPoint i.1) else configurationPoint i.1) + c := by
  classical
  rcases h with ⟨⟨anchor, hanchor⟩, e, he⟩
  letI : Nonempty (↥(selectedVertices m)) := ⟨⟨anchor, hanchor⟩⟩
  refine ⟨e, ?_⟩
  apply exists_complex_rigid_of_fintype_normSq_eq
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · have heij : e i ≠ e j := fun h' ↦ hij (e.injective h')
    rw [configuration_normSq i.1 j.1 (fun h' ↦ hij (Subtype.ext h')),
      configuration_normSq (e i).1 (e j).1 (fun h' ↦ heij (Subtype.ext h')), he i j]

end Erdos232

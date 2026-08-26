/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Models of Flypitch's `ZFC` are models of the Mathlib-side `ZFC`

The Mathlib-side theory `Erdos501.FOL.ZFC` (Challenge / `Erdos501.FOL.Statement`) mirrors
Flypitch's `ZFC` axiom by axiom.  The eight fixed axioms translate to Flypitch's *by
definitional unfolding* (`tr axiomOfEmptyset = axiom_of_emptyset` etc. are all `rfl`), and the
strong collection scheme is transferred semantically (`Erdos501.FOL.Collection`).  Hence every
Flypitch structure `S` satisfying Flypitch's `ZFC` gives an `L`-structure `toM S` satisfying `ZFC`
(`toM_models_ZFC`).
-/
import ErdosProblems.Erdos501.FOL.Collection

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Fol

namespace Erdos501.FOL

/-! ### The fixed axioms translate to Flypitch's -/

theorem tr_axiomOfEmptyset : tr axiomOfEmptyset = axiom_of_emptyset := rfl
theorem tr_axiomOfOrderedPairs : tr axiomOfOrderedPairs = axiom_of_ordered_pairs := rfl
theorem tr_axiomOfExtensionality : tr axiomOfExtensionality = axiom_of_extensionality := rfl
theorem tr_axiomOfUnion : tr axiomOfUnion = axiom_of_union := rfl
theorem tr_axiomOfPowerset : tr axiomOfPowerset = axiom_of_powerset := rfl
theorem tr_axiomOfInfinity : tr axiomOfInfinity = axiom_of_infinity := rfl
theorem tr_axiomOfRegularity : tr axiomOfRegularity = axiom_of_regularity := rfl
theorem tr_zornsLemma : tr zornsLemma = zorns_lemma := rfl

/-! ### Membership in Flypitch's `ZFC` -/

lemma axiom_of_emptyset_mem_ZFC : axiom_of_emptyset ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_ordered_pairs_mem_ZFC : axiom_of_ordered_pairs ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_extensionality_mem_ZFC : axiom_of_extensionality ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_union_mem_ZFC : axiom_of_union ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_powerset_mem_ZFC : axiom_of_powerset ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_infinity_mem_ZFC : axiom_of_infinity ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_regularity_mem_ZFC : axiom_of_regularity ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma zorns_lemma_mem_ZFC : zorns_lemma ∈ _root_.ZFC := by simp [_root_.ZFC]
lemma axiom_of_collection_mem_ZFC {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2)) :
    axiom_of_collection ϕ ∈ _root_.ZFC := by
  simp only [_root_.ZFC, Set.mem_union, Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
  exact Or.inr ⟨n, ϕ, rfl⟩

/-! ### The transfer -/

section

variable (S : Fol.Structure L_ZFC)

attribute [local instance] toM

/-- A Flypitch structure satisfying Flypitch's `ZFC` is, as an `L`-structure, a model of the
Mathlib-side `ZFC`. -/
theorem toM_models_ZFC [Nonempty S.carrier] (h : S ⊨ₜ _root_.ZFC) : S.carrier ⊨ ZFC := by
  refine ⟨fun φ hφ => ?_⟩
  simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iUnion,
    Set.mem_range] at hφ
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨n, ψ, rfl⟩
  · exact (realize_sentence_tr S _).mpr (tr_axiomOfEmptyset ▸ h axiom_of_emptyset_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr
      (tr_axiomOfOrderedPairs ▸ h axiom_of_ordered_pairs_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr
      (tr_axiomOfExtensionality ▸ h axiom_of_extensionality_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr (tr_axiomOfUnion ▸ h axiom_of_union_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr (tr_axiomOfPowerset ▸ h axiom_of_powerset_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr (tr_axiomOfInfinity ▸ h axiom_of_infinity_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr (tr_axiomOfRegularity ▸ h axiom_of_regularity_mem_ZFC)
  · exact (realize_sentence_tr S _).mpr (tr_zornsLemma ▸ h zorns_lemma_mem_ZFC)
  · exact toM_realize_collectionAxiom S ψ (h (axiom_of_collection_mem_ZFC (tr ψ)))

end

end Erdos501.FOL

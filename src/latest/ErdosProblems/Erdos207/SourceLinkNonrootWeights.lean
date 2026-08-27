/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkBlockWeights

/-! # The density factor supplied by a noninitial, nondistinguished triangle -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceLinkMarking.root_not_mem_initial_later
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x) :
    x.root ∉ x.initial ∪ x.later :=
  fun hroot ↦ disjoint_left.mp hx.2.2.1 hroot hx.2.2.2.1

theorem SourceLinkMarking.nonroot_system_eq
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x) :
    x.system \ {x.root} = (x.initial ∪ x.later) ∪ x.candidate.erase x.root := by
  change ((x.initial ∪ x.later) ∪ x.candidate) \ {x.root} = _
  rw [union_sdiff_distrib, sdiff_singleton_eq_erase, sdiff_singleton_eq_erase,
    erase_eq_of_notMem (SourceLinkMarking.root_not_mem_initial_later hx)]

theorem SourceLinkMarking.nonroot_base_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x) (π : TripleOn V → ℝ≥0) :
    setWeight π x.initial * setWeight π x.later * setWeight π (x.candidate.erase x.root) =
      setWeight π (x.system \ {x.root}) := by
  rw [SourceLinkMarking.nonroot_system_eq hx]
  unfold setWeight
  rw [prod_union (hx.2.2.1.mono (Subset.refl _) (erase_subset _ _)), prod_union hx.2.1]

theorem SourceLinkMarking.nonroot_block_weight_le_density
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x)
    (f₀ f₁ f₂ π : TripleOn V → ℝ≥0) (fe : Sym2 V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T ∈ x.initial, f₀ T ≤ π T)
    (h₁ : ∀ T ∈ x.later, f₁ T ≤ p * π T)
    (h₂ : ∀ T ∈ x.candidate.erase x.root, f₂ T * setWeight fe (tripleEdgeFinset T) ≤ p * π T) :
    setWeight f₀ x.initial * setWeight f₁ x.later *
        (∏ T ∈ x.candidate.erase x.root, f₂ T * setWeight fe (tripleEdgeFinset T)) ≤
      p * setWeight π (x.system \ {x.root}) := by
  have hI : setWeight f₀ x.initial ≤ setWeight π x.initial := prod_le_prod' h₀
  have hD : setWeight f₁ x.later ≤ p ^ x.later.card * setWeight π x.later := by
    calc
      _ ≤ ∏ T ∈ x.later, p * π T := prod_le_prod' h₁
      _ = _ := by simp only [setWeight, prod_mul_distrib, prod_const]
  have hC : (∏ T ∈ x.candidate.erase x.root, f₂ T * setWeight fe (tripleEdgeFinset T)) ≤
      p ^ (x.candidate.erase x.root).card * setWeight π (x.candidate.erase x.root) := by
    calc
      _ ≤ ∏ T ∈ x.candidate.erase x.root, p * π T := prod_le_prod' h₂
      _ = _ := by simp only [setWeight, prod_mul_distrib, prod_const]
  have hpos : 1 ≤ x.later.card + (x.candidate.erase x.root).card := by
    have hnon := card_pos.mpr hx.2.2.2.2.2.2.2
    have hbound := card_union_le x.later (x.candidate.erase x.root)
    omega
  have hp' : p ^ (x.later.card + (x.candidate.erase x.root).card) ≤ p := by
    simpa only [pow_one] using pow_le_pow_of_le_one (show 0 ≤ p from zero_le) hp hpos
  calc
    _ ≤ setWeight π x.initial * (p ^ x.later.card * setWeight π x.later) *
        (p ^ (x.candidate.erase x.root).card * setWeight π (x.candidate.erase x.root)) := by gcongr
    _ = p ^ (x.later.card + (x.candidate.erase x.root).card) *
        (setWeight π x.initial * setWeight π x.later * setWeight π (x.candidate.erase x.root)) := by
      rw [pow_add]
      ring
    _ ≤ p * (setWeight π x.initial * setWeight π x.later * setWeight π (x.candidate.erase x.root)) := by gcongr
    _ = _ := by rw [SourceLinkMarking.nonroot_base_weight hx π]

end

end Erdos207

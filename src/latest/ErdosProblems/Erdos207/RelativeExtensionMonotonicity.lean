/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeExtensionFromJoint

/-!
# Monotonicity tools for relative extension weights

Point weights are monotone in the expected direction.  Selection sets have
the opposite effect: deleting a larger sampled reservoir can only increase
the worst rooted extension weight when all point weights are at most one.
This is exactly the comparison needed to pass from a sampled link reservoir
to the matching chosen inside it.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma setWeight_mono_pointwise
    {W : Type*} [DecidableEq W] {pi rho : W → ℝ≥0}
    (h : ∀ x, pi x ≤ rho x) (S : Finset W) :
    setWeight pi S ≤ setWeight rho S := by
  unfold setWeight
  exact Finset.prod_le_prod' fun x _hx ↦ h x

lemma extensionWeight_mono_pointwise
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) {pi rho : W → ℝ≥0}
    (h : ∀ x, pi x ≤ rho x) (A : Finset W) :
    extensionWeight F pi A ≤ extensionWeight F rho A := by
  classical
  unfold extensionWeight
  apply sum_le_sum
  intro i _hi
  by_cases hAi : A ⊆ F i
  · simp only [if_pos hAi]
    exact setWeight_mono_pointwise h _
  · simp only [if_neg hAi]
    exact zero_le

theorem HasExtensionBound.mono_weight
    {W I : Type*} [DecidableEq W] [Fintype I]
    {F : I → Finset W} {pi rho : W → ℝ≥0} {kappa : ℝ≥0}
    (hF : HasExtensionBound F rho kappa)
    (h : ∀ x, pi x ≤ rho x) :
    HasExtensionBound F pi kappa := by
  intro A
  exact (extensionWeight_mono_pointwise F h A).trans (hF A)

/-- Enlarging the common scalar cutoff preserves an extension bound. -/
theorem HasExtensionBound.mono_bound
    {W I : Type*} [DecidableEq W] [Fintype I]
    {F : I → Finset W} {pi : W → ℝ≥0} {kappa kappaOut : ℝ≥0}
    (hF : HasExtensionBound F pi kappa) (h : kappa ≤ kappaOut) :
    HasExtensionBound F pi kappaOut := by
  intro A
  exact (hF A).trans h

/-- Product weights with factors at most one are antitone in the underlying
finite set. -/
lemma setWeight_antitone_of_le_one
    {W : Type*} [DecidableEq W] (pi : W → ℝ≥0)
    (hpi : ∀ x, pi x ≤ 1) {S T : Finset W} (hST : S ⊆ T) :
    setWeight pi T ≤ setWeight pi S := by
  unfold setWeight
  exact Finset.prod_le_prod_of_subset_of_le_one' hST
    (fun x _hx _hxS ↦ hpi x)

/-- If `P` is contained in the sampled reservoir `R`, every extension term
relative to `P` is dominated by the term relative to `R` rooted at `A \ R`.
The root change is essential; a fixed-root monotonicity statement is false.
-/
lemma extensionWeight_sdiff_le_of_selected_subset
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) (pi : W → ℝ≥0)
    (hpi : ∀ x, pi x ≤ 1) {P R : Finset W} (hPR : P ⊆ R)
    (A : Finset W) :
    extensionWeight (fun i ↦ F i \ P) pi A ≤
      extensionWeight (fun i ↦ F i \ R) pi (A \ R) := by
  classical
  unfold extensionWeight
  apply sum_le_sum
  intro i _hi
  by_cases hA : A ⊆ F i \ P
  · have hAR : A \ R ⊆ F i \ R := by
      intro x hx
      have hxA : x ∈ A := (mem_sdiff.mp hx).1
      have hxR : x ∉ R := (mem_sdiff.mp hx).2
      have hxFP := mem_sdiff.mp (hA hxA)
      exact mem_sdiff.mpr ⟨hxFP.1, hxR⟩
    rw [if_pos hA, if_pos hAR]
    apply setWeight_antitone_of_le_one pi hpi
    intro x hx
    have hxFR := mem_sdiff.mp (mem_sdiff.mp hx).1
    have hxNotAR := (mem_sdiff.mp hx).2
    have hxNotA : x ∉ A := by
      intro hxA
      exact hxNotAR (mem_sdiff.mpr ⟨hxA, hxFR.2⟩)
    exact mem_sdiff.mpr
      ⟨mem_sdiff.mpr ⟨hxFR.1, fun hxP ↦ hxFR.2 (hPR hxP)⟩, hxNotA⟩
  · rw [if_neg hA]
    exact zero_le

/-- A uniform extension bound proved after deleting the whole reservoir also
holds after deleting any selected subfamily of that reservoir. -/
theorem HasExtensionBound.of_subset_selected
    {W I : Type*} [DecidableEq W] [Fintype I]
    {F : I → Finset W} {pi : W → ℝ≥0} {kappa : ℝ≥0}
    (hpi : ∀ x, pi x ≤ 1) {P R : Finset W} (hPR : P ⊆ R)
    (hR : HasExtensionBound (fun i ↦ F i \ R) pi kappa) :
    HasExtensionBound (fun i ↦ F i \ P) pi kappa := by
  intro A
  exact (extensionWeight_sdiff_le_of_selected_subset
    F pi hpi hPR A).trans (hR (A \ R))

end

end Erdos207

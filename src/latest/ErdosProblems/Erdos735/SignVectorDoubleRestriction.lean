/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.SignVectorArrangement

/-!
# Deletion--restriction inside a fixed central plane

This file begins the one-dimensional region count required for the projective arrangement. It
proves that a sign cone feasible on `ker h` is split by `k` exactly when it is feasible on the
double restriction `ker h ∩ ker k`. The perturbation stays inside `ker h` and uses the squared norm
of `h × k` for strict positivity.
-/

open scoped BigOperators Matrix
open Matrix

namespace Erdos735.SignVector

noncomputable section

def RestrictedExtensionRealizable {I : Type*}
    (n : I → Vec3) (h k : Vec3) (s : I → Bool) (b : Bool) : Prop :=
  ∃ x, Realizes n s x ∧ h ⬝ᵥ x = 0 ∧ 0 < signed b (k ⬝ᵥ x)

def DoubleRestrictedRealizable {I : Type*}
    (n : I → Vec3) (h k : Vec3) (s : I → Bool) : Prop :=
  ∃ x, Realizes n s x ∧ h ⬝ᵥ x = 0 ∧ k ⬝ᵥ x = 0

/-- The component of `k` in `ker h`, with denominators cleared. -/
def kernelPerturbation (h k : Vec3) : Vec3 :=
  (h ⬝ᵥ h) • k - (h ⬝ᵥ k) • h

@[simp] theorem dot_kernelPerturbation_left (h k : Vec3) :
    h ⬝ᵥ kernelPerturbation h k = 0 := by
  simp [kernelPerturbation, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

theorem dot_kernelPerturbation_right (h k : Vec3) :
    k ⬝ᵥ kernelPerturbation h k = (h ⨯₃ k) ⬝ᵥ (h ⨯₃ k) := by
  rw [cross_dot_cross]
  simp [kernelPerturbation, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_comm]

theorem dot_kernelPerturbation_right_pos {h k : Vec3} (hind : h ⨯₃ k ≠ 0) :
    0 < k ⬝ᵥ kernelPerturbation h k := by
  rw [dot_kernelPerturbation_right]
  exact dotProduct_self_pos hind

/-- Deletion--restriction inside `ker h`: a cone is feasible on the double kernel exactly when
both signs of `k` occur while retaining the equation `h · x = 0`. -/
theorem doubleRestrictedRealizable_iff_restrictedExtensions
    {I : Type*} [Fintype I] (n : I → Vec3) {h k : Vec3}
    (hind : h ⨯₃ k ≠ 0) (s : I → Bool) :
    DoubleRestrictedRealizable n h k s ↔
      RestrictedExtensionRealizable n h k s true ∧
        RestrictedExtensionRealizable n h k s false := by
  constructor
  · rintro ⟨x, hx, hx_h, hx_k⟩
    obtain ⟨c, hc, hplus, hminus⟩ :=
      exists_small_perturbation n s hx (kernelPerturbation h k)
    have hvk := dot_kernelPerturbation_right_pos hind
    constructor
    · refine ⟨x + c • kernelPerturbation h k, hplus, ?_, ?_⟩
      · simp [dotProduct_add, dotProduct_smul, smul_eq_mul, hx_h]
      · simpa [signed, dotProduct_add, dotProduct_smul, smul_eq_mul, hx_k] using
          mul_pos hc hvk
    · refine ⟨x - c • kernelPerturbation h k, hminus, ?_, ?_⟩
      · simp [dotProduct_sub, dotProduct_smul, smul_eq_mul, hx_h]
      · simpa [signed, dotProduct_sub, dotProduct_smul, smul_eq_mul, hx_k] using
          mul_pos hc hvk
  · rintro ⟨⟨xp, hxp, hp_h, hp⟩, ⟨xm, hxm, hm_h, hm⟩⟩
    have hp' : 0 < k ⬝ᵥ xp := by simpa [signed] using hp
    have hm' : k ⬝ᵥ xm < 0 := by simpa [signed] using hm
    let a : ℝ := k ⬝ᵥ xp
    let b : ℝ := k ⬝ᵥ xm
    have ha : 0 < a := hp'
    have hb : b < 0 := hm'
    have hden : 0 < a - b := by linarith
    let alpha : ℝ := -b / (a - b)
    let beta : ℝ := a / (a - b)
    have halpha : 0 < alpha := div_pos (neg_pos.mpr hb) hden
    have hbeta : 0 < beta := div_pos ha hden
    let z : Vec3 := alpha • xp + beta • xm
    refine ⟨z, ?_, ?_, ?_⟩
    · intro i
      simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul,
        signed_add, signed_mul]
      nlinarith [hxp i, hxm i]
    · simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [hp_h, hm_h]
      ring
    · simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul]
      change alpha * a + beta * b = 0
      dsimp only [alpha, beta]
      field_simp
      ring

theorem restrictedRealizable_iff_restrictedExtension_true_or_false
    {I : Type*} [Fintype I] (n : I → Vec3) {h k : Vec3}
    (hind : h ⨯₃ k ≠ 0) (s : I → Bool) :
    RestrictedRealizable n h s ↔
      RestrictedExtensionRealizable n h k s true ∨
        RestrictedExtensionRealizable n h k s false := by
  constructor
  · rintro ⟨x, hx, hx_h⟩
    rcases lt_trichotomy (k ⬝ᵥ x) 0 with hkneg | hkzero | hkpos
    · right
      exact ⟨x, hx, hx_h, by simpa [signed] using hkneg⟩
    · obtain ⟨c, hc, hplus, -⟩ :=
        exists_small_perturbation n s hx (kernelPerturbation h k)
      have hvk := dot_kernelPerturbation_right_pos hind
      left
      refine ⟨x + c • kernelPerturbation h k, hplus, ?_, ?_⟩
      · simp [dotProduct_add, dotProduct_smul, smul_eq_mul, hx_h]
      · simpa [signed, dotProduct_add, dotProduct_smul, smul_eq_mul, hkzero] using
          mul_pos hc hvk
    · left
      exact ⟨x, hx, hx_h, by simpa [signed] using hkpos⟩
  · rintro (⟨x, hx, hx_h, -⟩ | ⟨x, hx, hx_h, -⟩) <;>
      exact ⟨x, hx, hx_h⟩

noncomputable def restrictedExtensionFacePatterns {I : Type*} [Fintype I]
    (n : I → Vec3) (h k : Vec3) : Finset ((I → Bool) × Bool) := by
  classical
  exact Finset.univ.filter fun p ↦ RestrictedExtensionRealizable n h k p.1 p.2

noncomputable def doubleRestrictedFacePatterns {I : Type*} [Fintype I]
    (n : I → Vec3) (h k : Vec3) : Finset (I → Bool) := by
  classical
  exact Finset.univ.filter (DoubleRestrictedRealizable n h k)

noncomputable def restrictedExtensionFaceCount {I : Type*} [Fintype I]
    (n : I → Vec3) (h k : Vec3) : ℕ :=
  (restrictedExtensionFacePatterns n h k).card

noncomputable def doubleRestrictedFaceCount {I : Type*} [Fintype I]
    (n : I → Vec3) (h k : Vec3) : ℕ :=
  (doubleRestrictedFacePatterns n h k).card

/-- Inclusion--exclusion for the two new signs inside `ker h`. -/
theorem restrictedExtensionFaceCount_eq_add_doubleRestrictedFaceCount
    {I : Type*} [Fintype I] (n : I → Vec3) {h k : Vec3}
    (hind : h ⨯₃ k ≠ 0) :
    restrictedExtensionFaceCount n h k =
      restrictedFaceCount n h + doubleRestrictedFaceCount n h k := by
  classical
  let oldIndicator : (I → Bool) → ℕ := fun s ↦
    if RestrictedRealizable n h s then 1 else 0
  let doubleIndicator : (I → Bool) → ℕ := fun s ↦
    if DoubleRestrictedRealizable n h k s then 1 else 0
  let extensionIndicator : (I → Bool) → Bool → ℕ := fun s b ↦
    if RestrictedExtensionRealizable n h k s b then 1 else 0
  have hpoint (s : I → Bool) :
      extensionIndicator s true + extensionIndicator s false =
        oldIndicator s + doubleIndicator s := by
    have hor := restrictedRealizable_iff_restrictedExtension_true_or_false n hind s
    have hand := doubleRestrictedRealizable_iff_restrictedExtensions n hind s
    simp only [extensionIndicator, oldIndicator, doubleIndicator]
    by_cases hp : RestrictedExtensionRealizable n h k s true <;>
      by_cases hm : RestrictedExtensionRealizable n h k s false <;>
      simp [hp, hm, hor, hand]
  calc
    restrictedExtensionFaceCount n h k =
        ∑ p : (I → Bool) × Bool,
          if RestrictedExtensionRealizable n h k p.1 p.2 then 1 else 0 := by
      rw [restrictedExtensionFaceCount, restrictedExtensionFacePatterns,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ s : I → Bool, ∑ b : Bool, extensionIndicator s b := by
      rw [← Finset.univ_product_univ]
      exact Finset.sum_product _ _ _
    _ = ∑ s : I → Bool,
        (extensionIndicator s true + extensionIndicator s false) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Fintype.sum_bool]
    _ = ∑ s : I → Bool, (oldIndicator s + doubleIndicator s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hpoint s
    _ = (∑ s : I → Bool, oldIndicator s) +
          ∑ s : I → Bool, doubleIndicator s := Finset.sum_add_distrib
    _ = restrictedFaceCount n h + doubleRestrictedFaceCount n h k := by
      simp only [oldIndicator, doubleIndicator, restrictedFaceCount,
        restrictedFacePatterns, doubleRestrictedFaceCount, doubleRestrictedFacePatterns,
        Finset.card_eq_sum_ones, Finset.sum_filter]

lemma restrictedRealizable_insertNormal_iff_restrictedExtensionRealizable
    {I : Type*} (n : I → Vec3) (h k : Vec3) (s : Option I → Bool) :
    RestrictedRealizable (insertNormal n k) h s ↔
      RestrictedExtensionRealizable n h k (optionSignEquiv s).1 (optionSignEquiv s).2 := by
  constructor
  · rintro ⟨x, hx, hx_h⟩
    exact ⟨x, (fun i ↦ hx (some i)), hx_h, hx none⟩
  · rintro ⟨x, hx, hx_h, hxk⟩
    refine ⟨x, fun i ↦ ?_, hx_h⟩
    cases i with
    | none => exact hxk
    | some i => exact hx i

theorem restrictedFaceCount_insertNormal_eq_restrictedExtensionFaceCount
    {I : Type*} [Fintype I] (n : I → Vec3) (h k : Vec3) :
    restrictedFaceCount (insertNormal n k) h = restrictedExtensionFaceCount n h k := by
  classical
  have hmap :
      restrictedExtensionFacePatterns n h k =
        (restrictedFacePatterns (insertNormal n k) h).map optionSignEquiv.toEmbedding := by
    ext p
    constructor
    · intro hp
      have hp' : RestrictedExtensionRealizable n h k p.1 p.2 := by
        simpa [restrictedExtensionFacePatterns] using hp
      refine Finset.mem_map.mpr ⟨optionSignEquiv.symm p, ?_, ?_⟩
      · simp only [restrictedFacePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (restrictedRealizable_insertNormal_iff_restrictedExtensionRealizable n h k _).mpr
          (by simpa using hp')
      · exact optionSignEquiv.apply_symm_apply p
    · intro hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hp
      simp only [restrictedExtensionFacePatterns, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (restrictedRealizable_insertNormal_iff_restrictedExtensionRealizable n h k s).mp
        (by simpa [restrictedFacePatterns] using hs)
  simp only [restrictedFaceCount, restrictedExtensionFaceCount]
  rw [hmap, Finset.card_map]

/-- Deletion--restriction recurrence inside the fixed plane `ker h`. -/
theorem restrictedFaceCount_insertNormal
    {I : Type*} [Fintype I] (n : I → Vec3) {h k : Vec3}
    (hind : h ⨯₃ k ≠ 0) :
    restrictedFaceCount (insertNormal n k) h =
      restrictedFaceCount n h + doubleRestrictedFaceCount n h k := by
  rw [restrictedFaceCount_insertNormal_eq_restrictedExtensionFaceCount]
  exact restrictedExtensionFaceCount_eq_add_doubleRestrictedFaceCount n hind

end

end Erdos735.SignVector
